use crate::constraint::ConstraintOps;
use crate::nf::NF;
use crate::node::{step_node, Node, NodeStep};
use crate::term::TermStore;
use crate::work::{step_bind_producer, step_table_producer, ProducerStep, Tables, Work};
use crossbeam_deque::Injector;
use std::sync::atomic::{AtomicBool, AtomicUsize, Ordering};
use std::sync::Arc;

use crate::join::{AndJoiner, JoinStep};
use crate::queue::{AnswerQueue, AnswerSink, BlockedOn, SinkResult, WakeHub};

pub enum Task<C: ConstraintOps> {
    Search(SearchTask<C>),
    Join(JoinTask<C>),
    FixProducer(FixProducerTask<C>),
    BindProducer(BindProducerTask<C>),
    #[cfg(test)]
    TestBlocked(TestBlockedTask<C>),
}

#[derive(Debug, Clone)]
pub enum TaskStatus {
    Progress,
    Blocked(BlockedOn),
    Done,
}

pub struct TaskContext<C: ConstraintOps> {
    pub terms: Arc<TermStore>,
    pub injector: Arc<Injector<Task<C>>>,
    pub pending: Arc<AtomicUsize>,
    pub budget: usize,
    pub queue_bound: usize,
    pub wake_hub: Arc<WakeHub>,
    pub cancelled: Arc<AtomicBool>,
}

impl<C: ConstraintOps> TaskContext<C> {
    pub fn spawn(&self, task: Task<C>) {
        if self.cancelled.load(Ordering::Acquire) {
            return;
        }
        self.pending.fetch_add(1, Ordering::AcqRel);
        self.injector.push(task);
    }
}

impl<C: ConstraintOps> Task<C> {
    pub fn run(&mut self, ctx: &TaskContext<C>) -> TaskStatus {
        if ctx.cancelled.load(Ordering::Acquire) {
            return TaskStatus::Done;
        }
        match self {
            Task::Search(task) => task.run(ctx),
            Task::Join(task) => task.run(ctx),
            Task::FixProducer(task) => task.run(ctx),
            Task::BindProducer(task) => task.run(ctx),
            #[cfg(test)]
            Task::TestBlocked(task) => task.run(ctx),
        }
    }
}

#[cfg(test)]
pub struct TestBlockedTask<C: ConstraintOps> {
    runs: Arc<AtomicUsize>,
    kind: TestBlockedKind,
    _marker: std::marker::PhantomData<C>,
}

#[cfg(test)]
enum TestBlockedKind {
    Forever { waker: crate::queue::QueueWaker },
    Once { blocked_on: BlockedOn, done: bool },
}

#[cfg(test)]
impl<C: ConstraintOps> TestBlockedTask<C> {
    pub fn block_forever(runs: Arc<AtomicUsize>, waker: crate::queue::QueueWaker) -> Self {
        Self {
            runs,
            kind: TestBlockedKind::Forever { waker },
            _marker: std::marker::PhantomData,
        }
    }

    pub fn block_once(runs: Arc<AtomicUsize>, blocked_on: BlockedOn) -> Self {
        Self {
            runs,
            kind: TestBlockedKind::Once {
                blocked_on,
                done: false,
            },
            _marker: std::marker::PhantomData,
        }
    }

    fn run(&mut self, _ctx: &TaskContext<C>) -> TaskStatus {
        self.runs.fetch_add(1, Ordering::AcqRel);
        match &mut self.kind {
            TestBlockedKind::Forever { waker } => TaskStatus::Blocked(waker.blocked_on()),
            TestBlockedKind::Once { blocked_on, done } => {
                if *done {
                    TaskStatus::Done
                } else {
                    *done = true;
                    TaskStatus::Blocked(blocked_on.clone())
                }
            }
        }
    }
}

pub struct FixProducerTask<C: ConstraintOps> {
    table: Arc<crate::work::Table<C>>,
    tables: Tables<C>,
}

impl<C: ConstraintOps> FixProducerTask<C> {
    pub fn new(table: Arc<crate::work::Table<C>>, tables: Tables<C>) -> Self {
        Self { table, tables }
    }

    pub fn run(&mut self, ctx: &TaskContext<C>) -> TaskStatus {
        let step = step_table_producer(&self.table, ctx.terms.as_ref(), &self.tables);
        match step {
            ProducerStep::Done => TaskStatus::Done,
            ProducerStep::Blocked => TaskStatus::Blocked(self.table.blocked_on()),
            ProducerStep::Progress => TaskStatus::Progress,
        }
    }
}

pub struct BindProducerTask<C: ConstraintOps> {
    state: Arc<parking_lot::Mutex<crate::work::BindProducerState<C>>>,
}

impl<C: ConstraintOps> BindProducerTask<C> {
    pub fn new(state: Arc<parking_lot::Mutex<crate::work::BindProducerState<C>>>) -> Self {
        Self { state }
    }

    pub fn run(&mut self, ctx: &TaskContext<C>) -> TaskStatus {
        let step = step_bind_producer(&self.state, ctx.terms.as_ref());
        match step {
            ProducerStep::Done => TaskStatus::Done,
            ProducerStep::Blocked => TaskStatus::Blocked(self.state.lock().blocked_on()),
            ProducerStep::Progress => TaskStatus::Progress,
        }
    }
}

pub struct SearchTask<C: ConstraintOps> {
    node: Node<C>,
    sink: Option<AnswerSink<C>>,
    pending_out: Option<NF<C>>,
    pending_done: bool,
}

impl<C: ConstraintOps> SearchTask<C> {
    pub fn new(node: Node<C>, sink: AnswerSink<C>) -> Self {
        Self {
            node,
            sink: Some(sink),
            pending_out: None,
            pending_done: false,
        }
    }

    fn ensure_fix_producer(&mut self, ctx: &TaskContext<C>) {
        let fix = match &self.node {
            Node::Work(work) => match work.as_ref() {
                Work::Fix(fix) => Some(fix),
                _ => None,
            },
            _ => None,
        };
        let Some(fix) = fix else {
            return;
        };
        if fix.table.try_mark_producer_active() {
            ctx.spawn(Task::FixProducer(FixProducerTask::new(
                fix.table.clone(),
                fix.tables.clone(),
            )));
        }
    }

    fn ensure_bind_producer(&mut self, ctx: &TaskContext<C>) {
        let bind = match &self.node {
            Node::Work(work) => match work.as_ref() {
                Work::Bind(bind) => Some(bind),
                _ => None,
            },
            _ => None,
        };
        let Some(bind) = bind else {
            return;
        };
        let state = bind.producer_state();
        let mut guard = state.lock();
        if guard.is_active() || guard.is_closed() {
            return;
        }
        guard.mark_active();
        drop(guard);
        ctx.spawn(Task::BindProducer(BindProducerTask::new(state)));
    }

    fn try_split_and(&mut self, ctx: &TaskContext<C>) -> bool {
        if self.pending_out.is_some() {
            return false;
        }

        let work_box = match &mut self.node {
            Node::Work(work) => work,
            _ => return false,
        };

        let work = std::mem::replace(work_box, Box::new(Work::Done));
        let (parts, seen, pending, turn) = match *work {
            Work::AndGroup(group) => (group.parts, group.seen, group.pending, group.turn),
            Work::Meet(meet) => {
                let left = *meet.left;
                let right = *meet.right;
                let seen = vec![meet.seen_l, meet.seen_r];
                let pending = meet.pending;
                let turn = if meet.flip { 1 } else { 0 };
                (vec![left, right], seen, pending, turn)
            }
            other => {
                **work_box = other;
                return false;
            }
        };

        let sink = match self.sink.take() {
            Some(sink) => sink,
            None => return false,
        };

        let join_waker = ctx.wake_hub.waker();
        let mut receivers = Vec::with_capacity(parts.len());
        let mut done = Vec::with_capacity(parts.len());

        for part in parts {
            let (tx, rx) =
                AnswerQueue::bounded_with_waker::<C>(ctx.queue_bound, join_waker.clone());
            let is_done = matches!(part, Node::Fail);
            if !is_done {
                ctx.spawn(Task::Search(SearchTask::new(part, AnswerSink::Queue(tx))));
            }
            receivers.push(rx);
            done.push(is_done);
        }

        let joiner = AndJoiner::from_state(receivers, done, seen, pending, turn, join_waker);
        ctx.spawn(Task::Join(JoinTask::new(joiner, sink)));
        self.node = Node::Fail;
        true
    }

    pub fn run(&mut self, ctx: &TaskContext<C>) -> TaskStatus {
        if self.sink.is_none() {
            return TaskStatus::Done;
        }

        if let Some(nf) = self.pending_out.take() {
            match self.sink.as_mut().unwrap().push(nf.clone()) {
                SinkResult::Accepted => {
                    if self.pending_done {
                        self.pending_done = false;
                        self.sink = None;
                        return TaskStatus::Done;
                    }
                }
                SinkResult::Full => {
                    self.pending_out = Some(nf);
                    let blocked = self
                        .sink
                        .as_ref()
                        .and_then(|sink| sink.blocked_on())
                        .expect("queue sink should provide a waker");
                    return TaskStatus::Blocked(blocked);
                }
                SinkResult::Closed => return TaskStatus::Done,
            }
        }

        let budget = ctx.budget.max(1);
        for _ in 0..budget {
            self.ensure_fix_producer(ctx);
            self.ensure_bind_producer(ctx);
            if self.try_split_and(ctx) {
                return TaskStatus::Done;
            }

            let current = std::mem::replace(&mut self.node, Node::Fail);
            match step_node(current, ctx.terms.as_ref()) {
                NodeStep::Emit(nf, rest) => {
                    self.node = rest;
                    let is_done = matches!(self.node, Node::Fail);
                    match self.sink.as_mut().unwrap().push(nf.clone()) {
                        SinkResult::Accepted => {
                            if is_done {
                                self.sink = None;
                                return TaskStatus::Done;
                            }
                            return TaskStatus::Progress;
                        }
                        SinkResult::Full => {
                            self.pending_out = Some(nf);
                            self.pending_done = is_done;
                            let blocked = self
                                .sink
                                .as_ref()
                                .and_then(|sink| sink.blocked_on())
                                .expect("queue sink should provide a waker");
                            return TaskStatus::Blocked(blocked);
                        }
                        SinkResult::Closed => return TaskStatus::Done,
                    }
                }
                NodeStep::Continue(rest) => {
                    self.node = rest;
                }
                NodeStep::Exhausted => {
                    self.node = Node::Fail;
                    self.sink = None;
                    return TaskStatus::Done;
                }
            }
        }

        TaskStatus::Progress
    }
}

pub struct JoinTask<C: ConstraintOps> {
    joiner: AndJoiner<C>,
    sink: AnswerSink<C>,
}

impl<C: ConstraintOps> JoinTask<C> {
    pub fn new(joiner: AndJoiner<C>, sink: AnswerSink<C>) -> Self {
        Self { joiner, sink }
    }

    pub fn run(&mut self, ctx: &TaskContext<C>) -> TaskStatus {
        match self.joiner.step(ctx.terms.as_ref(), &mut self.sink) {
            JoinStep::Progress => TaskStatus::Progress,
            JoinStep::Blocked(wait) => TaskStatus::Blocked(wait),
            JoinStep::Done => TaskStatus::Done,
        }
    }
}
