use crate::constraint::ConstraintOps;
use crate::fast_lock::FastLock;
use crate::nf::NF;
use crate::node::{step_node, Node, NodeStep};
use crate::queue::{BlockedOn, QueueWaker, WakeHub};
use crate::rel::{Rel, RelId};
use crate::term::TermStore;
use dashmap::DashMap;
use rustc_hash::FxHashSet;
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::Arc;

use super::{CallMode, PipeWork, Work, WorkStep};

// FixWork: Call-context tabling for recursive calls
// ============================================================================

type BindId = u64;

static NEXT_BIND_ID: AtomicU64 = AtomicU64::new(1);

#[derive(Clone, Debug)]
pub(crate) struct Binding<C: Clone> {
    pub(crate) rel: RelId,
    pub(crate) id: BindId,
    pub(crate) body: Arc<Rel<C>>,
}

/// Environment for Fix bindings (RelId -> Rel body).
///
/// Arc-wrapped Vec for O(1) cloning. bind() copies the Vec since the old
/// Env remains shared, but clone() is just an Arc bump.
#[derive(Clone, Debug, Default)]
pub struct Env<C: Clone> {
    bindings: Arc<Vec<Binding<C>>>,
}

impl<C: Clone> Env<C> {
    /// Create an empty environment.
    pub fn new() -> Self {
        Self {
            bindings: Arc::new(Vec::new()),
        }
    }

    /// Bind a RelId to a Rel body.
    pub fn bind(&self, id: RelId, body: Arc<Rel<C>>) -> Self {
        let binding = Binding {
            rel: id,
            id: NEXT_BIND_ID.fetch_add(1, Ordering::Relaxed),
            body,
        };
        let mut new_bindings = (*self.bindings).clone();
        new_bindings.push(binding);
        Self {
            bindings: Arc::new(new_bindings),
        }
    }

    /// Look up a binding.
    pub(crate) fn lookup(&self, id: RelId) -> Option<&Binding<C>> {
        self.bindings.iter().rev().find(|binding| binding.rel == id)
    }

    /// Check if a binding exists.
    pub fn contains(&self, id: RelId) -> bool {
        self.lookup(id).is_some()
    }
}

/// Key for call-context tabling.
///
/// Identifies a recursive call by its RelId and adjacent boundary constraints.
/// Two calls with the same key should share their tabled answers.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct CallKey<C: ConstraintOps> {
    /// The relation being called.
    pub rel: RelId,
    /// Unique binding id for the Fix scope.
    pub bind_id: BindId,
    /// Left boundary NF (if any).
    pub left: Option<NF<C>>,
    /// Right boundary NF (if any).
    pub right: Option<NF<C>>,
}

impl<C: ConstraintOps> CallKey<C> {
    /// Create a new CallKey.
    pub fn new(rel: RelId, bind_id: BindId, left: Option<NF<C>>, right: Option<NF<C>>) -> Self {
        Self {
            rel,
            bind_id,
            left,
            right,
        }
    }
}

/// State of a tabled call's producer.
#[derive(Clone, Debug, PartialEq)]
pub enum ProducerState {
    /// Producer hasn't started yet.
    NotStarted,
    /// Producer is currently running.
    Running,
    /// Producer has completed.
    Done,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ProducerStep {
    Progress,
    Blocked,
    Done,
}

/// Spec for rebuilding a producer iteration.
#[derive(Clone, Debug)]
pub struct ProducerSpec<C: ConstraintOps> {
    /// CallKey for ReplayOnly protection.
    pub key: Arc<CallKey<C>>,
    /// Body of the Fix relation.
    pub body: Arc<Rel<C>>,
    /// Left boundary to apply for this call.
    pub left: Option<NF<C>>,
    /// Right boundary to apply for this call.
    pub right: Option<NF<C>>,
    /// Environment for resolving Fix bindings.
    pub env: Env<C>,
}

#[derive(Debug)]
pub(crate) struct TableAnswers<C: ConstraintOps> {
    answers: Vec<Arc<NF<C>>>,
    seen: FxHashSet<Arc<NF<C>>>,
    waker: QueueWaker,
}

#[derive(Debug)]
pub(crate) struct TableProducer<C: ConstraintOps> {
    state: ProducerState,
    producer: Option<Node<C>>,
    spec: Option<ProducerSpec<C>>,
    iteration_start_len: usize,
    /// Semi-naive: answers before this index were already composed in
    /// previous iterations. Only answers at index >= replay_watermark
    /// are replayed when building the next iteration's producer.
    replay_watermark: usize,
    producer_task_active: bool,
}

/// A table entry for a recursive call.
///
/// Stores the answers produced so far and the producer state.
#[derive(Debug)]
pub struct Table<C: ConstraintOps> {
    answers: FastLock<TableAnswers<C>>,
    producer: FastLock<TableProducer<C>>,
}

impl<C: ConstraintOps> Table<C> {
    /// Create a new empty table.
    pub fn new() -> Self {
        Self::with_waker(QueueWaker::noop())
    }

    pub fn with_waker(waker: QueueWaker) -> Self {
        Self {
            answers: FastLock::new(TableAnswers {
                answers: Vec::new(),
                seen: FxHashSet::default(),
                waker,
            }),
            producer: FastLock::new(TableProducer {
                state: ProducerState::NotStarted,
                producer: None,
                spec: None,
                iteration_start_len: 0,
                replay_watermark: 0,
                producer_task_active: false,
            }),
        }
    }

    /// Add an answer to the table.
    pub fn add_answer(&self, nf: NF<C>) -> bool {
        let arc_nf = Arc::new(nf);
        let mut answers = self.answers.lock();
        if answers.seen.insert(Arc::clone(&arc_nf)) {
            answers.answers.push(arc_nf);
            answers.waker.wake();
            true
        } else {
            false
        }
    }

    /// Mark the producer as running.
    pub fn start_producer(
        &self,
        producer: Node<C>,
        spec: ProducerSpec<C>,
        iteration_start_len: usize,
    ) {
        let mut guard = self.producer.lock();
        guard.state = ProducerState::Running;
        guard.producer = Some(producer);
        guard.spec = Some(spec);
        guard.iteration_start_len = iteration_start_len;
    }

    /// Ensure producer spec is initialized once.
    pub fn ensure_producer_spec(&self, spec: ProducerSpec<C>) {
        let mut guard = self.producer.lock();
        if guard.spec.is_none() {
            guard.spec = Some(spec);
        }
    }

    /// Mark the producer as done.
    pub fn finish_producer(&self) {
        {
            let mut guard = self.producer.lock();
            guard.state = ProducerState::Done;
            guard.producer = None;
        }
        self.answers.lock().waker.wake();
    }

    /// Check if producer is done.
    pub fn is_done(&self) -> bool {
        self.producer.lock().state == ProducerState::Done
    }

    /// Check if producer is running.
    pub fn is_running(&self) -> bool {
        self.producer.lock().state == ProducerState::Running
    }

    pub fn producer_state(&self) -> ProducerState {
        self.producer.lock().state.clone()
    }

    pub fn producer_task_active(&self) -> bool {
        self.producer.lock().producer_task_active
    }

    pub fn set_producer_task_active(&self, active: bool) {
        self.producer.lock().producer_task_active = active;
    }

    pub fn try_mark_producer_active(&self) -> bool {
        let mut guard = self.producer.lock();
        if guard.producer_task_active || guard.state == ProducerState::Done || guard.spec.is_none()
        {
            false
        } else {
            guard.producer_task_active = true;
            true
        }
    }

    pub fn producer_spec_is_some(&self) -> bool {
        self.producer.lock().spec.is_some()
    }

    pub fn producer_spec_clone(&self) -> Option<ProducerSpec<C>> {
        self.producer.lock().spec.clone()
    }

    pub fn take_producer_node(&self) -> Option<Node<C>> {
        self.producer.lock().producer.take()
    }

    pub fn set_producer_node(&self, node: Node<C>) {
        self.producer.lock().producer = Some(node);
    }

    pub fn iteration_start_len(&self) -> usize {
        self.producer.lock().iteration_start_len
    }

    pub fn set_iteration_start_len(&self, len: usize) {
        self.producer.lock().iteration_start_len = len;
    }

    pub fn replay_watermark(&self) -> usize {
        self.producer.lock().replay_watermark
    }

    pub fn set_replay_watermark(&self, watermark: usize) {
        self.producer.lock().replay_watermark = watermark;
    }

    pub fn producer_has_node(&self) -> bool {
        self.producer.lock().producer.is_some()
    }

    pub fn answers_len(&self) -> usize {
        self.answers.lock().answers.len()
    }

    pub fn answer_at(&self, index: usize) -> Option<Arc<NF<C>>> {
        self.answers.lock().answers.get(index).cloned()
    }

    /// Get all answers.
    pub fn all_answers(&self) -> Vec<Arc<NF<C>>> {
        self.answers.lock().answers.clone()
    }

    /// Get answers starting from the given index (for semi-naive delta replay).
    pub fn answers_from(&self, start: usize) -> Vec<Arc<NF<C>>> {
        let answers = self.answers.lock();
        if start >= answers.answers.len() {
            Vec::new()
        } else {
            answers.answers[start..].to_vec()
        }
    }

    pub fn blocked_on(&self) -> BlockedOn {
        self.answers.lock().waker.blocked_on()
    }
}

#[cfg(test)]
impl<C: ConstraintOps> Table<C> {
    pub(crate) fn lock_answers_for_test(
        &self,
    ) -> crate::fast_lock::FastLockGuard<'_, TableAnswers<C>> {
        self.answers.lock()
    }

    pub(crate) fn try_lock_answers_for_test(
        &self,
    ) -> Option<crate::fast_lock::FastLockGuard<'_, TableAnswers<C>>> {
        self.answers.try_lock()
    }

    pub(crate) fn lock_producer_for_test(
        &self,
    ) -> crate::fast_lock::FastLockGuard<'_, TableProducer<C>> {
        self.producer.lock()
    }

    pub(crate) fn try_lock_producer_for_test(
        &self,
    ) -> Option<crate::fast_lock::FastLockGuard<'_, TableProducer<C>>> {
        self.producer.try_lock()
    }

    pub(crate) fn set_producer_spec_for_test(&self, spec: ProducerSpec<C>, state: ProducerState) {
        let mut guard = self.producer.lock();
        guard.spec = Some(spec);
        guard.state = state;
    }
}

impl<C: ConstraintOps> Default for Table<C> {
    fn default() -> Self {
        Self::new()
    }
}

fn make_replay_producer<C: ConstraintOps>(
    spec: &ProducerSpec<C>,
    tables: &Tables<C>,
    replay_watermark: usize,
) -> Node<C> {
    let mut producer_pipe = PipeWork::from_rel_with_boundaries(
        spec.body.as_ref().clone(),
        spec.left.clone(),
        spec.right.clone(),
        spec.env.clone(),
        tables.clone(),
    );
    producer_pipe.call_mode = CallMode::ReplayOnly(spec.key.clone(), replay_watermark);
    Node::Work(Box::new(Work::Pipe(Box::new(producer_pipe))))
}

pub fn step_table_producer<C: ConstraintOps>(
    table: &Arc<Table<C>>,
    terms: &mut TermStore,
    tables: &Tables<C>,
) -> ProducerStep {
    let state = table.producer_state();
    if state == ProducerState::Done {
        table.set_producer_task_active(false);
        return ProducerStep::Done;
    }

    if state == ProducerState::NotStarted {
        let Some(spec) = table.producer_spec_clone() else {
            table.finish_producer();
            table.set_producer_task_active(false);
            return ProducerStep::Done;
        };
        // First iteration: watermark = 0, replay all existing answers
        let producer_node = make_replay_producer(&spec, tables, 0);
        table.start_producer(producer_node, spec, table.answers_len());
    }

    let current = table.take_producer_node().unwrap_or(Node::Fail);

    let step = step_node(current, terms);
    match step {
        NodeStep::Emit(nf, rest) => {
            let _ = table.add_answer(*nf);
            table.set_producer_node(rest);
            ProducerStep::Progress
        }
        NodeStep::Continue(rest) => {
            table.set_producer_node(rest);
            ProducerStep::Progress
        }
        NodeStep::Exhausted => {
            let has_new = table.answers_len() > table.iteration_start_len();
            if has_new {
                let Some(spec) = table.producer_spec_clone() else {
                    table.finish_producer();
                    table.set_producer_task_active(false);
                    return ProducerStep::Done;
                };
                // Semi-naive: the delta for the next iteration starts at the
                // previous iteration_start_len. Only answers from this index
                // onward will be replayed by ReplayOnly calls.
                let watermark = table.iteration_start_len();
                table.set_replay_watermark(watermark);
                table.set_iteration_start_len(table.answers_len());
                table.set_producer_node(make_replay_producer(&spec, tables, watermark));
                ProducerStep::Progress
            } else {
                table.finish_producer();
                table.set_producer_task_active(false);
                ProducerStep::Done
            }
        }
    }
}

type TableMap<C> = DashMap<CallKey<C>, Arc<Table<C>>>;

/// Collection of tables for call-context tabling.
///
/// Uses a shared concurrent map so all clones see the same tables.
#[derive(Clone, Debug)]
pub struct Tables<C: ConstraintOps> {
    map: Arc<TableMap<C>>,
    wake_hub: Arc<WakeHub>,
}

impl<C: ConstraintOps> Tables<C> {
    /// Create an empty Tables collection.
    pub fn new() -> Self {
        let (wake_hub, _rx) = WakeHub::new();
        Self {
            map: Arc::new(DashMap::new()),
            wake_hub,
        }
    }

    /// Look up a table by CallKey.
    pub fn lookup(&self, key: &CallKey<C>) -> Option<Arc<Table<C>>> {
        self.map.get(key).map(|entry| entry.value().clone())
    }

    /// Get or create a table for a CallKey.
    pub fn get_or_create(&self, key: &CallKey<C>) -> Arc<Table<C>> {
        if let Some(table) = self.map.get(key) {
            return table.value().clone();
        }
        let table = Arc::new(Table::with_waker(self.waker()));
        let entry = self.map.entry(key.clone()).or_insert(table.clone());
        entry.value().clone()
    }

    pub fn waker(&self) -> QueueWaker {
        self.wake_hub.waker()
    }
}

impl<C: ConstraintOps> Default for Tables<C> {
    fn default() -> Self {
        Self::new()
    }
}

/// Result of stepping a FixWork in-place (no allocation).
pub enum FixStepResult<C: ConstraintOps> {
    /// Emit an answer; FixWork has been updated in-place for continuation.
    Emit(NF<C>),
    /// No answer yet; FixWork has been updated in-place for continuation.
    More,
    /// Done; no more answers.
    Done,
}

/// FixWork: table handle that streams answers and steps the producer inline.
///
/// The producer runs in iterations. Each iteration evaluates the body with
/// replay-only calls for the current CallKey.
#[derive(Clone, Debug)]
pub struct FixWork<C: ConstraintOps> {
    /// The CallKey for this tabled call (Arc-wrapped for O(1) clone).
    pub key: Arc<CallKey<C>>,
    /// Reference to the table.
    pub table: Arc<Table<C>>,
    /// Current answer index for this handle.
    pub answer_index: usize,
    /// Tables for nested calls.
    pub tables: Tables<C>,
}

impl<C: ConstraintOps> FixWork<C> {
    /// Create a new FixWork handle.
    pub fn new(
        key: Arc<CallKey<C>>,
        table: Arc<Table<C>>,
        start_index: usize,
        tables: Tables<C>,
    ) -> Self {
        Self {
            key,
            table,
            answer_index: start_index,
            tables,
        }
    }

    /// Step this FixWork handle, allocating a new Box<Work> for continuation.
    pub fn step(&mut self, terms: &mut TermStore) -> WorkStep<C> {
        match self.step_in_place(terms) {
            FixStepResult::Emit(nf) => WorkStep::Emit(nf, Box::new(Work::Fix(self.clone()))),
            FixStepResult::More => WorkStep::More(Box::new(Work::Fix(self.clone()))),
            FixStepResult::Done => WorkStep::Done,
        }
    }

    /// Step this FixWork handle in-place (no clone, no allocation).
    ///
    /// Modifies `answer_index` and returns the step outcome.
    /// The caller can reuse the existing Box<Work> instead of allocating.
    pub fn step_in_place(&mut self, terms: &mut TermStore) -> FixStepResult<C> {
        if let Some(arc_nf) = self.table.answer_at(self.answer_index) {
            self.answer_index += 1;
            return FixStepResult::Emit(Arc::unwrap_or_clone(arc_nf));
        }

        if self.table.is_done() {
            return FixStepResult::Done;
        }

        if !self.table.try_mark_producer_active() {
            if self.table.is_done() {
                return FixStepResult::Done;
            }
            return FixStepResult::More;
        }

        let step = step_table_producer(&self.table, terms, &self.tables);
        self.table.set_producer_task_active(false);

        if let Some(arc_nf) = self.table.answer_at(self.answer_index) {
            self.answer_index += 1;
            return FixStepResult::Emit(Arc::unwrap_or_clone(arc_nf));
        }

        match step {
            ProducerStep::Done => FixStepResult::Done,
            ProducerStep::Progress | ProducerStep::Blocked => FixStepResult::More,
        }
    }
}
