use crate::constraint::ConstraintOps;
use crate::fast_lock::FastLock;
use crate::nf::NF;
use crate::node::{step_node, Node, NodeStep};
use crate::queue::{BlockedOn, QueueWaker, WakeHub};
use crate::rel::{Rel, RelId};
use crate::term::TermStore;
use dashmap::DashMap;
use rustc_hash::FxHashMap;
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::Arc;

use super::{CallMode, PipeWork, U64HashSet, Work, WorkStep};

// FixWork: Call-context tabling for recursive calls
// ============================================================================

type BindId = u64;

static NEXT_BIND_ID: AtomicU64 = AtomicU64::new(1);

#[derive(Clone, Debug)]
pub(crate) struct Binding<C: Clone> {
    pub(crate) id: BindId,
    pub(crate) body: Arc<Rel<C>>,
}

/// Environment for Fix bindings (RelId -> Rel body).
///
/// Uses FxHashMap for O(1) lookup. Arc-wrapped for O(1) cloning.
/// bind() uses Arc::make_mut for copy-on-write: when the Arc has a single
/// owner (common during env construction), the map is mutated in place
/// without cloning.
#[derive(Clone, Debug)]
pub struct Env<C: Clone> {
    map: Arc<FxHashMap<RelId, Binding<C>>>,
}

impl<C: Clone> Default for Env<C> {
    fn default() -> Self {
        Self::new()
    }
}

impl<C: Clone> Env<C> {
    /// Create an empty environment.
    pub fn new() -> Self {
        Self {
            map: Arc::new(FxHashMap::default()),
        }
    }

    /// Bind a RelId to a Rel body.
    pub fn bind(&self, id: RelId, body: Arc<Rel<C>>) -> Self {
        let binding = Binding {
            id: NEXT_BIND_ID.fetch_add(1, Ordering::Relaxed),
            body,
        };
        let mut new_map = Arc::clone(&self.map);
        Arc::make_mut(&mut new_map).insert(id, binding);
        Self { map: new_map }
    }

    /// Build an environment from a map of named relations.
    /// Only `Rel::Fix` entries are bound (others are ignored).
    pub fn from_defs<S: std::borrow::Borrow<str>>(
        defs: &std::collections::HashMap<S, Rel<C>>,
    ) -> Self {
        let mut env = Self::new();
        for rel in defs.values() {
            if let Rel::Fix(id, body) = rel {
                env = env.bind(*id, body.clone());
            }
        }
        env
    }

    /// Look up a binding.
    pub(crate) fn lookup(&self, id: RelId) -> Option<&Binding<C>> {
        self.map.get(&id)
    }

    /// Check if a binding exists.
    pub fn contains(&self, id: RelId) -> bool {
        self.map.contains_key(&id)
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
    answers: Vec<NF<C>>,
    seen: U64HashSet,
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
                seen: U64HashSet::default(),
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
        let mut answers = self.answers.lock();
        if answers.seen.insert(nf.hash_value()) {
            answers.answers.push(nf);
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

    /// Initialize producer for first iteration.
    ///
    /// If spec exists, builds a replay producer, starts it, and returns `Some(spec)`.
    /// If no spec, finishes the producer and returns `None`.
    /// Consolidates `producer_state + producer_spec_clone + start_producer + answers_len`
    /// into two lock acquisitions instead of four.
    fn initialize_producer(&self) -> Option<ProducerSpec<C>> {
        let mut guard = self.producer.lock();
        let spec = guard.spec.clone()?;
        let answers_len = self.answers.lock().answers.len();
        guard.state = ProducerState::Running;
        guard.iteration_start_len = answers_len;
        Some(spec)
    }

    /// Try to advance to the next fixpoint iteration after producer exhaustion.
    ///
    /// Returns `Some(spec, watermark)` if new answers exist (iteration should continue),
    /// or `None` if fixpoint reached (no new answers).
    /// Consolidates `answers_len + iteration_start_len + producer_spec_clone +
    /// set_replay_watermark + set_iteration_start_len` into two lock acquisitions.
    fn try_advance_iteration(&self) -> Option<(ProducerSpec<C>, usize)> {
        let mut guard = self.producer.lock();
        let answers_len = self.answers.lock().answers.len();
        if answers_len <= guard.iteration_start_len {
            return None;
        }
        let spec = guard.spec.clone()?;
        let watermark = guard.iteration_start_len;
        guard.replay_watermark = watermark;
        guard.iteration_start_len = answers_len;
        Some((spec, watermark))
    }

    /// Mark the producer as done.
    pub fn finish_producer(&self) {
        {
            let mut guard = self.producer.lock();
            guard.state = ProducerState::Done;
            guard.producer = None;
            guard.producer_task_active = false;
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

    pub fn take_producer_node(&self) -> Option<Node<C>> {
        self.producer.lock().producer.take()
    }

    pub fn set_producer_node(&self, node: Node<C>) {
        self.producer.lock().producer = Some(node);
    }

    pub fn producer_has_node(&self) -> bool {
        self.producer.lock().producer.is_some()
    }

    pub fn answers_len(&self) -> usize {
        self.answers.lock().answers.len()
    }

    pub fn answer_at(&self, index: usize) -> Option<NF<C>> {
        self.answers.lock().answers.get(index).cloned()
    }

    /// Get all answers.
    pub fn all_answers(&self) -> Vec<NF<C>> {
        self.answers.lock().answers.clone()
    }

    /// Get answers starting from the given index (for semi-naive delta replay).
    pub fn answers_from(&self, start: usize) -> Vec<NF<C>> {
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
        return ProducerStep::Done;
    }

    if state == ProducerState::NotStarted {
        let Some(spec) = table.initialize_producer() else {
            table.finish_producer();
            return ProducerStep::Done;
        };
        // First iteration: watermark = 0, replay all existing answers
        let producer_node = make_replay_producer(&spec, tables, 0);
        table.set_producer_node(producer_node);
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
            if let Some((spec, watermark)) = table.try_advance_iteration() {
                // Semi-naive: the delta for the next iteration starts at the
                // previous iteration_start_len. Only answers from this index
                // onward will be replayed by ReplayOnly calls.
                table.set_producer_node(make_replay_producer(&spec, tables, watermark));
                ProducerStep::Progress
            } else {
                table.finish_producer();
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
        let waker = self.waker();
        self.map
            .entry(key.clone())
            .or_insert_with(|| Arc::new(Table::with_waker(waker)))
            .value()
            .clone()
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

use super::InPlaceStepResult;

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
            InPlaceStepResult::Emit(nf) => WorkStep::Emit(nf, Box::new(Work::Fix(self.clone()))),
            InPlaceStepResult::More => WorkStep::More(Box::new(Work::Fix(self.clone()))),
            InPlaceStepResult::Done => WorkStep::Done,
        }
    }

    /// Step this FixWork handle in-place (no clone, no allocation).
    ///
    /// Modifies `answer_index` and returns the step outcome.
    /// The caller can reuse the existing Box<Work> instead of allocating.
    pub fn step_in_place(&mut self, terms: &mut TermStore) -> InPlaceStepResult<C> {
        if let Some(nf) = self.table.answer_at(self.answer_index) {
            self.answer_index += 1;
            return InPlaceStepResult::Emit(nf);
        }

        if self.table.is_done() {
            return InPlaceStepResult::Done;
        }

        if !self.table.try_mark_producer_active() {
            if self.table.is_done() {
                return InPlaceStepResult::Done;
            }
            return InPlaceStepResult::More;
        }

        let step = step_table_producer(&self.table, terms, &self.tables);
        self.table.set_producer_task_active(false);

        if let Some(nf) = self.table.answer_at(self.answer_index) {
            self.answer_index += 1;
            return InPlaceStepResult::Emit(nf);
        }

        match step {
            ProducerStep::Done => InPlaceStepResult::Done,
            ProducerStep::Progress | ProducerStep::Blocked => InPlaceStepResult::More,
        }
    }
}
