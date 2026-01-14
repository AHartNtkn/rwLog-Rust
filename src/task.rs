use crate::goal::{GoalId, RelId};
use crate::nf::NF;
use smallvec::SmallVec;

#[cfg(feature = "tracing")]
use crate::trace::trace;

/// Unique identifier for a task.
pub type TaskId = u32;

/// The state of a task during evaluation.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TaskState<C> {
    /// Task is ready to be stepped.
    Ready,

    /// Task has produced an answer (NF).
    Yielded(NF<C>),

    /// Task is blocked waiting for a relation to produce answers.
    Blocked(RelId),

    /// Task has completed (no more answers).
    Done,
}

/// A continuation frame representing pending work.
///
/// Continuations form a stack that captures what to do
/// after the current goal produces an answer.
#[derive(Debug, Clone)]
pub enum Kont<C> {
    /// Waiting for left side of Seq to produce answers.
    /// Once we get answers, compose each with right_pending.
    SeqNext {
        /// Answers accumulated from left side.
        left_answers: Vec<NF<C>>,
        /// The remaining goals in the sequence.
        remaining: SmallVec<[GoalId; 4]>,
    },

    /// Waiting for left side of Both to produce answers.
    /// Once we get answers, meet each with right side.
    BothNext {
        /// Answers accumulated from left side.
        left_answers: Vec<NF<C>>,
        /// The remaining goals in the conjunction.
        remaining: SmallVec<[GoalId; 4]>,
    },

    /// Waiting for current Alt branch, with remaining branches pending.
    AltNext {
        /// Remaining branches to try if current fails.
        remaining: SmallVec<[GoalId; 4]>,
    },

    /// Processing answers from a Fix relation.
    FixFrame {
        /// The relation being defined.
        rel_id: RelId,
        /// The body of the relation.
        body: GoalId,
        /// The Fix goal ID (for recursive calls).
        fix_goal: GoalId,
    },
}

/// A task represents a unit of work in the evaluator.
///
/// Tasks have:
/// - A current goal being evaluated
/// - A stack of continuations (pending work)
/// - A state (ready, yielded, blocked, done)
/// - An input NF being transformed
#[derive(Debug, Clone)]
pub struct Task<C> {
    /// Unique identifier for this task.
    pub id: TaskId,

    /// The current goal being evaluated.
    pub goal: GoalId,

    /// The continuation stack (what to do after current goal).
    pub kont: SmallVec<[Kont<C>; 8]>,

    /// Current task state.
    pub state: TaskState<C>,

    /// The current input NF being transformed.
    pub input: NF<C>,
}

impl<C: Clone + Default> Task<C> {
    /// Create a new task.
    pub fn new(id: TaskId, goal: GoalId, input: NF<C>) -> Self {
        Self {
            id,
            goal,
            kont: SmallVec::new(),
            state: TaskState::Ready,
            input,
        }
    }

    /// Check if the task is ready to be stepped.
    pub fn is_ready(&self) -> bool {
        matches!(self.state, TaskState::Ready)
    }

    /// Check if the task has yielded an answer.
    pub fn is_yielded(&self) -> bool {
        matches!(self.state, TaskState::Yielded(_))
    }

    /// Check if the task is blocked.
    pub fn is_blocked(&self) -> bool {
        matches!(self.state, TaskState::Blocked(_))
    }

    /// Check if the task is done.
    pub fn is_done(&self) -> bool {
        matches!(self.state, TaskState::Done)
    }

    /// Get the yielded answer, if any.
    pub fn get_answer(&self) -> Option<&NF<C>> {
        match &self.state {
            TaskState::Yielded(nf) => Some(nf),
            _ => None,
        }
    }

    /// Get the relation this task is blocked on, if any.
    pub fn blocked_on(&self) -> Option<RelId> {
        match &self.state {
            TaskState::Blocked(rel_id) => Some(*rel_id),
            _ => None,
        }
    }

    /// Push a continuation onto the stack.
    pub fn push_kont(&mut self, kont: Kont<C>) {
        #[cfg(feature = "tracing")]
        {
            let kont_type = match &kont {
                Kont::SeqNext { .. } => "SeqNext",
                Kont::BothNext { .. } => "BothNext",
                Kont::AltNext { .. } => "AltNext",
                Kont::FixFrame { .. } => "FixFrame",
            };
            trace!(
                task_id = self.id,
                kont_type,
                new_depth = self.kont.len() + 1,
                "push_kont"
            );
        }
        self.kont.push(kont);
    }

    /// Pop a continuation from the stack.
    pub fn pop_kont(&mut self) -> Option<Kont<C>> {
        let popped = self.kont.pop();
        #[cfg(feature = "tracing")]
        if let Some(ref kont) = popped {
            let kont_type = match kont {
                Kont::SeqNext { .. } => "SeqNext",
                Kont::BothNext { .. } => "BothNext",
                Kont::AltNext { .. } => "AltNext",
                Kont::FixFrame { .. } => "FixFrame",
            };
            trace!(
                task_id = self.id,
                kont_type,
                remaining_depth = self.kont.len(),
                "pop_kont"
            );
        }
        popped
    }

    /// Check if the continuation stack is empty.
    pub fn kont_is_empty(&self) -> bool {
        self.kont.is_empty()
    }

    /// Set the task state to Ready.
    pub fn set_ready(&mut self) {
        self.state = TaskState::Ready;
    }

    /// Set the task state to Yielded with an answer.
    pub fn set_yielded(&mut self, nf: NF<C>) {
        self.state = TaskState::Yielded(nf);
    }

    /// Set the task state to Blocked on a relation.
    pub fn set_blocked(&mut self, rel_id: RelId) {
        self.state = TaskState::Blocked(rel_id);
    }

    /// Set the task state to Done.
    pub fn set_done(&mut self) {
        self.state = TaskState::Done;
    }

    /// Update the current goal.
    pub fn set_goal(&mut self, goal: GoalId) {
        self.goal = goal;
    }

    /// Update the input NF.
    pub fn set_input(&mut self, input: NF<C>) {
        self.input = input;
    }

    /// Find a FixFrame for the given relation in the continuation stack.
    /// Returns the Fix goal ID if found.
    pub fn find_fix_goal(&self, target_rel_id: RelId) -> Option<GoalId> {
        for kont in self.kont.iter().rev() {
            if let Kont::FixFrame {
                rel_id, fix_goal, ..
            } = kont
            {
                if *rel_id == target_rel_id {
                    return Some(*fix_goal);
                }
            }
        }
        None
    }
}

/// Pool of tasks being managed by the evaluator.
#[derive(Debug, Default)]
pub struct TaskPool<C> {
    tasks: Vec<Task<C>>,
    next_id: TaskId,
}

impl<C: Clone + Default> TaskPool<C> {
    /// Create a new empty task pool.
    pub fn new() -> Self {
        Self {
            tasks: Vec::new(),
            next_id: 0,
        }
    }

    /// Spawn a new task and return its ID.
    pub fn spawn(&mut self, goal: GoalId, input: NF<C>) -> TaskId {
        let id = self.next_id;
        self.next_id += 1;
        let task = Task::new(id, goal, input);
        self.tasks.push(task);
        id
    }

    /// Get a task by ID.
    pub fn get(&self, id: TaskId) -> Option<&Task<C>> {
        self.tasks.iter().find(|t| t.id == id)
    }

    /// Get a mutable reference to a task by ID.
    pub fn get_mut(&mut self, id: TaskId) -> Option<&mut Task<C>> {
        self.tasks.iter_mut().find(|t| t.id == id)
    }

    /// Get the next ready task, if any.
    pub fn next_ready(&mut self) -> Option<&mut Task<C>> {
        self.tasks.iter_mut().find(|t| t.is_ready())
    }

    /// Get all tasks blocked on a specific relation.
    pub fn blocked_on(&self, rel_id: RelId) -> Vec<TaskId> {
        self.tasks
            .iter()
            .filter(|t| t.blocked_on() == Some(rel_id))
            .map(|t| t.id)
            .collect()
    }

    /// Count of tasks in various states.
    pub fn count_ready(&self) -> usize {
        self.tasks.iter().filter(|t| t.is_ready()).count()
    }

    pub fn count_blocked(&self) -> usize {
        self.tasks.iter().filter(|t| t.is_blocked()).count()
    }

    pub fn count_done(&self) -> usize {
        self.tasks.iter().filter(|t| t.is_done()).count()
    }

    /// Total number of tasks.
    pub fn len(&self) -> usize {
        self.tasks.len()
    }

    /// Check if the pool is empty.
    pub fn is_empty(&self) -> bool {
        self.tasks.is_empty()
    }

    /// Remove completed tasks.
    pub fn cleanup_done(&mut self) {
        self.tasks.retain(|t| !t.is_done());
    }

    /// Iterator over all tasks.
    pub fn iter(&self) -> impl Iterator<Item = &Task<C>> {
        self.tasks.iter()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::wire::Wire;

    fn make_identity_nf() -> NF<()> {
        let match_pats = smallvec::smallvec![];
        let build_pats = smallvec::smallvec![];
        NF::new(match_pats, Wire::identity(0), build_pats)
    }

    // ========== TASK STATE TESTS ==========

    #[test]
    fn task_state_ready() {
        let state: TaskState<()> = TaskState::Ready;
        assert!(matches!(state, TaskState::Ready));
    }

    #[test]
    fn task_state_yielded() {
        let nf = make_identity_nf();
        let state: TaskState<()> = TaskState::Yielded(nf.clone());
        match state {
            TaskState::Yielded(answer) => assert_eq!(answer, nf),
            _ => panic!("Expected Yielded"),
        }
    }

    #[test]
    fn task_state_blocked() {
        let state: TaskState<()> = TaskState::Blocked(5);
        match state {
            TaskState::Blocked(rel_id) => assert_eq!(rel_id, 5),
            _ => panic!("Expected Blocked"),
        }
    }

    #[test]
    fn task_state_done() {
        let state: TaskState<()> = TaskState::Done;
        assert!(matches!(state, TaskState::Done));
    }

    // ========== TASK CREATION TESTS ==========

    #[test]
    fn new_task_is_ready() {
        let task: Task<()> = Task::new(0, 1, make_identity_nf());
        assert!(task.is_ready());
        assert!(!task.is_yielded());
        assert!(!task.is_blocked());
        assert!(!task.is_done());
    }

    #[test]
    fn new_task_has_empty_kont() {
        let task: Task<()> = Task::new(0, 1, make_identity_nf());
        assert!(task.kont_is_empty());
    }

    #[test]
    fn task_id_is_set() {
        let task: Task<()> = Task::new(42, 1, make_identity_nf());
        assert_eq!(task.id, 42);
    }

    #[test]
    fn task_goal_is_set() {
        let task: Task<()> = Task::new(0, 99, make_identity_nf());
        assert_eq!(task.goal, 99);
    }

    // ========== TASK STATE TRANSITIONS ==========

    #[test]
    fn set_yielded() {
        let mut task: Task<()> = Task::new(0, 1, make_identity_nf());
        let nf = make_identity_nf();
        task.set_yielded(nf.clone());

        assert!(task.is_yielded());
        assert_eq!(task.get_answer(), Some(&nf));
    }

    #[test]
    fn set_blocked() {
        let mut task: Task<()> = Task::new(0, 1, make_identity_nf());
        task.set_blocked(7);

        assert!(task.is_blocked());
        assert_eq!(task.blocked_on(), Some(7));
    }

    #[test]
    fn set_done() {
        let mut task: Task<()> = Task::new(0, 1, make_identity_nf());
        task.set_done();

        assert!(task.is_done());
        assert!(!task.is_ready());
    }

    #[test]
    fn set_ready_after_yielded() {
        let mut task: Task<()> = Task::new(0, 1, make_identity_nf());
        task.set_yielded(make_identity_nf());
        task.set_ready();

        assert!(task.is_ready());
        assert!(!task.is_yielded());
    }

    // ========== CONTINUATION STACK TESTS ==========

    #[test]
    fn push_and_pop_kont() {
        let mut task: Task<()> = Task::new(0, 1, make_identity_nf());

        let kont = Kont::AltNext {
            remaining: smallvec::smallvec![2, 3],
        };
        task.push_kont(kont.clone());

        assert!(!task.kont_is_empty());

        let popped = task.pop_kont();
        assert!(matches!(popped, Some(Kont::AltNext { .. })));
        assert!(task.kont_is_empty());
    }

    #[test]
    fn multiple_kont_lifo() {
        let mut task: Task<()> = Task::new(0, 1, make_identity_nf());

        task.push_kont(Kont::AltNext {
            remaining: smallvec::smallvec![1],
        });
        task.push_kont(Kont::SeqNext {
            left_answers: vec![],
            remaining: smallvec::smallvec![2],
        });
        task.push_kont(Kont::BothNext {
            left_answers: vec![],
            remaining: smallvec::smallvec![3],
        });

        // LIFO order
        assert!(matches!(task.pop_kont(), Some(Kont::BothNext { .. })));
        assert!(matches!(task.pop_kont(), Some(Kont::SeqNext { .. })));
        assert!(matches!(task.pop_kont(), Some(Kont::AltNext { .. })));
        assert!(task.pop_kont().is_none());
    }

    #[test]
    fn pop_empty_returns_none() {
        let mut task: Task<()> = Task::new(0, 1, make_identity_nf());
        assert!(task.pop_kont().is_none());
    }

    // ========== TASK MODIFICATION TESTS ==========

    #[test]
    fn set_goal() {
        let mut task: Task<()> = Task::new(0, 1, make_identity_nf());
        task.set_goal(42);
        assert_eq!(task.goal, 42);
    }

    #[test]
    fn set_input() {
        let mut task: Task<()> = Task::new(0, 1, make_identity_nf());
        let new_input = make_identity_nf();
        task.set_input(new_input.clone());
        assert_eq!(task.input, new_input);
    }

    // ========== KONT VARIANT TESTS ==========

    #[test]
    fn kont_seq_next() {
        let kont: Kont<()> = Kont::SeqNext {
            left_answers: vec![make_identity_nf()],
            remaining: smallvec::smallvec![1, 2, 3],
        };

        match kont {
            Kont::SeqNext { left_answers, remaining } => {
                assert_eq!(left_answers.len(), 1);
                assert_eq!(remaining.len(), 3);
            }
            _ => panic!("Expected SeqNext"),
        }
    }

    #[test]
    fn kont_both_next() {
        let kont: Kont<()> = Kont::BothNext {
            left_answers: vec![make_identity_nf(), make_identity_nf()],
            remaining: smallvec::smallvec![4, 5],
        };

        match kont {
            Kont::BothNext { left_answers, remaining } => {
                assert_eq!(left_answers.len(), 2);
                assert_eq!(remaining.len(), 2);
            }
            _ => panic!("Expected BothNext"),
        }
    }

    #[test]
    fn kont_alt_next() {
        let kont: Kont<()> = Kont::AltNext {
            remaining: smallvec::smallvec![6, 7, 8, 9],
        };

        match kont {
            Kont::AltNext { remaining } => {
                assert_eq!(remaining.len(), 4);
            }
            _ => panic!("Expected AltNext"),
        }
    }

    #[test]
    fn kont_fix_frame() {
        let kont: Kont<()> = Kont::FixFrame {
            rel_id: 10,
            body: 20,
            fix_goal: 30,
        };

        match kont {
            Kont::FixFrame {
                rel_id,
                body,
                fix_goal,
            } => {
                assert_eq!(rel_id, 10);
                assert_eq!(body, 20);
                assert_eq!(fix_goal, 30);
            }
            _ => panic!("Expected FixFrame"),
        }
    }

    // ========== TASK POOL TESTS ==========

    #[test]
    fn new_pool_is_empty() {
        let pool: TaskPool<()> = TaskPool::new();
        assert!(pool.is_empty());
        assert_eq!(pool.len(), 0);
    }

    #[test]
    fn spawn_returns_unique_ids() {
        let mut pool: TaskPool<()> = TaskPool::new();
        let id1 = pool.spawn(0, make_identity_nf());
        let id2 = pool.spawn(1, make_identity_nf());
        let id3 = pool.spawn(2, make_identity_nf());

        assert_eq!(id1, 0);
        assert_eq!(id2, 1);
        assert_eq!(id3, 2);
        assert_eq!(pool.len(), 3);
    }

    #[test]
    fn get_task_by_id() {
        let mut pool: TaskPool<()> = TaskPool::new();
        let id = pool.spawn(42, make_identity_nf());

        let task = pool.get(id);
        assert!(task.is_some());
        assert_eq!(task.unwrap().goal, 42);
    }

    #[test]
    fn get_invalid_id_returns_none() {
        let pool: TaskPool<()> = TaskPool::new();
        assert!(pool.get(100).is_none());
    }

    #[test]
    fn get_mut_allows_modification() {
        let mut pool: TaskPool<()> = TaskPool::new();
        let id = pool.spawn(0, make_identity_nf());

        if let Some(task) = pool.get_mut(id) {
            task.set_blocked(5);
        }

        assert!(pool.get(id).unwrap().is_blocked());
    }

    #[test]
    fn next_ready_finds_ready_task() {
        let mut pool: TaskPool<()> = TaskPool::new();
        pool.spawn(0, make_identity_nf());
        pool.spawn(1, make_identity_nf());

        // Both should be ready initially
        let task = pool.next_ready();
        assert!(task.is_some());
        assert!(task.unwrap().is_ready());
    }

    #[test]
    fn next_ready_skips_non_ready() {
        let mut pool: TaskPool<()> = TaskPool::new();
        let id1 = pool.spawn(0, make_identity_nf());
        let id2 = pool.spawn(1, make_identity_nf());

        // Mark first as done
        pool.get_mut(id1).unwrap().set_done();

        // Should find the second one
        let task = pool.next_ready();
        assert!(task.is_some());
        assert_eq!(task.unwrap().id, id2);
    }

    #[test]
    fn blocked_on_finds_tasks() {
        let mut pool: TaskPool<()> = TaskPool::new();
        let id1 = pool.spawn(0, make_identity_nf());
        let _id2 = pool.spawn(1, make_identity_nf());
        let id3 = pool.spawn(2, make_identity_nf());

        pool.get_mut(id1).unwrap().set_blocked(5);
        pool.get_mut(id3).unwrap().set_blocked(5);
        // id2 stays ready

        let blocked = pool.blocked_on(5);
        assert_eq!(blocked.len(), 2);
        assert!(blocked.contains(&id1));
        assert!(blocked.contains(&id3));
    }

    #[test]
    fn count_states() {
        let mut pool: TaskPool<()> = TaskPool::new();
        let id1 = pool.spawn(0, make_identity_nf());
        let id2 = pool.spawn(1, make_identity_nf());
        let _id3 = pool.spawn(2, make_identity_nf());
        let _id4 = pool.spawn(3, make_identity_nf());

        pool.get_mut(id1).unwrap().set_done();
        pool.get_mut(id2).unwrap().set_blocked(1);
        // _id3, _id4 stay ready

        assert_eq!(pool.count_ready(), 2);
        assert_eq!(pool.count_blocked(), 1);
        assert_eq!(pool.count_done(), 1);
    }

    #[test]
    fn cleanup_done_removes_completed() {
        let mut pool: TaskPool<()> = TaskPool::new();
        let id1 = pool.spawn(0, make_identity_nf());
        let id2 = pool.spawn(1, make_identity_nf());
        let id3 = pool.spawn(2, make_identity_nf());

        pool.get_mut(id1).unwrap().set_done();
        pool.get_mut(id3).unwrap().set_done();

        pool.cleanup_done();

        assert_eq!(pool.len(), 1);
        assert!(pool.get(id2).is_some());
        assert!(pool.get(id1).is_none());
        assert!(pool.get(id3).is_none());
    }

    #[test]
    fn iter_over_tasks() {
        let mut pool: TaskPool<()> = TaskPool::new();
        pool.spawn(0, make_identity_nf());
        pool.spawn(1, make_identity_nf());
        pool.spawn(2, make_identity_nf());

        let tasks: Vec<_> = pool.iter().collect();
        assert_eq!(tasks.len(), 3);
    }

    // ========== COMPLEX SCENARIOS ==========

    #[test]
    fn simulate_task_lifecycle() {
        let mut pool: TaskPool<()> = TaskPool::new();
        let id = pool.spawn(0, make_identity_nf());

        // Initially ready
        assert!(pool.get(id).unwrap().is_ready());

        // Becomes blocked on relation
        pool.get_mut(id).unwrap().set_blocked(1);
        assert!(pool.get(id).unwrap().is_blocked());
        assert_eq!(pool.blocked_on(1), vec![id]);

        // Relation produces answer, task resumes
        pool.get_mut(id).unwrap().set_ready();
        assert!(pool.get(id).unwrap().is_ready());

        // Task yields an answer
        pool.get_mut(id).unwrap().set_yielded(make_identity_nf());
        assert!(pool.get(id).unwrap().is_yielded());

        // Consumer takes answer, task continues
        pool.get_mut(id).unwrap().set_ready();

        // Eventually completes
        pool.get_mut(id).unwrap().set_done();
        assert!(pool.get(id).unwrap().is_done());
    }

    #[test]
    fn nested_continuations() {
        let mut task: Task<()> = Task::new(0, 0, make_identity_nf());

        // Simulate entering nested goals
        // Alt(Seq(g1, g2), g3)

        // Enter Alt
        task.push_kont(Kont::AltNext {
            remaining: smallvec::smallvec![10], // g3
        });

        // Enter Seq (first branch of Alt)
        task.push_kont(Kont::SeqNext {
            left_answers: vec![],
            remaining: smallvec::smallvec![2], // g2
        });

        // Now evaluating g1, when it yields:
        // 1. Pop SeqNext, process with g2
        // 2. If Seq fails, pop AltNext, try g3

        assert_eq!(task.kont.len(), 2);

        // Pop Seq continuation
        let seq_kont = task.pop_kont();
        assert!(matches!(seq_kont, Some(Kont::SeqNext { .. })));

        // Pop Alt continuation
        let alt_kont = task.pop_kont();
        assert!(matches!(alt_kont, Some(Kont::AltNext { .. })));

        assert!(task.kont_is_empty());
    }
}
