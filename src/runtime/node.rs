//! Node types for the dataflow runtime.
//!
//! Each node maintains:
//! - `out_set`: Deduplication set of canonicalized NFs
//! - `out_vec`: Stable emission order of NFs
//! - `demand_goals`: Set of boundary demands
//! - `need`: Scheduling demand counter
//! - `dependents`: Parent edges for propagating outputs
//!
//! Node kinds:
//! - Atom: Emits a single canonical NF
//! - Or: Lazy interleaving with turn bit
//! - Join: Meet or Compose operations with task queues
//! - Table: Fixpoint storage with goal tracking
//! - Call: Interface to tables with goal filtering

use crate::constraint::ConstraintOps;
use crate::nf::{canon_nf, NF};
use crate::runtime::goal::{canon_goal, Goal};
use crate::term::TermStore;
use std::collections::{HashSet, VecDeque};

/// Node identifier in the runtime graph.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct NodeId(pub u32);

impl NodeId {
    /// Create a new node ID.
    pub fn new(id: u32) -> Self {
        Self(id)
    }

    /// Get the raw ID value.
    pub fn raw(self) -> u32 {
        self.0
    }
}

/// Common state shared by all node types.
#[derive(Debug)]
pub struct NodeState<C> {
    /// Deduplication set of canonicalized NFs.
    pub out_set: HashSet<NF<C>>,
    /// Stable emission order of NFs.
    pub out_vec: Vec<NF<C>>,
    /// Set of boundary demands (disjunctive).
    pub demand_goals: HashSet<Goal>,
    /// Scheduling demand counter.
    /// Node runs only if need > 0.
    pub need: u32,
    /// Parent edges for output propagation.
    pub dependents: Vec<NodeId>,
    /// Whether this node has finished producing all outputs.
    pub exhausted: bool,
}

impl<C: ConstraintOps> Default for NodeState<C> {
    fn default() -> Self {
        Self::new()
    }
}

impl<C: ConstraintOps> NodeState<C> {
    /// Create empty node state.
    pub fn new() -> Self {
        Self {
            out_set: HashSet::new(),
            out_vec: Vec::new(),
            demand_goals: HashSet::new(),
            need: 0,
            dependents: Vec::new(),
            exhausted: false,
        }
    }

    /// Add an output NF, canonicalizing and deduplicating.
    /// Returns true if the NF was new and added.
    pub fn add_output(&mut self, nf: NF<C>, terms: &mut TermStore) -> bool {
        let canon = canon_nf(&nf, terms);
        if self.out_set.contains(&canon) {
            return false;
        }
        self.out_set.insert(canon.clone());
        self.out_vec.push(canon);
        true
    }

    /// Add a demand goal, canonicalizing and deduplicating.
    /// Returns true if the goal was new and added.
    /// New goals reopen exhausted nodes (set exhausted=false) so they can
    /// process the new goal.
    pub fn add_demand(&mut self, goal: Goal, terms: &mut TermStore) -> bool {
        let canon = canon_goal(&goal, terms);
        if self.demand_goals.contains(&canon) {
            return false;
        }
        self.demand_goals.insert(canon);
        self.exhausted = false; // New goal reopens the node
        true
    }

    /// Add a dependent node.
    pub fn add_dependent(&mut self, node: NodeId) {
        if !self.dependents.contains(&node) {
            self.dependents.push(node);
        }
    }
}

/// Result of stepping a node.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum StepResult {
    /// Node produced output or made progress.
    Progress,
    /// Node is blocked waiting for input.
    Blocked,
    /// Node is done (has emitted all outputs it can).
    Done,
}

/// A task in a join node's queue.
#[derive(Debug, Clone)]
pub struct JoinTask {
    /// Which side this task came from ('L' or 'R').
    pub side: JoinSide,
    /// Index into the originating side's out_vec.
    pub idx: usize,
    /// Current position in the iteration.
    pub pos: usize,
    /// Limit for this task (how many items to process).
    pub limit: usize,
}

/// Which side of a join.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum JoinSide {
    Left,
    Right,
}

/// Node kind with operator-specific state.
#[derive(Debug)]
pub enum NodeKind<C> {
    /// Atom: emits a single NF once.
    Atom {
        nf: NF<C>,
        emitted: bool,
    },

    /// Or: lazy interleaving of two children.
    Or {
        left: NodeId,
        right: NodeId,
        /// Cursor into left child's out_vec.
        left_pos: usize,
        /// Cursor into right child's out_vec.
        right_pos: usize,
        /// Turn bit for interleaving (0 = left, 1 = right).
        turn: u8,
    },

    /// Join: compose or meet of two children.
    Join {
        left: NodeId,
        right: NodeId,
        /// Operation type.
        op: JoinOp,
        /// How many left outputs have been seen (for join tasks).
        left_seen: usize,
        /// How many right outputs have been seen (for join tasks).
        right_seen: usize,
        /// How many left outputs have been processed for goal synthesis.
        goal_left_seen: usize,
        /// How many right outputs have been processed for goal synthesis.
        goal_right_seen: usize,
        /// Task queue for left-originating tasks.
        tasks_left: VecDeque<JoinTask>,
        /// Task queue for right-originating tasks.
        tasks_right: VecDeque<JoinTask>,
        /// Turn bit for task queue alternation.
        turn: u8,
        /// Turn bit for seeding when both sides empty.
        seed_turn: u8,
    },

    /// Table: fixpoint storage for recursive definitions.
    Table {
        /// Name of the table (for debugging).
        name: String,
        /// Root of the body graph (if set).
        body_root: Option<NodeId>,
        /// Cursor into body's output.
        body_pos: usize,
        /// Registered goals.
        goals: HashSet<Goal>,
    },

    /// Call: interface to a table with goal filtering.
    Call {
        /// Table to call.
        table_id: NodeId,
        /// Cursor into table's output.
        table_pos: usize,
        /// Goals that have been registered with the table.
        registered_goals: HashSet<Goal>,
    },
}

/// Join operation type.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum JoinOp {
    /// Sequential composition: left ; right
    Compose,
    /// Conjunction/intersection: left & right
    Meet,
}

/// A node in the dataflow graph.
#[derive(Debug)]
pub struct Node<C> {
    /// Unique identifier.
    pub id: NodeId,
    /// Common state.
    pub state: NodeState<C>,
    /// Node-specific kind and state.
    pub kind: NodeKind<C>,
}

impl<C: ConstraintOps> Node<C> {
    /// Create an Atom node.
    pub fn atom(id: NodeId, nf: NF<C>, terms: &mut TermStore) -> Self {
        let canon = canon_nf(&nf, terms);
        Self {
            id,
            state: NodeState::new(),
            kind: NodeKind::Atom {
                nf: canon,
                emitted: false,
            },
        }
    }

    /// Create an Or node.
    pub fn or(id: NodeId, left: NodeId, right: NodeId) -> Self {
        Self {
            id,
            state: NodeState::new(),
            kind: NodeKind::Or {
                left,
                right,
                left_pos: 0,
                right_pos: 0,
                turn: 0,
            },
        }
    }

    /// Create a Join node (compose or meet).
    pub fn join(id: NodeId, left: NodeId, right: NodeId, op: JoinOp) -> Self {
        Self {
            id,
            state: NodeState::new(),
            kind: NodeKind::Join {
                left,
                right,
                op,
                left_seen: 0,
                right_seen: 0,
                goal_left_seen: 0,
                goal_right_seen: 0,
                tasks_left: VecDeque::new(),
                tasks_right: VecDeque::new(),
                turn: 0,
                seed_turn: 0,
            },
        }
    }

    /// Create a Table node.
    pub fn table(id: NodeId, name: String) -> Self {
        Self {
            id,
            state: NodeState::new(),
            kind: NodeKind::Table {
                name,
                body_root: None,
                body_pos: 0,
                goals: HashSet::new(),
            },
        }
    }

    /// Create a Call node.
    pub fn call(id: NodeId, table_id: NodeId) -> Self {
        Self {
            id,
            state: NodeState::new(),
            kind: NodeKind::Call {
                table_id,
                table_pos: 0,
                registered_goals: HashSet::new(),
            },
        }
    }

    /// Set the body root for a Table node.
    pub fn set_body_root(&mut self, body_root: NodeId) {
        if let NodeKind::Table {
            body_root: ref mut br,
            ..
        } = self.kind
        {
            *br = Some(body_root);
        }
    }

    /// Register a goal with a Table node.
    /// Returns true if the goal was new.
    pub fn register_goal(&mut self, goal: Goal, terms: &mut TermStore) -> bool {
        if let NodeKind::Table { ref mut goals, .. } = self.kind {
            let canon = canon_goal(&goal, terms);
            if goals.contains(&canon) {
                return false;
            }
            goals.insert(canon);
            true
        } else {
            false
        }
    }

    /// Check if this is a Table node.
    pub fn is_table(&self) -> bool {
        matches!(self.kind, NodeKind::Table { .. })
    }

    /// Get the left child if this is an Or or Join node.
    pub fn left_child(&self) -> Option<NodeId> {
        match &self.kind {
            NodeKind::Or { left, .. } | NodeKind::Join { left, .. } => Some(*left),
            _ => None,
        }
    }

    /// Get the right child if this is an Or or Join node.
    pub fn right_child(&self) -> Option<NodeId> {
        match &self.kind {
            NodeKind::Or { right, .. } | NodeKind::Join { right, .. } => Some(*right),
            _ => None,
        }
    }

    /// Get the table ID if this is a Call node.
    pub fn table_id(&self) -> Option<NodeId> {
        match &self.kind {
            NodeKind::Call { table_id, .. } => Some(*table_id),
            _ => None,
        }
    }

    /// Get the body root if this is a Table node.
    pub fn body_root(&self) -> Option<NodeId> {
        match &self.kind {
            NodeKind::Table { body_root, .. } => *body_root,
            _ => None,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::symbol::SymbolStore;
    use smallvec::smallvec;

    fn setup() -> (SymbolStore, TermStore) {
        (SymbolStore::new(), TermStore::new())
    }

    // ========================================================================
    // NODE ID TESTS
    // ========================================================================

    #[test]
    fn node_id_equality() {
        let id1 = NodeId::new(1);
        let id2 = NodeId::new(1);
        let id3 = NodeId::new(2);
        assert_eq!(id1, id2);
        assert_ne!(id1, id3);
    }

    #[test]
    fn node_id_raw_value() {
        let id = NodeId::new(42);
        assert_eq!(id.raw(), 42);
    }

    // ========================================================================
    // NODE STATE TESTS
    // ========================================================================

    #[test]
    fn node_state_initially_empty() {
        let state: NodeState<()> = NodeState::new();
        assert!(state.out_set.is_empty());
        assert!(state.out_vec.is_empty());
        assert!(state.demand_goals.is_empty());
        assert_eq!(state.need, 0);
        assert!(state.dependents.is_empty());
        assert!(!state.exhausted);
    }

    #[test]
    fn node_state_add_output_deduplicates() {
        let (symbols, mut terms) = setup();
        let z = symbols.intern("z");
        let z_term = terms.app0(z);
        let nf: NF<()> = NF::new(smallvec![z_term], smallvec![z_term]);

        let mut state: NodeState<()> = NodeState::new();

        // First add should succeed
        assert!(state.add_output(nf.clone(), &mut terms));
        assert_eq!(state.out_vec.len(), 1);

        // Second add of same NF should fail
        assert!(!state.add_output(nf, &mut terms));
        assert_eq!(state.out_vec.len(), 1);
    }

    #[test]
    fn node_state_add_output_canonicalizes() {
        let (symbols, mut terms) = setup();
        let z = symbols.intern("z");
        let z_term = terms.app0(z);

        // NF with non-canonical variable numbering
        let v5 = terms.var(5);
        let nf: NF<()> = NF::new(smallvec![v5], smallvec![z_term]);

        let mut state: NodeState<()> = NodeState::new();
        state.add_output(nf, &mut terms);

        // Should be canonicalized to use $0
        let v0 = terms.var(0);
        let expected: NF<()> = NF::new(smallvec![v0], smallvec![z_term]);
        assert!(state.out_set.contains(&expected));
    }

    #[test]
    fn node_state_add_demand_deduplicates() {
        let (_, mut terms) = setup();
        let v0 = terms.var(0);
        let goal = Goal::match_only(smallvec![v0]);

        let mut state: NodeState<()> = NodeState::new();

        // First add should succeed
        assert!(state.add_demand(goal.clone(), &mut terms));
        assert_eq!(state.demand_goals.len(), 1);

        // Second add of same goal should fail
        assert!(!state.add_demand(goal, &mut terms));
        assert_eq!(state.demand_goals.len(), 1);
    }

    #[test]
    fn node_state_add_dependent_deduplicates() {
        let mut state: NodeState<()> = NodeState::new();
        let dep = NodeId::new(5);

        state.add_dependent(dep);
        assert_eq!(state.dependents.len(), 1);

        state.add_dependent(dep);
        assert_eq!(state.dependents.len(), 1);
    }

    // ========================================================================
    // ATOM NODE TESTS
    // ========================================================================

    #[test]
    fn atom_node_creation() {
        let (symbols, mut terms) = setup();
        let z = symbols.intern("z");
        let z_term = terms.app0(z);
        let nf: NF<()> = NF::new(smallvec![z_term], smallvec![z_term]);

        let node = Node::atom(NodeId::new(0), nf, &mut terms);

        assert_eq!(node.id, NodeId::new(0));
        matches!(node.kind, NodeKind::Atom { emitted: false, .. });
    }

    #[test]
    fn atom_node_stores_canonical_nf() {
        let (symbols, mut terms) = setup();
        let z = symbols.intern("z");
        let z_term = terms.app0(z);

        // Non-canonical variable
        let v5 = terms.var(5);
        let nf: NF<()> = NF::new(smallvec![v5], smallvec![z_term]);

        let node = Node::atom(NodeId::new(0), nf, &mut terms);

        // Should store canonical version
        if let NodeKind::Atom { ref nf, .. } = node.kind {
            let v0 = terms.var(0);
            assert_eq!(nf.match_boundary[0], v0);
        }
    }

    // ========================================================================
    // OR NODE TESTS
    // ========================================================================

    #[test]
    fn or_node_creation() {
        let left = NodeId::new(1);
        let right = NodeId::new(2);
        let node: Node<()> = Node::or(NodeId::new(0), left, right);

        assert_eq!(node.id, NodeId::new(0));
        assert_eq!(node.left_child(), Some(left));
        assert_eq!(node.right_child(), Some(right));
    }

    #[test]
    fn or_node_initial_state() {
        let node: Node<()> = Node::or(NodeId::new(0), NodeId::new(1), NodeId::new(2));

        if let NodeKind::Or {
            left_pos,
            right_pos,
            turn,
            ..
        } = node.kind
        {
            assert_eq!(left_pos, 0);
            assert_eq!(right_pos, 0);
            assert_eq!(turn, 0);
        }
    }

    // ========================================================================
    // JOIN NODE TESTS
    // ========================================================================

    #[test]
    fn join_compose_node_creation() {
        let left = NodeId::new(1);
        let right = NodeId::new(2);
        let node: Node<()> = Node::join(NodeId::new(0), left, right, JoinOp::Compose);

        assert_eq!(node.id, NodeId::new(0));
        assert_eq!(node.left_child(), Some(left));
        assert_eq!(node.right_child(), Some(right));

        if let NodeKind::Join { op, .. } = node.kind {
            assert_eq!(op, JoinOp::Compose);
        }
    }

    #[test]
    fn join_meet_node_creation() {
        let left = NodeId::new(1);
        let right = NodeId::new(2);
        let node: Node<()> = Node::join(NodeId::new(0), left, right, JoinOp::Meet);

        if let NodeKind::Join { op, .. } = node.kind {
            assert_eq!(op, JoinOp::Meet);
        }
    }

    #[test]
    fn join_node_initial_state() {
        let node: Node<()> = Node::join(
            NodeId::new(0),
            NodeId::new(1),
            NodeId::new(2),
            JoinOp::Compose,
        );

        if let NodeKind::Join {
            left_seen,
            right_seen,
            ref tasks_left,
            ref tasks_right,
            turn,
            ..
        } = node.kind
        {
            assert_eq!(left_seen, 0);
            assert_eq!(right_seen, 0);
            assert!(tasks_left.is_empty());
            assert!(tasks_right.is_empty());
            assert_eq!(turn, 0);
        }
    }

    // ========================================================================
    // TABLE NODE TESTS
    // ========================================================================

    #[test]
    fn table_node_creation() {
        let node: Node<()> = Node::table(NodeId::new(0), "add".to_string());

        assert_eq!(node.id, NodeId::new(0));
        assert!(node.is_table());
        assert_eq!(node.body_root(), None);
    }

    #[test]
    fn table_node_set_body_root() {
        let mut node: Node<()> = Node::table(NodeId::new(0), "add".to_string());
        let body = NodeId::new(5);

        node.set_body_root(body);
        assert_eq!(node.body_root(), Some(body));
    }

    #[test]
    fn table_node_register_goal() {
        let (_, mut terms) = setup();
        let v0 = terms.var(0);
        let goal = Goal::match_only(smallvec![v0]);

        let mut node: Node<()> = Node::table(NodeId::new(0), "add".to_string());

        // First registration succeeds
        assert!(node.register_goal(goal.clone(), &mut terms));

        // Second registration of same goal fails
        assert!(!node.register_goal(goal, &mut terms));
    }

    // ========================================================================
    // CALL NODE TESTS
    // ========================================================================

    #[test]
    fn call_node_creation() {
        let table = NodeId::new(5);
        let node: Node<()> = Node::call(NodeId::new(0), table);

        assert_eq!(node.id, NodeId::new(0));
        assert_eq!(node.table_id(), Some(table));
        assert!(!node.is_table());
    }

    #[test]
    fn call_node_initial_state() {
        let node: Node<()> = Node::call(NodeId::new(0), NodeId::new(5));

        if let NodeKind::Call {
            table_pos,
            ref registered_goals,
            ..
        } = node.kind
        {
            assert_eq!(table_pos, 0);
            assert!(registered_goals.is_empty());
        }
    }

    // ========================================================================
    // JOIN TASK TESTS
    // ========================================================================

    #[test]
    fn join_task_creation() {
        let task = JoinTask {
            side: JoinSide::Left,
            idx: 0,
            pos: 0,
            limit: 5,
        };

        assert_eq!(task.side, JoinSide::Left);
        assert_eq!(task.idx, 0);
        assert_eq!(task.pos, 0);
        assert_eq!(task.limit, 5);
    }
}
