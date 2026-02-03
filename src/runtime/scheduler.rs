//! Worklist scheduler for the dataflow runtime.
//!
//! The scheduler maintains:
//! - A vector of nodes
//! - A worklist of node IDs to process
//! - A scheduled set to avoid duplicate enqueuing
//!
//! Key invariant: A node runs ONLY if `need > 0`.

use crate::constraint::ConstraintOps;
use crate::kernel::compose::compose_nf;
use crate::kernel::meet::meet_nf;
use crate::nf::{canon_nf, max_var_in_nf, shift_nf_vars, NF};
use crate::runtime::goal::{canon_goal, goal_matches, goal_matches_boundary, Goal};
use crate::runtime::node::{JoinOp, JoinSide, JoinTask, Node, NodeId, NodeKind};
use crate::term::TermStore;
use std::collections::{HashSet, VecDeque};

/// Maximum pairs to process per join step (to prevent runaway).
const MAX_JOIN_PAIRS: usize = 32;

/// Runtime state for the dataflow evaluator.
#[derive(Debug)]
pub struct Runtime<C> {
    /// All nodes in the graph.
    pub nodes: Vec<Node<C>>,
    /// Worklist of nodes to process.
    pub worklist: VecDeque<NodeId>,
    /// Tracks which nodes are currently in the worklist.
    pub scheduled: HashSet<NodeId>,
    /// Global variable counter for freshening.
    pub var_counter: u32,
}

impl<C: ConstraintOps> Default for Runtime<C> {
    fn default() -> Self {
        Self::new()
    }
}

impl<C: ConstraintOps> Runtime<C> {
    /// Create a new empty runtime.
    pub fn new() -> Self {
        Self {
            nodes: Vec::new(),
            worklist: VecDeque::new(),
            scheduled: HashSet::new(),
            var_counter: 0,
        }
    }

    /// Add a node to the runtime, returning its ID.
    pub fn add_node(&mut self, node: Node<C>) -> NodeId {
        let id = NodeId::new(self.nodes.len() as u32);
        self.nodes.push(node);
        id
    }

    /// Get a reference to a node.
    pub fn get_node(&self, id: NodeId) -> Option<&Node<C>> {
        self.nodes.get(id.raw() as usize)
    }

    /// Get a mutable reference to a node.
    pub fn get_node_mut(&mut self, id: NodeId) -> Option<&mut Node<C>> {
        self.nodes.get_mut(id.raw() as usize)
    }

    /// Add a dependency edge from source to dependent.
    pub fn add_edge(&mut self, source: NodeId, dependent: NodeId) {
        if let Some(node) = self.get_node_mut(source) {
            node.state.add_dependent(dependent);
        }
    }

    /// Enqueue a node to the worklist (if not already scheduled).
    pub fn enqueue(&mut self, id: NodeId) {
        if !self.scheduled.contains(&id) {
            self.scheduled.insert(id);
            self.worklist.push_back(id);
        }
    }

    /// Activate a node (set need > 0 and enqueue).
    pub fn activate(&mut self, id: NodeId) {
        if let Some(node) = self.get_node_mut(id) {
            if node.state.need == 0 {
                node.state.need = 1;
            }
        }
        self.enqueue(id);
    }

    /// Request more output from a node (increment need and enqueue).
    pub fn request(&mut self, id: NodeId) {
        if let Some(node) = self.get_node_mut(id) {
            node.state.need = node.state.need.saturating_add(1);
        }
        self.enqueue(id);
    }

    /// Decrement need for a node.
    pub fn satisfy(&mut self, id: NodeId) {
        if let Some(node) = self.get_node_mut(id) {
            node.state.need = node.state.need.saturating_sub(1);
        }
    }

    /// Add a demand goal to a node.
    pub fn add_demand(&mut self, id: NodeId, goal: Goal, terms: &mut TermStore) -> bool {
        if let Some(node) = self.get_node_mut(id) {
            if node.state.add_demand(goal, terms) {
                self.enqueue(id);
                return true;
            }
        }
        false
    }

    /// Generate a fresh variable ID.
    pub fn fresh_var(&mut self) -> u32 {
        let v = self.var_counter;
        self.var_counter += 1;
        v
    }

    /// Freshen an NF with new variable IDs.
    pub fn freshen_nf(&mut self, nf: &NF<C>, terms: &mut TermStore) -> NF<C> {
        let max = max_var_in_nf(nf, terms).map(|m| m + 1).unwrap_or(0);
        let offset = self.var_counter;
        self.var_counter += max;
        shift_nf_vars(nf, offset, terms)
    }

    /// Run the worklist until stop condition or empty.
    ///
    /// Returns the remaining fuel.
    pub fn run_with_fuel<F>(&mut self, fuel: usize, stop: F, terms: &mut TermStore) -> usize
    where
        F: Fn(&Self) -> bool,
    {
        let mut remaining = fuel;
        while remaining > 0 {
            if stop(self) {
                break;
            }
            if self.worklist.is_empty() {
                break;
            }
            let id = self.worklist.pop_front().unwrap();
            self.scheduled.remove(&id);

            // Only step if need > 0
            let need = self.get_node(id).map(|n| n.state.need).unwrap_or(0);
            if need > 0 {
                self.step_node(id, terms);
            }
            remaining -= 1;
        }
        remaining
    }

    /// Step a single node.
    pub fn step_node(&mut self, id: NodeId, terms: &mut TermStore) {
        // We need to extract the node kind to avoid borrow issues
        let kind_data = {
            let node = match self.get_node(id) {
                Some(n) => n,
                None => return,
            };
            extract_kind_data(&node.kind)
        };

        match kind_data {
            KindData::Atom => self.step_atom(id, terms),
            KindData::Or { left, right } => self.step_or(id, left, right, terms),
            KindData::Join { left, right, op } => self.step_join(id, left, right, op, terms),
            KindData::Table { body_root } => self.step_table(id, body_root, terms),
            KindData::Call { table_id } => self.step_call(id, table_id, terms),
        }
    }

    /// Step an Atom node: emit its NF once if compatible with at least one goal.
    ///
    /// Goal-aware pruning: If the atom's NF is not compatible with any demanded
    /// goal, it emits nothing but still marks itself exhausted. This is critical
    /// for termination - incompatible atoms must exhaust so their parents don't
    /// keep polling them forever.
    ///
    /// Key invariants:
    /// - emitted=true means the atom HAS produced output (won't produce again)
    /// - emitted=false means it hasn't produced output yet (may produce if compatible goal arrives)
    /// - exhausted=true means no more work to do with CURRENT goals
    /// - New goals reopen (exhausted=false) and trigger re-check if emitted=false
    fn step_atom(&mut self, id: NodeId, terms: &mut TermStore) {
        // Extract state
        let (exhausted, emitted, nf, goals) = {
            let node = self.get_node(id).unwrap();
            let goals: Vec<Goal> = node.state.demand_goals.iter().cloned().collect();
            match &node.kind {
                NodeKind::Atom { emitted, nf } => {
                    (node.state.exhausted, *emitted, nf.clone(), goals)
                }
                _ => return,
            }
        };

        // Return early if exhausted or no goals
        if exhausted || goals.is_empty() {
            return;
        }

        // Already emitted - just mark exhausted and return (atoms only emit once)
        if emitted {
            if let Some(node) = self.get_node_mut(id) {
                node.state.exhausted = true;
                let dependents = node.state.dependents.clone();
                for dep in dependents {
                    self.enqueue(dep);
                }
            }
            return;
        }

        // Check goal compatibility and emit if compatible
        let compatible = goals.iter().any(|g| goal_matches(g, &nf, terms));
        if compatible {
            // Mark emitted ONLY if we actually emit
            if let Some(node) = self.get_node_mut(id) {
                if let NodeKind::Atom {
                    emitted: ref mut e, ..
                } = node.kind
                {
                    *e = true;
                }
            }
            self.add_output_and_notify(id, nf, terms);
        }

        // Always mark exhausted after checking (but emitted only if we emitted)
        // New goals will reopen via add_demand setting exhausted=false
        if let Some(node) = self.get_node_mut(id) {
            node.state.exhausted = true;
            let dependents = node.state.dependents.clone();
            for dep in dependents {
                self.enqueue(dep);
            }
        }
    }

    /// Step an Or node: lazy interleaving.
    fn step_or(&mut self, id: NodeId, left: NodeId, right: NodeId, terms: &mut TermStore) {
        // Propagate demand goals to both children
        let goals: Vec<Goal> = {
            let node = self.get_node(id).unwrap();
            node.state.demand_goals.iter().cloned().collect()
        };
        for goal in goals {
            self.add_demand(left, goal.clone(), terms);
            self.add_demand(right, goal, terms);
        }

        // Get current state
        let (left_pos, right_pos, turn) = {
            let node = self.get_node(id).unwrap();
            match &node.kind {
                NodeKind::Or {
                    left_pos,
                    right_pos,
                    turn,
                    ..
                } => (*left_pos, *right_pos, *turn),
                _ => return,
            }
        };

        // Check availability of outputs and exhaustion state
        let (left_len, left_exhausted) = self
            .get_node(left)
            .map(|n| (n.state.out_vec.len(), n.state.exhausted))
            .unwrap_or((0, true));
        let (right_len, right_exhausted) = self
            .get_node(right)
            .map(|n| (n.state.out_vec.len(), n.state.exhausted))
            .unwrap_or((0, true));
        let left_avail = left_pos < left_len;
        let right_avail = right_pos < right_len;

        // Check if we've consumed all available outputs from exhausted children
        let left_done = left_exhausted && !left_avail;
        let right_done = right_exhausted && !right_avail;

        // If both children are done, mark Or as exhausted
        if left_done && right_done {
            if let Some(node) = self.get_node_mut(id) {
                node.state.exhausted = true;
            }
            return;
        }

        // Interleave based on turn
        let (output, new_left_pos, new_right_pos, new_turn) = if turn == 0 {
            if left_avail {
                let nf = self.get_node(left).unwrap().state.out_vec[left_pos].clone();
                (Some(nf), left_pos + 1, right_pos, 1)
            } else if right_avail {
                let nf = self.get_node(right).unwrap().state.out_vec[right_pos].clone();
                (Some(nf), left_pos, right_pos + 1, 0)
            } else {
                // Both empty, request more from non-exhausted children
                if !left_exhausted {
                    self.activate(left);
                }
                if !right_exhausted {
                    self.activate(right);
                }
                (None, left_pos, right_pos, turn)
            }
        } else {
            if right_avail {
                let nf = self.get_node(right).unwrap().state.out_vec[right_pos].clone();
                (Some(nf), left_pos, right_pos + 1, 0)
            } else if left_avail {
                let nf = self.get_node(left).unwrap().state.out_vec[left_pos].clone();
                (Some(nf), left_pos + 1, right_pos, 1)
            } else {
                // Both empty, request more from non-exhausted children
                if !right_exhausted {
                    self.activate(right);
                }
                if !left_exhausted {
                    self.activate(left);
                }
                (None, left_pos, right_pos, turn)
            }
        };

        // Update state
        if let Some(node) = self.get_node_mut(id) {
            if let NodeKind::Or {
                left_pos: ref mut lp,
                right_pos: ref mut rp,
                turn: ref mut t,
                ..
            } = node.kind
            {
                *lp = new_left_pos;
                *rp = new_right_pos;
                *t = new_turn;
            }
        }

        // Add output if we got one
        if let Some(nf) = output {
            self.add_output_and_notify(id, nf, terms);

            // Re-enqueue if more available
            let left_len = self.get_node(left).map(|n| n.state.out_vec.len()).unwrap_or(0);
            let right_len = self.get_node(right).map(|n| n.state.out_vec.len()).unwrap_or(0);
            if new_left_pos < left_len || new_right_pos < right_len {
                self.enqueue(id);
            }
        }
    }

    /// Step a Join node: compose or meet.
    fn step_join(
        &mut self,
        id: NodeId,
        left: NodeId,
        right: NodeId,
        op: JoinOp,
        terms: &mut TermStore,
    ) {
        // Propagate demands
        self.propagate_join_demands(id, left, right, op, terms);

        // Get current state
        let (left_seen, right_seen) = {
            let node = self.get_node(id).unwrap();
            match &node.kind {
                NodeKind::Join {
                    left_seen,
                    right_seen,
                    ..
                } => (*left_seen, *right_seen),
                _ => return,
            }
        };

        // Check for blocking rule
        let left_len = self.get_node(left).map(|n| n.state.out_vec.len()).unwrap_or(0);
        let right_len = self.get_node(right).map(|n| n.state.out_vec.len()).unwrap_or(0);

        // Check exhaustion state of children
        let left_exhausted = self.get_node(left).map(|n| n.state.exhausted).unwrap_or(true);
        let right_exhausted = self.get_node(right).map(|n| n.state.exhausted).unwrap_or(true);

        // Block on emptiness (with seed_turn for dual symmetry)
        if left_len == 0 && right_len == 0 {
            // If both children are exhausted and empty, join is exhausted
            if left_exhausted && right_exhausted {
                if let Some(node) = self.get_node_mut(id) {
                    node.state.exhausted = true;
                }
                return;
            }

            // Check if either child already has goals (from propagate_join_demands)
            // If so, don't add unconstrained - just activate
            let left_has_goals = self
                .get_node(left)
                .map(|n| !n.state.demand_goals.is_empty())
                .unwrap_or(false);
            let right_has_goals = self
                .get_node(right)
                .map(|n| !n.state.demand_goals.is_empty())
                .unwrap_or(false);

            // If either already has goals, only activate the ones with goals
            // (Don't activate without goals - that causes default unconstrained expansion)
            if left_has_goals || right_has_goals {
                if left_has_goals && !left_exhausted {
                    self.activate(left);
                }
                if right_has_goals && !right_exhausted {
                    self.activate(right);
                }
                return;
            }

            // Neither child has goals yet - seed one with unconstrained
            // Prefer Atom side for seeding (symmetry under dual)
            let left_is_atom = self
                .get_node(left)
                .map(|n| matches!(n.kind, NodeKind::Atom { .. }))
                .unwrap_or(false);
            let right_is_atom = self
                .get_node(right)
                .map(|n| matches!(n.kind, NodeKind::Atom { .. }))
                .unwrap_or(false);

            // If one side is Atom and other is not, seed the Atom side
            if left_is_atom && !right_is_atom && !left_exhausted {
                self.add_demand(left, Goal::unconstrained(), terms);
                self.activate(left);
                return;
            }
            if right_is_atom && !left_is_atom && !right_exhausted {
                self.add_demand(right, Goal::unconstrained(), terms);
                self.activate(right);
                return;
            }

            // Both Atoms or neither - use alternation
            let seed_turn = {
                let node = self.get_node(id).unwrap();
                match &node.kind {
                    NodeKind::Join { seed_turn, .. } => *seed_turn,
                    _ => 0,
                }
            };
            if seed_turn == 0 && !left_exhausted {
                // Seed left with unconstrained goal (needed for goal-aware atom pruning)
                self.add_demand(left, Goal::unconstrained(), terms);
                self.activate(left);
                if let Some(node) = self.get_node_mut(id) {
                    if let NodeKind::Join {
                        seed_turn: ref mut st,
                        ..
                    } = node.kind
                    {
                        *st = 1;
                    }
                }
            } else if !right_exhausted {
                // Seed right with unconstrained goal
                self.add_demand(right, Goal::unconstrained(), terms);
                self.activate(right);
                if let Some(node) = self.get_node_mut(id) {
                    if let NodeKind::Join {
                        seed_turn: ref mut st,
                        ..
                    } = node.kind
                    {
                        *st = 0;
                    }
                }
            } else if !left_exhausted {
                // Right exhausted but left not - seed left
                self.add_demand(left, Goal::unconstrained(), terms);
                self.activate(left);
            }
            return;
        }

        // Blocking rule: if one side empty while other non-empty
        if left_len == 0 {
            if !left_exhausted {
                self.activate(left);
            } else {
                // Left is exhausted and empty - join cannot produce more outputs
                if let Some(node) = self.get_node_mut(id) {
                    node.state.exhausted = true;
                }
            }
            return;
        }
        if right_len == 0 {
            if !right_exhausted {
                self.activate(right);
            } else {
                // Right is exhausted and empty - join cannot produce more outputs
                if let Some(node) = self.get_node_mut(id) {
                    node.state.exhausted = true;
                }
            }
            return;
        }

        // Ingest deltas and create tasks
        // Following the Python prototype: update seen counts one at a time
        // so that right tasks can use the updated left_seen as their limit.
        let mut new_tasks_left: Vec<JoinTask> = Vec::new();
        let mut new_tasks_right: Vec<JoinTask> = Vec::new();

        // Track updated seen counts
        let mut updated_left_seen = left_seen;
        let mut updated_right_seen = right_seen;

        // New left items - create tasks against existing right items
        for i in left_seen..left_len {
            updated_left_seen += 1;
            if right_seen > 0 {
                new_tasks_left.push(JoinTask {
                    side: JoinSide::Left,
                    idx: i,
                    pos: 0,
                    limit: right_seen,
                });
            }
        }

        // New right items - create tasks against ALL left items (including new ones)
        for j in right_seen..right_len {
            updated_right_seen += 1;
            if updated_left_seen > 0 {
                new_tasks_right.push(JoinTask {
                    side: JoinSide::Right,
                    idx: j,
                    pos: 0,
                    limit: updated_left_seen,
                });
            }
        }

        // Update seen counts and add new tasks
        if let Some(node) = self.get_node_mut(id) {
            if let NodeKind::Join {
                left_seen: ref mut ls,
                right_seen: ref mut rs,
                tasks_left: ref mut tl,
                tasks_right: ref mut tr,
                ..
            } = node.kind
            {
                *ls = updated_left_seen;
                *rs = updated_right_seen;
                tl.extend(new_tasks_left);
                tr.extend(new_tasks_right);
            }
        }

        // Process tasks with turn-based alternation
        let mut pairs_processed = 0;
        let mut outputs: Vec<NF<C>> = Vec::new();

        while pairs_processed < MAX_JOIN_PAIRS {
            let (has_tasks_left, has_tasks_right, turn) = {
                let node = self.get_node(id).unwrap();
                match &node.kind {
                    NodeKind::Join {
                        tasks_left,
                        tasks_right,
                        turn,
                        ..
                    } => (!tasks_left.is_empty(), !tasks_right.is_empty(), *turn),
                    _ => break,
                }
            };

            if !has_tasks_left && !has_tasks_right {
                break;
            }

            let use_left = if turn == 0 {
                has_tasks_left || !has_tasks_right
            } else {
                !has_tasks_right && has_tasks_left
            };

            if use_left && has_tasks_left {
                // Process from left queue
                let task = {
                    let node = self.get_node_mut(id).unwrap();
                    if let NodeKind::Join { tasks_left, .. } = &mut node.kind {
                        tasks_left.pop_front()
                    } else {
                        None
                    }
                };

                if let Some(mut task) = task {
                    while task.pos < task.limit && pairs_processed < MAX_JOIN_PAIRS {
                        // Get the NFs
                        let left_nf = self.get_node(left).and_then(|n| n.state.out_vec.get(task.idx)).cloned();
                        let right_nf = self.get_node(right).and_then(|n| n.state.out_vec.get(task.pos)).cloned();

                        if let (Some(l), Some(r)) = (left_nf, right_nf) {
                            let lf = self.freshen_nf(&l, terms);
                            let rf = self.freshen_nf(&r, terms);

                            let result = match op {
                                JoinOp::Compose => compose_nf(&lf, &rf, terms),
                                JoinOp::Meet => meet_nf(&lf, &rf, terms),
                            };

                            if let Some(out) = result {
                                let canon = canon_nf(&out, terms);
                                outputs.push(canon);
                            }
                        }
                        task.pos += 1;
                        pairs_processed += 1;
                    }

                    // If task not complete, put it back
                    if task.pos < task.limit {
                        if let Some(node) = self.get_node_mut(id) {
                            if let NodeKind::Join { tasks_left, .. } = &mut node.kind {
                                tasks_left.push_front(task);
                            }
                        }
                    } else {
                        // Update turn
                        if let Some(node) = self.get_node_mut(id) {
                            if let NodeKind::Join { turn, .. } = &mut node.kind {
                                *turn = 1;
                            }
                        }
                    }
                }
            } else if has_tasks_right {
                // Process from right queue
                let task = {
                    let node = self.get_node_mut(id).unwrap();
                    if let NodeKind::Join { tasks_right, .. } = &mut node.kind {
                        tasks_right.pop_front()
                    } else {
                        None
                    }
                };

                if let Some(mut task) = task {
                    while task.pos < task.limit && pairs_processed < MAX_JOIN_PAIRS {
                        // Get the NFs
                        let right_nf = self.get_node(right).and_then(|n| n.state.out_vec.get(task.idx)).cloned();
                        let left_nf = self.get_node(left).and_then(|n| n.state.out_vec.get(task.pos)).cloned();

                        if let (Some(l), Some(r)) = (left_nf, right_nf) {
                            let lf = self.freshen_nf(&l, terms);
                            let rf = self.freshen_nf(&r, terms);

                            let result = match op {
                                JoinOp::Compose => compose_nf(&lf, &rf, terms),
                                JoinOp::Meet => meet_nf(&lf, &rf, terms),
                            };

                            if let Some(out) = result {
                                let canon = canon_nf(&out, terms);
                                outputs.push(canon);
                            }
                        }
                        task.pos += 1;
                        pairs_processed += 1;
                    }

                    // If task not complete, put it back
                    if task.pos < task.limit {
                        if let Some(node) = self.get_node_mut(id) {
                            if let NodeKind::Join { tasks_right, .. } = &mut node.kind {
                                tasks_right.push_front(task);
                            }
                        }
                    } else {
                        // Update turn
                        if let Some(node) = self.get_node_mut(id) {
                            if let NodeKind::Join { turn, .. } = &mut node.kind {
                                *turn = 0;
                            }
                        }
                    }
                }
            }
        }

        // Filter outputs by join's goals (Python: any_goal_compatible(self.goals, out))
        // Get the join's demand goals for filtering
        let join_goals: Vec<Goal> = self
            .get_node(id)
            .map(|n| n.state.demand_goals.iter().cloned().collect())
            .unwrap_or_default();

        // Add outputs and notify (only if compatible with at least one goal)
        for out in outputs {
            // If no goals, emit anyway (unconstrained case)
            // Otherwise, filter by goal compatibility
            let should_emit = join_goals.is_empty()
                || join_goals.iter().any(|g| goal_matches(g, &out, terms));
            if should_emit {
                self.add_output_and_notify(id, out, terms);
            }
        }

        // Re-enqueue if more tasks remain
        let has_more = {
            let node = self.get_node(id).unwrap();
            match &node.kind {
                NodeKind::Join {
                    tasks_left,
                    tasks_right,
                    ..
                } => !tasks_left.is_empty() || !tasks_right.is_empty(),
                _ => false,
            }
        };
        if has_more {
            self.enqueue(id);
        }

        // Check if join is exhausted: both children exhausted AND all tasks processed
        let (left_exhausted, right_exhausted) = (
            self.get_node(left).map(|n| n.state.exhausted).unwrap_or(true),
            self.get_node(right).map(|n| n.state.exhausted).unwrap_or(true),
        );
        let tasks_empty = {
            let node = self.get_node(id).unwrap();
            match &node.kind {
                NodeKind::Join {
                    tasks_left,
                    tasks_right,
                    ..
                } => tasks_left.is_empty() && tasks_right.is_empty(),
                _ => true,
            }
        };

        if left_exhausted && right_exhausted && tasks_empty {
            // Also verify we've processed all inputs
            let (left_seen_final, right_seen_final) = {
                let node = self.get_node(id).unwrap();
                match &node.kind {
                    NodeKind::Join { left_seen, right_seen, .. } => (*left_seen, *right_seen),
                    _ => (0, 0),
                }
            };
            let left_len_final = self.get_node(left).map(|n| n.state.out_vec.len()).unwrap_or(0);
            let right_len_final = self.get_node(right).map(|n| n.state.out_vec.len()).unwrap_or(0);

            if left_seen_final >= left_len_final && right_seen_final >= right_len_final {
                if let Some(node) = self.get_node_mut(id) {
                    node.state.exhausted = true;
                }
            }
        }
    }

    /// Propagate demands for a join node.
    ///
    /// This implements bidirectional goal synthesis from child outputs, matching the Python prototype.
    /// For each new child output, we synthesize goals for the other child to constrain what it produces.
    fn propagate_join_demands(
        &mut self,
        id: NodeId,
        left: NodeId,
        right: NodeId,
        op: JoinOp,
        terms: &mut TermStore,
    ) {
        let goals: Vec<Goal> = {
            let node = self.get_node(id).unwrap();
            node.state.demand_goals.iter().cloned().collect()
        };

        // Propagate outer constraints based on operation type
        match op {
            JoinOp::Meet => {
                // For meet, propagate goals unchanged to both children
                for goal in &goals {
                    self.add_demand(left, goal.clone(), terms);
                    self.add_demand(right, goal.clone(), terms);
                }
            }
            JoinOp::Compose => {
                // For compose, propagate output-side constraints
                for goal in &goals {
                    if let Some(ref match_bound) = goal.match_bound {
                        self.add_demand(left, Goal::match_only(match_bound.clone()), terms);
                    }
                    if let Some(ref build_bound) = goal.build_bound {
                        self.add_demand(right, Goal::build_only(build_bound.clone()), terms);
                    }
                }
            }
        }

        // Get cursors and output lengths
        let (goal_left_seen, goal_right_seen, left_len, right_len) = {
            let left_len = self
                .get_node(left)
                .map(|n| n.state.out_vec.len())
                .unwrap_or(0);
            let right_len = self
                .get_node(right)
                .map(|n| n.state.out_vec.len())
                .unwrap_or(0);
            let node = self.get_node(id).unwrap();
            let (gls, grs) = match &node.kind {
                NodeKind::Join {
                    goal_left_seen,
                    goal_right_seen,
                    ..
                } => (*goal_left_seen, *goal_right_seen),
                _ => (0, 0),
            };
            (gls, grs, left_len, right_len)
        };

        // Synthesize goals from NEW left outputs -> constrain right
        // Only synthesize from outputs that are compatible with our goals
        if goal_left_seen < left_len {
            let new_left_outputs: Vec<NF<C>> = self
                .get_node(left)
                .map(|n| n.state.out_vec[goal_left_seen..].to_vec())
                .unwrap_or_default();

            for lnf in new_left_outputs {
                // Only synthesize if this output is goal-compatible
                // (If no goals, always synthesize to bootstrap)
                let compatible = goals.is_empty()
                    || goals.iter().any(|g| {
                        // For Compose: left output must match on match side
                        // For Meet: left output must match on both sides
                        match op {
                            JoinOp::Compose => {
                                g.match_bound.is_none()
                                    || goal_matches_boundary(
                                        g.match_bound.as_ref(),
                                        &lnf.match_boundary,
                                        terms,
                                    )
                            }
                            JoinOp::Meet => goal_matches(g, &lnf, terms),
                        }
                    });

                if !compatible {
                    continue;
                }

                match op {
                    JoinOp::Compose => {
                        let base_goals = if goals.is_empty() {
                            vec![Goal::unconstrained()]
                        } else {
                            goals.clone()
                        };
                        for g in &base_goals {
                            let new_goal = Goal::from_options(
                                Some(lnf.build_boundary.clone()),
                                g.build_bound.clone(),
                            );
                            self.add_demand(right, new_goal, terms);
                        }
                    }
                    JoinOp::Meet => {
                        let new_goal = Goal::both(
                            lnf.match_boundary.clone(),
                            lnf.build_boundary.clone(),
                        );
                        self.add_demand(right, new_goal, terms);
                    }
                }
            }
        }

        // Synthesize goals from NEW right outputs -> constrain left
        if goal_right_seen < right_len {
            let new_right_outputs: Vec<NF<C>> = self
                .get_node(right)
                .map(|n| n.state.out_vec[goal_right_seen..].to_vec())
                .unwrap_or_default();

            for rnf in new_right_outputs {
                // Only synthesize if this output is goal-compatible
                let compatible = goals.is_empty()
                    || goals.iter().any(|g| {
                        match op {
                            JoinOp::Compose => {
                                g.build_bound.is_none()
                                    || goal_matches_boundary(
                                        g.build_bound.as_ref(),
                                        &rnf.build_boundary,
                                        terms,
                                    )
                            }
                            JoinOp::Meet => goal_matches(g, &rnf, terms),
                        }
                    });

                if !compatible {
                    continue;
                }

                match op {
                    JoinOp::Compose => {
                        let base_goals = if goals.is_empty() {
                            vec![Goal::unconstrained()]
                        } else {
                            goals.clone()
                        };
                        for g in &base_goals {
                            let new_goal = Goal::from_options(
                                g.match_bound.clone(),
                                Some(rnf.match_boundary.clone()),
                            );
                            self.add_demand(left, new_goal, terms);
                        }
                    }
                    JoinOp::Meet => {
                        let new_goal = Goal::both(
                            rnf.match_boundary.clone(),
                            rnf.build_boundary.clone(),
                        );
                        self.add_demand(left, new_goal, terms);
                    }
                }
            }
        }

        // Update cursors
        if let Some(node) = self.get_node_mut(id) {
            if let NodeKind::Join {
                goal_left_seen: ref mut gls,
                goal_right_seen: ref mut grs,
                ..
            } = node.kind
            {
                *gls = left_len;
                *grs = right_len;
            }
        }
    }

    /// Step a Table node: propagate goals to body, pull answers.
    fn step_table(&mut self, id: NodeId, body_root: Option<NodeId>, terms: &mut TermStore) {
        let body = match body_root {
            Some(b) => b,
            None => {
                // No body means no answers possible - mark exhausted
                if let Some(node) = self.get_node_mut(id) {
                    node.state.exhausted = true;
                }
                return;
            }
        };

        // Get registered goals from both sources:
        // - node.kind.goals: goals registered by Call nodes
        // - node.state.demand_goals: goals added directly (e.g., for root queries)
        let goals: Vec<Goal> = {
            let node = self.get_node(id).unwrap();
            let mut all_goals: Vec<Goal> = node.state.demand_goals.iter().cloned().collect();
            if let NodeKind::Table { goals, .. } = &node.kind {
                for g in goals {
                    if !all_goals.contains(g) {
                        all_goals.push(g.clone());
                    }
                }
            }
            all_goals
        };

        if goals.is_empty() {
            return;
        }

        // Propagate goals to body
        for goal in goals {
            self.add_demand(body, goal, terms);
        }

        // Activate body (only if not exhausted)
        let body_exhausted = self
            .get_node(body)
            .map(|n| n.state.exhausted)
            .unwrap_or(true);
        if !body_exhausted {
            self.activate(body);
        }

        // Pull new answers from body
        let body_pos = {
            let node = self.get_node(id).unwrap();
            match &node.kind {
                NodeKind::Table { body_pos, .. } => *body_pos,
                _ => return,
            }
        };

        let body_len = self.get_node(body).map(|n| n.state.out_vec.len()).unwrap_or(0);

        let mut outputs: Vec<NF<C>> = Vec::new();
        for i in body_pos..body_len {
            if let Some(nf) = self.get_node(body).and_then(|n| n.state.out_vec.get(i)).cloned() {
                outputs.push(nf);
            }
        }

        // Update body_pos
        if let Some(node) = self.get_node_mut(id) {
            if let NodeKind::Table { body_pos, .. } = &mut node.kind {
                *body_pos = body_len;
            }
        }

        // Add outputs
        for out in outputs {
            self.add_output_and_notify(id, out, terms);
        }

        // Check if table is exhausted: body is exhausted AND we've consumed all its outputs
        let body_exhausted = self
            .get_node(body)
            .map(|n| n.state.exhausted)
            .unwrap_or(true);
        let body_len_final = self.get_node(body).map(|n| n.state.out_vec.len()).unwrap_or(0);
        let body_pos_final = {
            let node = self.get_node(id).unwrap();
            match &node.kind {
                NodeKind::Table { body_pos, .. } => *body_pos,
                _ => 0,
            }
        };

        if body_exhausted && body_pos_final >= body_len_final {
            if let Some(node) = self.get_node_mut(id) {
                node.state.exhausted = true;
            }
        }
    }

    /// Step a Call node: register goals with table, pull matching answers.
    ///
    /// Key invariant from Python prototype: if Call has no goals, return early.
    /// DO NOT default to unconstrained - that causes recursive relations to
    /// compute their entire output space instead of just the demanded portion.
    fn step_call(&mut self, id: NodeId, table_id: NodeId, terms: &mut TermStore) {
        // Check exhausted and no goals - return early like Python prototype
        let (exhausted, goals) = {
            let node = self.get_node(id).unwrap();
            let goals: Vec<Goal> = node.state.demand_goals.iter().cloned().collect();
            (node.state.exhausted, goals)
        };

        if exhausted || goals.is_empty() {
            return;
        }


        // Register new goals with table
        let already_registered: HashSet<Goal> = {
            let node = self.get_node(id).unwrap();
            match &node.kind {
                NodeKind::Call {
                    registered_goals, ..
                } => registered_goals.clone(),
                _ => return,
            }
        };

        let mut new_goals_registered = false;
        for goal in &goals {
            let canon = canon_goal(goal, terms);
            if !already_registered.contains(&canon) {
                new_goals_registered = true;
                // Register with table
                if let Some(table) = self.get_node_mut(table_id) {
                    if let NodeKind::Table {
                        goals: ref mut tg, ..
                    } = table.kind
                    {
                        tg.insert(canon.clone());
                    }
                    table.state.need = table.state.need.saturating_add(1);
                }
                self.enqueue(table_id);

                // Mark as registered
                if let Some(node) = self.get_node_mut(id) {
                    if let NodeKind::Call {
                        registered_goals, ..
                    } = &mut node.kind
                    {
                        registered_goals.insert(canon);
                    }
                }
            }
        }

        // When new goals are registered, reset table_pos to rescan all table outputs
        // with the new goals. Old outputs may now match the new goals.
        if new_goals_registered {
            if let Some(node) = self.get_node_mut(id) {
                if let NodeKind::Call { table_pos, .. } = &mut node.kind {
                    *table_pos = 0;
                }
            }
        }

        // Activate table (only if not exhausted)
        let table_exhausted = self
            .get_node(table_id)
            .map(|n| n.state.exhausted)
            .unwrap_or(true);
        if !table_exhausted {
            self.activate(table_id);
        }

        // Pull matching answers from table
        let table_pos = {
            let node = self.get_node(id).unwrap();
            match &node.kind {
                NodeKind::Call { table_pos, .. } => *table_pos,
                _ => return,
            }
        };

        let table_len = self.get_node(table_id).map(|n| n.state.out_vec.len()).unwrap_or(0);

        let mut outputs: Vec<NF<C>> = Vec::new();
        for i in table_pos..table_len {
            if let Some(nf) = self.get_node(table_id).and_then(|n| n.state.out_vec.get(i)).cloned() {
                // Check if NF matches any of our goals
                let matches_goal = goals.iter().any(|g| goal_matches(g, &nf, terms));
                if matches_goal {
                    outputs.push(nf);
                }
            }
        }

        // Update table_pos
        if let Some(node) = self.get_node_mut(id) {
            if let NodeKind::Call { table_pos, .. } = &mut node.kind {
                *table_pos = table_len;
            }
        }

        // Add outputs
        for out in outputs {
            self.add_output_and_notify(id, out, terms);
        }

        // Check if call is exhausted: table is exhausted AND we've consumed all its outputs
        let table_exhausted = self
            .get_node(table_id)
            .map(|n| n.state.exhausted)
            .unwrap_or(true);
        let table_len_final = self.get_node(table_id).map(|n| n.state.out_vec.len()).unwrap_or(0);
        let table_pos_final = {
            let node = self.get_node(id).unwrap();
            match &node.kind {
                NodeKind::Call { table_pos, .. } => *table_pos,
                _ => 0,
            }
        };

        if table_exhausted && table_pos_final >= table_len_final {
            if let Some(node) = self.get_node_mut(id) {
                node.state.exhausted = true;
            }
        }
    }

    /// Add an output to a node and notify dependents.
    fn add_output_and_notify(&mut self, id: NodeId, nf: NF<C>, terms: &mut TermStore) {
        let added = {
            let node = self.get_node_mut(id).unwrap();
            node.state.add_output(nf, terms)
        };

        if added {
            // Notify dependents
            let dependents: Vec<NodeId> = {
                let node = self.get_node(id).unwrap();
                node.state.dependents.clone()
            };
            for dep in dependents {
                self.enqueue(dep);
            }
        }
    }
}

/// Extracted kind data for stepping (to avoid borrow issues).
enum KindData {
    Atom,
    Or { left: NodeId, right: NodeId },
    Join { left: NodeId, right: NodeId, op: JoinOp },
    Table { body_root: Option<NodeId> },
    Call { table_id: NodeId },
}

fn extract_kind_data<C>(kind: &NodeKind<C>) -> KindData {
    match kind {
        NodeKind::Atom { .. } => KindData::Atom,
        NodeKind::Or { left, right, .. } => KindData::Or {
            left: *left,
            right: *right,
        },
        NodeKind::Join { left, right, op, .. } => KindData::Join {
            left: *left,
            right: *right,
            op: *op,
        },
        NodeKind::Table { body_root, .. } => KindData::Table {
            body_root: *body_root,
        },
        NodeKind::Call { table_id, .. } => KindData::Call {
            table_id: *table_id,
        },
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
    // RUNTIME BASIC TESTS
    // ========================================================================

    #[test]
    fn runtime_initially_empty() {
        let rt: Runtime<()> = Runtime::new();
        assert!(rt.nodes.is_empty());
        assert!(rt.worklist.is_empty());
        assert!(rt.scheduled.is_empty());
        assert_eq!(rt.var_counter, 0);
    }

    #[test]
    fn runtime_add_node() {
        let (symbols, mut terms) = setup();
        let z = symbols.intern("z");
        let z_term = terms.app0(z);
        let nf: NF<()> = NF::new(smallvec![z_term], smallvec![z_term]);

        let mut rt: Runtime<()> = Runtime::new();
        let id = rt.add_node(Node::atom(NodeId::new(0), nf, &mut terms));

        assert_eq!(id, NodeId::new(0));
        assert_eq!(rt.nodes.len(), 1);
    }

    #[test]
    fn runtime_enqueue_deduplicates() {
        let mut rt: Runtime<()> = Runtime::new();
        rt.nodes.push(Node::table(NodeId::new(0), "test".to_string()));

        rt.enqueue(NodeId::new(0));
        assert_eq!(rt.worklist.len(), 1);

        rt.enqueue(NodeId::new(0));
        assert_eq!(rt.worklist.len(), 1); // Still 1, not 2
    }

    #[test]
    fn runtime_activate_sets_need() {
        let mut rt: Runtime<()> = Runtime::new();
        rt.nodes.push(Node::table(NodeId::new(0), "test".to_string()));

        assert_eq!(rt.nodes[0].state.need, 0);
        rt.activate(NodeId::new(0));
        assert_eq!(rt.nodes[0].state.need, 1);
        assert!(rt.scheduled.contains(&NodeId::new(0)));
    }

    #[test]
    fn runtime_fresh_var() {
        let mut rt: Runtime<()> = Runtime::new();
        assert_eq!(rt.fresh_var(), 0);
        assert_eq!(rt.fresh_var(), 1);
        assert_eq!(rt.fresh_var(), 2);
    }

    // ========================================================================
    // ATOM NODE STEPPING TESTS
    // ========================================================================

    #[test]
    fn step_atom_emits_once() {
        let (symbols, mut terms) = setup();
        let z = symbols.intern("z");
        let z_term = terms.app0(z);
        let nf: NF<()> = NF::new(smallvec![z_term], smallvec![z_term]);

        let mut rt: Runtime<()> = Runtime::new();
        let id = rt.add_node(Node::atom(NodeId::new(0), nf, &mut terms));
        rt.activate(id);
        // Goal-aware pruning: atoms only emit if demanded
        rt.add_demand(id, Goal::unconstrained(), &mut terms);

        // Step once
        rt.step_node(id, &mut terms);

        // Should have emitted the NF
        assert_eq!(rt.nodes[0].state.out_vec.len(), 1);

        // Step again - should not emit again
        rt.step_node(id, &mut terms);
        assert_eq!(rt.nodes[0].state.out_vec.len(), 1);
    }

    // ========================================================================
    // OR NODE STEPPING TESTS
    // ========================================================================

    #[test]
    fn step_or_interleaves() {
        let (symbols, mut terms) = setup();
        let z = symbols.intern("z");
        let s = symbols.intern("s");
        let z_term = terms.app0(z);
        let s_z = terms.app1(s, z_term);

        let nf1: NF<()> = NF::new(smallvec![z_term], smallvec![z_term]);
        let nf2: NF<()> = NF::new(smallvec![s_z], smallvec![s_z]);

        let mut rt: Runtime<()> = Runtime::new();
        let left_id = rt.add_node(Node::atom(NodeId::new(0), nf1, &mut terms));
        let right_id = rt.add_node(Node::atom(NodeId::new(1), nf2, &mut terms));
        let or_id = rt.add_node(Node::or(NodeId::new(2), left_id, right_id));

        rt.add_edge(left_id, or_id);
        rt.add_edge(right_id, or_id);

        // Activate and step atoms first (with demands for goal-aware pruning)
        rt.activate(left_id);
        rt.add_demand(left_id, Goal::unconstrained(), &mut terms);
        rt.step_node(left_id, &mut terms);
        rt.activate(right_id);
        rt.add_demand(right_id, Goal::unconstrained(), &mut terms);
        rt.step_node(right_id, &mut terms);

        // Now step Or
        rt.activate(or_id);
        rt.step_node(or_id, &mut terms);

        // Should have pulled from left first (turn = 0)
        assert_eq!(rt.nodes[2].state.out_vec.len(), 1);

        // Step again
        rt.step_node(or_id, &mut terms);

        // Should have pulled from right (turn = 1)
        assert_eq!(rt.nodes[2].state.out_vec.len(), 2);
    }

    // ========================================================================
    // JOIN NODE STEPPING TESTS
    // ========================================================================

    #[test]
    fn step_join_compose_basic() {
        let (symbols, mut terms) = setup();
        let z = symbols.intern("z");
        let z_term = terms.app0(z);
        let v0 = terms.var(0);

        // Left: z -> z
        // Right: z -> $0 (introduces a variable)
        let nf_left: NF<()> = NF::new(smallvec![z_term], smallvec![z_term]);
        let nf_right: NF<()> = NF::new(smallvec![z_term], smallvec![v0]);

        let mut rt: Runtime<()> = Runtime::new();
        let left_id = rt.add_node(Node::atom(NodeId::new(0), nf_left, &mut terms));
        let right_id = rt.add_node(Node::atom(NodeId::new(1), nf_right, &mut terms));
        let join_id = rt.add_node(Node::join(NodeId::new(2), left_id, right_id, JoinOp::Compose));

        rt.add_edge(left_id, join_id);
        rt.add_edge(right_id, join_id);

        // Activate and step atoms (with demands for goal-aware pruning)
        rt.activate(left_id);
        rt.add_demand(left_id, Goal::unconstrained(), &mut terms);
        rt.step_node(left_id, &mut terms);
        rt.activate(right_id);
        rt.add_demand(right_id, Goal::unconstrained(), &mut terms);
        rt.step_node(right_id, &mut terms);

        // Step join multiple times
        rt.activate(join_id);
        rt.step_node(join_id, &mut terms);
        rt.step_node(join_id, &mut terms);

        // Should have composed to produce z -> $0
        assert_eq!(rt.nodes[2].state.out_vec.len(), 1);
    }

    #[test]
    fn step_join_meet_basic() {
        let (symbols, mut terms) = setup();
        let z = symbols.intern("z");
        let z_term = terms.app0(z);

        // Both sides: z -> z
        let nf: NF<()> = NF::new(smallvec![z_term], smallvec![z_term]);

        let mut rt: Runtime<()> = Runtime::new();
        let left_id = rt.add_node(Node::atom(NodeId::new(0), nf.clone(), &mut terms));
        let right_id = rt.add_node(Node::atom(NodeId::new(1), nf, &mut terms));
        let join_id = rt.add_node(Node::join(NodeId::new(2), left_id, right_id, JoinOp::Meet));

        rt.add_edge(left_id, join_id);
        rt.add_edge(right_id, join_id);

        // Activate and step atoms (with demands for goal-aware pruning)
        rt.activate(left_id);
        rt.add_demand(left_id, Goal::unconstrained(), &mut terms);
        rt.step_node(left_id, &mut terms);
        rt.activate(right_id);
        rt.add_demand(right_id, Goal::unconstrained(), &mut terms);
        rt.step_node(right_id, &mut terms);

        // Step join multiple times
        rt.activate(join_id);
        rt.step_node(join_id, &mut terms);
        rt.step_node(join_id, &mut terms);

        // Should have produced z -> z (meet of identical NFs)
        assert_eq!(rt.nodes[2].state.out_vec.len(), 1);
    }

    // ========================================================================
    // TABLE AND CALL TESTS
    // ========================================================================

    #[test]
    fn table_and_call_basic() {
        let (symbols, mut terms) = setup();
        let z = symbols.intern("z");
        let z_term = terms.app0(z);
        let nf: NF<()> = NF::new(smallvec![z_term], smallvec![z_term]);

        let mut rt: Runtime<()> = Runtime::new();

        // Create table and its body (just an atom)
        let table_id = rt.add_node(Node::table(NodeId::new(0), "test".to_string()));
        let body_id = rt.add_node(Node::atom(NodeId::new(1), nf, &mut terms));

        // Set body root
        rt.nodes[0].set_body_root(body_id);
        rt.add_edge(body_id, table_id);

        // Create call node
        let call_id = rt.add_node(Node::call(NodeId::new(2), table_id));
        rt.add_edge(table_id, call_id);

        // Register a goal with call
        rt.nodes[2].state.add_demand(Goal::unconstrained(), &mut terms);

        // Activate and step
        rt.activate(call_id);
        rt.step_node(call_id, &mut terms);

        // Table should have the goal
        if let NodeKind::Table { ref goals, .. } = rt.nodes[0].kind {
            assert!(!goals.is_empty());
        }

        // Step table
        rt.step_node(table_id, &mut terms);

        // Step body (atom)
        rt.activate(body_id);
        rt.step_node(body_id, &mut terms);

        // Step table again to pull answer
        rt.step_node(table_id, &mut terms);

        // Table should have output
        assert_eq!(rt.nodes[0].state.out_vec.len(), 1);

        // Step call again to pull from table
        rt.step_node(call_id, &mut terms);

        // Call should have output
        assert_eq!(rt.nodes[2].state.out_vec.len(), 1);
    }
}
