use smallvec::SmallVec;

/// Unique identifier for a goal in the GoalStore.
pub type GoalId = u32;

/// Unique identifier for a rule (which compiles to an NF).
pub type RuleId = u32;

/// Unique identifier for a relation (used for recursion/tabling).
pub type RelId = u32;

/// The Goal IR represents relational programs as n-ary trees.
///
/// Goals are stored in a GoalStore and referenced by GoalId.
/// This representation is designed for efficient traversal and
/// pattern matching during evaluation.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Goal {
    /// Always fails - produces no answers.
    Fail,

    /// A single rewrite rule (compiles to an NF).
    Rule(RuleId),

    /// Disjunction: try alternatives in order.
    /// Produces answers from any branch that succeeds.
    Alt(SmallVec<[GoalId; 2]>),

    /// Sequential composition: apply goals in sequence.
    /// The output of each goal feeds into the next.
    Seq(SmallVec<[GoalId; 4]>),

    /// Conjunction/intersection: both goals must agree.
    /// Like logical AND - the answer must satisfy all goals.
    Both(SmallVec<[GoalId; 4]>),

    /// Recursive definition: defines a relation body.
    /// Fix(rel_id, body) means rel_id is defined as body.
    Fix(RelId, GoalId),

    /// Recursive call: invoke a relation.
    /// Used within Fix bodies to enable recursion.
    Call(RelId),
}

/// Storage for goals and rules.
///
/// Goals reference each other by GoalId.
/// Rules reference NFs by RuleId (stored separately).
#[derive(Debug, Default)]
pub struct GoalStore {
    goals: Vec<Goal>,
    rel_names: Vec<String>, // Relation names for debugging
}

impl GoalStore {
    /// Create a new empty goal store.
    pub fn new() -> Self {
        Self {
            goals: Vec::new(),
            rel_names: Vec::new(),
        }
    }

    /// Add a goal and return its GoalId.
    pub fn add_goal(&mut self, goal: Goal) -> GoalId {
        let id = self.goals.len() as GoalId;
        self.goals.push(goal);
        id
    }

    /// Get a goal by its ID.
    pub fn get(&self, id: GoalId) -> Option<&Goal> {
        self.goals.get(id as usize)
    }

    /// Number of goals in the store.
    pub fn len(&self) -> usize {
        self.goals.len()
    }

    /// Check if the store is empty.
    pub fn is_empty(&self) -> bool {
        self.goals.is_empty()
    }

    /// Add the Fail goal (reuses if already exists).
    pub fn fail(&mut self) -> GoalId {
        // Check if we already have a Fail goal
        for (i, g) in self.goals.iter().enumerate() {
            if matches!(g, Goal::Fail) {
                return i as GoalId;
            }
        }
        self.add_goal(Goal::Fail)
    }

    /// Add a rule goal.
    pub fn rule(&mut self, rule_id: RuleId) -> GoalId {
        self.add_goal(Goal::Rule(rule_id))
    }

    /// Add an Alt (disjunction) goal.
    pub fn alt(&mut self, branches: impl Into<SmallVec<[GoalId; 2]>>) -> GoalId {
        let branches = branches.into();
        if branches.is_empty() {
            return self.fail();
        }
        if branches.len() == 1 {
            return branches[0];
        }
        self.add_goal(Goal::Alt(branches))
    }

    /// Add a Seq (sequential composition) goal.
    pub fn seq(&mut self, steps: impl Into<SmallVec<[GoalId; 4]>>) -> GoalId {
        let steps = steps.into();
        if steps.is_empty() {
            // Empty sequence is identity - but we don't have identity goal
            // For now, return fail (should probably be handled differently)
            return self.fail();
        }
        if steps.len() == 1 {
            return steps[0];
        }
        self.add_goal(Goal::Seq(steps))
    }

    /// Add a Both (conjunction) goal.
    pub fn both(&mut self, goals: impl Into<SmallVec<[GoalId; 4]>>) -> GoalId {
        let goals = goals.into();
        if goals.is_empty() {
            return self.fail();
        }
        if goals.len() == 1 {
            return goals[0];
        }
        self.add_goal(Goal::Both(goals))
    }

    /// Add a Fix (recursive definition) goal.
    pub fn fix(&mut self, rel_id: RelId, body: GoalId) -> GoalId {
        self.add_goal(Goal::Fix(rel_id, body))
    }

    /// Add a Call (recursive call) goal.
    pub fn call(&mut self, rel_id: RelId) -> GoalId {
        self.add_goal(Goal::Call(rel_id))
    }

    /// Register a new relation and return its RelId.
    pub fn new_rel(&mut self, name: &str) -> RelId {
        let id = self.rel_names.len() as RelId;
        self.rel_names.push(name.to_string());
        id
    }

    /// Get the name of a relation.
    pub fn rel_name(&self, id: RelId) -> Option<&str> {
        self.rel_names.get(id as usize).map(|s| s.as_str())
    }

    /// Iterator over all goals.
    pub fn iter(&self) -> impl Iterator<Item = (GoalId, &Goal)> {
        self.goals.iter().enumerate().map(|(i, g)| (i as GoalId, g))
    }
}

/// Builder for constructing goal programs.
///
/// Provides a convenient DSL for building goal structures.
pub struct GoalBuilder<'a> {
    store: &'a mut GoalStore,
}

impl<'a> GoalBuilder<'a> {
    /// Create a new builder.
    pub fn new(store: &'a mut GoalStore) -> Self {
        Self { store }
    }

    /// Build a Fail goal.
    pub fn fail(&mut self) -> GoalId {
        self.store.fail()
    }

    /// Build a Rule goal.
    pub fn rule(&mut self, rule_id: RuleId) -> GoalId {
        self.store.rule(rule_id)
    }

    /// Build an Alt (disjunction) from two goals.
    pub fn or(&mut self, a: GoalId, b: GoalId) -> GoalId {
        self.store.alt(smallvec::smallvec![a, b])
    }

    /// Build a Seq (sequence) from two goals.
    pub fn then(&mut self, a: GoalId, b: GoalId) -> GoalId {
        self.store.seq(smallvec::smallvec![a, b])
    }

    /// Build a Both (conjunction) from two goals.
    pub fn and(&mut self, a: GoalId, b: GoalId) -> GoalId {
        self.store.both(smallvec::smallvec![a, b])
    }

    /// Build a Fix (recursive definition).
    pub fn fix(&mut self, rel_id: RelId, body: GoalId) -> GoalId {
        self.store.fix(rel_id, body)
    }

    /// Build a Call (recursive call).
    pub fn call(&mut self, rel_id: RelId) -> GoalId {
        self.store.call(rel_id)
    }

    /// Register a new relation.
    pub fn new_rel(&mut self, name: &str) -> RelId {
        self.store.new_rel(name)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    // ========== GOAL STORE TESTS ==========

    #[test]
    fn new_store_is_empty() {
        let store = GoalStore::new();
        assert!(store.is_empty());
        assert_eq!(store.len(), 0);
    }

    #[test]
    fn add_and_get_goal() {
        let mut store = GoalStore::new();
        let id = store.add_goal(Goal::Fail);
        assert_eq!(id, 0);
        assert_eq!(store.get(id), Some(&Goal::Fail));
    }

    #[test]
    fn add_multiple_goals() {
        let mut store = GoalStore::new();
        let id1 = store.add_goal(Goal::Fail);
        let id2 = store.add_goal(Goal::Rule(0));
        let id3 = store.add_goal(Goal::Rule(1));

        assert_eq!(id1, 0);
        assert_eq!(id2, 1);
        assert_eq!(id3, 2);
        assert_eq!(store.len(), 3);
    }

    #[test]
    fn get_invalid_id_returns_none() {
        let store = GoalStore::new();
        assert_eq!(store.get(0), None);
        assert_eq!(store.get(100), None);
    }

    #[test]
    fn fail_reuses_existing() {
        let mut store = GoalStore::new();
        let id1 = store.fail();
        let id2 = store.fail();
        assert_eq!(id1, id2, "Fail should be reused");
        assert_eq!(store.len(), 1);
    }

    #[test]
    fn rule_creates_new_goal() {
        let mut store = GoalStore::new();
        let id1 = store.rule(0);
        let id2 = store.rule(1);
        assert_ne!(id1, id2);
        assert_eq!(store.get(id1), Some(&Goal::Rule(0)));
        assert_eq!(store.get(id2), Some(&Goal::Rule(1)));
    }

    // ========== ALT TESTS ==========

    #[test]
    fn alt_empty_becomes_fail() {
        let mut store = GoalStore::new();
        let empty: SmallVec<[GoalId; 2]> = SmallVec::new();
        let id = store.alt(empty);
        assert_eq!(store.get(id), Some(&Goal::Fail));
    }

    #[test]
    fn alt_singleton_returns_element() {
        let mut store = GoalStore::new();
        let r = store.rule(0);
        let alt_id = store.alt(smallvec::smallvec![r]);
        assert_eq!(alt_id, r, "Singleton Alt should return the element");
    }

    #[test]
    fn alt_multiple_creates_alt() {
        let mut store = GoalStore::new();
        let r1 = store.rule(0);
        let r2 = store.rule(1);
        let alt_id = store.alt(smallvec::smallvec![r1, r2]);

        match store.get(alt_id) {
            Some(Goal::Alt(branches)) => {
                assert_eq!(branches.len(), 2);
                assert_eq!(branches[0], r1);
                assert_eq!(branches[1], r2);
            }
            _ => panic!("Expected Alt goal"),
        }
    }

    // ========== SEQ TESTS ==========

    #[test]
    fn seq_empty_becomes_fail() {
        let mut store = GoalStore::new();
        let empty: SmallVec<[GoalId; 4]> = SmallVec::new();
        let id = store.seq(empty);
        assert_eq!(store.get(id), Some(&Goal::Fail));
    }

    #[test]
    fn seq_singleton_returns_element() {
        let mut store = GoalStore::new();
        let r = store.rule(0);
        let seq_id = store.seq(smallvec::smallvec![r]);
        assert_eq!(seq_id, r);
    }

    #[test]
    fn seq_multiple_creates_seq() {
        let mut store = GoalStore::new();
        let r1 = store.rule(0);
        let r2 = store.rule(1);
        let r3 = store.rule(2);
        let seq_id = store.seq(smallvec::smallvec![r1, r2, r3]);

        match store.get(seq_id) {
            Some(Goal::Seq(steps)) => {
                assert_eq!(steps.len(), 3);
                assert_eq!(steps[0], r1);
                assert_eq!(steps[1], r2);
                assert_eq!(steps[2], r3);
            }
            _ => panic!("Expected Seq goal"),
        }
    }

    // ========== BOTH TESTS ==========

    #[test]
    fn both_empty_becomes_fail() {
        let mut store = GoalStore::new();
        let empty: SmallVec<[GoalId; 4]> = SmallVec::new();
        let id = store.both(empty);
        assert_eq!(store.get(id), Some(&Goal::Fail));
    }

    #[test]
    fn both_singleton_returns_element() {
        let mut store = GoalStore::new();
        let r = store.rule(0);
        let both_id = store.both(smallvec::smallvec![r]);
        assert_eq!(both_id, r);
    }

    #[test]
    fn both_multiple_creates_both() {
        let mut store = GoalStore::new();
        let r1 = store.rule(0);
        let r2 = store.rule(1);
        let both_id = store.both(smallvec::smallvec![r1, r2]);

        match store.get(both_id) {
            Some(Goal::Both(goals)) => {
                assert_eq!(goals.len(), 2);
                assert_eq!(goals[0], r1);
                assert_eq!(goals[1], r2);
            }
            _ => panic!("Expected Both goal"),
        }
    }

    // ========== FIX/CALL TESTS ==========

    #[test]
    fn fix_creates_fix_goal() {
        let mut store = GoalStore::new();
        let body = store.rule(0);
        let fix_id = store.fix(0, body);

        match store.get(fix_id) {
            Some(Goal::Fix(rel_id, goal_id)) => {
                assert_eq!(*rel_id, 0);
                assert_eq!(*goal_id, body);
            }
            _ => panic!("Expected Fix goal"),
        }
    }

    #[test]
    fn call_creates_call_goal() {
        let mut store = GoalStore::new();
        let call_id = store.call(0);

        match store.get(call_id) {
            Some(Goal::Call(rel_id)) => {
                assert_eq!(*rel_id, 0);
            }
            _ => panic!("Expected Call goal"),
        }
    }

    #[test]
    fn fix_with_recursive_call() {
        let mut store = GoalStore::new();
        let rel_id = store.new_rel("append");

        // Create a recursive goal: append = base | (rule ; append)
        let base = store.rule(0);
        let recursive_call = store.call(rel_id);
        let step = store.rule(1);
        let recursive_step = store.seq(smallvec::smallvec![step, recursive_call]);
        let body = store.alt(smallvec::smallvec![base, recursive_step]);
        let fix = store.fix(rel_id, body);

        assert!(store.get(fix).is_some());
        assert_eq!(store.rel_name(rel_id), Some("append"));
    }

    // ========== RELATION NAME TESTS ==========

    #[test]
    fn new_rel_returns_sequential_ids() {
        let mut store = GoalStore::new();
        let id1 = store.new_rel("append");
        let id2 = store.new_rel("reverse");
        let id3 = store.new_rel("member");

        assert_eq!(id1, 0);
        assert_eq!(id2, 1);
        assert_eq!(id3, 2);
    }

    #[test]
    fn rel_name_returns_correct_name() {
        let mut store = GoalStore::new();
        let id = store.new_rel("myrel");
        assert_eq!(store.rel_name(id), Some("myrel"));
    }

    #[test]
    fn rel_name_invalid_returns_none() {
        let store = GoalStore::new();
        assert_eq!(store.rel_name(0), None);
    }

    // ========== ITERATOR TESTS ==========

    #[test]
    fn iter_over_goals() {
        let mut store = GoalStore::new();
        store.fail();
        store.rule(0);
        store.rule(1);

        let items: Vec<_> = store.iter().collect();
        assert_eq!(items.len(), 3);
        assert_eq!(items[0], (0, &Goal::Fail));
        assert_eq!(items[1], (1, &Goal::Rule(0)));
        assert_eq!(items[2], (2, &Goal::Rule(1)));
    }

    // ========== GOAL BUILDER TESTS ==========

    #[test]
    fn builder_fail() {
        let mut store = GoalStore::new();
        let mut builder = GoalBuilder::new(&mut store);
        let id = builder.fail();
        assert_eq!(store.get(id), Some(&Goal::Fail));
    }

    #[test]
    fn builder_or() {
        let mut store = GoalStore::new();
        let mut builder = GoalBuilder::new(&mut store);
        let a = builder.rule(0);
        let b = builder.rule(1);
        let or_id = builder.or(a, b);

        match store.get(or_id) {
            Some(Goal::Alt(branches)) => {
                assert_eq!(branches.len(), 2);
            }
            _ => panic!("Expected Alt"),
        }
    }

    #[test]
    fn builder_then() {
        let mut store = GoalStore::new();
        let mut builder = GoalBuilder::new(&mut store);
        let a = builder.rule(0);
        let b = builder.rule(1);
        let seq_id = builder.then(a, b);

        match store.get(seq_id) {
            Some(Goal::Seq(steps)) => {
                assert_eq!(steps.len(), 2);
            }
            _ => panic!("Expected Seq"),
        }
    }

    #[test]
    fn builder_and() {
        let mut store = GoalStore::new();
        let mut builder = GoalBuilder::new(&mut store);
        let a = builder.rule(0);
        let b = builder.rule(1);
        let both_id = builder.and(a, b);

        match store.get(both_id) {
            Some(Goal::Both(goals)) => {
                assert_eq!(goals.len(), 2);
            }
            _ => panic!("Expected Both"),
        }
    }

    #[test]
    fn builder_fix_and_call() {
        let mut store = GoalStore::new();
        let mut builder = GoalBuilder::new(&mut store);

        let rel_id = builder.new_rel("test");
        let call = builder.call(rel_id);
        let body = builder.rule(0);
        let combined = builder.or(body, call);
        let fix = builder.fix(rel_id, combined);

        assert!(store.get(fix).is_some());
    }

    // ========== COMPLEX GOAL CONSTRUCTION ==========

    #[test]
    fn build_append_relation() {
        let mut store = GoalStore::new();

        // append([], Ys, Ys).
        // append([X|Xs], Ys, [X|Zs]) :- append(Xs, Ys, Zs).

        let append_rel = store.new_rel("append");

        // Base case: rule 0
        let base_case = store.rule(0);

        // Recursive case: rule 1 ; call(append)
        let recursive_step = store.rule(1);
        let recursive_call = store.call(append_rel);
        let recursive_case = store.seq(smallvec::smallvec![recursive_step, recursive_call]);

        // append = base | recursive
        let body = store.alt(smallvec::smallvec![base_case, recursive_case]);

        // Fix it
        let append_def = store.fix(append_rel, body);

        // Verify structure
        match store.get(append_def) {
            Some(Goal::Fix(rel_id, body_id)) => {
                assert_eq!(*rel_id, append_rel);
                match store.get(*body_id) {
                    Some(Goal::Alt(branches)) => {
                        assert_eq!(branches.len(), 2);
                    }
                    _ => panic!("Expected Alt body"),
                }
            }
            _ => panic!("Expected Fix"),
        }
    }

    #[test]
    fn build_nested_alternation() {
        let mut store = GoalStore::new();

        // (a | b) | (c | d)
        let a = store.rule(0);
        let b = store.rule(1);
        let c = store.rule(2);
        let d = store.rule(3);

        let ab = store.alt(smallvec::smallvec![a, b]);
        let cd = store.alt(smallvec::smallvec![c, d]);
        let all = store.alt(smallvec::smallvec![ab, cd]);

        match store.get(all) {
            Some(Goal::Alt(branches)) => {
                assert_eq!(branches.len(), 2);
                // Each branch is an Alt
                assert!(matches!(store.get(branches[0]), Some(Goal::Alt(_))));
                assert!(matches!(store.get(branches[1]), Some(Goal::Alt(_))));
            }
            _ => panic!("Expected Alt"),
        }
    }

    #[test]
    fn build_sequential_conjunction() {
        let mut store = GoalStore::new();

        // (a ; b) & (c ; d)
        let a = store.rule(0);
        let b = store.rule(1);
        let c = store.rule(2);
        let d = store.rule(3);

        let ab = store.seq(smallvec::smallvec![a, b]);
        let cd = store.seq(smallvec::smallvec![c, d]);
        let both = store.both(smallvec::smallvec![ab, cd]);

        match store.get(both) {
            Some(Goal::Both(goals)) => {
                assert_eq!(goals.len(), 2);
                assert!(matches!(store.get(goals[0]), Some(Goal::Seq(_))));
                assert!(matches!(store.get(goals[1]), Some(Goal::Seq(_))));
            }
            _ => panic!("Expected Both"),
        }
    }
}
