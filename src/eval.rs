use crate::goal::{Goal, GoalId, GoalStore, RelId, RuleId};
use crate::kernel::{compose_nf, meet_nf};
use crate::nf::NF;
use crate::task::{Kont, Task, TaskState};
use crate::term::TermStore;
#[cfg(feature = "tracing")]
use crate::trace::{debug, trace, debug_span};
use smallvec::SmallVec;

/// Storage for rules (RuleId -> NF).
#[derive(Debug, Default)]
pub struct RuleStore<C> {
    rules: Vec<NF<C>>,
}

impl<C: Clone> RuleStore<C> {
    /// Create a new empty rule store.
    pub fn new() -> Self {
        Self { rules: Vec::new() }
    }

    /// Add a rule and return its RuleId.
    pub fn add(&mut self, nf: NF<C>) -> RuleId {
        let id = self.rules.len() as RuleId;
        self.rules.push(nf);
        id
    }

    /// Get a rule by its ID.
    pub fn get(&self, id: RuleId) -> Option<&NF<C>> {
        self.rules.get(id as usize)
    }

    /// Number of rules.
    pub fn len(&self) -> usize {
        self.rules.len()
    }

    /// Check if empty.
    pub fn is_empty(&self) -> bool {
        self.rules.is_empty()
    }
}

/// Result of a single evaluation step.
#[derive(Debug, PartialEq, Eq)]
pub enum StepResult<C> {
    /// Task is still running.
    Continue,
    /// Task yielded an answer.
    Yielded(NF<C>),
    /// Task is blocked waiting on a relation.
    Blocked(RelId),
    /// Task is done (no more answers).
    Done,
}

/// Context for evaluation containing all stores.
pub struct EvalCtx<'a, C> {
    pub goals: &'a GoalStore,
    pub rules: &'a RuleStore<C>,
    pub terms: &'a mut TermStore,
}

/// Execute a single step of task evaluation.
///
/// Returns the result of the step indicating what happened.
pub fn step<C: Clone + Default + PartialEq>(
    task: &mut Task<C>,
    ctx: &mut EvalCtx<'_, C>,
) -> StepResult<C> {
    #[cfg(feature = "tracing")]
    let _span = debug_span!(
        "step",
        task_id = task.id,
        goal_id = task.goal,
        kont_depth = task.kont.len(),
    )
    .entered();

    // If task is not ready, return its current state
    if !task.is_ready() {
        #[cfg(feature = "tracing")]
        {
            let state_name = match &task.state {
                TaskState::Ready => "ready",
                TaskState::Yielded(_) => "yielded",
                TaskState::Blocked(_) => "blocked",
                TaskState::Done => "done",
            };
            trace!(state = state_name, "task_not_ready");
        }
        return match &task.state {
            TaskState::Yielded(nf) => StepResult::Yielded(nf.clone()),
            TaskState::Blocked(rel) => StepResult::Blocked(*rel),
            TaskState::Done => StepResult::Done,
            TaskState::Ready => unreachable!(),
        };
    }

    // Get the current goal (save goal_id for Fix)
    let goal_id = task.goal;
    let goal = match ctx.goals.get(goal_id) {
        Some(g) => g.clone(),
        None => {
            #[cfg(feature = "tracing")]
            debug!(goal_id, "goal_not_found");
            task.set_done();
            return StepResult::Done;
        }
    };

    #[cfg(feature = "tracing")]
    trace!(goal_type = ?std::mem::discriminant(&goal), "dispatch");

    match goal {
        Goal::Fail => handle_fail(task, ctx),

        Goal::Rule(rule_id) => handle_rule(task, rule_id, ctx),

        Goal::Alt(branches) => handle_alt(task, branches, ctx),

        Goal::Seq(steps) => handle_seq(task, steps, ctx),

        Goal::Both(goals) => handle_both(task, goals, ctx),

        Goal::Fix(rel_id, body) => handle_fix(task, rel_id, body, goal_id, ctx),

        Goal::Call(rel_id) => handle_call(task, rel_id, ctx),
    }
}

/// Handle the Fail goal - task produces no answers.
fn handle_fail<C: Clone + Default + PartialEq>(
    task: &mut Task<C>,
    ctx: &mut EvalCtx<'_, C>,
) -> StepResult<C> {
    // Fail produces no answers, so we need to backtrack
    backtrack(task, ctx)
}

/// Handle a Rule goal - apply the rule to produce an answer.
fn handle_rule<C: Clone + Default + PartialEq>(
    task: &mut Task<C>,
    rule_id: RuleId,
    ctx: &mut EvalCtx<'_, C>,
) -> StepResult<C> {
    #[cfg(feature = "tracing")]
    trace!(rule_id, "handle_rule");

    let rule = match ctx.rules.get(rule_id) {
        Some(r) => r.clone(),
        None => {
            #[cfg(feature = "tracing")]
            debug!(rule_id, "rule_not_found");
            task.set_done();
            return StepResult::Done;
        }
    };

    // Compose the rule with the current input
    #[cfg(feature = "tracing")]
    trace!(
        input_match_arity = task.input.match_pats.len(),
        input_build_arity = task.input.build_pats.len(),
        rule_match_arity = rule.match_pats.len(),
        rule_build_arity = rule.build_pats.len(),
        "composing"
    );

    match compose_nf(&task.input, &rule, ctx.terms) {
        Some(result) => {
            #[cfg(feature = "tracing")]
            trace!(
                result_match_arity = result.match_pats.len(),
                result_build_arity = result.build_pats.len(),
                "composition_success"
            );
            // Yield the result
            task.set_yielded(result.clone());
            StepResult::Yielded(result)
        }
        None => {
            #[cfg(feature = "tracing")]
            trace!("composition_failed");
            // Composition failed - backtrack
            backtrack(task, ctx)
        }
    }
}

/// Handle Alt (disjunction) - try first branch, queue others.
fn handle_alt<C: Clone + Default + PartialEq>(
    task: &mut Task<C>,
    branches: SmallVec<[GoalId; 2]>,
    ctx: &mut EvalCtx<'_, C>,
) -> StepResult<C> {
    #[cfg(feature = "tracing")]
    trace!(branch_count = branches.len(), "handle_alt");

    if branches.is_empty() {
        return backtrack(task, ctx);
    }

    // Try the first branch
    let first = branches[0];
    let remaining: SmallVec<[GoalId; 4]> = branches.iter().skip(1).copied().collect();

    #[cfg(feature = "tracing")]
    trace!(first_goal = first, remaining = remaining.len(), "alt_try_first");

    if !remaining.is_empty() {
        // Push continuation for remaining branches
        task.push_kont(Kont::AltNext { remaining });
    }

    // Continue with first branch
    task.set_goal(first);
    StepResult::Continue
}

/// Handle Seq (sequential composition) - evaluate first, compose with rest.
fn handle_seq<C: Clone + Default + PartialEq>(
    task: &mut Task<C>,
    steps: SmallVec<[GoalId; 4]>,
    ctx: &mut EvalCtx<'_, C>,
) -> StepResult<C> {
    #[cfg(feature = "tracing")]
    trace!(step_count = steps.len(), "handle_seq");

    if steps.is_empty() {
        return backtrack(task, ctx);
    }

    // Evaluate the first step
    let first = steps[0];
    let remaining: SmallVec<[GoalId; 4]> = steps.iter().skip(1).copied().collect();

    #[cfg(feature = "tracing")]
    trace!(first_goal = first, remaining = remaining.len(), "seq_start");

    if !remaining.is_empty() {
        // Push continuation for remaining steps
        task.push_kont(Kont::SeqNext {
            left_answers: Vec::new(),
            remaining,
        });
    }

    // Continue with first step
    task.set_goal(first);
    StepResult::Continue
}

/// Handle Both (conjunction) - evaluate first, meet with rest.
fn handle_both<C: Clone + Default + PartialEq>(
    task: &mut Task<C>,
    goals: SmallVec<[GoalId; 4]>,
    ctx: &mut EvalCtx<'_, C>,
) -> StepResult<C> {
    #[cfg(feature = "tracing")]
    trace!(goal_count = goals.len(), "handle_both");

    if goals.is_empty() {
        return backtrack(task, ctx);
    }

    // Evaluate the first goal
    let first = goals[0];
    let remaining: SmallVec<[GoalId; 4]> = goals.iter().skip(1).copied().collect();

    #[cfg(feature = "tracing")]
    trace!(first_goal = first, remaining = remaining.len(), "both_start");

    if !remaining.is_empty() {
        // Push continuation for remaining goals
        task.push_kont(Kont::BothNext {
            left_answers: Vec::new(),
            remaining,
        });
    }

    // Continue with first goal
    task.set_goal(first);
    StepResult::Continue
}

/// Handle Fix (recursive definition) - set up recursion.
fn handle_fix<C: Clone + Default + PartialEq>(
    task: &mut Task<C>,
    rel_id: RelId,
    body: GoalId,
    fix_goal: GoalId,
    _ctx: &mut EvalCtx<'_, C>,
) -> StepResult<C> {
    #[cfg(feature = "tracing")]
    trace!(rel_id, body_goal = body, fix_goal, "handle_fix");

    // Push a frame to track this recursive definition
    // Store fix_goal so recursive calls can re-enter the Fix
    task.push_kont(Kont::FixFrame {
        rel_id,
        body,
        fix_goal,
    });

    // Continue with the body
    task.set_goal(body);
    StepResult::Continue
}

/// Handle Call (recursive call) - block waiting for relation answers.
fn handle_call<C: Clone + Default + PartialEq>(
    task: &mut Task<C>,
    rel_id: RelId,
    _ctx: &mut EvalCtx<'_, C>,
) -> StepResult<C> {
    #[cfg(feature = "tracing")]
    debug!(rel_id, task_id = task.id, "handle_call_blocked");

    // Block on the relation
    task.set_blocked(rel_id);
    StepResult::Blocked(rel_id)
}

/// Backtrack to the next alternative.
///
/// Pops continuations and handles them appropriately until we find
/// something to do or determine we're done.
pub fn backtrack<C: Clone + Default + PartialEq>(
    task: &mut Task<C>,
    _ctx: &mut EvalCtx<'_, C>,
) -> StepResult<C> {
    #[cfg(feature = "tracing")]
    let _span = debug_span!(
        "backtrack",
        task_id = task.id,
        initial_depth = task.kont.len()
    )
    .entered();

    while let Some(kont) = task.pop_kont() {
        #[cfg(feature = "tracing")]
        trace!(kont_type = ?std::mem::discriminant(&kont), "pop_kont");

        match kont {
            Kont::AltNext { mut remaining } => {
                // Try the next alternative
                if !remaining.is_empty() {
                    let next = remaining.remove(0);
                    #[cfg(feature = "tracing")]
                    trace!(next_goal = next, remaining = remaining.len(), "alt_continue");
                    if !remaining.is_empty() {
                        task.push_kont(Kont::AltNext { remaining });
                    }
                    task.set_goal(next);
                    return StepResult::Continue;
                }
            }
            Kont::SeqNext { .. } => {
                // Sequence failed - continue backtracking
                #[cfg(feature = "tracing")]
                trace!("seq_failed");
            }
            Kont::BothNext { .. } => {
                // Conjunction failed - continue backtracking
                #[cfg(feature = "tracing")]
                trace!("both_failed");
            }
            Kont::FixFrame { .. } => {
                // Recursion failed - continue backtracking
                #[cfg(feature = "tracing")]
                trace!("fix_failed");
            }
        }
    }

    // No more continuations - we're done
    #[cfg(feature = "tracing")]
    debug!(task_id = task.id, "backtrack_exhausted");
    task.set_done();
    StepResult::Done
}

/// Resume a task after it has yielded an answer.
///
/// This processes the answer through the continuation stack.
pub fn resume_after_yield<C: Clone + Default + PartialEq>(
    task: &mut Task<C>,
    answer: NF<C>,
    ctx: &mut EvalCtx<'_, C>,
) -> StepResult<C> {
    #[cfg(feature = "tracing")]
    let _span = debug_span!(
        "resume_after_yield",
        task_id = task.id,
        kont_depth = task.kont.len()
    )
    .entered();

    // Pop the continuation and process the answer
    if let Some(kont) = task.pop_kont() {
        #[cfg(feature = "tracing")]
        trace!(kont_type = ?std::mem::discriminant(&kont), "processing_kont");

        match kont {
            Kont::AltNext { remaining } => {
                #[cfg(feature = "tracing")]
                trace!(remaining = remaining.len(), "alt_yield");

                // If there are konts below (e.g., SeqNext), the yield must flow
                // through them first. Don't push AltNext back until after.
                if !task.kont_is_empty() {
                    // Process through remaining konts (e.g., SeqNext)
                    let result = resume_after_yield(task, answer, ctx);

                    // Now push AltNext back for backtracking
                    if !remaining.is_empty() {
                        task.push_kont(Kont::AltNext { remaining });
                    }

                    return result;
                }

                // No konts below - push AltNext back and yield as final
                if !remaining.is_empty() {
                    task.push_kont(Kont::AltNext { remaining });
                }
                task.set_yielded(answer.clone());
                StepResult::Yielded(answer)
            }

            Kont::SeqNext {
                mut left_answers,
                remaining,
            } => {
                if remaining.is_empty() {
                    // All steps done - yield the answer
                    #[cfg(feature = "tracing")]
                    trace!("seq_complete");
                    task.set_yielded(answer.clone());
                    return StepResult::Yielded(answer);
                }

                // Accumulate this answer and continue with next step
                #[cfg(feature = "tracing")]
                trace!(
                    accumulated = left_answers.len() + 1,
                    remaining = remaining.len(),
                    "seq_continue"
                );
                left_answers.push(answer.clone());

                // Continue with next step, composing with the answer
                let next = remaining[0];
                let rest: SmallVec<[GoalId; 4]> = remaining.iter().skip(1).copied().collect();

                // Push updated continuation
                task.push_kont(Kont::SeqNext {
                    left_answers,
                    remaining: rest,
                });

                // Update input for next step
                task.set_input(answer);
                task.set_goal(next);
                task.set_ready();
                StepResult::Continue
            }

            Kont::BothNext {
                mut left_answers,
                remaining,
            } => {
                // Accumulate this answer
                left_answers.push(answer.clone());

                if remaining.is_empty() {
                    // All parts done - compute the meet of all answers
                    let mut result = left_answers[0].clone();
                    for ans in left_answers.iter().skip(1) {
                        match meet_nf(&result, ans, ctx.terms) {
                            Some(met) => result = met,
                            None => return backtrack(task, ctx),
                        }
                    }
                    task.set_yielded(result.clone());
                    return StepResult::Yielded(result);
                }

                // Continue with next part
                let next = remaining[0];
                let rest: SmallVec<[GoalId; 4]> = remaining.iter().skip(1).copied().collect();

                // Push updated continuation
                task.push_kont(Kont::BothNext {
                    left_answers,
                    remaining: rest,
                });

                task.set_goal(next);
                task.set_ready();
                StepResult::Continue
            }

            Kont::FixFrame { .. } => {
                // Recursive definition yielded - propagate the answer
                task.set_yielded(answer.clone());
                StepResult::Yielded(answer)
            }
        }
    } else {
        // No continuation - just yield the answer
        task.set_yielded(answer.clone());
        StepResult::Yielded(answer)
    }
}

/// Resume a task after a Call was satisfied with answers.
///
/// This is called when answers become available for a blocked relation.
/// The answer from the recursive call IS the output of the Call step,
/// so we process it through the continuation stack just like a Yielded answer.
pub fn resume_after_call<C: Clone + Default + PartialEq>(
    task: &mut Task<C>,
    answers: Vec<NF<C>>,
    ctx: &mut EvalCtx<'_, C>,
) -> StepResult<C> {
    if answers.is_empty() {
        // No answers from the call - backtrack
        return backtrack(task, ctx);
    }

    // Treat the first answer as if the Call yielded it
    // (proper implementation would fork tasks for multiple answers)
    let first_answer = answers[0].clone();
    task.set_ready();
    // Process the answer through the continuation stack
    resume_after_yield(task, first_answer, ctx)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::symbol::SymbolStore;
    use crate::term::TermStore;
    use crate::wire::Wire;

    // ========== HELPER FUNCTIONS ==========

    fn make_identity_nf() -> NF<()> {
        NF::new(
            smallvec::smallvec![],
            Wire::identity(0),
            smallvec::smallvec![],
        )
    }

    fn make_simple_nf(in_arity: u32, out_arity: u32) -> NF<()> {
        NF::new(
            smallvec::smallvec![],
            Wire::identity(in_arity.min(out_arity)),
            smallvec::smallvec![],
        )
    }

    fn setup_stores() -> (GoalStore, RuleStore<()>, TermStore, SymbolStore) {
        let goals = GoalStore::new();
        let rules = RuleStore::new();
        let terms = TermStore::new();
        let symbols = SymbolStore::new();
        (goals, rules, terms, symbols)
    }

    fn make_task(goal: GoalId) -> Task<()> {
        Task::new(0, goal, make_identity_nf())
    }

    // ========== RULE STORE TESTS ==========

    #[test]
    fn rule_store_new_is_empty() {
        let store: RuleStore<()> = RuleStore::new();
        assert!(store.is_empty());
        assert_eq!(store.len(), 0);
    }

    #[test]
    fn rule_store_add_and_get() {
        let mut store: RuleStore<()> = RuleStore::new();
        let nf = make_identity_nf();
        let id = store.add(nf.clone());

        assert_eq!(id, 0);
        assert_eq!(store.get(id), Some(&nf));
        assert_eq!(store.len(), 1);
    }

    #[test]
    fn rule_store_multiple_rules() {
        let mut store: RuleStore<()> = RuleStore::new();
        let id0 = store.add(make_identity_nf());
        let id1 = store.add(make_simple_nf(1, 1));
        let id2 = store.add(make_simple_nf(2, 2));

        assert_eq!(id0, 0);
        assert_eq!(id1, 1);
        assert_eq!(id2, 2);
        assert_eq!(store.len(), 3);
    }

    #[test]
    fn rule_store_invalid_id_returns_none() {
        let store: RuleStore<()> = RuleStore::new();
        assert!(store.get(0).is_none());
        assert!(store.get(100).is_none());
    }

    // ========== STEP RESULT TESTS ==========

    #[test]
    fn step_result_equality() {
        let r1: StepResult<()> = StepResult::Continue;
        let r2: StepResult<()> = StepResult::Continue;
        assert_eq!(r1, r2);

        let r3: StepResult<()> = StepResult::Done;
        let r4: StepResult<()> = StepResult::Done;
        assert_eq!(r3, r4);

        assert_ne!(r1, r3);
    }

    #[test]
    fn step_result_blocked() {
        let r1: StepResult<()> = StepResult::Blocked(5);
        let r2: StepResult<()> = StepResult::Blocked(5);
        assert_eq!(r1, r2);

        let r3: StepResult<()> = StepResult::Blocked(6);
        assert_ne!(r1, r3);
    }

    // ========== EVAL FAIL TESTS ==========

    #[test]
    fn step_fail_goal_produces_done() {
        let (mut goals, rules, mut terms, _symbols) = setup_stores();
        let fail_id = goals.fail();
        let mut task = make_task(fail_id);

        let mut ctx = EvalCtx {
            goals: &goals,
            rules: &rules,
            terms: &mut terms,
        };

        let result = step(&mut task, &mut ctx);
        assert_eq!(result, StepResult::Done);
        assert!(task.is_done());
    }

    #[test]
    fn fail_with_alt_continuation_tries_next() {
        let (mut goals, rules, mut terms, _symbols) = setup_stores();

        // Create: Alt(Fail, Rule(0))
        let fail_id = goals.fail();

        let mut task = make_task(fail_id);
        // Manually add AltNext continuation (simulating being inside an Alt)
        task.push_kont(Kont::AltNext {
            remaining: smallvec::smallvec![fail_id + 1], // Next branch
        });

        let mut ctx = EvalCtx {
            goals: &goals,
            rules: &rules,
            terms: &mut terms,
        };

        let result = step(&mut task, &mut ctx);
        // Should try the next alternative
        assert_eq!(result, StepResult::Continue);
        assert_eq!(task.goal, fail_id + 1);
    }

    // ========== EVAL RULE TESTS ==========

    #[test]
    fn step_rule_goal_yields_answer() {
        let (mut goals, mut rules, mut terms, _symbols) = setup_stores();

        let nf = make_identity_nf();
        let rule_id = rules.add(nf.clone());
        let goal_id = goals.rule(rule_id);
        let mut task = make_task(goal_id);

        let mut ctx = EvalCtx {
            goals: &goals,
            rules: &rules,
            terms: &mut terms,
        };

        let result = step(&mut task, &mut ctx);
        assert!(matches!(result, StepResult::Yielded(_)));
        assert!(task.is_yielded());
    }

    #[test]
    fn step_rule_with_invalid_id_produces_done() {
        let (mut goals, rules, mut terms, _symbols) = setup_stores();

        let goal_id = goals.rule(999); // Invalid rule ID
        let mut task = make_task(goal_id);

        let mut ctx = EvalCtx {
            goals: &goals,
            rules: &rules,
            terms: &mut terms,
        };

        let result = step(&mut task, &mut ctx);
        assert_eq!(result, StepResult::Done);
    }

    #[test]
    fn step_rule_composes_with_input() {
        let (mut goals, mut rules, mut terms, _symbols) = setup_stores();

        // Create a rule NF
        let nf = make_identity_nf();
        let rule_id = rules.add(nf);
        let goal_id = goals.rule(rule_id);

        // Create task with a specific input
        let input = make_identity_nf();
        let mut task = Task::new(0, goal_id, input);

        let mut ctx = EvalCtx {
            goals: &goals,
            rules: &rules,
            terms: &mut terms,
        };

        let result = step(&mut task, &mut ctx);
        assert!(matches!(result, StepResult::Yielded(_)));
    }

    // ========== EVAL ALT TESTS ==========

    #[test]
    fn step_alt_single_branch_continues() {
        let (mut goals, rules, mut terms, _symbols) = setup_stores();

        let rule_id = 0;
        let r = goals.rule(rule_id);
        // Single-element alt is optimized to just return the element
        // So we need to create a 2-element alt and check behavior
        let alt_id = goals.alt(smallvec::smallvec![r, r]);
        let mut task = make_task(alt_id);

        let mut ctx = EvalCtx {
            goals: &goals,
            rules: &rules,
            terms: &mut terms,
        };

        let result = step(&mut task, &mut ctx);
        assert_eq!(result, StepResult::Continue);
        assert_eq!(task.goal, r); // Should be evaluating first branch
    }

    #[test]
    fn step_alt_pushes_continuation_for_remaining() {
        let (mut goals, rules, mut terms, _symbols) = setup_stores();

        let r1 = goals.rule(0);
        let r2 = goals.rule(1);
        let r3 = goals.rule(2);
        let alt_id = goals.alt(smallvec::smallvec![r1, r2, r3]);
        let mut task = make_task(alt_id);

        let mut ctx = EvalCtx {
            goals: &goals,
            rules: &rules,
            terms: &mut terms,
        };

        step(&mut task, &mut ctx);

        // Should have AltNext continuation with r2, r3
        assert!(!task.kont_is_empty());
        match task.kont.last() {
            Some(Kont::AltNext { remaining }) => {
                assert_eq!(remaining.len(), 2);
                assert_eq!(remaining[0], r2);
                assert_eq!(remaining[1], r3);
            }
            _ => panic!("Expected AltNext continuation"),
        }
    }

    #[test]
    fn step_empty_alt_produces_done() {
        let (mut goals, rules, mut terms, _symbols) = setup_stores();

        // Empty alt becomes Fail
        let alt_id = goals.alt(smallvec::smallvec![]);
        let mut task = make_task(alt_id);

        let mut ctx = EvalCtx {
            goals: &goals,
            rules: &rules,
            terms: &mut terms,
        };

        let result = step(&mut task, &mut ctx);
        assert_eq!(result, StepResult::Done);
    }

    // ========== EVAL SEQ TESTS ==========

    #[test]
    fn step_seq_continues_with_first() {
        let (mut goals, rules, mut terms, _symbols) = setup_stores();

        let r1 = goals.rule(0);
        let r2 = goals.rule(1);
        let seq_id = goals.seq(smallvec::smallvec![r1, r2]);
        let mut task = make_task(seq_id);

        let mut ctx = EvalCtx {
            goals: &goals,
            rules: &rules,
            terms: &mut terms,
        };

        let result = step(&mut task, &mut ctx);
        assert_eq!(result, StepResult::Continue);
        assert_eq!(task.goal, r1);
    }

    #[test]
    fn step_seq_pushes_continuation() {
        let (mut goals, rules, mut terms, _symbols) = setup_stores();

        let r1 = goals.rule(0);
        let r2 = goals.rule(1);
        let r3 = goals.rule(2);
        let seq_id = goals.seq(smallvec::smallvec![r1, r2, r3]);
        let mut task = make_task(seq_id);

        let mut ctx = EvalCtx {
            goals: &goals,
            rules: &rules,
            terms: &mut terms,
        };

        step(&mut task, &mut ctx);

        // Should have SeqNext continuation
        assert!(!task.kont_is_empty());
        match task.kont.last() {
            Some(Kont::SeqNext {
                left_answers,
                remaining,
            }) => {
                assert!(left_answers.is_empty());
                assert_eq!(remaining.len(), 2);
                assert_eq!(remaining[0], r2);
                assert_eq!(remaining[1], r3);
            }
            _ => panic!("Expected SeqNext continuation"),
        }
    }

    #[test]
    fn step_empty_seq_produces_done() {
        let (mut goals, rules, mut terms, _symbols) = setup_stores();

        // Empty seq becomes Fail
        let seq_id = goals.seq(smallvec::smallvec![]);
        let mut task = make_task(seq_id);

        let mut ctx = EvalCtx {
            goals: &goals,
            rules: &rules,
            terms: &mut terms,
        };

        let result = step(&mut task, &mut ctx);
        assert_eq!(result, StepResult::Done);
    }

    // ========== EVAL BOTH TESTS ==========

    #[test]
    fn step_both_continues_with_first() {
        let (mut goals, rules, mut terms, _symbols) = setup_stores();

        let r1 = goals.rule(0);
        let r2 = goals.rule(1);
        let both_id = goals.both(smallvec::smallvec![r1, r2]);
        let mut task = make_task(both_id);

        let mut ctx = EvalCtx {
            goals: &goals,
            rules: &rules,
            terms: &mut terms,
        };

        let result = step(&mut task, &mut ctx);
        assert_eq!(result, StepResult::Continue);
        assert_eq!(task.goal, r1);
    }

    #[test]
    fn step_both_pushes_continuation() {
        let (mut goals, rules, mut terms, _symbols) = setup_stores();

        let r1 = goals.rule(0);
        let r2 = goals.rule(1);
        let both_id = goals.both(smallvec::smallvec![r1, r2]);
        let mut task = make_task(both_id);

        let mut ctx = EvalCtx {
            goals: &goals,
            rules: &rules,
            terms: &mut terms,
        };

        step(&mut task, &mut ctx);

        // Should have BothNext continuation
        assert!(!task.kont_is_empty());
        match task.kont.last() {
            Some(Kont::BothNext {
                left_answers,
                remaining,
            }) => {
                assert!(left_answers.is_empty());
                assert_eq!(remaining.len(), 1);
                assert_eq!(remaining[0], r2);
            }
            _ => panic!("Expected BothNext continuation"),
        }
    }

    #[test]
    fn step_empty_both_produces_done() {
        let (mut goals, rules, mut terms, _symbols) = setup_stores();

        // Empty both becomes Fail
        let both_id = goals.both(smallvec::smallvec![]);
        let mut task = make_task(both_id);

        let mut ctx = EvalCtx {
            goals: &goals,
            rules: &rules,
            terms: &mut terms,
        };

        let result = step(&mut task, &mut ctx);
        assert_eq!(result, StepResult::Done);
    }

    // ========== EVAL FIX TESTS ==========

    #[test]
    fn step_fix_pushes_frame_and_continues() {
        let (mut goals, rules, mut terms, _symbols) = setup_stores();

        let rel_id = goals.new_rel("test");
        let body = goals.rule(0);
        let fix_id = goals.fix(rel_id, body);
        let mut task = make_task(fix_id);

        let mut ctx = EvalCtx {
            goals: &goals,
            rules: &rules,
            terms: &mut terms,
        };

        let result = step(&mut task, &mut ctx);
        assert_eq!(result, StepResult::Continue);
        assert_eq!(task.goal, body);

        // Should have FixFrame continuation
        match task.kont.last() {
            Some(Kont::FixFrame {
                rel_id: frame_rel_id,
                body: frame_body,
                fix_goal: frame_fix_goal,
            }) => {
                assert_eq!(*frame_rel_id, rel_id);
                assert_eq!(*frame_body, body);
                assert_eq!(*frame_fix_goal, fix_id);
            }
            _ => panic!("Expected FixFrame continuation"),
        }
    }

    // ========== EVAL CALL TESTS ==========

    #[test]
    fn step_call_blocks_on_relation() {
        let (mut goals, rules, mut terms, _symbols) = setup_stores();

        let rel_id = goals.new_rel("test");
        let call_id = goals.call(rel_id);
        let mut task = make_task(call_id);

        let mut ctx = EvalCtx {
            goals: &goals,
            rules: &rules,
            terms: &mut terms,
        };

        let result = step(&mut task, &mut ctx);
        assert_eq!(result, StepResult::Blocked(rel_id));
        assert!(task.is_blocked());
        assert_eq!(task.blocked_on(), Some(rel_id));
    }

    // ========== BACKTRACK TESTS ==========

    #[test]
    fn backtrack_with_alt_continuation_tries_next() {
        let (mut goals, rules, mut terms, _symbols) = setup_stores();

        let r1 = goals.rule(0);
        let r2 = goals.rule(1);
        let fail_id = goals.fail();
        let mut task = make_task(fail_id);

        // Add AltNext continuation
        task.push_kont(Kont::AltNext {
            remaining: smallvec::smallvec![r1, r2],
        });

        let mut ctx = EvalCtx {
            goals: &goals,
            rules: &rules,
            terms: &mut terms,
        };

        let result = step(&mut task, &mut ctx);
        assert_eq!(result, StepResult::Continue);
        assert_eq!(task.goal, r1);

        // Should still have AltNext for r2
        match task.kont.last() {
            Some(Kont::AltNext { remaining }) => {
                assert_eq!(remaining.len(), 1);
                assert_eq!(remaining[0], r2);
            }
            _ => panic!("Expected AltNext continuation"),
        }
    }

    #[test]
    fn backtrack_with_empty_stack_produces_done() {
        let (mut goals, rules, mut terms, _symbols) = setup_stores();

        let fail_id = goals.fail();
        let mut task = make_task(fail_id);
        // No continuations

        let mut ctx = EvalCtx {
            goals: &goals,
            rules: &rules,
            terms: &mut terms,
        };

        let result = step(&mut task, &mut ctx);
        assert_eq!(result, StepResult::Done);
        assert!(task.is_done());
    }

    #[test]
    fn backtrack_skips_seq_continuation() {
        let (mut goals, rules, mut terms, _symbols) = setup_stores();

        let fail_id = goals.fail();
        let r1 = goals.rule(0);
        let mut task = make_task(fail_id);

        // Add SeqNext (should be skipped during backtrack)
        task.push_kont(Kont::SeqNext {
            left_answers: vec![],
            remaining: smallvec::smallvec![99],
        });
        // Add AltNext (should be tried)
        task.push_kont(Kont::AltNext {
            remaining: smallvec::smallvec![r1],
        });

        let mut ctx = EvalCtx {
            goals: &goals,
            rules: &rules,
            terms: &mut terms,
        };

        // The fail will backtrack, skip SeqNext, and try AltNext
        // But since AltNext is pushed after SeqNext, it will be popped first
        let result = step(&mut task, &mut ctx);
        assert_eq!(result, StepResult::Continue);
        assert_eq!(task.goal, r1);
    }

    // ========== RESUME AFTER YIELD TESTS ==========

    #[test]
    fn resume_after_yield_with_alt_next() {
        let (goals, rules, mut terms, _symbols) = setup_stores();

        let mut task = make_task(0);
        task.push_kont(Kont::AltNext {
            remaining: smallvec::smallvec![1, 2],
        });

        let answer = make_identity_nf();
        let mut ctx = EvalCtx {
            goals: &goals,
            rules: &rules,
            terms: &mut terms,
        };

        let result = resume_after_yield(&mut task, answer.clone(), &mut ctx);
        assert!(matches!(result, StepResult::Yielded(_)));
        assert!(task.is_yielded());

        // Should still have AltNext continuation for remaining branches
        match task.kont.last() {
            Some(Kont::AltNext { remaining }) => {
                assert_eq!(remaining.len(), 2);
            }
            _ => panic!("Expected AltNext continuation"),
        }
    }

    /// Regression test: When AltNext yields but SeqNext is below it,
    /// the yield must flow through SeqNext (compose with remaining steps).
    ///
    /// Stack: [SeqNext{remaining=[c]}, AltNext{remaining=[b]}]
    /// After resume_after_yield with answer from 'a':
    /// - AltNext yields and pushes itself back
    /// - BUT: the answer must continue through SeqNext to compose with 'c'
    /// - Final result should be Continue (to evaluate 'c' with the composed input)
    #[test]
    fn resume_after_yield_alt_over_seq_must_continue_through_seq() {
        let (mut goals, rules, mut terms, _symbols) = setup_stores();

        let next_step = goals.rule(0); // 'c' - the step after Alt in the Seq

        let mut task = make_task(0);
        // Stack bottom: SeqNext waiting to compose with 'c'
        task.push_kont(Kont::SeqNext {
            left_answers: vec![],
            remaining: smallvec::smallvec![next_step],
        });
        // Stack top: AltNext with more branches to try
        task.push_kont(Kont::AltNext {
            remaining: smallvec::smallvec![1, 2], // branches b, c still to try
        });

        let answer = make_identity_nf();
        let mut ctx = EvalCtx {
            goals: &goals,
            rules: &rules,
            terms: &mut terms,
        };

        // When Alt yields, the answer should flow through SeqNext
        let result = resume_after_yield(&mut task, answer.clone(), &mut ctx);

        // BUG: Currently returns Yielded, treating Alt's yield as final
        // CORRECT: Should return Continue, setting goal to next_step
        assert_eq!(
            result,
            StepResult::Continue,
            "BUG: Alt yield with SeqNext below must Continue through Seq, not Yield as final"
        );
        assert_eq!(
            task.goal, next_step,
            "BUG: After Alt yields into Seq, goal should be next step in Seq"
        );
        // AltNext should still be on stack (pushed back for trying more branches)
        assert!(
            task.kont.iter().any(|k| matches!(k, Kont::AltNext { .. })),
            "AltNext should remain on stack to try remaining branches"
        );
    }

    #[test]
    fn resume_after_yield_with_seq_next_continues() {
        let (mut goals, rules, mut terms, _symbols) = setup_stores();

        let r1 = goals.rule(0);
        let r2 = goals.rule(1);

        let mut task = make_task(r1);
        task.push_kont(Kont::SeqNext {
            left_answers: vec![],
            remaining: smallvec::smallvec![r1, r2],
        });

        let answer = make_identity_nf();
        let mut ctx = EvalCtx {
            goals: &goals,
            rules: &rules,
            terms: &mut terms,
        };

        let result = resume_after_yield(&mut task, answer.clone(), &mut ctx);
        assert_eq!(result, StepResult::Continue);
        assert_eq!(task.goal, r1);
        assert!(task.is_ready());
    }

    #[test]
    fn resume_after_yield_seq_final_step_yields() {
        let (goals, rules, mut terms, _symbols) = setup_stores();

        let mut task = make_task(0);
        task.push_kont(Kont::SeqNext {
            left_answers: vec![make_identity_nf()],
            remaining: smallvec::smallvec![], // No more steps
        });

        let answer = make_identity_nf();
        let mut ctx = EvalCtx {
            goals: &goals,
            rules: &rules,
            terms: &mut terms,
        };

        let result = resume_after_yield(&mut task, answer, &mut ctx);
        assert!(matches!(result, StepResult::Yielded(_)));
    }

    #[test]
    fn resume_after_yield_with_both_next_continues() {
        let (mut goals, rules, mut terms, _symbols) = setup_stores();

        let r1 = goals.rule(0);

        let mut task = make_task(0);
        task.push_kont(Kont::BothNext {
            left_answers: vec![],
            remaining: smallvec::smallvec![r1],
        });

        let answer = make_identity_nf();
        let mut ctx = EvalCtx {
            goals: &goals,
            rules: &rules,
            terms: &mut terms,
        };

        let result = resume_after_yield(&mut task, answer, &mut ctx);
        assert_eq!(result, StepResult::Continue);
        assert_eq!(task.goal, r1);
        assert!(task.is_ready());
    }

    #[test]
    fn resume_after_yield_both_final_computes_meet() {
        let (goals, rules, mut terms, _symbols) = setup_stores();

        let mut task = make_task(0);
        task.push_kont(Kont::BothNext {
            left_answers: vec![make_identity_nf()],
            remaining: smallvec::smallvec![], // No more goals
        });

        let answer = make_identity_nf();
        let mut ctx = EvalCtx {
            goals: &goals,
            rules: &rules,
            terms: &mut terms,
        };

        let result = resume_after_yield(&mut task, answer, &mut ctx);
        assert!(matches!(result, StepResult::Yielded(_)));
    }

    #[test]
    fn resume_after_yield_with_fix_frame_yields() {
        let (goals, rules, mut terms, _symbols) = setup_stores();

        let mut task = make_task(0);
        task.push_kont(Kont::FixFrame {
            rel_id: 0,
            body: 0,
            fix_goal: 0,
        });

        let answer = make_identity_nf();
        let mut ctx = EvalCtx {
            goals: &goals,
            rules: &rules,
            terms: &mut terms,
        };

        let result = resume_after_yield(&mut task, answer.clone(), &mut ctx);
        assert!(matches!(result, StepResult::Yielded(_)));
        assert!(task.is_yielded());
    }

    #[test]
    fn resume_after_yield_no_continuation_yields() {
        let (goals, rules, mut terms, _symbols) = setup_stores();

        let mut task = make_task(0);
        // No continuations

        let answer = make_identity_nf();
        let mut ctx = EvalCtx {
            goals: &goals,
            rules: &rules,
            terms: &mut terms,
        };

        let result = resume_after_yield(&mut task, answer, &mut ctx);
        assert!(matches!(result, StepResult::Yielded(_)));
        assert!(task.is_yielded());
    }

    // ========== RESUME AFTER CALL TESTS ==========

    #[test]
    fn resume_after_call_with_no_answers_backtracks() {
        let (mut goals, rules, mut terms, _symbols) = setup_stores();

        let fail_id = goals.fail();
        let mut task = make_task(fail_id);
        task.set_blocked(0);

        let mut ctx = EvalCtx {
            goals: &goals,
            rules: &rules,
            terms: &mut terms,
        };

        let result = resume_after_call(&mut task, vec![], &mut ctx);
        assert_eq!(result, StepResult::Done);
    }

    #[test]
    fn resume_after_call_with_answers_yields_when_no_continuation() {
        // resume_after_call now delegates to resume_after_yield
        // With no continuation, the answer is yielded as final
        let (mut goals, rules, mut terms, _symbols) = setup_stores();

        let r1 = goals.rule(0);
        let mut task = make_task(r1);
        task.set_blocked(0);

        let answers = vec![make_identity_nf()];
        let mut ctx = EvalCtx {
            goals: &goals,
            rules: &rules,
            terms: &mut terms,
        };

        let result = resume_after_call(&mut task, answers, &mut ctx);
        // With no continuation, the answer is yielded
        assert!(matches!(result, StepResult::Yielded(_)));
        assert!(task.is_yielded());
    }

    // ========== COMPLEX SCENARIO TESTS ==========

    #[test]
    fn evaluate_simple_rule() {
        let (mut goals, mut rules, mut terms, _symbols) = setup_stores();

        let nf = make_identity_nf();
        let rule_id = rules.add(nf);
        let goal_id = goals.rule(rule_id);
        let mut task = make_task(goal_id);

        let mut ctx = EvalCtx {
            goals: &goals,
            rules: &rules,
            terms: &mut terms,
        };

        // Step the task
        let result = step(&mut task, &mut ctx);

        // Should yield an answer
        assert!(matches!(result, StepResult::Yielded(_)));
        assert!(task.is_yielded());
        assert!(task.get_answer().is_some());
    }

    #[test]
    fn evaluate_alt_two_branches() {
        let (mut goals, mut rules, mut terms, _symbols) = setup_stores();

        let nf1 = make_identity_nf();
        let nf2 = make_identity_nf();
        let r1 = rules.add(nf1);
        let r2 = rules.add(nf2);

        let g1 = goals.rule(r1);
        let g2 = goals.rule(r2);
        let alt_id = goals.alt(smallvec::smallvec![g1, g2]);

        let mut task = make_task(alt_id);

        let mut ctx = EvalCtx {
            goals: &goals,
            rules: &rules,
            terms: &mut terms,
        };

        // Step 1: should continue to first branch
        let result1 = step(&mut task, &mut ctx);
        assert_eq!(result1, StepResult::Continue);
        assert_eq!(task.goal, g1);

        // Step 2: should yield from first branch
        let result2 = step(&mut task, &mut ctx);
        assert!(matches!(result2, StepResult::Yielded(_)));
    }

    #[test]
    fn evaluate_seq_two_steps() {
        let (mut goals, mut rules, mut terms, _symbols) = setup_stores();

        let nf1 = make_identity_nf();
        let nf2 = make_identity_nf();
        let r1 = rules.add(nf1);
        let r2 = rules.add(nf2);

        let g1 = goals.rule(r1);
        let g2 = goals.rule(r2);
        let seq_id = goals.seq(smallvec::smallvec![g1, g2]);

        let mut task = make_task(seq_id);

        let mut ctx = EvalCtx {
            goals: &goals,
            rules: &rules,
            terms: &mut terms,
        };

        // Step 1: should continue to first step
        let result1 = step(&mut task, &mut ctx);
        assert_eq!(result1, StepResult::Continue);
        assert_eq!(task.goal, g1);

        // Step 2: first step yields
        let result2 = step(&mut task, &mut ctx);
        assert!(matches!(result2, StepResult::Yielded(_)));
    }

    #[test]
    fn evaluate_fail_in_alt_tries_next() {
        let (mut goals, mut rules, mut terms, _symbols) = setup_stores();

        let nf = make_identity_nf();
        let rule_id = rules.add(nf);

        let fail_id = goals.fail();
        let rule_goal = goals.rule(rule_id);
        let alt_id = goals.alt(smallvec::smallvec![fail_id, rule_goal]);

        let mut task = make_task(alt_id);

        let mut ctx = EvalCtx {
            goals: &goals,
            rules: &rules,
            terms: &mut terms,
        };

        // Step 1: enter alt, continue to fail
        let result1 = step(&mut task, &mut ctx);
        assert_eq!(result1, StepResult::Continue);
        assert_eq!(task.goal, fail_id);

        // Step 2: fail backtracks to try next branch
        let result2 = step(&mut task, &mut ctx);
        assert_eq!(result2, StepResult::Continue);
        assert_eq!(task.goal, rule_goal);

        // Step 3: rule yields
        let result3 = step(&mut task, &mut ctx);
        assert!(matches!(result3, StepResult::Yielded(_)));
    }

    #[test]
    fn evaluate_nested_alt_seq() {
        let (mut goals, mut rules, mut terms, _symbols) = setup_stores();

        let nf = make_identity_nf();
        let r1 = rules.add(nf.clone());
        let r2 = rules.add(nf);

        // Build: Alt(Seq(r1, r2), Fail)
        let g1 = goals.rule(r1);
        let g2 = goals.rule(r2);
        let seq_id = goals.seq(smallvec::smallvec![g1, g2]);
        let fail_id = goals.fail();
        let alt_id = goals.alt(smallvec::smallvec![seq_id, fail_id]);

        let mut task = make_task(alt_id);

        let mut ctx = EvalCtx {
            goals: &goals,
            rules: &rules,
            terms: &mut terms,
        };

        // Should enter Alt, then Seq, then first rule
        let result1 = step(&mut task, &mut ctx);
        assert_eq!(result1, StepResult::Continue);

        // Continue stepping until we get a yield
        // This will go through: seq -> g1 -> yield
        let result2 = step(&mut task, &mut ctx);
        assert_eq!(result2, StepResult::Continue);

        let result3 = step(&mut task, &mut ctx);
        assert!(matches!(result3, StepResult::Yielded(_)));
    }

    #[test]
    fn task_not_ready_returns_current_state() {
        let (goals, rules, mut terms, _symbols) = setup_stores();

        let mut task = make_task(0);
        task.set_done();

        let mut ctx = EvalCtx {
            goals: &goals,
            rules: &rules,
            terms: &mut terms,
        };

        let result = step(&mut task, &mut ctx);
        assert_eq!(result, StepResult::Done);
    }

    #[test]
    fn invalid_goal_id_produces_done() {
        let (goals, rules, mut terms, _symbols) = setup_stores();

        let mut task = make_task(9999); // Invalid goal

        let mut ctx = EvalCtx {
            goals: &goals,
            rules: &rules,
            terms: &mut terms,
        };

        let result = step(&mut task, &mut ctx);
        assert_eq!(result, StepResult::Done);
    }

    // ========== BUG-SPECIFIC TESTS ==========
    // These tests isolate the specific bugs found in recursive Seq/Call handling

    /// Bug: When a Rule yields inside a Seq with remaining steps, the kont stack
    /// should still have SeqNext. The yield is intermediate, not final.
    #[test]
    fn seq_intermediate_yield_has_pending_continuation() {
        let (mut goals, mut rules, mut terms, _symbols) = setup_stores();

        let nf1 = make_identity_nf();
        let nf2 = make_identity_nf();
        let r1 = rules.add(nf1);
        let r2 = rules.add(nf2);

        // Seq(rule1, rule2) - when rule1 yields, SeqNext should still be on stack
        let g1 = goals.rule(r1);
        let g2 = goals.rule(r2);
        let seq_id = goals.seq(smallvec::smallvec![g1, g2]);

        let mut task = make_task(seq_id);

        let mut ctx = EvalCtx {
            goals: &goals,
            rules: &rules,
            terms: &mut terms,
        };

        // Step 1: enter Seq, pushes SeqNext, continues to g1
        let result1 = step(&mut task, &mut ctx);
        assert_eq!(result1, StepResult::Continue);
        assert_eq!(task.goal, g1);
        assert!(!task.kont_is_empty(), "SeqNext should be on stack");

        // Step 2: g1 (Rule) yields
        let result2 = step(&mut task, &mut ctx);
        assert!(matches!(result2, StepResult::Yielded(_)));

        // BUG CHECK: After first rule yields, kont stack should STILL have SeqNext
        // because there are remaining steps (g2) to execute
        assert!(
            !task.kont_is_empty(),
            "BUG: kont stack is empty after intermediate yield - SeqNext was lost"
        );

        // Verify it's actually a SeqNext with g2 remaining
        match task.kont.last() {
            Some(Kont::SeqNext { remaining, .. }) => {
                assert!(
                    remaining.contains(&g2),
                    "SeqNext should have g2 in remaining"
                );
            }
            other => panic!(
                "BUG: Expected SeqNext on kont stack, got {:?}",
                other
            ),
        }
    }

    /// Bug: resume_after_yield with SeqNext should set goal to next step and continue,
    /// not yield the intermediate result as final.
    #[test]
    fn resume_after_yield_seq_with_remaining_continues_to_next() {
        let (mut goals, rules, mut terms, _symbols) = setup_stores();

        let r1 = goals.rule(0);
        let r2 = goals.rule(1);

        let mut task = make_task(r1);
        // Simulate being inside Seq(r1, r2) after r1 started
        task.push_kont(Kont::SeqNext {
            left_answers: vec![],
            remaining: smallvec::smallvec![r2],
        });

        let answer = make_identity_nf();
        let mut ctx = EvalCtx {
            goals: &goals,
            rules: &rules,
            terms: &mut terms,
        };

        let result = resume_after_yield(&mut task, answer, &mut ctx);

        // Should continue to next step, NOT yield the intermediate result
        assert_eq!(
            result,
            StepResult::Continue,
            "BUG: resume_after_yield should Continue to next Seq step, not Yield intermediate"
        );
        assert_eq!(
            task.goal, r2,
            "BUG: goal should be set to next step (r2)"
        );
        assert!(task.is_ready(), "Task should be ready to continue");
    }

    /// Bug: After Call is satisfied, resume_after_call should feed answer through
    /// SeqNext continuation to continue with remaining steps.
    #[test]
    fn resume_after_call_feeds_into_seq_next() {
        let (mut goals, rules, mut terms, _symbols) = setup_stores();

        let wrap_goal = goals.rule(0); // This would be the wrap step $z -> (s $z)

        let mut task = make_task(0);
        // Simulate: Seq([peel, Call(add), wrap]) after Call blocked
        // kont stack has SeqNext waiting for Call result
        task.push_kont(Kont::SeqNext {
            left_answers: vec![],
            remaining: smallvec::smallvec![wrap_goal], // wrap is the remaining step
        });

        let call_answer = make_identity_nf(); // Represents result "z" from recursive add
        let mut ctx = EvalCtx {
            goals: &goals,
            rules: &rules,
            terms: &mut terms,
        };

        let result = resume_after_call(&mut task, vec![call_answer], &mut ctx);

        // Should continue to wrap step, not yield the Call's answer as final
        assert_eq!(
            result,
            StepResult::Continue,
            "BUG: resume_after_call should Continue to next Seq step (wrap)"
        );
        assert_eq!(
            task.goal, wrap_goal,
            "BUG: goal should be set to wrap step after Call satisfied"
        );
    }

    /// Verify: Seq(r1, r2) produces exactly one FINAL answer.
    /// Intermediate yields are allowed by the architecture and get composed via resume_after_yield.
    /// Only yields when kont_is_empty() are final answers that should be collected.
    #[test]
    fn seq_produces_one_final_answer() {
        let (mut goals, mut rules, mut terms, _symbols) = setup_stores();

        let nf = make_identity_nf();
        let r1 = rules.add(nf.clone());
        let r2 = rules.add(nf);

        let g1 = goals.rule(r1);
        let g2 = goals.rule(r2);
        let seq_id = goals.seq(smallvec::smallvec![g1, g2]);

        let mut task = make_task(seq_id);

        let mut ctx = EvalCtx {
            goals: &goals,
            rules: &rules,
            terms: &mut terms,
        };

        let mut final_answer_count = 0;
        let mut step_count = 0;
        let max_steps = 20;

        while step_count < max_steps && !task.is_done() {
            let result = step(&mut task, &mut ctx);
            step_count += 1;

            match result {
                StepResult::Yielded(ref _nf) => {
                    // Check if this is a final answer BEFORE processing continuations
                    if task.kont_is_empty() {
                        // Final answer - no more continuations to process
                        final_answer_count += 1;
                        backtrack(&mut task, &mut ctx);
                    } else {
                        // Intermediate yield - compose with next continuation
                        let answer = task.get_answer().unwrap().clone();
                        resume_after_yield(&mut task, answer, &mut ctx);
                    }
                }
                StepResult::Continue => continue,
                StepResult::Done => break,
                StepResult::Blocked(_) => break,
            }
        }

        // Seq(r1, r2) with identity rules should produce exactly 1 final answer
        assert_eq!(
            final_answer_count, 1,
            "Seq should produce exactly 1 final answer, got {}",
            final_answer_count
        );
    }

    // ========== BACKWARD QUERY SYMMETRY TESTS ==========
    // These tests verify that Seq properly composes when a variable
    // in the first step's output needs to unify with a ground term
    // in the second step's input.

    #[test]
    fn seq_backward_query_composes_var_with_ground() {
        // This tests the backward query scenario:
        // First rule: (cons z $0) -> $0 (add base case)
        // Second rule: z -> z (identity on ground term)
        // Expected composed result: (cons z z) -> z
        let (mut goals, mut rules, mut terms, symbols) = setup_stores();

        let cons_sym = symbols.intern("cons");
        let z_sym = symbols.intern("z");

        let z = terms.app0(z_sym);
        let v0 = terms.var(0);
        let cons_z_v0 = terms.app2(cons_sym, z, v0);

        // Rule 1: (cons z $0) -> $0
        let nf1 = NF::factor(cons_z_v0, v0, (), &mut terms);
        let r1 = rules.add(nf1);

        // Rule 2: z -> z (ground identity)
        let nf2 = NF::factor(z, z, (), &mut terms);
        let r2 = rules.add(nf2);

        let g1 = goals.rule(r1);
        let g2 = goals.rule(r2);
        let seq_id = goals.seq(smallvec::smallvec![g1, g2]);

        // Start with identity input $x -> $x
        let input_v0 = terms.var(0);
        let input_nf = NF::factor(input_v0, input_v0, (), &mut terms);
        let mut task = Task::new(0, seq_id, input_nf);

        let mut ctx = EvalCtx {
            goals: &goals,
            rules: &rules,
            terms: &mut terms,
        };

        let mut final_answers: Vec<NF<()>> = Vec::new();
        let mut step_count = 0;
        let max_steps = 50;

        while step_count < max_steps && !task.is_done() {
            let result = step(&mut task, &mut ctx);
            step_count += 1;

            match result {
                StepResult::Yielded(ref nf) => {
                    if task.kont_is_empty() {
                        final_answers.push(nf.clone());
                        backtrack(&mut task, &mut ctx);
                    } else {
                        let answer = task.get_answer().unwrap().clone();
                        resume_after_yield(&mut task, answer, &mut ctx);
                    }
                }
                StepResult::Continue => continue,
                StepResult::Done => break,
                StepResult::Blocked(_) => break,
            }
        }

        assert!(
            !final_answers.is_empty(),
            "Should produce at least one answer"
        );

        // The answer should be (cons z z) -> z
        let answer = &final_answers[0];

        // Check match pattern is (cons z z)
        let (match_f, match_c) = terms.is_app(answer.match_pats[0]).unwrap();
        assert_eq!(
            symbols.resolve(match_f),
            Some("cons"),
            "Match should be cons"
        );
        assert_eq!(match_c[0], z, "First arg of cons should be z");
        assert_eq!(
            match_c[1], z,
            "Second arg of cons should be z (variable bound), got {:?}",
            terms.is_var(match_c[1])
        );

        // Check build pattern is z
        assert_eq!(answer.build_pats[0], z, "Build should be z");
    }

    #[test]
    fn seq_backward_query_with_s_z() {
        // Tests: (cons z $0) -> $0 composed with (s z) -> (s z)
        // Expected: (cons z (s z)) -> (s z)
        let (mut goals, mut rules, mut terms, symbols) = setup_stores();

        let cons_sym = symbols.intern("cons");
        let z_sym = symbols.intern("z");
        let s_sym = symbols.intern("s");

        let z = terms.app0(z_sym);
        let s_z = terms.app1(s_sym, z);
        let v0 = terms.var(0);
        let cons_z_v0 = terms.app2(cons_sym, z, v0);

        // Rule 1: (cons z $0) -> $0
        let nf1 = NF::factor(cons_z_v0, v0, (), &mut terms);
        let r1 = rules.add(nf1);

        // Rule 2: (s z) -> (s z) (ground identity on (s z))
        let nf2 = NF::factor(s_z, s_z, (), &mut terms);
        let r2 = rules.add(nf2);

        let g1 = goals.rule(r1);
        let g2 = goals.rule(r2);
        let seq_id = goals.seq(smallvec::smallvec![g1, g2]);

        // Start with identity input
        let input_v0 = terms.var(0);
        let input_nf = NF::factor(input_v0, input_v0, (), &mut terms);
        let mut task = Task::new(0, seq_id, input_nf);

        let mut ctx = EvalCtx {
            goals: &goals,
            rules: &rules,
            terms: &mut terms,
        };

        let mut final_answers: Vec<NF<()>> = Vec::new();
        let mut step_count = 0;
        let max_steps = 50;

        while step_count < max_steps && !task.is_done() {
            let result = step(&mut task, &mut ctx);
            step_count += 1;

            match result {
                StepResult::Yielded(ref nf) => {
                    if task.kont_is_empty() {
                        final_answers.push(nf.clone());
                        backtrack(&mut task, &mut ctx);
                    } else {
                        let answer = task.get_answer().unwrap().clone();
                        resume_after_yield(&mut task, answer, &mut ctx);
                    }
                }
                StepResult::Continue => continue,
                StepResult::Done => break,
                StepResult::Blocked(_) => break,
            }
        }

        assert!(
            !final_answers.is_empty(),
            "Should produce at least one answer"
        );

        // The answer should be (cons z (s z)) -> (s z)
        let answer = &final_answers[0];

        // Check match pattern is (cons z (s z))
        let (match_f, match_c) = terms.is_app(answer.match_pats[0]).unwrap();
        assert_eq!(symbols.resolve(match_f), Some("cons"));
        assert_eq!(match_c[0], z, "First arg should be z");
        // Second arg should be (s z)
        let (s_f, s_c) = terms.is_app(match_c[1]).unwrap();
        assert_eq!(symbols.resolve(s_f), Some("s"));
        assert_eq!(s_c[0], z, "Arg of s should be z");

        // Check build pattern is (s z)
        assert_eq!(answer.build_pats[0], s_z, "Build should be (s z)");
    }

    /// Test that mimics REPL structure: Seq([Alt([rule1, rule2]), identity])
    /// This is what `add ; z` compiles to.
    #[test]
    fn seq_alt_with_identity_backward_query() {
        // This tests the exact structure the REPL creates:
        // add is an Alt of two rules:
        //   rule1: (cons z $0) -> $0
        //   rule2: (cons (s $0) $1) -> (s $2) where $2 = recursive result
        // For simplicity, we'll just use rule1 in the Alt
        // Query: add ; z  where z -> z is identity
        // Expected: (cons z z) -> z
        let (mut goals, mut rules, mut terms, symbols) = setup_stores();

        let cons_sym = symbols.intern("cons");
        let z_sym = symbols.intern("z");

        let z = terms.app0(z_sym);
        let v0 = terms.var(0);
        let cons_z_v0 = terms.app2(cons_sym, z, v0);

        // Rule 1: (cons z $0) -> $0 (add base case)
        let nf1 = NF::factor(cons_z_v0, v0, (), &mut terms);
        let r1 = rules.add(nf1);

        // Create Alt with just one rule (to isolate the issue)
        let g1 = goals.rule(r1);
        let add_alt = goals.alt(smallvec::smallvec![g1]);

        // Identity on z: z -> z
        let nf_z = NF::factor(z, z, (), &mut terms);
        let r_z = rules.add(nf_z);
        let z_identity = goals.rule(r_z);

        // Seq([add_alt, z_identity]) - this is what `add ; z` becomes
        let seq_id = goals.seq(smallvec::smallvec![add_alt, z_identity]);

        // Start with identity input $x -> $x
        let input_v0 = terms.var(0);
        let input_nf = NF::factor(input_v0, input_v0, (), &mut terms);
        let mut task = Task::new(0, seq_id, input_nf);

        let mut ctx = EvalCtx {
            goals: &goals,
            rules: &rules,
            terms: &mut terms,
        };

        let mut final_answers: Vec<NF<()>> = Vec::new();
        let mut step_count = 0;
        let max_steps = 100;

        eprintln!("=== Starting Seq([Alt([add_base]), z_identity]) test ===");
        while step_count < max_steps && !task.is_done() {
            let result = step(&mut task, &mut ctx);
            step_count += 1;

            match result {
                StepResult::Yielded(ref nf) => {
                    eprintln!("Step {}: Yielded - kont_empty={}", step_count, task.kont_is_empty());
                    eprintln!("  match_pats: {:?}", nf.match_pats);
                    eprintln!("  build_pats: {:?}", nf.build_pats);
                    if task.kont_is_empty() {
                        final_answers.push(nf.clone());
                        backtrack(&mut task, &mut ctx);
                    } else {
                        let answer = task.get_answer().unwrap().clone();
                        eprintln!("  Resuming with answer");
                        resume_after_yield(&mut task, answer, &mut ctx);
                    }
                }
                StepResult::Continue => continue,
                StepResult::Done => {
                    eprintln!("Step {}: Done", step_count);
                    break;
                }
                StepResult::Blocked(_) => {
                    eprintln!("Step {}: Blocked", step_count);
                    break;
                }
            }
        }

        eprintln!("Final answers: {}", final_answers.len());
        for (i, ans) in final_answers.iter().enumerate() {
            eprintln!("  Answer {}: match={:?}, build={:?}", i, ans.match_pats, ans.build_pats);
        }

        assert!(
            !final_answers.is_empty(),
            "Should produce at least one answer"
        );

        // The answer should be (cons z z) -> z
        let answer = &final_answers[0];

        // Check match pattern is (cons z z)
        let (match_f, match_c) = ctx.terms.is_app(answer.match_pats[0]).unwrap();
        assert_eq!(
            symbols.resolve(match_f),
            Some("cons"),
            "Match should be cons"
        );
        assert_eq!(match_c[0], z, "First arg of cons should be z");
        assert_eq!(
            match_c[1], z,
            "Second arg of cons should be z (variable bound to z)"
        );

        // Check build pattern is z
        assert_eq!(answer.build_pats[0], z, "Build should be z");
    }
}
