//! Evaluation benchmarks using Criterion.
//!
//! Run with: `cargo bench`
//!
//! These benchmarks measure the core evaluation loop performance including:
//! - Step dispatch for different goal types
//! - Composition operations
//! - Backtracking with varying depths

use criterion::{black_box, criterion_group, criterion_main, BenchmarkId, Criterion};
use rwlog::{
    eval::{backtrack, step, EvalCtx, StepResult},
    goal::GoalStore,
    nf::NF,
    symbol::SymbolStore,
    table::RuleStore,
    task::Task,
    term::TermStore,
};
use smallvec::smallvec;

/// Create the standard test stores for benchmarks.
fn setup_stores() -> (GoalStore, RuleStore<()>, TermStore, SymbolStore) {
    let symbols = SymbolStore::new();
    let terms = TermStore::new();
    let goals = GoalStore::new();
    let rules = RuleStore::new();
    (goals, rules, terms, symbols)
}

/// Build a Peano numeral with n successors: S(S(...S(Z)...))
fn build_peano(n: u32, z: lasso::Spur, s: lasso::Spur, terms: &TermStore) -> rwlog::term::TermId {
    let mut result = terms.app0(z);
    for _ in 0..n {
        result = terms.app1(s, result);
    }
    result
}

/// Benchmark the step function with a simple Rule goal.
fn bench_step_rule(c: &mut Criterion) {
    let (mut goals, mut rules, terms, symbols) = setup_stores();

    // Create a simple identity rule: $0 -> $0
    let v0 = terms.var(0);
    let nf = NF::factor(v0, v0, (), &terms);
    let rule_id = rules.add(nf.clone());
    let goal_id = goals.rule(rule_id);

    // Input: identity NF
    let input = NF::factor(v0, v0, (), &terms);

    c.bench_function("step_rule", |b| {
        b.iter(|| {
            let mut task = Task::new(0, goal_id, input.clone());
            let mut ctx = EvalCtx {
                goals: &goals,
                rules: &rules,
                terms: &terms,
            };
            step(black_box(&mut task), black_box(&mut ctx))
        });
    });
}

/// Benchmark the step function with Alt goals of varying branch counts.
fn bench_step_alt(c: &mut Criterion) {
    let mut group = c.benchmark_group("step_alt");

    for branches in [2, 4, 8] {
        group.bench_with_input(
            BenchmarkId::new("branches", branches),
            &branches,
            |b, &branches| {
                let (mut goals, mut rules, terms, _symbols) = setup_stores();

                // Create multiple identity rules
                let v0 = terms.var(0);
                let nf = NF::factor(v0, v0, (), &terms);

                let rule_goals: smallvec::SmallVec<[u32; 8]> = (0..branches)
                    .map(|_| {
                        let rule_id = rules.add(nf.clone());
                        goals.rule(rule_id)
                    })
                    .collect();

                let alt_goal = goals.alt(rule_goals);
                let input = NF::factor(v0, v0, (), &terms);

                b.iter(|| {
                    let mut task = Task::new(0, alt_goal, input.clone());
                    let mut ctx = EvalCtx {
                        goals: &goals,
                        rules: &rules,
                        terms: &terms,
                    };
                    step(black_box(&mut task), black_box(&mut ctx))
                });
            },
        );
    }

    group.finish();
}

/// Benchmark backtracking with varying continuation stack depths.
fn bench_backtrack(c: &mut Criterion) {
    use rwlog::task::Kont;

    let mut group = c.benchmark_group("backtrack");

    for depth in [2, 5, 10] {
        group.bench_with_input(BenchmarkId::new("depth", depth), &depth, |b, &depth| {
            let (mut goals, mut rules, terms, _symbols) = setup_stores();

            // Create a simple goal
            let v0 = terms.var(0);
            let nf = NF::factor(v0, v0, (), &terms);
            let rule_id = rules.add(nf.clone());
            let goal_id = goals.rule(rule_id);

            let input = NF::factor(v0, v0, (), &terms);

            b.iter(|| {
                let mut task = Task::new(0, goal_id, input.clone());

                // Push continuations to simulate depth
                for _ in 0..depth {
                    task.push_kont(Kont::AltNext {
                        alts: smallvec![goal_id],
                        input: input.clone(),
                    });
                }

                let mut ctx = EvalCtx {
                    goals: &goals,
                    rules: &rules,
                    terms: &terms,
                };

                backtrack(black_box(&mut task), black_box(&mut ctx))
            });
        });
    }

    group.finish();
}

/// Benchmark Peano addition for varying input sizes.
fn bench_peano_add(c: &mut Criterion) {
    // This benchmark requires the full addition relation to be set up
    // For now, we'll benchmark the composition operation directly

    let mut group = c.benchmark_group("peano_add");

    for n in [1, 3, 5] {
        group.bench_with_input(BenchmarkId::new("n", n), &n, |b, &n| {
            let (_goals, _rules, terms, symbols) = setup_stores();

            let z = symbols.intern("z");
            let s = symbols.intern("s");
            let cons = symbols.intern("cons");

            // Build input: (cons peano(n) peano(n))
            let num = build_peano(n, z, s, &terms);
            let input_term = terms.app2(cons, num, num);

            // Create an NF from this
            let v0 = terms.var(0);
            let _input_nf = NF::factor(input_term, v0, (), &terms);

            b.iter(|| {
                // Benchmark NF creation (factoring)
                black_box(NF::factor(input_term, v0, (), &terms))
            });
        });
    }

    group.finish();
}

criterion_group!(
    benches,
    bench_step_rule,
    bench_step_alt,
    bench_backtrack,
    bench_peano_add
);
criterion_main!(benches);
