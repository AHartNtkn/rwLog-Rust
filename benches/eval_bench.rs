//! Evaluation benchmarks using Criterion.
//!
//! Run with: `cargo bench`
//!
//! These benchmarks measure the core evaluation loop performance including:
//! - Engine stepping for simple relations
//! - Or branching with varying widths/depths
//! - NF factoring for larger ground terms

use criterion::{black_box, criterion_group, criterion_main, BatchSize, BenchmarkId, Criterion};
use rwlog::{engine::Engine, nf::NF, rel::Rel, symbol::SymbolStore, term::TermStore};
use std::sync::Arc;

/// Build a left-leaning Or tree from a list of Rel atoms.
fn build_or_chain(rels: Vec<Arc<Rel<()>>>) -> Rel<()> {
    let rel = rels
        .into_iter()
        .reduce(|left, right| Arc::new(Rel::Or(left, right)))
        .expect("at least one rel");
    rel.as_ref().clone()
}

fn make_identity_nf(terms: &mut TermStore) -> NF<()> {
    let v0 = terms.var(0);
    NF::factor(v0, v0, (), terms)
}

fn make_ground_nf(name: &str, symbols: &SymbolStore, terms: &mut TermStore) -> NF<()> {
    let f = symbols.intern(name);
    let term = terms.app0(f);
    NF::factor(term, term, (), terms)
}

/// Build a Peano numeral with n successors: S(S(...S(Z)...))
fn build_peano(n: u32, z: lasso::Spur, s: lasso::Spur, terms: &TermStore) -> rwlog::term::TermId {
    let mut result = terms.app0(z);
    for _ in 0..n {
        result = terms.app1(s, result);
    }
    result
}

/// Benchmark engine iteration on a simple atom.
fn bench_step_rule(c: &mut Criterion) {
    c.bench_function("engine_step_atom", |b| {
        b.iter_batched(
            || {
                let mut terms = TermStore::new();
                let nf = make_identity_nf(&mut terms);
                let rel = Rel::Atom(Arc::new(nf));
                Engine::new(rel, terms)
            },
            |mut engine| black_box(engine.next()),
            BatchSize::SmallInput,
        )
    });
}

/// Benchmark engine traversal of Or with varying branch counts.
fn bench_step_alt(c: &mut Criterion) {
    let mut group = c.benchmark_group("step_alt");

    for branches in [2, 4, 8] {
        group.bench_with_input(
            BenchmarkId::new("branches", branches),
            &branches,
            |b, &branches| {
                b.iter_batched(
                    || {
                        let mut terms = TermStore::new();
                        let symbols = SymbolStore::new();
                        let mut atoms = Vec::with_capacity(branches as usize);
                        for idx in 0..branches {
                            let name = format!("A{idx}");
                            let nf = make_ground_nf(&name, &symbols, &mut terms);
                            atoms.push(Arc::new(Rel::Atom(Arc::new(nf))));
                        }
                        let rel = build_or_chain(atoms);
                        Engine::new(rel, terms)
                    },
                    |mut engine| black_box(engine.collect_answers()),
                    BatchSize::SmallInput,
                );
            },
        );
    }

    group.finish();
}

/// Benchmark Or depth with left-leaning nesting.
fn bench_backtrack(c: &mut Criterion) {
    let mut group = c.benchmark_group("backtrack");

    for depth in [2, 5, 10] {
        group.bench_with_input(BenchmarkId::new("depth", depth), &depth, |b, &depth| {
            b.iter_batched(
                || {
                    let mut terms = TermStore::new();
                    let symbols = SymbolStore::new();
                    let mut rel = {
                        let nf = make_ground_nf("A0", &symbols, &mut terms);
                        Arc::new(Rel::Atom(Arc::new(nf)))
                    };
                    for idx in 1..=depth {
                        let nf = make_ground_nf(&format!("A{idx}"), &symbols, &mut terms);
                        let next = Arc::new(Rel::Atom(Arc::new(nf)));
                        rel = Arc::new(Rel::Or(rel, next));
                    }
                    Engine::new(rel.as_ref().clone(), terms)
                },
                |mut engine| black_box(engine.collect_answers()),
                BatchSize::SmallInput,
            );
        });
    }

    group.finish();
}

/// Benchmark Peano addition for varying input sizes.
fn bench_peano_add(c: &mut Criterion) {
    let mut group = c.benchmark_group("peano_add");

    for n in [1, 3, 5] {
        group.bench_with_input(BenchmarkId::new("n", n), &n, |b, &n| {
            let mut terms = TermStore::new();
            let symbols = SymbolStore::new();

            let z = symbols.intern("z");
            let s = symbols.intern("s");
            let cons = symbols.intern("cons");

            // Build input: (cons peano(n) peano(n))
            let num = build_peano(n, z, s, &terms);
            let input_term = terms.app2(cons, num, num);

            // Create an NF from this
            let v0 = terms.var(0);
            let _input_nf = NF::factor(input_term, v0, (), &mut terms);

            b.iter(|| {
                // Benchmark NF creation (factoring)
                black_box(NF::factor(input_term, v0, (), &mut terms))
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
