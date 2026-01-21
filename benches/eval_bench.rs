//! Evaluation benchmarks using Criterion.
//!
//! Run with: `cargo bench`
//!
//! These benchmarks measure the core evaluation loop performance including:
//! - Step dispatch for different Rel shapes
//! - Or rotation progression
//! - NF factoring costs

use criterion::{black_box, criterion_group, criterion_main, BenchmarkId, Criterion};
use rwlog::{
    nf::NF,
    node::{step_node, Node, NodeStep},
    rel::Rel,
    symbol::SymbolStore,
    term::TermStore,
    work::{rel_to_node, Env, Tables},
};
use std::sync::Arc;

/// Create the standard test stores for benchmarks.
fn setup_stores() -> (TermStore, SymbolStore) {
    let symbols = SymbolStore::new();
    let terms = TermStore::new();
    (terms, symbols)
}

/// Build a Peano numeral with n successors: S(S(...S(Z)...))
fn build_peano(n: u32, z: lasso::Spur, s: lasso::Spur, terms: &TermStore) -> rwlog::term::TermId {
    let mut result = terms.app0(z);
    for _ in 0..n {
        result = terms.app1(s, result);
    }
    result
}

fn or_tree(mut rels: Vec<Rel<()>>) -> Rel<()> {
    let mut iter = rels.drain(..);
    let mut acc = iter.next().expect("at least one rel");
    for rel in iter {
        acc = Rel::Or(Arc::new(acc), Arc::new(rel));
    }
    acc
}

/// Benchmark a single step on a trivial Atom.
fn bench_step_atom(c: &mut Criterion) {
    let (terms, _symbols) = setup_stores();
    let v0 = terms.var(0);
    let nf = NF::factor(v0, v0, (), &terms);
    let rel = Rel::Atom(Arc::new(nf));
    let env = Env::new();
    let tables = Tables::new();
    let node = rel_to_node(&rel, &env, &tables);

    c.bench_function("step_atom", |b| {
        b.iter(|| {
            let step = step_node(node.clone(), &terms);
            black_box(step)
        });
    });
}

/// Benchmark a single step on Or nodes of varying branch counts.
fn bench_step_or(c: &mut Criterion) {
    let mut group = c.benchmark_group("step_or");

    for branches in [2, 4, 8] {
        group.bench_with_input(
            BenchmarkId::new("branches", branches),
            &branches,
            |b, &branches| {
                let (terms, _symbols) = setup_stores();
                let v0 = terms.var(0);
                let nf = NF::factor(v0, v0, (), &terms);

                let rels: Vec<_> = (0..branches)
                    .map(|_| Rel::Atom(Arc::new(nf.clone())))
                    .collect();
                let rel = or_tree(rels);
                let env = Env::new();
                let tables = Tables::new();
                let node = rel_to_node(&rel, &env, &tables);

                b.iter(|| {
                    let step = step_node(node.clone(), &terms);
                    black_box(step)
                });
            },
        );
    }

    group.finish();
}

/// Benchmark advancing through Or rotation for different depths.
fn bench_or_rotation(c: &mut Criterion) {
    let mut group = c.benchmark_group("or_rotation");

    for depth in [2, 5, 10] {
        group.bench_with_input(BenchmarkId::new("depth", depth), &depth, |b, &depth| {
            let (terms, _symbols) = setup_stores();
            let v0 = terms.var(0);
            let nf = NF::factor(v0, v0, (), &terms);
            let rels: Vec<_> = (0..depth)
                .map(|_| Rel::Atom(Arc::new(nf.clone())))
                .collect();
            let rel = or_tree(rels);
            let env = Env::new();
            let tables = Tables::new();
            let base = rel_to_node(&rel, &env, &tables);

            b.iter(|| {
                let mut node = base.clone();
                for _ in 0..depth {
                    let current = std::mem::replace(&mut node, Node::Fail);
                    match step_node(current, &terms) {
                        NodeStep::Emit(_, rest) | NodeStep::Continue(rest) => node = rest,
                        NodeStep::Exhausted => break,
                    }
                }
                black_box(node)
            });
        });
    }

    group.finish();
}

/// Benchmark Peano NF factoring for varying input sizes.
fn bench_peano_add(c: &mut Criterion) {
    let mut group = c.benchmark_group("peano_factor");

    for n in [1, 3, 5] {
        group.bench_with_input(BenchmarkId::new("n", n), &n, |b, &n| {
            let (terms, symbols) = setup_stores();

            let z = symbols.intern("z");
            let s = symbols.intern("s");
            let cons = symbols.intern("cons");

            // Build input: (cons peano(n) peano(n))
            let num = build_peano(n, z, s, &terms);
            let input_term = terms.app2(cons, num, num);

            let v0 = terms.var(0);

            b.iter(|| black_box(NF::factor(input_term, v0, (), &terms)));
        });
    }

    group.finish();
}

criterion_group!(
    benches,
    bench_step_atom,
    bench_step_or,
    bench_or_rotation,
    bench_peano_add
);
criterion_main!(benches);
