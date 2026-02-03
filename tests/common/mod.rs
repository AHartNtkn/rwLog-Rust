#![allow(dead_code)]

use std::collections::{HashMap, HashSet};
use std::sync::Arc;

use rwlog::engine::Engine;
use rwlog::nf::{direct_rule_terms, NF};
use rwlog::rel::Rel;
use rwlog::symbol::{FuncId, SymbolStore};
use rwlog::term::{Term, TermId, TermStore};

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Shape {
    Var(u32),
    App(String, Vec<Shape>),
}

pub fn shape_var(idx: u32) -> Shape {
    Shape::Var(idx)
}

pub fn shape_atom(name: &str) -> Shape {
    Shape::App(name.to_string(), Vec::new())
}

pub fn shape_app(name: &str, kids: Vec<Shape>) -> Shape {
    Shape::App(name.to_string(), kids)
}

pub fn shape_peano(n: usize) -> Shape {
    if n == 0 {
        shape_atom("z")
    } else {
        shape_app("s", vec![shape_peano(n - 1)])
    }
}

pub fn sym(symbols: &SymbolStore, name: &str) -> FuncId {
    symbols.intern(name)
}

pub fn t_atom(symbols: &SymbolStore, terms: &TermStore, name: &str) -> TermId {
    let f = sym(symbols, name);
    terms.app0(f)
}

pub fn t_var(terms: &TermStore, idx: u32) -> TermId {
    terms.var(idx)
}

pub fn t_app1(terms: &TermStore, func: FuncId, child: TermId) -> TermId {
    terms.app1(func, child)
}

pub fn t_app2(terms: &TermStore, func: FuncId, left: TermId, right: TermId) -> TermId {
    terms.app2(func, left, right)
}

pub fn t_peano(symbols: &SymbolStore, terms: &TermStore, n: usize) -> TermId {
    let z = t_atom(symbols, terms, "z");
    if n == 0 {
        return z;
    }
    let s = sym(symbols, "s");
    let mut out = z;
    for _ in 0..n {
        out = t_app1(terms, s, out);
    }
    out
}

pub fn rel_rule(lhs: TermId, rhs: TermId, terms: &mut TermStore) -> Rel<()> {
    Rel::Atom(Arc::new(NF::factor(lhs, rhs, (), terms)))
}

pub fn rel_at(term: TermId, terms: &mut TermStore) -> Rel<()> {
    rel_rule(term, term, terms)
}

pub fn rel_seq(parts: Vec<Rel<()>>) -> Rel<()> {
    let arcs: Vec<Arc<Rel<()>>> = parts.into_iter().map(Arc::new).collect();
    Rel::Seq(Arc::from(arcs))
}

pub fn rel_or(left: Rel<()>, right: Rel<()>) -> Rel<()> {
    Rel::Or(Arc::new(left), Arc::new(right))
}

pub fn rel_and(left: Rel<()>, right: Rel<()>) -> Rel<()> {
    Rel::And(Arc::new(left), Arc::new(right))
}

fn shape_term(
    term: TermId,
    terms: &TermStore,
    symbols: &SymbolStore,
    map: &mut HashMap<u32, u32>,
    next: &mut u32,
) -> Shape {
    match terms.resolve(term) {
        Some(Term::Var(idx)) => {
            let entry = map.entry(idx).or_insert_with(|| {
                let fresh = *next;
                *next += 1;
                fresh
            });
            Shape::Var(*entry)
        }
        Some(Term::App(func, kids)) => {
            let name = symbols
                .resolve(func)
                .unwrap_or("<unknown>")
                .to_string();
            let mut rendered = Vec::with_capacity(kids.len());
            for kid in kids.iter().copied() {
                rendered.push(shape_term(kid, terms, symbols, map, next));
            }
            Shape::App(name, rendered)
        }
        None => Shape::App("<invalid>".to_string(), Vec::new()),
    }
}

pub fn pair_shape(
    lhs: TermId,
    rhs: TermId,
    terms: &TermStore,
    symbols: &SymbolStore,
) -> (Shape, Shape) {
    let mut map = HashMap::new();
    let mut next = 0;
    let lhs_shape = shape_term(lhs, terms, symbols, &mut map, &mut next);
    let rhs_shape = shape_term(rhs, terms, symbols, &mut map, &mut next);
    (lhs_shape, rhs_shape)
}

pub fn nf_pair_shape<C: Clone>(
    nf: &NF<C>,
    terms: &mut TermStore,
    symbols: &SymbolStore,
) -> (Shape, Shape) {
    let (lhs, rhs) = direct_rule_terms(nf, terms).expect("expected unary relation");
    pair_shape(lhs, rhs, terms, symbols)
}

pub fn collect_pair_shapes(
    rel: Rel<()>,
    terms: TermStore,
    symbols: &SymbolStore,
    limit: Option<usize>,
) -> Vec<(Shape, Shape)> {
    let mut engine = Engine::new(rel, terms);
    let mut out = Vec::new();
    while let Some(nf) = engine.next() {
        let (lhs, rhs) = direct_rule_terms(&nf, engine.terms_mut())
            .expect("expected unary relation");
        out.push(pair_shape(lhs, rhs, engine.terms_mut(), symbols));
        if let Some(max) = limit {
            if out.len() >= max {
                break;
            }
        }
    }
    out
}

pub fn assert_pairs(actual: Vec<(Shape, Shape)>, expected: &[(Shape, Shape)]) {
    let actual_set: HashSet<(Shape, Shape)> = actual.iter().cloned().collect();
    let expected_set: HashSet<(Shape, Shape)> = expected.iter().cloned().collect();
    assert_eq!(actual_set, expected_set, "answer set mismatch");
    assert_eq!(
        actual.len(),
        expected_set.len(),
        "expected no duplicate answers"
    );
}

fn canonicalize_shape_pair(lhs: &Shape, rhs: &Shape) -> (Shape, Shape) {
    fn remap(
        shape: &Shape,
        map: &mut HashMap<u32, u32>,
        next: &mut u32,
    ) -> Shape {
        match shape {
            Shape::Var(idx) => {
                let entry = map.entry(*idx).or_insert_with(|| {
                    let fresh = *next;
                    *next += 1;
                    fresh
                });
                Shape::Var(*entry)
            }
            Shape::App(name, kids) => {
                let mapped = kids.iter().map(|kid| remap(kid, map, next)).collect();
                Shape::App(name.clone(), mapped)
            }
        }
    }

    let mut map = HashMap::new();
    let mut next = 0;
    let lhs_mapped = remap(lhs, &mut map, &mut next);
    let rhs_mapped = remap(rhs, &mut map, &mut next);
    (lhs_mapped, rhs_mapped)
}

pub fn assert_rel_pairs_with_dual<F>(
    symbols: &SymbolStore,
    expected: &[(Shape, Shape)],
    build: &F,
) where
    F: Fn(&mut TermStore, &SymbolStore) -> Rel<()>,
{
    let mut terms = TermStore::new();
    let rel = build(&mut terms, symbols);
    let actual = collect_pair_shapes(rel, terms, symbols, None);
    assert_pairs(actual, expected);

    let mut terms_dual = TermStore::new();
    let rel_dual = {
        let rel = build(&mut terms_dual, symbols);
        rwlog::rel::dual(&rel, &mut terms_dual)
    };
    let dual_pairs = collect_pair_shapes(rel_dual, terms_dual, symbols, None);
    let expected_dual: Vec<(Shape, Shape)> = expected
        .iter()
        .map(|(lhs, rhs)| canonicalize_shape_pair(rhs, lhs))
        .collect();
    assert_pairs(dual_pairs, &expected_dual);
}
