//! The normal store of the sorts, on trees.
//!
//! This is the reference the store version is tested against: the one
//! normal store (`Raw.Normal` in `lean/RwLog/Sorts/Normal.lean`) that has the
//! solutions of a problem (`Prob` in `lean/RwLog/Sorts/Reduce.lean`), or
//! nothing when the problem has no solution. The sorts must be well formed.
//!
//! How it is found:
//!
//! 1. Solve the equations and apply the solution.
//! 2. Push each sort down the pattern it is said of, to variables.
//! 3. Until nothing changes:
//!    * bring each exclusion to solved form under the sorts. One that cannot
//!      hold is dropped, and one that always holds kills the store;
//!    * the values a variable can take are its sorts without the ground
//!      terms it alone is excluded from. With no root symbol left the store
//!      is dead, and with one the variable is replaced by that symbol
//!      applied to new variables;
//!    * a variable gets every declared sort that holds all its values.
//! 4. Drop every exclusion that names a variable not in the pattern, number
//!    the variables in the order they first occur, write each exclusion with
//!    aliases bound to the earlier variable, drop the exclusions another one
//!    implies, and list them in order.

use super::{ap, put, put_list, sy, v, T};
use rwlog_core::store::{Node, Store, TermId};
use std::cell::RefCell;
use std::cmp::Ordering;
use std::collections::{BTreeMap, BTreeSet};

pub type Name = u32;
pub type Key = (u32, usize);
pub type Conj = BTreeSet<Name>;

/// `SortDef` of the specification.
#[derive(Clone, Debug, Default)]
pub struct Def {
    pub cases: Vec<(u32, Vec<Option<Name>>)>,
    pub rest: Option<(Vec<Key>, Option<Name>)>,
}

/// A first-order pattern.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum P {
    V(usize),
    F(u32, Vec<P>),
}

pub fn pv(n: usize) -> P {
    P::V(n)
}
pub fn pf(f: u32, args: Vec<P>) -> P {
    P::F(f, args)
}

impl P {
    pub fn vars(&self, out: &mut Vec<usize>) {
        match self {
            P::V(x) => {
                if !out.contains(x) {
                    out.push(*x)
                }
            }
            P::F(_, args) => args.iter().for_each(|a| a.vars(out)),
        }
    }

    pub fn is_ground(&self) -> bool {
        let mut vs = Vec::new();
        self.vars(&mut vs);
        vs.is_empty()
    }

    pub fn subst(&self, s: &BTreeMap<usize, P>) -> P {
        match self {
            P::V(x) => match s.get(x) {
                Some(p) => p.clone(),
                None => self.clone(),
            },
            P::F(f, args) => P::F(*f, args.iter().map(|a| a.subst(s)).collect()),
        }
    }

    fn occurs(&self, x: usize) -> bool {
        match self {
            P::V(y) => x == *y,
            P::F(_, args) => args.iter().any(|a| a.occurs(x)),
        }
    }

    /// The pattern as a term of the specification: the symbol applied to
    /// the arguments one at a time.
    pub fn tree(&self) -> T {
        match self {
            P::V(x) => v(*x as u128),
            P::F(f, args) => args.iter().fold(sy(*f), |acc, a| ap(acc, a.tree())),
        }
    }
}

/// `patCmp` of the specification.
pub fn pat_cmp(a: &T, b: &T) -> Ordering {
    match (a, b) {
        (T::V(x), T::V(y)) => x.cmp(y),
        (T::V(_), _) => Ordering::Less,
        (_, T::V(_)) => Ordering::Greater,
        (T::S(f), T::S(g)) => f.cmp(g),
        (T::S(_), _) => Ordering::Less,
        (_, T::S(_)) => Ordering::Greater,
        (T::A(a1, a2), T::A(b1, b2)) => pat_cmp(a1, b1).then_with(|| pat_cmp(a2, b2)),
    }
}

/// An exclusion in solved form: not all of `$x = p`.
pub type Binds = Vec<(usize, P)>;

/// `bindsCmp` of the specification.
pub fn binds_cmp(a: &Binds, b: &Binds) -> Ordering {
    let key = |x: &Binds| -> Vec<T> { x.iter().map(|(y, p)| ap(v(*y as u128), p.tree())).collect() };
    let (ka, kb) = (key(a), key(b));
    for (x, y) in ka.iter().zip(&kb) {
        let o = pat_cmp(x, y);
        if o != Ordering::Equal {
            return o;
        }
    }
    ka.len().cmp(&kb.len())
}

/// `Prob` of the specification.
#[derive(Clone, Debug)]
pub struct Prob {
    pub t: P,
    pub e: Vec<(P, P)>,
    pub a: Vec<(Name, P)>,
    pub x: Vec<Vec<(P, P)>>,
}

/// `Raw` of the specification.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Raw {
    pub t: P,
    pub c: Vec<Conj>,
    pub x: Vec<Binds>,
}

impl Raw {
    /// The raw store as a problem with the same solutions.
    pub fn prob(&self) -> Prob {
        let mut a = Vec::new();
        for (i, c) in self.c.iter().enumerate() {
            for n in c {
                a.push((*n, pv(i)));
            }
        }
        let x = self
            .x
            .iter()
            .map(|b| b.iter().map(|(y, p)| (pv(*y), p.clone())).collect())
            .collect();
        Prob { t: self.t.clone(), e: Vec::new(), a, x }
    }
}

/// How many terms sorts have in common. Well-formed sorts have no other
/// number.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Size {
    Empty,
    One(P),
    Infinite,
}

/// A root a term in some sorts may have: one the declarations name, or one
/// of the symbols they do not name, with no argument or with some.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Root {
    Named(Key),
    Fresh0,
    FreshN,
}

pub struct Sorts {
    pub defs: Vec<(Name, Def)>,
    sizes: RefCell<BTreeMap<Conj, Size>>,
}

impl Sorts {
    pub fn new(defs: Vec<(Name, Def)>) -> Sorts {
        Sorts { defs, sizes: RefCell::new(BTreeMap::new()) }
    }

    fn def(&self, n: Name) -> Option<&Def> {
        self.defs.iter().find(|(m, _)| *m == n).map(|(_, d)| d)
    }

    /// The declared names.
    pub fn names(&self) -> Vec<Name> {
        let mut out = Vec::new();
        for (n, _) in &self.defs {
            if !out.contains(n) {
                out.push(*n);
            }
        }
        out
    }

    pub fn step(&self, n: Name, key: Key) -> Option<Vec<Option<Name>>> {
        let d = self.def(n)?;
        if let Some((_, args)) = d.cases.iter().find(|(f, a)| (*f, a.len()) == key) {
            return Some(args.clone());
        }
        match &d.rest {
            Some((ex, arg)) if !ex.contains(&key) => Some(vec![*arg; key.1]),
            _ => None,
        }
    }

    pub fn member(&self, n: Name, t: &P) -> bool {
        match t {
            P::V(_) => panic!("a ground term has no variable"),
            P::F(f, args) => match self.step(n, (*f, args.len())) {
                None => false,
                Some(sorts) => sorts
                    .iter()
                    .zip(args)
                    .all(|(s, a)| s.is_none_or(|m| self.member(m, a))),
            },
        }
    }

    /// Every name declared or said of an argument, each once: the first to
    /// occur comes last.
    pub fn all_names(&self) -> Vec<Name> {
        let mut out = Vec::new();
        let mut note = |n: Name| {
            if !out.contains(&n) {
                out.insert(0, n);
            }
        };
        for (n, d) in &self.defs {
            note(*n);
            for (_, kids) in &d.cases {
                kids.iter().flatten().for_each(|k| note(*k));
            }
            if let Some((_, Some(k))) = &d.rest {
                note(*k);
            }
        }
        out
    }

    pub fn step_conj(&self, c: &Conj, key: Key) -> Option<Vec<Conj>> {
        let mut kids = vec![Conj::new(); key.1];
        for n in c {
            let args = self.step(*n, key)?;
            for (kid, a) in kids.iter_mut().zip(args) {
                kid.extend(a);
            }
        }
        Some(kids)
    }

    fn named(&self, n: Name, into: &mut Vec<Key>) {
        if let Some(d) = self.def(n) {
            let cases = d.cases.iter().map(|(f, a)| (*f, a.len()));
            let excluded = d.rest.iter().flat_map(|(ex, _)| ex.iter().copied());
            for k in cases.chain(excluded) {
                if !into.contains(&k) {
                    into.push(k);
                }
            }
        }
    }

    /// The roots a term in all of `c` may have, with the sorts of the
    /// arguments. `extra` are roots to treat as named. The symbols no
    /// declaration names stand together: with no argument, and with some,
    /// where the one set of sorts is that of every argument.
    fn roots(&self, c: &Conj, extra: &[Key]) -> Vec<(Root, Vec<Conj>)> {
        let mut keys = extra.to_vec();
        for n in c {
            self.named(*n, &mut keys);
        }
        let mut out = Vec::new();
        for k in keys {
            if let Some(kids) = self.step_conj(c, k) {
                out.push((Root::Named(k), kids));
            }
        }
        let rests: Option<Vec<Option<Name>>> = c
            .iter()
            .map(|n| self.def(*n).and_then(|d| d.rest.as_ref()).map(|(_, a)| *a))
            .collect();
        if let Some(args) = rests {
            out.push((Root::Fresh0, Vec::new()));
            out.push((Root::FreshN, vec![args.into_iter().flatten().collect()]));
        }
        out
    }

    /// How many terms are in all of `c`.
    pub fn size(&self, c: &Conj) -> Size {
        if let Some(s) = self.sizes.borrow().get(c) {
            return s.clone();
        }
        // Every set of sorts an argument below may have to be in.
        let mut graph: BTreeMap<Conj, Vec<(Root, Vec<Conj>)>> = BTreeMap::new();
        let mut todo = vec![c.clone()];
        while let Some(d) = todo.pop() {
            if graph.contains_key(&d) {
                continue;
            }
            let roots = self.roots(&d, &[]);
            for (_, kids) in &roots {
                todo.extend(kids.iter().cloned());
            }
            graph.insert(d, roots);
        }
        let mut live: BTreeSet<Conj> = BTreeSet::new();
        loop {
            let before = live.len();
            for (d, roots) in &graph {
                if roots.iter().any(|(_, kids)| kids.iter().all(|k| live.contains(k))) {
                    live.insert(d.clone());
                }
            }
            if live.len() == before {
                break;
            }
        }
        let alive = |kids: &Vec<Conj>| kids.iter().all(|k| live.contains(k));
        let mut finite: BTreeSet<Conj> = BTreeSet::new();
        loop {
            let before = finite.len();
            for (d, roots) in &graph {
                let all = roots.iter().filter(|(_, kids)| alive(kids)).all(|(r, kids)| {
                    matches!(r, Root::Named(_)) && kids.iter().all(|k| finite.contains(k))
                });
                if all {
                    finite.insert(d.clone());
                }
            }
            if finite.len() == before {
                break;
            }
        }
        let result = if !live.contains(c) {
            Size::Empty
        } else if !finite.contains(c) {
            Size::Infinite
        } else {
            let mut terms = Vec::new();
            for (r, kids) in &graph[c] {
                if !alive(kids) {
                    continue;
                }
                let Root::Named((f, _)) = r else { unreachable!() };
                let args: Vec<P> = kids
                    .iter()
                    .map(|k| match self.size(k) {
                        Size::One(p) => p,
                        other => panic!("the sorts are not well formed: {:?} has {:?}", k, other),
                    })
                    .collect();
                terms.push(pf(*f, args));
            }
            assert!(terms.len() == 1, "the sorts are not well formed: {:?} has {:?}", c, terms);
            Size::One(terms.remove(0))
        };
        self.sizes.borrow_mut().insert(c.clone(), result.clone());
        result
    }

    fn live(&self, c: &Conj) -> bool {
        self.size(c) != Size::Empty
    }

    /// The roots of `c` with a term.
    fn live_roots(&self, c: &Conj, extra: &[Key]) -> Vec<(Root, Vec<Conj>)> {
        let mut roots = self.roots(c, extra);
        roots.retain(|(_, kids)| kids.iter().all(|k| self.live(k)));
        roots
    }

    /// What `n` does at a root of `c`, when `n`'s named roots were given as
    /// `extra`.
    fn step_root(&self, n: Name, r: Root) -> Option<Vec<Option<Name>>> {
        match r {
            Root::Named(k) => self.step(n, k),
            Root::Fresh0 => self.def(n)?.rest.as_ref().map(|_| Vec::new()),
            Root::FreshN => self.def(n)?.rest.as_ref().map(|(_, a)| vec![*a]),
        }
    }

    /// Is every term in all of `c` in `n`?
    pub fn included(&self, c: &Conj, n: Name) -> bool {
        // A pair is refuted when a term of the sorts is not in the sort.
        type Pair = (Conj, Name);
        let mut graph: BTreeMap<Pair, Vec<Option<Vec<Pair>>>> = BTreeMap::new();
        let mut todo = vec![(c.clone(), n)];
        while let Some(pair) = todo.pop() {
            if graph.contains_key(&pair) {
                continue;
            }
            let mut extra = Vec::new();
            self.named(pair.1, &mut extra);
            let mut edges = Vec::new();
            for (r, kids) in self.live_roots(&pair.0, &extra) {
                match self.step_root(pair.1, r) {
                    None => edges.push(None),
                    Some(sorts) => {
                        let sub: Vec<Pair> = kids
                            .into_iter()
                            .zip(sorts)
                            .filter_map(|(k, s)| s.map(|m| (k, m)))
                            .collect();
                        todo.extend(sub.iter().cloned());
                        edges.push(Some(sub));
                    }
                }
            }
            graph.insert(pair, edges);
        }
        let mut refuted: BTreeSet<Pair> = BTreeSet::new();
        loop {
            let before = refuted.len();
            for (pair, edges) in &graph {
                let bad = edges.iter().any(|e| match e {
                    None => true,
                    Some(sub) => sub.iter().any(|p| refuted.contains(p)),
                });
                if bad {
                    refuted.insert(pair.clone());
                }
            }
            if refuted.len() == before {
                break;
            }
        }
        !refuted.contains(&(c.clone(), n))
    }

    /// `Sorts.sole` of the specification: the one root of the members of `c`
    /// that are not in `gone`, with the sorts of its arguments. Nothing when
    /// every sort of `c` has a rest, when no member is left, or when two are
    /// left with different roots.
    pub fn sole(&self, c: &Conj, gone: &[P]) -> Option<(Key, Vec<Conj>)> {
        if c.iter().all(|n| self.def(*n).is_some_and(|d| d.rest.is_some())) {
            return None;
        }
        let mut keys: Vec<Key> = Vec::new();
        for n in c {
            if let Some(d) = self.def(*n) {
                for (f, a) in &d.cases {
                    if !keys.contains(&(*f, a.len())) {
                        keys.push((*f, a.len()));
                    }
                }
            }
        }
        for k in roots_of(gone) {
            if !keys.contains(&k) {
                keys.push(k);
            }
        }
        let mut left = Vec::new();
        for k in keys {
            let Some(kids) = self.step_conj(c, k) else { continue };
            let sizes: Vec<Size> = kids.iter().map(|d| self.size(d)).collect();
            if sizes.iter().any(|z| matches!(z, Size::Empty)) {
                continue;
            }
            let only: Option<Vec<P>> = sizes
                .into_iter()
                .map(|z| match z {
                    Size::One(p) => Some(p),
                    _ => None,
                })
                .collect();
            if only.is_some_and(|args| gone.contains(&pf(k.0, args))) {
                continue;
            }
            left.push((k, kids));
        }
        if left.len() == 1 {
            left.pop()
        } else {
            None
        }
    }

    /// Is every term in all of `c`, but the ground terms `gone`, in `n`?
    pub fn included_but(&self, c: &Conj, n: Name, gone: &[P]) -> bool {
        if self.included(c, n) {
            return true;
        }
        if gone.is_empty() {
            return false;
        }
        let mut extra = Vec::new();
        self.named(n, &mut extra);
        for g in gone {
            if let P::F(f, args) = g {
                if !extra.contains(&(*f, args.len())) {
                    extra.push((*f, args.len()));
                }
            }
        }
        for (r, kids) in self.live_roots(c, &extra) {
            let sorts = self.step_root(n, r);
            let Root::Named((f, _)) = r else {
                // Infinitely many symbols: none of their terms may be left out.
                match sorts {
                    None => return false,
                    Some(sorts) => {
                        for (k, s) in kids.iter().zip(sorts) {
                            if s.is_some_and(|m| !self.included(k, m)) {
                                return false;
                            }
                        }
                    }
                }
                continue;
            };
            let here: Vec<&Vec<P>> = gone
                .iter()
                .filter_map(|g| match g {
                    P::F(h, args) if *h == f && args.len() == kids.len() => Some(args),
                    _ => None,
                })
                .collect();
            let ones: Vec<Option<P>> = kids
                .iter()
                .map(|k| match self.size(k) {
                    Size::One(p) => Some(p),
                    _ => None,
                })
                .collect();
            match sorts {
                None => {
                    // Every term with this root is left out of `n`.
                    let only: Option<Vec<P>> = ones.iter().cloned().collect();
                    match only {
                        Some(args) if here.contains(&&args) => {}
                        _ => return false,
                    }
                }
                Some(sorts) => {
                    for (i, s) in sorts.iter().enumerate() {
                        let Some(m) = s else { continue };
                        if self.included(&kids[i], *m) {
                            continue;
                        }
                        // Terms left out at argument `i`: the other
                        // arguments are free, so each must have one value.
                        let mut sub = Vec::new();
                        for args in &here {
                            let mut same = true;
                            for (j, one) in ones.iter().enumerate() {
                                if j != i && one.as_ref() != Some(&args[j]) {
                                    same = false;
                                }
                            }
                            if same {
                                sub.push(args[i].clone());
                            }
                        }
                        let fixed = ones.iter().enumerate().all(|(j, o)| j == i || o.is_some());
                        if !fixed || !self.included_but(&kids[i], *m, &sub) {
                            return false;
                        }
                    }
                }
            }
        }
        true
    }
}

/// The most general solution of the equations, with every variable it binds
/// replaced in what it binds the others to. Of two variables made equal the
/// later is bound to the earlier.
pub fn mgu(eqs: &[(P, P)]) -> Option<BTreeMap<usize, P>> {
    let mut s: BTreeMap<usize, P> = BTreeMap::new();
    let mut todo: Vec<(P, P)> = eqs.iter().rev().cloned().collect();
    while let Some((a, b)) = todo.pop() {
        let (a, b) = (a.subst(&s), b.subst(&s));
        if a == b {
            continue;
        }
        let (x, t) = match (a, b) {
            (P::V(x), P::V(y)) => (x.max(y), P::V(x.min(y))),
            (P::V(x), t) | (t, P::V(x)) => (x, t),
            (P::F(f, xs), P::F(g, ys)) => {
                if f != g || xs.len() != ys.len() {
                    return None;
                }
                todo.extend(xs.into_iter().zip(ys).rev());
                continue;
            }
        };
        if t.occurs(x) {
            return None;
        }
        let one = BTreeMap::from([(x, t.clone())]);
        for p in s.values_mut() {
            *p = p.subst(&one);
        }
        s.insert(x, t);
    }
    Some(s)
}

/// `unitOn` of the specification: the ground term the equations `e` hold
/// exactly at, as the value of the variable `v`. That is when their most
/// general solution binds `v` to a ground term and binds nothing else.
pub fn unit_on(v: usize, e: &[(P, P)]) -> Option<P> {
    let theta = mgu(e)?;
    if theta.len() != 1 {
        return None;
    }
    theta.get(&v).filter(|g| g.is_ground()).cloned()
}

/// `gone` of the specification: the terms the exclusions `x` exclude the
/// variable `v` from, in the order of the exclusions.
pub fn gone(x: &[Vec<(P, P)>], v: usize) -> Vec<P> {
    x.iter().filter_map(|e| unit_on(v, e)).collect()
}

/// A list of exclusions, each a list of equations, in the store.
pub fn put_excls(s: &mut Store, x: &[Vec<(P, P)>]) -> TermId {
    let mut out = s.alloc(Node::Nil);
    for e in x.iter().rev() {
        let h = put_eqns(s, e);
        out = s.alloc(Node::App(h, out));
    }
    out
}

/// A list of equations in the store, each the application of its two sides.
pub fn put_eqns(s: &mut Store, e: &[(P, P)]) -> TermId {
    let mut out = s.alloc(Node::Nil);
    for (a, b) in e.iter().rev() {
        let x = put_pat(s, a);
        let y = put_pat(s, b);
        let h = s.alloc(Node::App(x, y));
        out = s.alloc(Node::App(h, out));
    }
    out
}

/// `push` of the specification as a set: the sorts the variables of `p`
/// must be in for `p` to be in the sort `n`, or nothing when a sort rejects
/// a symbol of `p`.
pub fn push(s: &Sorts, n: Name, p: &P) -> Option<BTreeSet<(usize, Name)>> {
    let mut conj = BTreeMap::new();
    if !constrain(s, &mut conj, p, &Conj::from([n])) {
        return None;
    }
    Some(conj.iter().flat_map(|(x, c)| c.iter().map(|m| (*x, *m))).collect())
}

/// Require `p` to be in all of `c`, by sorts on its variables. False when
/// a symbol of `p` is one a sort rejects.
fn constrain(s: &Sorts, conj: &mut BTreeMap<usize, Conj>, p: &P, c: &Conj) -> bool {
    if c.is_empty() {
        return true;
    }
    match p {
        P::V(x) => {
            conj.entry(*x).or_default().extend(c.iter().copied());
            true
        }
        P::F(f, args) => match s.step_conj(c, (*f, args.len())) {
            None => false,
            Some(kids) => args.iter().zip(&kids).all(|(a, k)| constrain(s, conj, a, k)),
        },
    }
}

enum Excl {
    /// The equations cannot all hold: the exclusion says nothing.
    Vacuous,
    /// The equations always hold: nothing is left.
    Dead,
    Solved(BTreeMap<usize, P>),
}

/// An exclusion in solved form under the sorts. A variable its equations
/// leave with one value is bound to it.
fn solve_excl(s: &Sorts, conj: &BTreeMap<usize, Conj>, eqs: &[(P, P)]) -> Excl {
    let Some(mut binds) = mgu(eqs) else { return Excl::Vacuous };
    if binds.is_empty() {
        return Excl::Dead;
    }
    let mut local = conj.clone();
    for (x, p) in &binds {
        if let Some(c) = local.remove(x) {
            if !constrain(s, &mut local, p, &c) {
                return Excl::Vacuous;
            }
        }
    }
    let changed: Vec<usize> = local
        .iter()
        .filter(|(y, c)| conj.get(y) != Some(c))
        .map(|(y, _)| *y)
        .collect();
    for y in changed {
        match s.size(&local[&y]) {
            Size::Empty => return Excl::Vacuous,
            Size::Infinite => {}
            Size::One(g) => {
                let one = BTreeMap::from([(y, g.clone())]);
                for p in binds.values_mut() {
                    *p = p.subst(&one);
                }
                binds.insert(y, g);
            }
        }
    }
    Excl::Solved(binds)
}

fn roots_of(gone: &[P]) -> Vec<Key> {
    let mut out = Vec::new();
    for g in gone {
        if let P::F(f, args) = g {
            if !out.contains(&(*f, args.len())) {
                out.push((*f, args.len()));
            }
        }
    }
    out
}

/// The normal store with the solutions of the problem, or nothing when it
/// has none.
pub fn normal(s: &Sorts, prob: &Prob) -> Option<Raw> {
    let theta = mgu(&prob.e)?;
    let mut t = prob.t.subst(&theta);
    let mut x: Vec<Vec<(P, P)>> = prob
        .x
        .iter()
        .map(|e| e.iter().map(|(a, b)| (a.subst(&theta), b.subst(&theta))).collect())
        .collect();
    let mut conj: BTreeMap<usize, Conj> = BTreeMap::new();
    for (n, p) in &prob.a {
        if !constrain(s, &mut conj, &p.subst(&theta), &Conj::from([*n])) {
            return None;
        }
    }
    let mut all = Vec::new();
    t.vars(&mut all);
    for e in &x {
        for (a, b) in e {
            a.vars(&mut all);
            b.vars(&mut all);
        }
    }
    all.extend(conj.keys().copied());
    let mut next = all.iter().max().map_or(0, |m| m + 1);

    let solved = loop {
        let mut solved: Vec<BTreeMap<usize, P>> = Vec::new();
        let mut kept = Vec::new();
        for e in &x {
            match solve_excl(s, &conj, e) {
                Excl::Vacuous => {}
                Excl::Dead => return None,
                Excl::Solved(b) => {
                    solved.push(b);
                    kept.push(e.clone());
                }
            }
        }
        x = kept;
        let mut vars = Vec::new();
        t.vars(&mut vars);
        for e in &x {
            for (a, b) in e {
                a.vars(&mut vars);
                b.vars(&mut vars);
            }
        }
        for y in conj.keys() {
            if !vars.contains(y) {
                vars.push(*y);
            }
        }
        let mut changed = false;
        for y in vars {
            let c = conj.get(&y).cloned().unwrap_or_default();
            let gone: Vec<P> = solved
                .iter()
                .filter(|b| b.len() == 1)
                .filter_map(|b| b.get(&y))
                .filter(|g| g.is_ground())
                .cloned()
                .collect();
            let mut roots = s.live_roots(&c, &roots_of(&gone));
            roots.retain(|(r, kids)| {
                let Root::Named((f, _)) = r else { return true };
                let only: Option<Vec<P>> = kids
                    .iter()
                    .map(|k| match s.size(k) {
                        Size::One(p) => Some(p),
                        _ => None,
                    })
                    .collect();
                !only.is_some_and(|args| gone.contains(&pf(*f, args)))
            });
            if roots.is_empty() {
                return None;
            }
            // The symbols no declaration names are more than one root.
            if let [(Root::Named((f, _)), kids)] = roots.as_slice() {
                let args: Vec<P> = kids
                    .iter()
                    .map(|_| {
                        next += 1;
                        pv(next - 1)
                    })
                    .collect();
                conj.remove(&y);
                for (a, k) in args.iter().zip(kids) {
                    assert!(constrain(s, &mut conj, a, k));
                }
                let one = BTreeMap::from([(y, pf(*f, args))]);
                t = t.subst(&one);
                for e in x.iter_mut() {
                    for (a, b) in e.iter_mut() {
                        *a = a.subst(&one);
                        *b = b.subst(&one);
                    }
                }
                changed = true;
                break;
            }
            for n in s.names() {
                if !c.contains(&n) && s.included_but(&c, n, &gone) {
                    conj.entry(y).or_default().insert(n);
                    changed = true;
                }
            }
            if changed {
                break;
            }
        }
        if !changed {
            break solved;
        }
    };

    // The variables of the pattern, numbered as they first occur.
    let mut order = Vec::new();
    t.vars(&mut order);
    let number: BTreeMap<usize, P> =
        order.iter().enumerate().map(|(i, y)| (*y, pv(i))).collect();
    let seen = |p: &P| {
        let mut vs = Vec::new();
        p.vars(&mut vs);
        vs.iter().all(|y| order.contains(y))
    };
    let mut excl: Vec<Binds> = Vec::new();
    for b in &solved {
        if !b.iter().all(|(y, p)| order.contains(y) && seen(p)) {
            continue;
        }
        let eqs: Vec<(P, P)> =
            b.iter().map(|(y, p)| (number[y].clone(), p.subst(&number))).collect();
        let binds: Binds = mgu(&eqs).expect("a solved exclusion has a solution").into_iter().collect();
        if !excl.contains(&binds) {
            excl.push(binds);
        }
    }
    // One exclusion implies another when its equations make the other's hold.
    let implies = |a: &Binds, b: &Binds| {
        let m: BTreeMap<usize, P> = a.iter().cloned().collect();
        b.iter().all(|(y, p)| pv(*y).subst(&m) == p.subst(&m))
    };
    let mut x: Vec<Binds> = excl
        .iter()
        .filter(|a| !excl.iter().any(|b| b != *a && implies(a, b)))
        .cloned()
        .collect();
    x.sort_by(binds_cmp);
    let c = order.iter().map(|y| conj.get(y).cloned().unwrap_or_default()).collect();
    Some(Raw { t: t.subst(&number), c, x })
}

// Sorts in the store.

/// A sort or any term, as the store has it.
pub fn put_kid(s: &mut Store, k: &Option<Name>) -> TermId {
    match k {
        None => s.alloc(Node::Nil),
        Some(n) => s.alloc(Node::Sym(*n)),
    }
}

fn put_ids(s: &mut Store, ids: &[TermId]) -> TermId {
    let mut out = s.alloc(Node::Nil);
    for id in ids.iter().rev() {
        out = s.alloc(Node::App(*id, out));
    }
    out
}

/// The declarations as the store has them (`rwlog_core::sorts`).
pub fn put_sorts(s: &mut Store, sorts: &Sorts) -> TermId {
    let mut decls = Vec::new();
    for (name, def) in &sorts.defs {
        let mut cases = Vec::new();
        for (f, kids) in &def.cases {
            let kids: Vec<TermId> = kids.iter().map(|k| put_kid(s, k)).collect();
            let kids = put_ids(s, &kids);
            let f = s.alloc(Node::Sym(*f));
            cases.push(s.alloc(Node::App(f, kids)));
        }
        let cases = put_ids(s, &cases);
        let rest = match &def.rest {
            None => s.alloc(Node::Nil),
            Some((excluded, kid)) => {
                let mut ex = Vec::new();
                for (f, n) in excluded {
                    let nil = s.alloc(Node::Nil);
                    let units = put_ids(s, &vec![nil; *n]);
                    let f = s.alloc(Node::Sym(*f));
                    ex.push(s.alloc(Node::App(f, units)));
                }
                let ex = put_ids(s, &ex);
                let kid = put_kid(s, kid);
                s.alloc(Node::App(ex, kid))
            }
        };
        let def = s.alloc(Node::App(cases, rest));
        let name = s.alloc(Node::Sym(*name));
        decls.push(s.alloc(Node::App(name, def)));
    }
    put_ids(s, &decls)
}

/// A list of names in the store.
pub fn put_names(s: &mut Store, names: &[Name]) -> TermId {
    let ids: Vec<TermId> = names.iter().map(|n| s.alloc(Node::Sym(*n))).collect();
    put_ids(s, &ids)
}

/// A list of names, read back.
pub fn get_names(s: &mut Store, mut p: TermId) -> Vec<Name> {
    let mut out = Vec::new();
    loop {
        match s.read(p) {
            Node::Nil => return out,
            Node::App(h, t) => {
                match s.read(h) {
                    Node::Sym(n) => out.push(n),
                    _ => panic!("not a name"),
                }
                p = t;
            }
            _ => panic!("a term where a list was expected"),
        }
    }
}

/// A list of lists of names, read back.
pub fn get_conjs(s: &mut Store, mut p: TermId) -> Vec<Vec<Name>> {
    let mut out = Vec::new();
    loop {
        match s.read(p) {
            Node::Nil => return out,
            Node::App(h, t) => {
                out.push(get_names(s, h));
                p = t;
            }
            _ => panic!("a term where a list was expected"),
        }
    }
}

/// The members of a conjunction as the store lists them: in the order of
/// `names` from its end.
pub fn canon(names: &[Name], c: &Conj) -> Vec<Name> {
    names.iter().rev().filter(|n| c.contains(n)).copied().collect()
}

/// A pattern in the store.
pub fn put_pat(s: &mut Store, p: &P) -> TermId {
    put(s, &p.tree())
}

/// A list of sorts or any term, read back.
pub fn get_kids(s: &mut Store, mut p: TermId) -> Vec<Option<Name>> {
    let mut out = Vec::new();
    loop {
        match s.read(p) {
            Node::Nil => return out,
            Node::App(h, t) => {
                out.push(match s.read(h) {
                    Node::Nil => None,
                    Node::Sym(n) => Some(n),
                    _ => panic!("neither a sort nor any term"),
                });
                p = t;
            }
            _ => panic!("a term where a list was expected"),
        }
    }
}

/// The patterns as a list of the store.
pub fn put_pats(s: &mut Store, ps: &[P]) -> TermId {
    let ts: Vec<T> = ps.iter().map(P::tree).collect();
    put_list(s, &ts)
}
