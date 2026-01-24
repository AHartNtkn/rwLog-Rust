use crate::constraint::ConstraintDisplay;
use crate::nf::apply_var_renaming;
use crate::subst::{apply_subst, Subst};
use crate::symbol::FuncId;
use crate::term::{Term, TermId, TermStore};
use hashbrown::{HashMap, HashSet};
use smallvec::SmallVec;
use std::cmp::Ordering;
use std::collections::VecDeque;
use std::hash::{Hash, Hasher};
use std::sync::atomic::{AtomicU64, Ordering as AtomicOrdering};
use std::sync::Arc;

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct PredId(pub u32);

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct RuleId(pub u32);

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct OccId(pub u32);

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct Cid(pub u32);

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct RVar(pub u32);

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct BuiltinId(pub u32);

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct PatId(pub u32);

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub enum PatNode {
    RVar(RVar),
    App {
        f: FuncId,
        kids: SmallVec<[PatId; 4]>,
    },
}

#[derive(Clone, Debug, Default)]
pub struct PatArena {
    nodes: Vec<PatNode>,
}

impl PatArena {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn push(&mut self, n: PatNode) -> PatId {
        let id = PatId(self.nodes.len() as u32);
        self.nodes.push(n);
        id
    }

    pub fn get(&self, p: PatId) -> &PatNode {
        &self.nodes[p.0 as usize]
    }
}

#[derive(Clone, Debug)]
pub struct RVarEnv {
    gen: u32,
    stamp: Vec<u32>,
    val: Vec<TermId>,
    trail: SmallVec<[RVar; 32]>,
}

impl RVarEnv {
    pub fn new(n_rvars: u32) -> Self {
        let n = n_rvars as usize;
        Self {
            gen: 1,
            stamp: vec![0; n],
            val: vec![TermId::from_raw(0); n],
            trail: SmallVec::new(),
        }
    }

    pub fn reset(&mut self) {
        self.gen = self.gen.wrapping_add(1);
        if self.gen == 0 {
            for s in &mut self.stamp {
                *s = 0;
            }
            self.gen = 1;
        }
        self.trail.clear();
    }

    pub fn trail_len(&self) -> usize {
        self.trail.len()
    }

    pub fn unwind(&mut self, to_len: usize) {
        while self.trail.len() > to_len {
            let RVar(v) = self.trail.pop().unwrap();
            self.stamp[v as usize] = 0;
        }
    }

    pub fn get(&self, r: RVar) -> Option<TermId> {
        let i = r.0 as usize;
        if i < self.stamp.len() && self.stamp[i] == self.gen {
            Some(self.val[i])
        } else {
            None
        }
    }

    pub fn bind(&mut self, r: RVar, t: TermId) -> bool {
        let i = r.0 as usize;
        if i >= self.stamp.len() {
            return false;
        }
        if self.stamp[i] == self.gen {
            self.val[i] == t
        } else {
            self.stamp[i] = self.gen;
            self.val[i] = t;
            self.trail.push(r);
            true
        }
    }
}

pub fn match_pat_bind(
    pats: &PatArena,
    terms: &TermStore,
    pat: PatId,
    term: TermId,
    env: &mut RVarEnv,
) -> bool {
    let mut stack: SmallVec<[(PatId, TermId); 32]> = SmallVec::new();
    stack.push((pat, term));
    while let Some((p, t)) = stack.pop() {
        match pats.get(p) {
            PatNode::RVar(rv) => {
                if !env.bind(*rv, t) {
                    return false;
                }
            }
            PatNode::App { f, kids } => match terms.resolve(t) {
                Some(Term::App(tf, tks)) => {
                    if *f != tf || kids.len() != tks.len() {
                        return false;
                    }
                    for (cp, ct) in kids.iter().zip(tks.iter()) {
                        stack.push((*cp, *ct));
                    }
                }
                _ => return false,
            },
        }
    }
    true
}

pub fn match_pat_nobind(
    pats: &PatArena,
    terms: &TermStore,
    pat: PatId,
    term: TermId,
    env: &RVarEnv,
) -> bool {
    let mut stack: SmallVec<[(PatId, TermId); 32]> = SmallVec::new();
    stack.push((pat, term));
    while let Some((p, t)) = stack.pop() {
        match pats.get(p) {
            PatNode::RVar(rv) => match env.get(*rv) {
                Some(tv) if tv == t => {}
                _ => return false,
            },
            PatNode::App { f, kids } => match terms.resolve(t) {
                Some(Term::App(tf, tks)) => {
                    if *f != tf || kids.len() != tks.len() {
                        return false;
                    }
                    for (cp, ct) in kids.iter().zip(tks.iter()) {
                        stack.push((*cp, *ct));
                    }
                }
                _ => return false,
            },
        }
    }
    true
}

pub trait Theory: Send + Sync + 'static {
    type Store: Clone + Send + Sync + Default + 'static;

    fn entails_eq(store: &Self::Store, a: TermId, b: TermId) -> bool;
    fn entails_neq(store: &Self::Store, a: TermId, b: TermId) -> bool;
    fn extract_subst(store: &Self::Store) -> Subst;
    fn merge_store(a: &Self::Store, b: &Self::Store) -> Option<Self::Store>;
    fn apply_subst(store: &Self::Store, subst: &Subst, terms: &mut TermStore) -> Self::Store;
    fn freeze_store(store: &Self::Store) -> Vec<u8>;
    fn thaw_store(bytes: &[u8]) -> Self::Store;
    fn remap_vars(store: &Self::Store, map: &[Option<u32>], terms: &mut TermStore) -> Self::Store;
    fn collect_vars(store: &Self::Store, terms: &TermStore, out: &mut Vec<u32>);
    fn is_empty(store: &Self::Store) -> bool;
}

#[derive(Clone, Default, Debug)]
pub struct NoTheory;

impl Theory for NoTheory {
    type Store = ();

    fn entails_eq(_store: &Self::Store, a: TermId, b: TermId) -> bool {
        a == b
    }

    fn entails_neq(_store: &Self::Store, a: TermId, b: TermId) -> bool {
        a != b
    }

    fn extract_subst(_store: &Self::Store) -> Subst {
        Subst::default()
    }

    fn merge_store(_a: &Self::Store, _b: &Self::Store) -> Option<Self::Store> {
        Some(())
    }

    fn apply_subst(_store: &Self::Store, _subst: &Subst, _terms: &mut TermStore) -> Self::Store {}

    fn freeze_store(_store: &Self::Store) -> Vec<u8> {
        Vec::new()
    }

    fn thaw_store(_bytes: &[u8]) -> Self::Store {}

    fn remap_vars(
        _store: &Self::Store,
        _map: &[Option<u32>],
        _terms: &mut TermStore,
    ) -> Self::Store {
    }

    fn collect_vars(_store: &Self::Store, _terms: &TermStore, _out: &mut Vec<u32>) {}

    fn is_empty(_store: &Self::Store) -> bool {
        true
    }
}

pub struct Builtin<T: Theory> {
    pub arity: u8,
    pub guard: fn(&T::Store, &TermStore, &[TermId]) -> bool,
    pub add: fn(&mut T::Store, &TermStore, &[TermId]) -> bool,
}

pub struct BuiltinRegistry<T: Theory> {
    pub builtins: Vec<Builtin<T>>,
}

impl<T: Theory> Copy for Builtin<T> {}

impl<T: Theory> Clone for Builtin<T> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<T: Theory> std::fmt::Debug for Builtin<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Builtin")
            .field("arity", &self.arity)
            .finish()
    }
}

impl<T: Theory> Clone for BuiltinRegistry<T> {
    fn clone(&self) -> Self {
        Self {
            builtins: self.builtins.clone(),
        }
    }
}

impl<T: Theory> std::fmt::Debug for BuiltinRegistry<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("BuiltinRegistry")
            .field("builtins_len", &self.builtins.len())
            .finish()
    }
}

impl<T: Theory> Default for BuiltinRegistry<T> {
    fn default() -> Self {
        Self {
            builtins: Vec::new(),
        }
    }
}

impl<T: Theory> BuiltinRegistry<T> {
    pub fn get(&self, id: BuiltinId) -> &Builtin<T> {
        &self.builtins[id.0 as usize]
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash)]
pub enum GVal {
    RVar(RVar),
    Const(TermId),
}

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub enum GuardInstr {
    Eq(GVal, GVal),
    Neq(GVal, GVal),
    TopFunctor { t: GVal, f: FuncId, arity: u8 },
    MatchPat { pat: PatId, t: GVal },
    Call { bid: BuiltinId, args: Box<[GVal]> },
}

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub struct GuardProg {
    pub code: Box<[GuardInstr]>,
}

impl GuardProg {
    pub fn empty() -> Self {
        Self { code: Box::new([]) }
    }

    pub fn new(code: Vec<GuardInstr>) -> Self {
        Self {
            code: code.into_boxed_slice(),
        }
    }

    pub fn eval<T: Theory>(
        &self,
        pats: &PatArena,
        terms: &TermStore,
        builtins: &T::Store,
        reg: &BuiltinRegistry<T>,
        env: &RVarEnv,
    ) -> bool {
        for ins in self.code.iter() {
            let ok = match ins {
                GuardInstr::Eq(a, b) => {
                    let (ta, tb) = match eval_gval_pair(env, *a, *b) {
                        Some(pair) => pair,
                        None => return false,
                    };
                    T::entails_eq(builtins, ta, tb)
                }
                GuardInstr::Neq(a, b) => {
                    let (ta, tb) = match eval_gval_pair(env, *a, *b) {
                        Some(pair) => pair,
                        None => return false,
                    };
                    T::entails_neq(builtins, ta, tb)
                }
                GuardInstr::TopFunctor { t, f, arity } => {
                    let tt = match eval_gval(env, *t) {
                        Some(x) => x,
                        None => return false,
                    };
                    match terms.resolve(tt) {
                        Some(Term::App(tf, kids)) => tf == *f && kids.len() == (*arity as usize),
                        _ => false,
                    }
                }
                GuardInstr::MatchPat { pat, t } => {
                    let tt = match eval_gval(env, *t) {
                        Some(x) => x,
                        None => return false,
                    };
                    match_pat_nobind(pats, terms, *pat, tt, env)
                }
                GuardInstr::Call { bid, args } => {
                    let b = reg.get(*bid);
                    if args.len() != b.arity as usize {
                        return false;
                    }
                    let av = match collect_gval_args(args, env) {
                        Some(v) => v,
                        None => return false,
                    };
                    (b.guard)(builtins, terms, &av)
                }
            };
            if !ok {
                return false;
            }
        }
        true
    }
}

fn eval_gval_pair(env: &RVarEnv, a: GVal, b: GVal) -> Option<(TermId, TermId)> {
    Some((eval_gval(env, a)?, eval_gval(env, b)?))
}

fn collect_gval_args(args: &[GVal], env: &RVarEnv) -> Option<SmallVec<[TermId; 8]>> {
    args.iter().map(|a| eval_gval(env, *a)).collect()
}

fn eval_gval(env: &RVarEnv, v: GVal) -> Option<TermId> {
    match v {
        GVal::Const(t) => Some(t),
        GVal::RVar(rv) => env.get(rv),
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash)]
pub enum ArgExpr {
    RVar(RVar),
    Const(TermId),
    Pat(PatId),
}

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub enum BodyInstr {
    AddChr {
        pred: PredId,
        args: Box<[ArgExpr]>,
    },
    AddBuiltin {
        bid: BuiltinId,
        args: Box<[ArgExpr]>,
    },
    Fail,
}

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub struct BodyProg {
    pub code: Box<[BodyInstr]>,
}

impl BodyProg {
    pub fn new(code: Vec<BodyInstr>) -> Self {
        Self {
            code: code.into_boxed_slice(),
        }
    }

    pub fn exec<T: Theory>(
        &self,
        pats: &PatArena,
        terms: &mut TermStore,
        reg: &BuiltinRegistry<T>,
        env: &RVarEnv,
        st: &mut ChrState<T>,
    ) -> bool {
        for ins in self.code.iter() {
            match ins {
                BodyInstr::AddChr { pred, args } => {
                    let av = match collect_args(args, pats, terms, env) {
                        Some(v) => v,
                        None => return false,
                    };
                    st.introduce(*pred, &av, terms);
                }
                BodyInstr::AddBuiltin { bid, args } => {
                    let b = reg.get(*bid);
                    if args.len() != b.arity as usize {
                        return false;
                    }
                    let av = match collect_args(args, pats, terms, env) {
                        Some(v) => v,
                        None => return false,
                    };
                    if !(b.add)(&mut st.builtins, terms, &av) {
                        return false;
                    }
                }
                BodyInstr::Fail => return false,
            }
        }
        true
    }
}

fn collect_args(
    args: &[ArgExpr],
    pats: &PatArena,
    terms: &mut TermStore,
    env: &RVarEnv,
) -> Option<SmallVec<[TermId; 8]>> {
    let mut av: SmallVec<[TermId; 8]> = SmallVec::new();
    for a in args.iter() {
        av.push(eval_arg_expr(pats, terms, env, *a)?);
    }
    Some(av)
}

fn eval_arg_expr(
    pats: &PatArena,
    terms: &mut TermStore,
    env: &RVarEnv,
    e: ArgExpr,
) -> Option<TermId> {
    match e {
        ArgExpr::RVar(rv) => env.get(rv),
        ArgExpr::Const(t) => Some(t),
        ArgExpr::Pat(p) => instantiate_pat(pats, terms, env, p),
    }
}

pub fn instantiate_pat(
    pats: &PatArena,
    terms: &mut TermStore,
    env: &RVarEnv,
    root: PatId,
) -> Option<TermId> {
    let mut stack: Vec<(PatId, usize)> = vec![(root, 0)];
    let mut out: Vec<TermId> = Vec::new();
    while let Some((p, i)) = stack.pop() {
        match pats.get(p) {
            PatNode::RVar(rv) => {
                let t = env.get(*rv)?;
                out.push(t);
            }
            PatNode::App { f, kids } => {
                if i < kids.len() {
                    stack.push((p, i + 1));
                    stack.push((kids[i], 0));
                } else {
                    let n = kids.len();
                    if out.len() < n {
                        return None;
                    }
                    let start = out.len() - n;
                    let args = &out[start..];
                    let t = terms.app(*f, args.iter().copied().collect());
                    out.truncate(start);
                    out.push(t);
                }
            }
        }
    }
    if out.len() == 1 {
        Some(out[0])
    } else {
        None
    }
}

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub struct HeadPat {
    pub pred: PredId,
    pub args: Box<[PatId]>,
}

impl HeadPat {
    pub fn new(pred: PredId, args: Vec<PatId>) -> Self {
        Self {
            pred,
            args: args.into_boxed_slice(),
        }
    }
}

#[derive(Clone, Debug)]
pub struct PredDecl {
    pub name: String,
    pub arity: u8,
    pub index_specs: Box<[IndexSpec]>,
}

#[derive(Clone, Debug)]
pub enum IndexSpec {
    PredOnly,
    ArgTerm(u8),
    ArgTopFunctor(u8),
    ArgPairTerm(u8, u8),
}

#[derive(Clone, Debug)]
pub enum IndexData {
    PredOnly,
    ArgTerm(HashMap<TermId, Vec<Cid>>),
    ArgTopFunctor(HashMap<FuncId, Vec<Cid>>),
    ArgPairTerm(HashMap<(TermId, TermId), Vec<Cid>>),
}

#[derive(Clone, Debug)]
pub struct PredStore {
    pub all: Vec<Cid>,
    pub indexes: Vec<IndexData>,
}

impl PredStore {
    fn new(specs: &[IndexSpec]) -> Self {
        let mut indexes = Vec::with_capacity(specs.len());
        for spec in specs {
            let idx = match spec {
                IndexSpec::PredOnly => IndexData::PredOnly,
                IndexSpec::ArgTerm(_) => IndexData::ArgTerm(HashMap::new()),
                IndexSpec::ArgTopFunctor(_) => IndexData::ArgTopFunctor(HashMap::new()),
                IndexSpec::ArgPairTerm(_, _) => IndexData::ArgPairTerm(HashMap::new()),
            };
            indexes.push(idx);
        }
        Self {
            all: Vec::new(),
            indexes,
        }
    }

    fn insert(&mut self, cid: Cid, inst: &CInstance, terms: &TermStore, specs: &[IndexSpec]) {
        self.all.push(cid);
        for (i, spec) in specs.iter().enumerate() {
            match (spec, &mut self.indexes[i]) {
                (IndexSpec::PredOnly, _) => {}
                (IndexSpec::ArgTerm(pos), IndexData::ArgTerm(map)) => {
                    let p = *pos as usize;
                    if p < inst.args.len() {
                        map.entry(inst.args[p]).or_default().push(cid);
                    }
                }
                (IndexSpec::ArgTopFunctor(pos), IndexData::ArgTopFunctor(map)) => {
                    let p = *pos as usize;
                    if p < inst.args.len() {
                        if let Some(Term::App(f, _)) = terms.resolve(inst.args[p]) {
                            map.entry(f).or_default().push(cid);
                        }
                    }
                }
                (IndexSpec::ArgPairTerm(a, b), IndexData::ArgPairTerm(map)) => {
                    let ia = *a as usize;
                    let ib = *b as usize;
                    if ia < inst.args.len() && ib < inst.args.len() {
                        let key = (inst.args[ia], inst.args[ib]);
                        map.entry(key).or_default().push(cid);
                    }
                }
                _ => {}
            }
        }
    }
}

#[derive(Clone, Debug)]
pub struct CInstance {
    pub cid: Cid,
    pub pred: PredId,
    pub args: SmallVec<[TermId; 4]>,
    pub alive: bool,
}

#[derive(Clone, Debug)]
pub struct ChrStore {
    pub inst: Vec<CInstance>,
    pub preds: Vec<PredStore>,
    pub alive_count: u32,
    pub dead_count: u32,
}

impl ChrStore {
    pub fn new(preds: &[PredDecl]) -> Self {
        let mut pred_stores = Vec::with_capacity(preds.len());
        for pred in preds {
            pred_stores.push(PredStore::new(&pred.index_specs));
        }
        Self {
            inst: Vec::new(),
            preds: pred_stores,
            alive_count: 0,
            dead_count: 0,
        }
    }

    fn add_chr(
        &mut self,
        cid: Cid,
        pred: PredId,
        args: &[TermId],
        terms: &TermStore,
        specs: &[IndexSpec],
    ) {
        let mut sv: SmallVec<[TermId; 4]> = SmallVec::new();
        sv.extend_from_slice(args);
        let inst = CInstance {
            cid,
            pred,
            args: sv,
            alive: true,
        };
        self.inst.push(inst);
        let pred_store = &mut self.preds[pred.0 as usize];
        let inst_ref = &self.inst[cid.0 as usize];
        pred_store.insert(cid, inst_ref, terms, specs);
        self.alive_count += 1;
    }

    fn mark_dead(&mut self, cid: Cid) {
        if let Some(inst) = self.inst.get_mut(cid.0 as usize) {
            if inst.alive {
                inst.alive = false;
                self.alive_count = self.alive_count.saturating_sub(1);
                self.dead_count += 1;
            }
        }
    }

    fn rebuild_indexes(&mut self, preds: &[PredDecl], terms: &TermStore) {
        self.preds = preds
            .iter()
            .map(|p| PredStore::new(&p.index_specs))
            .collect();
        self.alive_count = 0;
        self.dead_count = 0;
        for inst in self.inst.iter() {
            if inst.alive {
                self.alive_count += 1;
                let pred = inst.pred;
                let specs = &preds[pred.0 as usize].index_specs;
                self.preds[pred.0 as usize].insert(inst.cid, inst, terms, specs);
            } else {
                self.dead_count += 1;
            }
        }
    }
}

#[derive(Clone, Copy, Debug)]
pub enum ProbeKind {
    ScanAll,
    Index(u8),
}

#[derive(Clone, Copy, Debug)]
pub enum KeyMode {
    None,
    RVar(u32),
    FunctorConst(FuncId),
    PairRVar(u32, u32),
}

#[derive(Clone, Debug)]
pub struct JoinStep {
    pub head: u8,
    pub pred: PredId,
    pub probe: ProbeKind,
    pub key_mode: KeyMode,
}

#[derive(Clone, Debug)]
pub struct Occurrence {
    pub occ_id: OccId,
    pub anchor_head: u8,
    pub steps: SmallVec<[JoinStep; 4]>,
    pub removed_mask: u64,
}

#[derive(Debug)]
pub struct Rule<T: Theory> {
    pub rid: RuleId,
    pub n_rvars: u32,
    pub heads: Box<[HeadPat]>,
    pub guard: GuardProg,
    pub body: BodyProg,
    pub priority: i32,
    pub is_propagation: bool,
    pub occs: Box<[Occurrence]>,
    pub removed_mask: u64,
    _phantom: std::marker::PhantomData<T>,
}

impl<T: Theory> Clone for Rule<T> {
    fn clone(&self) -> Self {
        Self {
            rid: self.rid,
            n_rvars: self.n_rvars,
            heads: self.heads.clone(),
            guard: self.guard.clone(),
            body: self.body.clone(),
            priority: self.priority,
            is_propagation: self.is_propagation,
            occs: self.occs.clone(),
            removed_mask: self.removed_mask,
            _phantom: std::marker::PhantomData,
        }
    }
}

#[derive(Clone, Debug)]
pub struct OccRef {
    pub rid: RuleId,
    pub occ: u16,
}

#[derive(Debug)]
pub struct ChrProgram<T: Theory> {
    pub preds: Box<[PredDecl]>,
    pub rules: Box<[Rule<T>]>,
    pub triggers: Vec<Vec<OccRef>>,
    pub pats: PatArena,
    pub builtins: BuiltinRegistry<T>,
    pub pred_names: HashMap<String, PredId>,
    pub program_id: u64,
}

impl<T: Theory> Clone for ChrProgram<T> {
    fn clone(&self) -> Self {
        Self {
            preds: self.preds.clone(),
            rules: self.rules.clone(),
            triggers: self.triggers.clone(),
            pats: self.pats.clone(),
            builtins: self.builtins.clone(),
            pred_names: self.pred_names.clone(),
            program_id: self.program_id,
        }
    }
}

#[derive(Clone, Debug)]
struct RuleDraft {
    kept: Vec<HeadPat>,
    removed: Vec<HeadPat>,
    guard: GuardProg,
    body: BodyProg,
    priority: i32,
}

#[derive(Clone, Debug)]
pub struct ChrProgramBuilder<T: Theory> {
    preds: Vec<PredDecl>,
    pred_names: HashMap<String, PredId>,
    rules: Vec<RuleDraft>,
    pats: PatArena,
    builtins: BuiltinRegistry<T>,
}

impl<T: Theory> ChrProgramBuilder<T> {
    pub fn new(builtins: BuiltinRegistry<T>) -> Self {
        Self {
            preds: Vec::new(),
            pred_names: HashMap::new(),
            rules: Vec::new(),
            pats: PatArena::new(),
            builtins,
        }
    }

    pub fn pred(&mut self, name: &str, arity: u8, index_specs: Vec<IndexSpec>) -> PredId {
        let id = PredId(self.preds.len() as u32);
        self.preds.push(PredDecl {
            name: name.to_string(),
            arity,
            index_specs: index_specs.into_boxed_slice(),
        });
        self.pred_names.insert(name.to_string(), id);
        id
    }

    pub fn pred_id(&self, name: &str) -> Option<PredId> {
        self.pred_names.get(name).copied()
    }

    pub fn pred_arity(&self, pred: PredId) -> Option<u8> {
        self.preds.get(pred.0 as usize).map(|p| p.arity)
    }

    pub fn pat_var(&mut self, rvar: RVar) -> PatId {
        self.pats.push(PatNode::RVar(rvar))
    }

    pub fn pat_app(&mut self, f: FuncId, kids: Vec<PatId>) -> PatId {
        let mut sv: SmallVec<[PatId; 4]> = SmallVec::new();
        sv.extend_from_slice(&kids);
        self.pats.push(PatNode::App { f, kids: sv })
    }

    pub fn rule(
        &mut self,
        kept: Vec<HeadPat>,
        removed: Vec<HeadPat>,
        guard: GuardProg,
        body: BodyProg,
        priority: i32,
    ) -> RuleId {
        let rid = RuleId(self.rules.len() as u32);
        self.rules.push(RuleDraft {
            kept,
            removed,
            guard,
            body,
            priority,
        });
        rid
    }

    pub fn build(self) -> Arc<ChrProgram<T>> {
        let program_id = NEXT_PROGRAM_ID.fetch_add(1, AtomicOrdering::Relaxed);
        let mut rules = Vec::with_capacity(self.rules.len());
        for (idx, draft) in self.rules.into_iter().enumerate() {
            let mut heads = Vec::new();
            let kept_len = draft.kept.len();
            heads.extend(draft.kept.into_iter());
            heads.extend(draft.removed.into_iter());

            let mut removed_mask = 0u64;
            for i in kept_len..heads.len() {
                if i < 64 {
                    removed_mask |= 1u64 << i;
                }
            }

            let n_rvars = max_rvar_in_heads(&heads, &self.pats);
            let occs = compile_occurrences(
                RuleId(idx as u32),
                &heads,
                &self.preds,
                &self.pats,
                removed_mask,
            );

            let is_propagation = removed_mask == 0;
            rules.push(Rule {
                rid: RuleId(idx as u32),
                n_rvars,
                heads: heads.into_boxed_slice(),
                guard: draft.guard,
                body: draft.body,
                priority: draft.priority,
                is_propagation,
                occs,
                removed_mask,
                _phantom: std::marker::PhantomData,
            });
        }

        let mut triggers: Vec<Vec<OccRef>> = vec![Vec::new(); self.preds.len()];
        for rule in rules.iter() {
            for (occ_idx, occ) in rule.occs.iter().enumerate() {
                let head = &rule.heads[occ.anchor_head as usize];
                triggers[head.pred.0 as usize].push(OccRef {
                    rid: rule.rid,
                    occ: occ_idx as u16,
                });
            }
        }

        for occs in triggers.iter_mut() {
            occs.sort_by(|a, b| occ_ref_order(a, b, &rules));
        }

        Arc::new(ChrProgram {
            preds: self.preds.into_boxed_slice(),
            rules: rules.into_boxed_slice(),
            triggers,
            pats: self.pats,
            builtins: self.builtins,
            pred_names: self.pred_names,
            program_id,
        })
    }
}

fn occ_ref_order<T: Theory>(a: &OccRef, b: &OccRef, rules: &[Rule<T>]) -> Ordering {
    let ra = &rules[a.rid.0 as usize];
    let rb = &rules[b.rid.0 as usize];
    rb.priority
        .cmp(&ra.priority)
        .then_with(|| a.rid.cmp(&b.rid))
        .then_with(|| a.occ.cmp(&b.occ))
}

fn max_rvar_in_heads(heads: &[HeadPat], pats: &PatArena) -> u32 {
    let mut max = None;
    for head in heads {
        for arg in head.args.iter() {
            collect_rvars(*arg, pats, &mut max);
        }
    }
    max.map(|v| v + 1).unwrap_or(0)
}

fn collect_rvars(p: PatId, pats: &PatArena, max: &mut Option<u32>) {
    match pats.get(p) {
        PatNode::RVar(rv) => {
            *max = Some(max.map_or(rv.0, |m| m.max(rv.0)));
        }
        PatNode::App { kids, .. } => {
            for kid in kids.iter() {
                collect_rvars(*kid, pats, max);
            }
        }
    }
}

fn compile_occurrences(
    _rid: RuleId,
    heads: &[HeadPat],
    preds: &[PredDecl],
    pats: &PatArena,
    removed_mask: u64,
) -> Box<[Occurrence]> {
    let mut occs = Vec::with_capacity(heads.len());
    for anchor in 0..heads.len() {
        let steps = compile_join_steps(anchor, heads, preds, pats);
        occs.push(Occurrence {
            occ_id: OccId(anchor as u32),
            anchor_head: anchor as u8,
            steps,
            removed_mask,
        });
    }
    occs.into_boxed_slice()
}

fn compile_join_steps(
    anchor: usize,
    heads: &[HeadPat],
    preds: &[PredDecl],
    pats: &PatArena,
) -> SmallVec<[JoinStep; 4]> {
    let mut bound = HashSet::new();
    collect_head_rvars(&heads[anchor], pats, &mut bound);

    let mut remaining: Vec<usize> = (0..heads.len()).filter(|i| *i != anchor).collect();
    let mut steps: SmallVec<[JoinStep; 4]> = SmallVec::new();

    while !remaining.is_empty() {
        let mut best_idx = None;
        let mut best_score = i32::MAX;
        let mut best_probe = ProbeKind::ScanAll;
        let mut best_key = KeyMode::None;

        for &head_idx in remaining.iter() {
            let head = &heads[head_idx];
            let pred_decl = &preds[head.pred.0 as usize];
            let (score, probe, key) = best_probe_for_head(head, pred_decl, pats, &bound);
            if score < best_score
                || (score == best_score
                    && match best_idx {
                        None => true,
                        Some(b) => head_idx < b,
                    })
            {
                best_score = score;
                best_idx = Some(head_idx);
                best_probe = probe;
                best_key = key;
            }
        }

        let head_idx = best_idx.expect("remaining not empty");
        let head = &heads[head_idx];
        steps.push(JoinStep {
            head: head_idx as u8,
            pred: head.pred,
            probe: best_probe,
            key_mode: best_key,
        });

        collect_head_rvars(head, pats, &mut bound);
        remaining.retain(|i| *i != head_idx);
    }

    steps
}

fn collect_head_rvars(head: &HeadPat, pats: &PatArena, out: &mut HashSet<u32>) {
    for arg in head.args.iter() {
        collect_pat_rvars(*arg, pats, out);
    }
}

fn collect_pat_rvars(p: PatId, pats: &PatArena, out: &mut HashSet<u32>) {
    match pats.get(p) {
        PatNode::RVar(rv) => {
            out.insert(rv.0);
        }
        PatNode::App { kids, .. } => {
            for kid in kids.iter() {
                collect_pat_rvars(*kid, pats, out);
            }
        }
    }
}

fn head_arg_rvar(head: &HeadPat, pats: &PatArena, pos: usize) -> Option<RVar> {
    head.args.get(pos).and_then(|p| match pats.get(*p) {
        PatNode::RVar(rv) => Some(*rv),
        _ => None,
    })
}

fn head_arg_functor(head: &HeadPat, pats: &PatArena, pos: usize) -> Option<FuncId> {
    head.args.get(pos).and_then(|p| match pats.get(*p) {
        PatNode::App { f, .. } => Some(*f),
        _ => None,
    })
}

fn best_probe_for_head(
    head: &HeadPat,
    pred_decl: &PredDecl,
    pats: &PatArena,
    bound: &HashSet<u32>,
) -> (i32, ProbeKind, KeyMode) {
    let mut best_score = 3;
    let mut best_probe = ProbeKind::ScanAll;
    let mut best_key = KeyMode::None;

    for (i, spec) in pred_decl.index_specs.iter().enumerate() {
        match spec {
            IndexSpec::ArgPairTerm(a, b) => {
                let ra = head_arg_rvar(head, pats, *a as usize);
                let rb = head_arg_rvar(head, pats, *b as usize);
                if let (Some(ra), Some(rb)) = (ra, rb) {
                    if bound.contains(&ra.0) && bound.contains(&rb.0) && 0 < best_score {
                        best_score = 0;
                        best_probe = ProbeKind::Index(i as u8);
                        best_key = KeyMode::PairRVar(ra.0, rb.0);
                    }
                }
            }
            IndexSpec::ArgTerm(pos) => {
                if let Some(rv) = head_arg_rvar(head, pats, *pos as usize) {
                    if bound.contains(&rv.0) && 1 < best_score {
                        best_score = 1;
                        best_probe = ProbeKind::Index(i as u8);
                        best_key = KeyMode::RVar(rv.0);
                    }
                }
            }
            IndexSpec::ArgTopFunctor(pos) => {
                if let Some(f) = head_arg_functor(head, pats, *pos as usize) {
                    if 2 < best_score {
                        best_score = 2;
                        best_probe = ProbeKind::Index(i as u8);
                        best_key = KeyMode::FunctorConst(f);
                    }
                }
            }
            IndexSpec::PredOnly => {}
        }
    }

    (best_score, best_probe, best_key)
}

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub enum TokenKey {
    Small(SmallVec<[Cid; 4]>),
    Large(SmallVec<[Cid; 8]>),
}

impl TokenKey {
    fn from_cids(mut cids: Vec<Cid>) -> Self {
        cids.sort();
        if cids.len() <= 4 {
            TokenKey::Small(cids.into_iter().collect())
        } else {
            TokenKey::Large(cids.into_iter().collect())
        }
    }
}

#[derive(Clone, Debug)]
pub struct TokenStore {
    pub fired: Vec<HashSet<TokenKey>>,
}

impl TokenStore {
    fn new(n_rules: usize) -> Self {
        Self {
            fired: (0..n_rules).map(|_| HashSet::new()).collect(),
        }
    }
}

pub struct ChrState<T: Theory> {
    pub store: ChrStore,
    pub builtins: T::Store,
    pub tokens: TokenStore,
    pub next_cid: u32,
    pub agenda: VecDeque<Cid>,
    pub program: Arc<ChrProgram<T>>,
    failed: bool,
}

impl<T: Theory> Clone for ChrState<T> {
    fn clone(&self) -> Self {
        Self {
            store: self.store.clone(),
            builtins: self.builtins.clone(),
            tokens: self.tokens.clone(),
            next_cid: self.next_cid,
            agenda: self.agenda.clone(),
            program: self.program.clone(),
            failed: self.failed,
        }
    }
}

impl<T: Theory> ChrState<T> {
    pub fn new(program: Arc<ChrProgram<T>>, builtins: T::Store) -> Self {
        let n_rules = program.rules.len();
        Self {
            store: ChrStore::new(&program.preds),
            builtins,
            tokens: TokenStore::new(n_rules),
            next_cid: 0,
            agenda: VecDeque::new(),
            program,
            failed: false,
        }
    }

    pub fn introduce(&mut self, pred: PredId, args: &[TermId], terms: &TermStore) -> Cid {
        let cid = Cid(self.next_cid);
        self.next_cid = self.next_cid.saturating_add(1);
        let specs = &self.program.preds[pred.0 as usize].index_specs;
        self.store.add_chr(cid, pred, args, terms, specs);
        self.agenda.push_back(cid);
        cid
    }

    pub fn solve_to_fixpoint(&mut self, terms: &mut TermStore) -> bool {
        if self.failed {
            return false;
        }
        self.store.rebuild_indexes(&self.program.preds, terms);
        while let Some(cid) = self.agenda.pop_front() {
            if !self.is_alive(cid) {
                continue;
            }
            let pred = self.store.inst[cid.0 as usize].pred;
            let triggers = &self.program.triggers[pred.0 as usize];
            for occ_ref in triggers.iter() {
                if let Some(tuple) = self.find_match_by_ids(occ_ref.rid, occ_ref.occ, cid, terms) {
                    if !self.apply_rule_by_id(occ_ref.rid, &tuple, terms) {
                        self.failed = true;
                        return false;
                    }
                    break;
                }
            }
        }
        !self.failed
    }

    fn find_match(
        &self,
        rule: &Rule<T>,
        occ: &Occurrence,
        active: Cid,
        terms: &TermStore,
    ) -> Option<Vec<Cid>> {
        let mut env = RVarEnv::new(rule.n_rvars);
        let mut chosen: Vec<Option<Cid>> = vec![None; rule.heads.len()];
        env.reset();
        let anchor_head = &rule.heads[occ.anchor_head as usize];
        let inst = &self.store.inst[active.0 as usize];
        if !match_head(&self.program.pats, terms, anchor_head, inst, &mut env) {
            return None;
        }
        chosen[occ.anchor_head as usize] = Some(active);
        self.search_steps(rule, occ, 0, &mut env, &mut chosen, terms)
    }

    fn find_match_by_ids(
        &self,
        rid: RuleId,
        occ_idx: u16,
        active: Cid,
        terms: &TermStore,
    ) -> Option<Vec<Cid>> {
        let rule = &self.program.rules[rid.0 as usize];
        let occ = &rule.occs[occ_idx as usize];
        self.find_match(rule, occ, active, terms)
    }

    fn search_steps(
        &self,
        rule: &Rule<T>,
        occ: &Occurrence,
        step_idx: usize,
        env: &mut RVarEnv,
        chosen: &mut Vec<Option<Cid>>,
        terms: &TermStore,
    ) -> Option<Vec<Cid>> {
        if step_idx == occ.steps.len() {
            if !rule.guard.eval(
                &self.program.pats,
                terms,
                &self.builtins,
                &self.program.builtins,
                env,
            ) {
                return None;
            }
            let tuple: Vec<Cid> = chosen.iter().map(|c| c.expect("head cid")).collect();
            if rule.is_propagation {
                let token = TokenKey::from_cids(tuple.clone());
                if self.tokens.fired[rule.rid.0 as usize].contains(&token) {
                    return None;
                }
            }
            return Some(tuple);
        }

        let step = &occ.steps[step_idx];
        let cands = self.candidates_for_step(step, env);
        for &cid in cands.iter() {
            if !self.is_alive(cid) || chosen.iter().any(|c| c == &Some(cid)) {
                continue;
            }
            let trail = env.trail_len();
            let head = &rule.heads[step.head as usize];
            let inst = &self.store.inst[cid.0 as usize];
            if match_head(&self.program.pats, terms, head, inst, env) {
                chosen[step.head as usize] = Some(cid);
                if let Some(tuple) = self.search_steps(rule, occ, step_idx + 1, env, chosen, terms)
                {
                    return Some(tuple);
                }
                chosen[step.head as usize] = None;
            }
            env.unwind(trail);
        }
        None
    }

    fn candidates_for_step<'a>(&'a self, step: &JoinStep, env: &RVarEnv) -> &'a [Cid] {
        static EMPTY: [Cid; 0] = [];
        let pred_store = &self.store.preds[step.pred.0 as usize];
        match step.probe {
            ProbeKind::ScanAll => pred_store.all.as_slice(),
            ProbeKind::Index(idx) => {
                let idx_usize = idx as usize;
                if idx_usize >= pred_store.indexes.len() {
                    return &EMPTY;
                }
                match (&pred_store.indexes[idx_usize], step.key_mode) {
                    (IndexData::ArgTerm(map), KeyMode::RVar(v)) => {
                        if let Some(t) = env.get(RVar(v)) {
                            map.get(&t).map(|v| v.as_slice()).unwrap_or(&EMPTY)
                        } else {
                            &EMPTY
                        }
                    }
                    (IndexData::ArgTopFunctor(map), KeyMode::FunctorConst(f)) => {
                        map.get(&f).map(|v| v.as_slice()).unwrap_or(&EMPTY)
                    }
                    (IndexData::ArgPairTerm(map), KeyMode::PairRVar(a, b)) => {
                        if let (Some(ta), Some(tb)) = (env.get(RVar(a)), env.get(RVar(b))) {
                            map.get(&(ta, tb)).map(|v| v.as_slice()).unwrap_or(&EMPTY)
                        } else {
                            &EMPTY
                        }
                    }
                    _ => &EMPTY,
                }
            }
        }
    }

    fn apply_rule_by_id(&mut self, rid: RuleId, tuple: &[Cid], terms: &mut TermStore) -> bool {
        let (removed_mask, is_propagation, n_rvars, heads, body, pats, builtins) = {
            let rule = &self.program.rules[rid.0 as usize];
            (
                rule.removed_mask,
                rule.is_propagation,
                rule.n_rvars,
                rule.heads.clone(),
                rule.body.clone(),
                self.program.pats.clone(),
                self.program.builtins.clone(),
            )
        };

        if is_propagation {
            let token = TokenKey::from_cids(tuple.to_vec());
            self.tokens.fired[rid.0 as usize].insert(token);
        }

        for (i, cid) in tuple.iter().copied().enumerate() {
            if (removed_mask & (1u64 << i)) != 0 {
                self.store.mark_dead(cid);
            }
        }

        let mut env = RVarEnv::new(n_rvars);
        env.reset();
        for (i, cid) in tuple.iter().copied().enumerate() {
            let head = &heads[i];
            let inst = &self.store.inst[cid.0 as usize];
            if !match_head(&pats, terms, head, inst, &mut env) {
                return false;
            }
        }

        body.exec(&pats, terms, &builtins, &env, self)
    }

    fn is_alive(&self, cid: Cid) -> bool {
        matches!(
            self.store.inst.get(cid.0 as usize),
            Some(inst) if inst.alive
        )
    }

    fn apply_subst_to_store(&mut self, subst: &Subst, terms: &mut TermStore) {
        for inst in self.store.inst.iter_mut() {
            if inst.alive {
                for arg in inst.args.iter_mut() {
                    *arg = apply_subst(*arg, subst, terms);
                }
            }
        }
        self.builtins = T::apply_subst(&self.builtins, subst, terms);
    }

    fn enqueue_all_alive(&mut self) {
        self.agenda.clear();
        for (idx, inst) in self.store.inst.iter().enumerate() {
            if inst.alive {
                self.agenda.push_back(Cid(idx as u32));
            }
        }
    }
}

fn match_head(
    pats: &PatArena,
    terms: &TermStore,
    head: &HeadPat,
    inst: &CInstance,
    env: &mut RVarEnv,
) -> bool {
    if head.pred != inst.pred {
        return false;
    }
    if head.args.len() != inst.args.len() {
        return false;
    }
    for (pat, term) in head.args.iter().zip(inst.args.iter()) {
        if !match_pat_bind(pats, terms, *pat, *term, env) {
            return false;
        }
    }
    true
}

static NEXT_PROGRAM_ID: AtomicU64 = AtomicU64::new(1);

// ---------- Snapshot freeze/thaw ----------

struct ByteWriter {
    buf: Vec<u8>,
}

impl ByteWriter {
    fn new() -> Self {
        Self { buf: Vec::new() }
    }

    fn push_u32(&mut self, x: u32) {
        self.buf.extend_from_slice(&x.to_le_bytes());
    }

    fn push_bytes(&mut self, bs: &[u8]) {
        self.buf.extend_from_slice(bs);
    }

    fn into_vec(self) -> Vec<u8> {
        self.buf
    }
}

struct ByteReader<'a> {
    bs: &'a [u8],
    i: usize,
}

impl<'a> ByteReader<'a> {
    fn new(bs: &'a [u8]) -> Self {
        Self { bs, i: 0 }
    }

    fn read_u32(&mut self) -> Option<u32> {
        if self.i + 4 > self.bs.len() {
            return None;
        }
        let mut arr = [0u8; 4];
        arr.copy_from_slice(&self.bs[self.i..self.i + 4]);
        self.i += 4;
        Some(u32::from_le_bytes(arr))
    }

    fn read_bytes(&mut self, n: usize) -> Option<&'a [u8]> {
        if self.i + n > self.bs.len() {
            return None;
        }
        let s = &self.bs[self.i..self.i + n];
        self.i += n;
        Some(s)
    }
}

#[derive(Clone, Debug)]
struct AliveRec {
    pred: PredId,
    args: SmallVec<[TermId; 4]>,
    old_cid: u32,
}

impl PartialEq for AliveRec {
    fn eq(&self, other: &Self) -> bool {
        self.pred == other.pred
            && self.args.as_slice() == other.args.as_slice()
            && self.old_cid == other.old_cid
    }
}

impl Eq for AliveRec {}

impl Ord for AliveRec {
    fn cmp(&self, other: &Self) -> Ordering {
        match self.pred.cmp(&other.pred) {
            Ordering::Equal => match self.args.as_slice().cmp(other.args.as_slice()) {
                Ordering::Equal => self.old_cid.cmp(&other.old_cid),
                x => x,
            },
            x => x,
        }
    }
}

impl PartialOrd for AliveRec {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

pub fn freeze_chr<T: Theory>(st: &ChrState<T>) -> Vec<u8> {
    let mut alive: Vec<AliveRec> = Vec::new();
    for (i, inst) in st.store.inst.iter().enumerate() {
        if inst.alive {
            alive.push(AliveRec {
                pred: inst.pred,
                args: inst.args.clone(),
                old_cid: i as u32,
            });
        }
    }

    alive.sort();

    let mut remap: Vec<u32> = vec![u32::MAX; st.store.inst.len()];
    for (new_cid, rec) in alive.iter().enumerate() {
        remap[rec.old_cid as usize] = new_cid as u32;
    }

    let mut w = ByteWriter::new();
    w.push_u32(alive.len() as u32);
    for rec in alive.iter() {
        w.push_u32(rec.pred.0);
        w.push_u32(rec.args.len() as u32);
        for a in rec.args.iter() {
            w.push_u32(a.raw());
        }
    }

    let b = T::freeze_store(&st.builtins);
    w.push_u32(b.len() as u32);
    w.push_bytes(&b);

    let mut token_rules: Vec<(u32, Vec<TokenKey>)> = Vec::new();
    for (rid, set) in st.tokens.fired.iter().enumerate() {
        if !st.program.rules[rid].is_propagation {
            continue;
        }
        if set.is_empty() {
            continue;
        }
        let mut toks: Vec<TokenKey> = Vec::new();
        'tok: for t in set.iter() {
            let mut cids: Vec<Cid> = Vec::new();
            for Cid(old) in token_cids(t).iter().copied() {
                let m = *remap.get(old as usize).unwrap_or(&u32::MAX);
                if m == u32::MAX {
                    continue 'tok;
                }
                cids.push(Cid(m));
            }
            toks.push(TokenKey::from_cids(cids));
        }
        toks.sort_by_key(format_token);
        toks.dedup();
        if !toks.is_empty() {
            token_rules.push((rid as u32, toks));
        }
    }
    token_rules.sort_by_key(|(rid, _)| *rid);

    w.push_u32(token_rules.len() as u32);
    for (rid, toks) in token_rules.iter() {
        w.push_u32(*rid);
        w.push_u32(toks.len() as u32);
        for t in toks.iter() {
            let cids = token_cids(t);
            w.push_u32(cids.len() as u32);
            for cid in cids {
                w.push_u32(cid.0);
            }
        }
    }

    w.into_vec()
}

fn token_cids(token: &TokenKey) -> &[Cid] {
    match token {
        TokenKey::Small(sv) => sv.as_slice(),
        TokenKey::Large(sv) => sv.as_slice(),
    }
}

fn format_token(token: &TokenKey) -> Vec<u32> {
    token_cids(token).iter().map(|c| c.0).collect()
}

pub fn thaw_chr<T: Theory>(
    program: Arc<ChrProgram<T>>,
    bytes: &[u8],
    terms: &TermStore,
) -> Option<ChrState<T>> {
    let mut r = ByteReader::new(bytes);
    let n_constraints = r.read_u32()? as usize;
    let mut st = ChrState::<T>::new(program.clone(), T::thaw_store(&[]));
    st.store = ChrStore::new(&program.preds);

    for _ in 0..n_constraints {
        let pred = PredId(r.read_u32()?);
        let arity = r.read_u32()? as usize;
        let mut args: Vec<TermId> = Vec::with_capacity(arity);
        for _ in 0..arity {
            args.push(TermId::from_raw(r.read_u32()?));
        }
        st.introduce(pred, &args, terms);
    }

    let b_len = r.read_u32()? as usize;
    let b_bytes = r.read_bytes(b_len)?;
    st.builtins = T::thaw_store(b_bytes);

    let n_token_rules = r.read_u32()? as usize;
    st.tokens = TokenStore::new(program.rules.len());
    for _ in 0..n_token_rules {
        let rid = r.read_u32()? as usize;
        let n_tokens = r.read_u32()? as usize;
        let set = st.tokens.fired.get_mut(rid)?;
        for _ in 0..n_tokens {
            let k = r.read_u32()? as usize;
            let mut sv: SmallVec<[Cid; 8]> = SmallVec::new();
            for _ in 0..k {
                sv.push(Cid(r.read_u32()?));
            }
            set.insert(TokenKey::from_cids(sv.into_vec()));
        }
    }

    st.agenda.clear();
    Some(st)
}

impl<T: Theory> ChrProgram<T> {
    pub fn pred_id(&self, name: &str) -> Option<PredId> {
        self.pred_names.get(name).copied()
    }

    pub fn pred_name(&self, pred: PredId) -> Option<&str> {
        self.preds
            .get(pred.0 as usize)
            .map(|decl| decl.name.as_str())
    }

    pub fn pred_arity(&self, pred: PredId) -> Option<u8> {
        self.preds.get(pred.0 as usize).map(|decl| decl.arity)
    }

    pub fn empty() -> Arc<Self> {
        Arc::new(ChrProgram {
            preds: Box::new([]),
            rules: Box::new([]),
            triggers: Vec::new(),
            pats: PatArena::new(),
            builtins: BuiltinRegistry::default(),
            pred_names: HashMap::new(),
            program_id: NEXT_PROGRAM_ID.fetch_add(1, AtomicOrdering::Relaxed),
        })
    }
}

impl<T: Theory> Default for ChrState<T> {
    fn default() -> Self {
        ChrState::new(ChrProgram::empty(), T::Store::default())
    }
}

impl<T: Theory> PartialEq for ChrState<T> {
    fn eq(&self, other: &Self) -> bool {
        if self.program.program_id != other.program.program_id {
            return false;
        }
        freeze_chr(self) == freeze_chr(other)
    }
}

impl<T: Theory> Eq for ChrState<T> {}

impl<T: Theory> Hash for ChrState<T> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.program.program_id.hash(state);
        freeze_chr(self).hash(state);
    }
}

impl<T: Theory> crate::constraint::ConstraintOps for ChrState<T> {
    fn combine(&self, other: &Self) -> Option<Self> {
        if self.failed || other.failed {
            return None;
        }
        if self.program.program_id != other.program.program_id {
            let self_empty = self.is_empty();
            let other_empty = other.is_empty();
            if self_empty && other_empty {
                return Some(if self.program.program_id <= other.program.program_id {
                    self.clone()
                } else {
                    other.clone()
                });
            }
            if self_empty {
                return Some(other.clone());
            }
            if other_empty {
                return Some(self.clone());
            }
            return None;
        }
        let builtins = T::merge_store(&self.builtins, &other.builtins)?;
        let mut merged = self.clone();
        merged.builtins = builtins;
        merged.agenda.clear();

        let mut remap: Vec<Option<Cid>> = vec![None; other.store.inst.len()];
        for (idx, inst) in other.store.inst.iter().enumerate() {
            if !inst.alive {
                continue;
            }
            let cid = Cid(merged.next_cid);
            merged.next_cid = merged.next_cid.saturating_add(1);
            merged.store.inst.push(CInstance {
                cid,
                pred: inst.pred,
                args: inst.args.clone(),
                alive: true,
            });
            remap[idx] = Some(cid);
            merged.store.alive_count += 1;
        }

        for (rid, set) in other.tokens.fired.iter().enumerate() {
            if !other.program.rules[rid].is_propagation {
                continue;
            }
            for token in set.iter() {
                let mut cids = Vec::new();
                let mut ok = true;
                for cid in token_cids(token).iter().copied() {
                    let mapped = remap.get(cid.0 as usize).and_then(|c| *c);
                    if let Some(ncid) = mapped {
                        cids.push(ncid);
                    } else {
                        ok = false;
                        break;
                    }
                }
                if ok {
                    let new_token = TokenKey::from_cids(cids);
                    merged.tokens.fired[rid].insert(new_token);
                }
            }
        }

        Some(merged)
    }

    fn normalize(&self, terms: &mut TermStore) -> Option<(Self, Option<Subst>)> {
        if self.failed {
            return None;
        }
        let mut st = self.clone();
        st.store.rebuild_indexes(&st.program.preds, terms);
        st.enqueue_all_alive();
        if !st.solve_to_fixpoint(terms) {
            return None;
        }

        let subst = T::extract_subst(&st.builtins);
        let subst_opt = if subst.is_empty() {
            None
        } else {
            Some(subst.clone())
        };
        if !subst.is_empty() {
            st.apply_subst_to_store(&subst, terms);
            st.store.rebuild_indexes(&st.program.preds, terms);
        }
        st.agenda.clear();
        Some((st, subst_opt))
    }

    fn apply_subst(&self, subst: &Subst, terms: &mut TermStore) -> Self {
        let mut st = self.clone();
        if !subst.is_empty() {
            st.apply_subst_to_store(subst, terms);
        }
        st
    }

    fn remap_vars(&self, map: &[Option<u32>], terms: &mut TermStore) -> Self {
        let mut st = self.clone();
        for inst in st.store.inst.iter_mut() {
            if inst.alive {
                for arg in inst.args.iter_mut() {
                    *arg = apply_var_renaming(*arg, map, terms);
                }
            }
        }
        st.builtins = T::remap_vars(&st.builtins, map, terms);
        st.store.rebuild_indexes(&st.program.preds, terms);
        st.agenda.clear();
        st
    }

    fn collect_vars(&self, terms: &TermStore, out: &mut Vec<u32>) {
        for inst in self.store.inst.iter() {
            if inst.alive {
                for arg in inst.args.iter().copied() {
                    out.extend(crate::nf::collect_vars_ordered(arg, terms));
                }
            }
        }
        T::collect_vars(&self.builtins, terms, out);
    }

    fn is_empty(&self) -> bool {
        self.store.alive_count == 0 && T::is_empty(&self.builtins)
    }

    fn is_satisfiable(&self) -> bool {
        !self.failed
    }
}

impl<T: Theory> ConstraintDisplay for ChrState<T> {
    fn fmt_constraints(
        &self,
        terms: &mut TermStore,
        symbols: &crate::symbol::SymbolStore,
    ) -> Result<Option<String>, String> {
        if self.store.alive_count == 0 {
            return Ok(None);
        }

        let mut parts = Vec::new();
        for inst in self.store.inst.iter().filter(|c| c.alive) {
            let pred_name = self.program.pred_name(inst.pred).unwrap_or("unknown");
            if inst.args.is_empty() {
                parts.push(pred_name.to_string());
            } else {
                let mut s = String::new();
                s.push('(');
                s.push_str(pred_name);
                for arg in inst.args.iter().copied() {
                    let arg_str = crate::term::format_term(arg, terms, symbols)?;
                    s.push(' ');
                    s.push_str(&arg_str);
                }
                s.push(')');
                parts.push(s);
            }
        }

        if parts.is_empty() {
            Ok(None)
        } else {
            Ok(Some(parts.join(", ")))
        }
    }
}

#[cfg(test)]
#[path = "../tests/chr.rs"]
mod tests;
