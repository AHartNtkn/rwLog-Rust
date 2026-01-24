// ===== src/chr/mod.rs =====
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
mod tests;


// ===== src/constraint.rs =====
use std::hash::Hash;

use crate::nf::apply_var_renaming;
use crate::subst::Subst;
use crate::symbol::SymbolStore;
use crate::term::{Term, TermStore};

/// Trait for constraint systems that can be combined with NFs.
///
/// Constraints represent additional conditions that must be satisfied
/// beyond the structural matching of terms. Examples include:
/// - Disequality constraints (X != Y)
/// - Type constraints (X : Int)
/// - Arithmetic constraints (X > 0)
///
/// The Unit constraint (implemented by `()`) represents no constraints,
/// which is useful for pure structural rewriting.
pub trait ConstraintOps: Clone + Eq + Hash + Default + Send + Sync {
    /// Combine two constraints (conjunction).
    ///
    /// Returns None if the constraints are inconsistent.
    fn combine(&self, other: &Self) -> Option<Self>;

    /// Normalize the constraint, potentially producing substitutions.
    ///
    /// Returns the simplified constraint and any substitutions that
    /// were derived from the constraint.
    fn normalize(&self, terms: &mut TermStore) -> Option<(Self, Option<Subst>)>;

    /// Apply a substitution to the constraint.
    fn apply_subst(&self, subst: &Subst, terms: &mut TermStore) -> Self;

    /// Remap variable indices according to a renaming map.
    fn remap_vars(&self, map: &[Option<u32>], terms: &mut TermStore) -> Self;

    /// Collect variable indices referenced by this constraint.
    fn collect_vars(&self, _terms: &TermStore, _out: &mut Vec<u32>) {}

    /// Check if this is the trivial (empty) constraint.
    fn is_empty(&self) -> bool;

    /// Check if this constraint is satisfiable.
    fn is_satisfiable(&self) -> bool;
}

pub trait ConstraintDisplay {
    fn fmt_constraints(
        &self,
        _terms: &mut TermStore,
        _symbols: &SymbolStore,
    ) -> Result<Option<String>, String> {
        Ok(None)
    }
}

/// Unit constraint - represents no constraints.
///
/// This is the simplest constraint system where all constraints
/// are trivially satisfied. Useful for pure term rewriting without
/// additional constraint handling.
impl ConstraintOps for () {
    fn combine(&self, _other: &Self) -> Option<Self> {
        Some(())
    }

    fn normalize(&self, _terms: &mut TermStore) -> Option<(Self, Option<Subst>)> {
        Some(((), None))
    }

    fn apply_subst(&self, _subst: &Subst, _terms: &mut TermStore) -> Self {}

    fn remap_vars(&self, _map: &[Option<u32>], _terms: &mut TermStore) -> Self {}

    fn collect_vars(&self, _terms: &TermStore, _out: &mut Vec<u32>) {}

    fn is_empty(&self) -> bool {
        true
    }

    fn is_satisfiable(&self) -> bool {
        true
    }
}

impl ConstraintDisplay for () {}

/// A disequality constraint: X != t
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Disequality {
    /// Variable index.
    pub var: u32,
    /// Term ID that the variable must not equal.
    pub term: crate::term::TermId,
}

/// A set of disequality constraints.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Default)]
pub struct DiseqConstraint {
    /// List of disequalities.
    constraints: Vec<Disequality>,
}

impl DiseqConstraint {
    /// Create an empty disequality constraint.
    pub fn new() -> Self {
        Self {
            constraints: Vec::new(),
        }
    }

    /// Add a disequality: var != term.
    pub fn add(&mut self, var: u32, term: crate::term::TermId) {
        let diseq = Disequality { var, term };
        if !self.constraints.contains(&diseq) {
            self.constraints.push(diseq);
        }
    }

    /// Get the number of constraints.
    pub fn len(&self) -> usize {
        self.constraints.len()
    }

    /// Check if there are no constraints.
    pub fn is_empty(&self) -> bool {
        self.constraints.is_empty()
    }

    /// Iterator over disequalities.
    pub fn iter(&self) -> impl Iterator<Item = &Disequality> {
        self.constraints.iter()
    }
}

impl ConstraintOps for DiseqConstraint {
    fn combine(&self, other: &Self) -> Option<Self> {
        let mut result = self.clone();
        for diseq in &other.constraints {
            if !result.constraints.contains(diseq) {
                result.constraints.push(diseq.clone());
            }
        }
        Some(result)
    }

    fn normalize(&self, _terms: &mut TermStore) -> Option<(Self, Option<Subst>)> {
        if !self.is_satisfiable() {
            return None;
        }
        Some((self.clone(), None))
    }

    fn apply_subst(&self, subst: &Subst, terms: &mut TermStore) -> Self {
        let mut out = self.clone();
        for diseq in out.constraints.iter_mut() {
            if let Some(bound) = subst.get(diseq.var) {
                if let Some(Term::Var(new_var)) = terms.resolve(bound) {
                    diseq.var = new_var;
                }
            }
            diseq.term = crate::subst::apply_subst(diseq.term, subst, terms);
        }
        out
    }

    fn remap_vars(&self, map: &[Option<u32>], terms: &mut TermStore) -> Self {
        let mut out = self.clone();
        for diseq in out.constraints.iter_mut() {
            if (diseq.var as usize) < map.len() {
                if let Some(new_var) = map[diseq.var as usize] {
                    diseq.var = new_var;
                }
            }
            diseq.term = apply_var_renaming(diseq.term, map, terms);
        }
        out
    }

    fn collect_vars(&self, terms: &TermStore, out: &mut Vec<u32>) {
        for diseq in self.constraints.iter() {
            out.push(diseq.var);
            out.extend(crate::nf::collect_vars_ordered(diseq.term, terms));
        }
    }

    fn is_empty(&self) -> bool {
        self.constraints.is_empty()
    }

    fn is_satisfiable(&self) -> bool {
        // Disequalities are always satisfiable unless we can prove otherwise
        // A more complete implementation would check for contradictions
        true
    }
}

impl ConstraintDisplay for DiseqConstraint {}

/// A type constraint: X : Type
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct TypeConstraint {
    /// Term to constrain.
    pub term: crate::term::TermId,
    /// Type identifier.
    pub type_id: u32,
}

/// A set of type constraints.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Default)]
pub struct TypeConstraints {
    /// List of type constraints.
    constraints: Vec<TypeConstraint>,
}

impl TypeConstraints {
    /// Create empty type constraints.
    pub fn new() -> Self {
        Self {
            constraints: Vec::new(),
        }
    }

    /// Add a type constraint: term : type_id.
    pub fn add(&mut self, term: crate::term::TermId, type_id: u32) {
        let tc = TypeConstraint { term, type_id };
        // Check for conflicting type constraint
        for existing in &self.constraints {
            if existing.term == term && existing.type_id != type_id {
                // Conflicting types - this would make it unsatisfiable
                // For now, we just don't add duplicates
                return;
            }
        }
        if !self.constraints.contains(&tc) {
            self.constraints.push(tc);
        }
    }

    /// Get the type constraint for a variable.
    pub fn get_type(&self, term: crate::term::TermId) -> Option<u32> {
        self.constraints
            .iter()
            .find(|tc| tc.term == term)
            .map(|tc| tc.type_id)
    }

    /// Get the number of constraints.
    pub fn len(&self) -> usize {
        self.constraints.len()
    }

    /// Check if there are no constraints.
    pub fn is_empty(&self) -> bool {
        self.constraints.is_empty()
    }
}

impl ConstraintOps for TypeConstraints {
    fn combine(&self, other: &Self) -> Option<Self> {
        let mut result = self.clone();
        for tc in &other.constraints {
            // Check for conflicting types
            if let Some(existing_type) = result.get_type(tc.term) {
                if existing_type != tc.type_id {
                    return None; // Inconsistent types
                }
            } else {
                result.constraints.push(tc.clone());
            }
        }
        Some(result)
    }

    fn normalize(&self, _terms: &mut TermStore) -> Option<(Self, Option<Subst>)> {
        if !self.is_satisfiable() {
            return None;
        }
        let mut out = self.clone();
        out.constraints
            .sort_by(|a, b| (a.term, a.type_id).cmp(&(b.term, b.type_id)));
        out.constraints
            .dedup_by(|a, b| a.term == b.term && a.type_id == b.type_id);
        Some((out, None))
    }

    fn apply_subst(&self, subst: &Subst, terms: &mut TermStore) -> Self {
        let mut out = self.clone();
        for tc in out.constraints.iter_mut() {
            tc.term = crate::subst::apply_subst(tc.term, subst, terms);
        }
        out
    }

    fn remap_vars(&self, map: &[Option<u32>], terms: &mut TermStore) -> Self {
        let mut out = self.clone();
        for tc in out.constraints.iter_mut() {
            tc.term = apply_var_renaming(tc.term, map, terms);
        }
        out.constraints
            .sort_by(|a, b| (a.term, a.type_id).cmp(&(b.term, b.type_id)));
        out.constraints
            .dedup_by(|a, b| a.term == b.term && a.type_id == b.type_id);
        out
    }

    fn collect_vars(&self, terms: &TermStore, out: &mut Vec<u32>) {
        for tc in self.constraints.iter() {
            out.extend(crate::nf::collect_vars_ordered(tc.term, terms));
        }
    }

    fn is_empty(&self) -> bool {
        self.constraints.is_empty()
    }

    fn is_satisfiable(&self) -> bool {
        // Check for conflicting type constraints on the same variable
        for (i, tc1) in self.constraints.iter().enumerate() {
            for tc2 in self.constraints.iter().skip(i + 1) {
                if tc1.term == tc2.term && tc1.type_id != tc2.type_id {
                    return false;
                }
            }
        }
        true
    }
}

impl ConstraintDisplay for TypeConstraints {}

/// Combined constraint holding both disequalities and types.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Default)]
pub struct CombinedConstraint {
    /// Disequality constraints.
    pub diseqs: DiseqConstraint,
    /// Type constraints.
    pub types: TypeConstraints,
}

impl CombinedConstraint {
    /// Create empty combined constraint.
    pub fn new() -> Self {
        Self {
            diseqs: DiseqConstraint::new(),
            types: TypeConstraints::new(),
        }
    }

    /// Add a disequality constraint.
    pub fn add_diseq(&mut self, var: u32, term: crate::term::TermId) {
        self.diseqs.add(var, term);
    }

    /// Add a type constraint.
    pub fn add_type(&mut self, term: crate::term::TermId, type_id: u32) {
        self.types.add(term, type_id);
    }
}

impl ConstraintOps for CombinedConstraint {
    fn combine(&self, other: &Self) -> Option<Self> {
        let diseqs = self.diseqs.combine(&other.diseqs)?;
        let types = self.types.combine(&other.types)?;
        Some(Self { diseqs, types })
    }

    fn normalize(&self, terms: &mut TermStore) -> Option<(Self, Option<Subst>)> {
        let (diseqs, _) = self.diseqs.normalize(terms)?;
        let (types, _) = self.types.normalize(terms)?;
        Some((Self { diseqs, types }, None))
    }

    fn apply_subst(&self, subst: &Subst, terms: &mut TermStore) -> Self {
        Self {
            diseqs: self.diseqs.apply_subst(subst, terms),
            types: self.types.apply_subst(subst, terms),
        }
    }

    fn remap_vars(&self, map: &[Option<u32>], terms: &mut TermStore) -> Self {
        Self {
            diseqs: self.diseqs.remap_vars(map, terms),
            types: self.types.remap_vars(map, terms),
        }
    }

    fn collect_vars(&self, terms: &TermStore, out: &mut Vec<u32>) {
        self.diseqs.collect_vars(terms, out);
        self.types.collect_vars(terms, out);
    }

    fn is_empty(&self) -> bool {
        self.diseqs.is_empty() && self.types.is_empty()
    }

    fn is_satisfiable(&self) -> bool {
        self.diseqs.is_satisfiable() && self.types.is_satisfiable()
    }
}

impl ConstraintDisplay for CombinedConstraint {}


#[cfg(test)]
mod tests;


// ===== src/drop_fresh.rs =====
use smallvec::SmallVec;

/// A DropFresh represents a monotone partial injection between two arities.
///
/// Semantically: Start with `in_arity` values, the DropFresh specifies which
/// input positions map to which output positions. Positions not in the
/// mapping are "dropped" (inputs) or "fresh" (outputs).
///
/// The map is a list of (input_pos, output_pos) pairs that must be:
/// - Strictly increasing in both coordinates
/// - All input positions < in_arity
/// - All output positions < out_arity
///
/// Example: DropFresh { in: 3, out: 2, map: [(0,0), (2,1)] }
/// - Input 0 maps to output 0
/// - Input 1 is dropped
/// - Input 2 maps to output 1
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct DropFresh<C> {
    /// Number of input positions.
    pub in_arity: u32,
    /// Number of output positions.
    pub out_arity: u32,
    /// Monotone partial injection: (input_pos, output_pos) pairs.
    /// Must be strictly increasing in both coordinates.
    pub map: SmallVec<[(u32, u32); 4]>,
    /// Associated constraint.
    pub constraint: C,
}

impl<C: Default> DropFresh<C> {
    /// Create an identity DropFresh of the given arity.
    /// Maps position i to position i for all i in 0..arity.
    pub fn identity(arity: u32) -> Self {
        let map: SmallVec<[(u32, u32); 4]> = (0..arity).map(|i| (i, i)).collect();
        Self {
            in_arity: arity,
            out_arity: arity,
            map,
            constraint: C::default(),
        }
    }
}

impl<C> DropFresh<C> {
    /// Create an identity DropFresh of the given arity with a specific constraint.
    /// Maps position i to position i for all i in 0..arity.
    pub fn identity_with_constraint(arity: u32, constraint: C) -> Self {
        let map: SmallVec<[(u32, u32); 4]> = (0..arity).map(|i| (i, i)).collect();
        Self {
            in_arity: arity,
            out_arity: arity,
            map,
            constraint,
        }
    }
}

impl<C: Clone> DropFresh<C> {
    /// Create a new DropFresh with validation.
    /// Returns None if the mapping is not monotone or out of bounds.
    pub fn new(
        in_arity: u32,
        out_arity: u32,
        map: SmallVec<[(u32, u32); 4]>,
        constraint: C,
    ) -> Option<Self> {
        let drop_fresh = Self {
            in_arity,
            out_arity,
            map,
            constraint,
        };
        if drop_fresh.validate() {
            Some(drop_fresh)
        } else {
            None
        }
    }

    /// Create a DropFresh that drops all inputs and produces all fresh outputs.
    /// No inputs are connected to outputs.
    pub fn disconnect(in_arity: u32, out_arity: u32, constraint: C) -> Self {
        Self {
            in_arity,
            out_arity,
            map: SmallVec::new(),
            constraint,
        }
    }

    /// Compose two DropFresh values: self ; other.
    /// The output arity of self must match the input arity of other.
    /// Returns None if arities don't match.
    pub fn compose(&self, other: &DropFresh<C>) -> Option<DropFresh<C>>
    where
        C: Default,
    {
        if self.out_arity != other.in_arity {
            return None;
        }

        // Compose the mappings:
        // For each (in_a, mid) in self.map and (mid, out_b) in other.map
        // where mid matches, produce (in_a, out_b)
        let mut result_map = SmallVec::new();

        // Use merge-join since both maps are sorted by their output/input respectively
        let mut i = 0;
        let mut j = 0;

        while i < self.map.len() && j < other.map.len() {
            let (in_a, mid_a) = self.map[i];
            let (mid_b, out_b) = other.map[j];

            if mid_a < mid_b {
                // self's output not in other's input, skip
                i += 1;
            } else if mid_a > mid_b {
                // other's input not in self's output, skip
                j += 1;
            } else {
                // mid_a == mid_b: they connect
                result_map.push((in_a, out_b));
                i += 1;
                j += 1;
            }
        }

        Some(DropFresh {
            in_arity: self.in_arity,
            out_arity: other.out_arity,
            map: result_map,
            constraint: C::default(),
        })
    }

    /// Get the number of positions that are mapped (shared between in and out).
    pub fn shared_count(&self) -> usize {
        self.map.len()
    }

    /// Check if this is an identity DropFresh.
    pub fn is_identity(&self) -> bool {
        if self.in_arity != self.out_arity {
            return false;
        }
        if self.map.len() != self.in_arity as usize {
            return false;
        }
        // Check that each position maps to itself
        self.map
            .iter()
            .enumerate()
            .all(|(i, &(inp, out))| inp == i as u32 && out == i as u32)
    }

    /// Check if this DropFresh connects no positions.
    pub fn is_disconnect(&self) -> bool {
        self.map.is_empty()
    }

    /// Get the output position for a given input position, if mapped.
    pub fn forward(&self, input_pos: u32) -> Option<u32> {
        // Binary search since map is sorted by input position
        self.map
            .binary_search_by_key(&input_pos, |&(inp, _)| inp)
            .ok()
            .map(|idx| self.map[idx].1)
    }

    /// Get the input position for a given output position, if mapped.
    pub fn backward(&self, output_pos: u32) -> Option<u32> {
        // Linear search since map is sorted by input, not output
        // (Could optimize with a parallel sorted structure if needed)
        self.map
            .iter()
            .find(|&&(_, out)| out == output_pos)
            .map(|&(inp, _)| inp)
    }

    /// Validate that the DropFresh is well-formed.
    fn validate(&self) -> bool {
        // Empty map is always valid
        if self.map.is_empty() {
            return true;
        }

        // Check bounds and strict monotonicity
        let mut prev_in = None;
        let mut prev_out = None;

        for &(inp, out) in &self.map {
            // Check bounds
            if inp >= self.in_arity || out >= self.out_arity {
                return false;
            }

            // Check strictly increasing in input positions
            if let Some(p) = prev_in {
                if inp <= p {
                    return false;
                }
            }
            prev_in = Some(inp);

            // Check strictly increasing in output positions
            if let Some(p) = prev_out {
                if out <= p {
                    return false;
                }
            }
            prev_out = Some(out);
        }

        true
    }
}


#[cfg(test)]
mod tests;


// ===== src/engine.rs =====
//! Engine - Top-level evaluation loop for relational queries.
//!
//! The Engine orchestrates the search through a Rel tree by:
//! 1. Converting Rel to initial Node tree
//! 2. Stepping through the Node tree using Or rotation
//! 3. Yielding NF answers via next()

use crate::constraint::ConstraintDisplay;
use crate::constraint::ConstraintOps;
use crate::nf::{format_nf, NF};
use crate::node::{step_node, Node, NodeStep};
use crate::rel::Rel;
use crate::symbol::SymbolStore;
use crate::term::TermStore;
use crate::work::{rel_to_node, Env, Tables};
use std::collections::HashSet;

/// Result of a single step in the Engine.
#[derive(Clone, Debug)]
pub enum StepResult<C: ConstraintOps> {
    /// Produced an answer NF
    Emit(NF<C>),
    /// No more answers (exhausted)
    Exhausted,
    /// Internal rotation/restructuring happened, continue stepping
    Continue,
}

/// Evaluation engine for relational queries.
///
/// Converts a Rel expression into a stream of NF answers using
/// Or rotation interleaving and Work stepping.
pub struct Engine<C: ConstraintOps> {
    /// Root of the search tree
    root: Node<C>,
    /// Term store for creating/looking up terms
    terms: TermStore,
    /// Dedup set for emitted answers (set semantics).
    seen: HashSet<NF<C>>,
}

impl<C: ConstraintOps> Engine<C> {
    /// Create a new Engine from a Rel expression.
    pub fn new(rel: Rel<C>, terms: TermStore) -> Self {
        Self::new_with_env(rel, terms, Env::new())
    }

    /// Create a new Engine with an explicit environment.
    pub fn new_with_env(rel: Rel<C>, terms: TermStore, env: Env<C>) -> Self {
        let tables = Tables::new();
        let root = rel_to_node(&rel, &env, &tables);
        Self {
            root,
            terms,
            seen: HashSet::new(),
        }
    }

    pub fn format_nf(&mut self, nf: &NF<C>, symbols: &SymbolStore) -> Result<String, String>
    where
        C: ConstraintDisplay,
    {
        format_nf(nf, &mut self.terms, symbols)
    }

    /// Take a single step in the evaluation.
    fn step(&mut self) -> StepResult<C> {
        // Take ownership of root, step it, and update root with result
        let current = std::mem::replace(&mut self.root, Node::Fail);
        match step_node(current, &mut self.terms) {
            NodeStep::Emit(nf, rest) => {
                self.root = rest;
                StepResult::Emit(nf)
            }
            NodeStep::Continue(rest) => {
                self.root = rest;
                StepResult::Continue
            }
            NodeStep::Exhausted => {
                self.root = Node::Fail;
                StepResult::Exhausted
            }
        }
    }

    /// Check if the engine is exhausted.
    pub fn is_exhausted(&self) -> bool {
        matches!(self.root, Node::Fail)
    }

    /// Get reference to the term store.
    pub fn terms(&self) -> &TermStore {
        &self.terms
    }

    /// Get mutable reference to the term store.
    pub fn terms_mut(&mut self) -> &mut TermStore {
        &mut self.terms
    }

    /// Consume the engine and return the term store.
    pub fn into_terms(self) -> TermStore {
        self.terms
    }

    /// Create an iterator over all answers.
    ///
    /// The iterator yields NF answers until the engine is exhausted.
    pub fn iter(&mut self) -> QueryIter<'_, C> {
        QueryIter { engine: self }
    }

    /// Collect all answers into a vector.
    ///
    /// This consumes all answers from the query.
    pub fn collect_answers(&mut self) -> Vec<NF<C>> {
        self.iter().collect()
    }

    /// Count the number of answers (consumes them).
    pub fn count_answers(&mut self) -> usize {
        self.iter().count()
    }
}

impl<C: ConstraintOps> Iterator for Engine<C> {
    type Item = NF<C>;

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            match self.step() {
                StepResult::Emit(nf) => {
                    if self.seen.insert(nf.clone()) {
                        return Some(nf);
                    }
                }
                StepResult::Exhausted => return None,
                StepResult::Continue => continue,
            }
        }
    }
}

/// Iterator over query answers.
///
/// Yields NF answers from the engine until exhausted.
pub struct QueryIter<'a, C: ConstraintOps> {
    engine: &'a mut Engine<C>,
}

impl<'a, C: ConstraintOps> Iterator for QueryIter<'a, C> {
    type Item = NF<C>;

    fn next(&mut self) -> Option<Self::Item> {
        self.engine.next()
    }
}

/// Convenience function to run a query and collect all answers.
pub fn query<C: ConstraintOps>(rel: Rel<C>, terms: TermStore) -> Vec<NF<C>> {
    let mut engine = Engine::new(rel, terms);
    engine.collect_answers()
}

/// Convenience function to run a query and get the first answer.
pub fn query_first<C: ConstraintOps>(rel: Rel<C>, terms: TermStore) -> Option<NF<C>> {
    let mut engine = Engine::new(rel, terms);
    engine.next()
}


#[cfg(test)]
mod tests;


// ===== src/factors.rs =====
//! Factors - A rope-of-slices for efficient deque operations on Rel sequences.
//!
//! This data structure allows O(1) push/pop from both ends without copying,
//! by maintaining a list of slices into Arc-backed arrays.

use crate::rel::Rel;
use smallvec::SmallVec;
use std::sync::Arc;

/// A slice into an Arc-backed array of Rel elements.
///
/// Represents a contiguous sub-range [start, end) of the underlying array.
#[derive(Clone, Debug)]
pub struct Slice<C> {
    /// The underlying shared array.
    arc: Arc<[Arc<Rel<C>>]>,
    /// Start index (inclusive).
    start: usize,
    /// End index (exclusive).
    end: usize,
}

impl<C> Slice<C> {
    /// Create a new Slice covering the entire array.
    pub fn new(arc: Arc<[Arc<Rel<C>>]>) -> Self {
        let end = arc.len();
        Self { arc, start: 0, end }
    }

    /// Create a Slice with a specific range.
    pub fn with_range(arc: Arc<[Arc<Rel<C>>]>, start: usize, end: usize) -> Self {
        debug_assert!(start <= end);
        debug_assert!(end <= arc.len());
        Self { arc, start, end }
    }

    /// Check if this slice is empty.
    pub fn is_empty(&self) -> bool {
        self.start >= self.end
    }

    /// Get the number of elements in this slice.
    pub fn len(&self) -> usize {
        self.end.saturating_sub(self.start)
    }

    /// Get the first element, if any.
    pub fn front(&self) -> Option<&Arc<Rel<C>>> {
        if self.is_empty() {
            None
        } else {
            Some(&self.arc[self.start])
        }
    }

    /// Get the last element, if any.
    pub fn back(&self) -> Option<&Arc<Rel<C>>> {
        if self.is_empty() {
            None
        } else {
            Some(&self.arc[self.end - 1])
        }
    }

    /// Pop the first element from this slice.
    fn pop_front(&mut self) -> Option<Arc<Rel<C>>> {
        if self.is_empty() {
            None
        } else {
            let elem = Arc::clone(&self.arc[self.start]);
            self.start += 1;
            Some(elem)
        }
    }

    /// Pop the last element from this slice.
    fn pop_back(&mut self) -> Option<Arc<Rel<C>>> {
        if self.is_empty() {
            None
        } else {
            self.end -= 1;
            Some(Arc::clone(&self.arc[self.end]))
        }
    }
}

/// A rope-of-slices for efficient deque operations on Rel sequences.
///
/// Maintains a list of slices, allowing O(1) push/pop from both ends.
/// Empty slices are automatically filtered out to maintain the invariant
/// that all slices in `chunks` are non-empty (or `chunks` is empty).
#[derive(Clone, Debug)]
pub struct Factors<C> {
    /// The list of slices. Invariant: all slices are non-empty.
    chunks: SmallVec<[Slice<C>; 4]>,
}

impl<C> Factors<C> {
    /// Create a new empty Factors.
    pub fn new() -> Self {
        Self {
            chunks: SmallVec::new(),
        }
    }

    /// Create Factors from a sequence (single slice).
    pub fn from_seq(seq: Arc<[Arc<Rel<C>>]>) -> Self {
        let slice = Slice::new(seq);
        if slice.is_empty() {
            Self::new()
        } else {
            let mut chunks = SmallVec::new();
            chunks.push(slice);
            Self { chunks }
        }
    }

    /// Check if empty.
    pub fn is_empty(&self) -> bool {
        self.chunks.is_empty()
    }

    /// Get the total number of elements across all slices.
    pub fn len(&self) -> usize {
        self.chunks.iter().map(|s| s.len()).sum()
    }

    /// Collect all elements into a Vec in order.
    pub fn to_vec(&self) -> Vec<Arc<Rel<C>>> {
        let mut out = Vec::new();
        for slice in &self.chunks {
            for idx in slice.start..slice.end {
                out.push(Arc::clone(&slice.arc[idx]));
            }
        }
        out
    }

    /// Get the first element, if any.
    pub fn front(&self) -> Option<&Arc<Rel<C>>> {
        self.chunks.first().and_then(|s| s.front())
    }

    /// Get the last element, if any.
    pub fn back(&self) -> Option<&Arc<Rel<C>>> {
        self.chunks.last().and_then(|s| s.back())
    }

    /// Pop the first element.
    pub fn pop_front(&mut self) -> Option<Arc<Rel<C>>> {
        if self.chunks.is_empty() {
            return None;
        }

        let elem = self.chunks[0].pop_front();

        // Remove slice if it became empty
        if self.chunks[0].is_empty() {
            self.chunks.remove(0);
        }

        elem
    }

    /// Pop the last element.
    pub fn pop_back(&mut self) -> Option<Arc<Rel<C>>> {
        if self.chunks.is_empty() {
            return None;
        }

        let last_idx = self.chunks.len() - 1;
        let elem = self.chunks[last_idx].pop_back();

        // Remove slice if it became empty
        if self.chunks[last_idx].is_empty() {
            self.chunks.pop();
        }

        elem
    }

    /// Push a slice to the front. Empty slices are ignored.
    pub fn push_front_slice(&mut self, slice: Slice<C>) {
        if !slice.is_empty() {
            self.chunks.insert(0, slice);
        }
    }

    /// Push a slice to the back. Empty slices are ignored.
    pub fn push_back_slice(&mut self, slice: Slice<C>) {
        if !slice.is_empty() {
            self.chunks.push(slice);
        }
    }

    /// Push a single Rel to the front.
    pub fn push_front_rel(&mut self, rel: Arc<Rel<C>>) {
        let arr: Arc<[Arc<Rel<C>>]> = Arc::from(vec![rel]);
        self.push_front_slice(Slice::new(arr));
    }

    /// Push a single Rel to the back.
    pub fn push_back_rel(&mut self, rel: Arc<Rel<C>>) {
        let arr: Arc<[Arc<Rel<C>>]> = Arc::from(vec![rel]);
        self.push_back_slice(Slice::new(arr));
    }

    /// Push a Seq's contents to the front as a slice.
    pub fn push_front_slice_from_seq(&mut self, seq: Arc<[Arc<Rel<C>>]>) {
        self.push_front_slice(Slice::new(seq));
    }

    /// Push a Seq's contents to the back as a slice.
    pub fn push_back_slice_from_seq(&mut self, seq: Arc<[Arc<Rel<C>>]>) {
        self.push_back_slice(Slice::new(seq));
    }
}

impl<C> Default for Factors<C> {
    fn default() -> Self {
        Self::new()
    }
}


#[cfg(test)]
mod tests;


// ===== src/join.rs =====
use crate::constraint::ConstraintOps;
use crate::kernel::meet_nf;
use crate::nf::NF;
use crate::term::TermStore;
use std::collections::{HashSet, VecDeque};

use crate::queue::{AnswerReceiver, AnswerSink, BlockedOn, QueueWaker, RecvResult, SinkResult};

#[derive(Debug, Clone)]
pub enum JoinStep {
    Progress,
    Blocked(BlockedOn),
    Done,
}

#[derive(Debug)]
struct JoinPart<C> {
    receiver: AnswerReceiver<C>,
    done: bool,
}

#[derive(Debug)]
pub struct AndJoiner<C: ConstraintOps> {
    parts: Vec<JoinPart<C>>,
    pub(crate) seen: Vec<Vec<NF<C>>>,
    seen_sets: Vec<HashSet<NF<C>>>,
    pub(crate) pending: VecDeque<NF<C>>,
    pending_set: HashSet<NF<C>>,
    pub(crate) turn: usize,
    waker: QueueWaker,
    last_empty_epoch: Option<u64>,
}

impl<C: ConstraintOps> AndJoiner<C> {
    #[cfg(test)]
    pub fn new(receivers: Vec<AnswerReceiver<C>>) -> Self {
        let count = receivers.len();
        let parts = receivers
            .into_iter()
            .map(|receiver| JoinPart {
                receiver,
                done: false,
            })
            .collect();
        Self {
            parts,
            seen: vec![Vec::new(); count],
            seen_sets: vec![HashSet::new(); count],
            pending: VecDeque::new(),
            pending_set: HashSet::new(),
            turn: 0,
            waker: QueueWaker::noop(),
            last_empty_epoch: None,
        }
    }

    pub fn from_state(
        receivers: Vec<AnswerReceiver<C>>,
        done: Vec<bool>,
        seen: Vec<Vec<NF<C>>>,
        pending: VecDeque<NF<C>>,
        turn: usize,
        waker: QueueWaker,
    ) -> Self {
        let seen_sets = seen
            .iter()
            .map(|items| items.iter().cloned().collect())
            .collect();
        let pending_set = pending.iter().cloned().collect();
        let parts = receivers
            .into_iter()
            .zip(done)
            .map(|(receiver, done)| JoinPart { receiver, done })
            .collect();
        Self {
            parts,
            seen,
            seen_sets,
            pending,
            pending_set,
            turn,
            waker,
            last_empty_epoch: None,
        }
    }

    fn push_pending(&mut self, nf: NF<C>) {
        if self.pending_set.insert(nf.clone()) {
            self.pending.push_back(nf);
        }
    }

    fn enqueue_meets(&mut self, idx: usize, nf: NF<C>, terms: &mut TermStore) {
        if self.parts.len() == 1 {
            self.push_pending(nf);
            return;
        }

        let mut acc = vec![nf];
        for (j, seen_j) in self.seen.iter().enumerate() {
            if j == idx {
                continue;
            }
            if seen_j.is_empty() {
                return;
            }

            let mut next = Vec::new();
            for left in acc.iter() {
                for right in seen_j.iter() {
                    if let Some(met) = meet_nf(left, right, terms) {
                        next.push(met);
                    }
                }
            }
            if next.is_empty() {
                return;
            }
            acc = next;
        }

        for result in acc {
            self.push_pending(result);
        }
    }

    pub fn step(&mut self, terms: &mut TermStore, sink: &mut AnswerSink<C>) -> JoinStep {
        if let Some(nf) = self.pending.front().cloned() {
            match sink.push(nf.clone()) {
                SinkResult::Accepted => {
                    self.pending.pop_front();
                    self.pending_set.remove(&nf);
                    return JoinStep::Progress;
                }
                SinkResult::Full => {
                    return JoinStep::Blocked(
                        sink.blocked_on()
                            .expect("queue sink should provide a waker"),
                    )
                }
                SinkResult::Closed => return JoinStep::Done,
            }
        }

        if self.parts.is_empty() {
            return JoinStep::Done;
        }

        if self
            .parts
            .iter()
            .enumerate()
            .any(|(idx, part)| part.done && self.seen[idx].is_empty())
        {
            return JoinStep::Done;
        }

        if self.parts.iter().all(|part| part.done) {
            return JoinStep::Done;
        }

        let current_epoch = self.waker.epoch();
        if self.last_empty_epoch == Some(current_epoch) {
            return JoinStep::Blocked(self.waker.blocked_on());
        }

        let part_count = self.parts.len();
        for offset in 0..part_count {
            let idx = (self.turn + offset) % part_count;
            if self.parts[idx].done {
                continue;
            }

            match self.parts[idx].receiver.try_recv() {
                RecvResult::Empty => continue,
                RecvResult::Closed => {
                    self.last_empty_epoch = None;
                    self.parts[idx].done = true;
                    self.turn = (idx + 1) % part_count;
                    if self.seen[idx].is_empty() {
                        return JoinStep::Done;
                    }
                    return JoinStep::Progress;
                }
                RecvResult::Item(nf) => {
                    self.last_empty_epoch = None;
                    self.turn = (idx + 1) % part_count;
                    if self.seen_sets[idx].insert(nf.clone()) {
                        self.seen[idx].push(nf.clone());
                        self.enqueue_meets(idx, nf, terms);
                    }
                    if let Some(result) = self.pending.front().cloned() {
                        match sink.push(result.clone()) {
                            SinkResult::Accepted => {
                                self.pending.pop_front();
                                self.pending_set.remove(&result);
                                return JoinStep::Progress;
                            }
                            SinkResult::Full => {
                                return JoinStep::Blocked(
                                    sink.blocked_on()
                                        .expect("queue sink should provide a waker"),
                                )
                            }
                            SinkResult::Closed => return JoinStep::Done,
                        }
                    }
                    return JoinStep::Progress;
                }
            }
        }

        self.last_empty_epoch = Some(current_epoch);
        JoinStep::Blocked(self.waker.blocked_on())
    }
}


#[cfg(test)]
mod tests;


// ===== src/kernel/compose.rs =====
use crate::constraint::ConstraintOps;
use crate::nf::{collect_tensor, factor_tensor, NF};
use crate::term::TermStore;
#[cfg(feature = "tracing")]
use crate::trace::{debug_span, trace};

use super::util::{
    apply_subst_list, max_var_index_terms, remap_constraint_vars, shift_vars_list, unify_term_lists,
};

/// Compose two NFs in sequence: a ; b
///
/// This computes the composition where:
/// - First, a's match patterns are matched against input
/// - Variables are routed through a's DropFresh
/// - a's build patterns are constructed
/// - b's match patterns are matched against a's output
/// - Variables are routed through b's DropFresh
/// - b's build patterns are constructed
///
/// Returns None if composition fails (unification failure at interface).
pub fn compose_nf<C: ConstraintOps>(a: &NF<C>, b: &NF<C>, terms: &mut TermStore) -> Option<NF<C>> {
    #[cfg(feature = "tracing")]
    let _span = debug_span!(
        "compose_nf",
        a_match_arity = a.match_pats.len(),
        a_build_arity = a.build_pats.len(),
        b_match_arity = b.match_pats.len(),
        b_build_arity = b.build_pats.len(),
        a_drop_fresh_in = a.drop_fresh.in_arity,
        a_drop_fresh_out = a.drop_fresh.out_arity,
        b_drop_fresh_in = b.drop_fresh.in_arity,
        b_drop_fresh_out = b.drop_fresh.out_arity,
    )
    .entered();

    if a.build_pats.len() != b.match_pats.len() {
        #[cfg(feature = "tracing")]
        trace!(
            a_build = a.build_pats.len(),
            b_match = b.match_pats.len(),
            "arity_mismatch"
        );
        return None; // Arity mismatch
    }

    let rw1 = collect_tensor(a, terms);
    let mut rw2 = collect_tensor(b, terms);
    let b_max_var = max_var_index_terms(&rw2.lhs, terms).max(max_var_index_terms(&rw2.rhs, terms));

    let b_var_offset = max_var_index_terms(&rw1.lhs, terms)
        .max(max_var_index_terms(&rw1.rhs, terms))
        .map(|v| v + 1)
        .unwrap_or(0);

    if b_var_offset != 0 {
        rw2.lhs = shift_vars_list(&rw2.lhs, b_var_offset, terms);
        rw2.rhs = shift_vars_list(&rw2.rhs, b_var_offset, terms);
    }

    #[cfg(feature = "tracing")]
    trace!(
        a_rhs = ?rw1.rhs,
        b_lhs_shifted = ?rw2.lhs,
        b_var_offset,
        "unifying_interface"
    );

    let mgu = match unify_term_lists(&rw1.rhs, &rw2.lhs, terms) {
        Some(mgu) => {
            #[cfg(feature = "tracing")]
            trace!(mgu_size = mgu.len(), "unification_success");
            mgu
        }
        None => {
            #[cfg(feature = "tracing")]
            trace!("unification_failed");
            return None;
        }
    };

    let mut new_match = apply_subst_list(&rw1.lhs, &mgu, terms);
    let mut new_build = apply_subst_list(&rw2.rhs, &mgu, terms);

    let b_constraint =
        remap_constraint_vars(&b.drop_fresh.constraint, b_max_var, b_var_offset, terms);

    let combined = match a.drop_fresh.constraint.combine(&b_constraint) {
        Some(c) => c,
        None => {
            #[cfg(feature = "tracing")]
            trace!("compose_constraint_conflict");
            return None;
        }
    };
    let combined = combined.apply_subst(&mgu, terms);

    let (normalized, subst_opt) = match combined.normalize(terms) {
        Some(result) => result,
        None => {
            #[cfg(feature = "tracing")]
            trace!("compose_constraint_unsat");
            return None;
        }
    };
    if let Some(subst) = subst_opt {
        new_match = apply_subst_list(&new_match, &subst, terms);
        new_build = apply_subst_list(&new_build, &subst, terms);
    }

    Some(factor_tensor(new_match, new_build, normalized, terms))
}


#[cfg(test)]
mod tests;


// ===== src/kernel/dual.rs =====
//! Dual operation for NFs - swaps match/build and inverts DropFresh direction.
//!
//! The dual of a relation R is its converse: if R relates a to b,
//! then dual(R) relates b to a.

use crate::constraint::ConstraintOps;
use crate::drop_fresh::DropFresh;
use crate::nf::{collect_tensor, factor_tensor, NF};
use crate::term::TermStore;
use smallvec::SmallVec;

/// Compute the dual of a DropFresh.
///
/// The dual swaps input and output arities, and inverts the mapping.
/// After inversion, the map is re-sorted by first coordinate to maintain
/// the strictly-increasing invariant.
///
/// Properties:
/// - dual(dual(w)) == w (involution)
/// - dual swaps in_arity and out_arity
/// - Constraint is preserved
pub fn dual_drop_fresh<C: Clone>(drop_fresh: &DropFresh<C>) -> DropFresh<C> {
    // Swap arities
    let new_in_arity = drop_fresh.out_arity;
    let new_out_arity = drop_fresh.in_arity;

    // Invert map: (i, j) -> (j, i)
    let mut inverted: SmallVec<[(u32, u32); 4]> =
        drop_fresh.map.iter().map(|&(i, j)| (j, i)).collect();

    // CRITICAL: Re-sort by first coordinate to maintain invariant
    // The original map is sorted by i, so after inversion the j values
    // (now first) may not be in order.
    inverted.sort_by_key(|&(first, _)| first);

    DropFresh {
        in_arity: new_in_arity,
        out_arity: new_out_arity,
        map: inverted,
        constraint: drop_fresh.constraint.clone(),
    }
}

/// Compute the dual of a Normal Form.
///
/// The dual:
/// - Swaps match_pats and build_pats
/// - Dualizes the DropFresh
///
/// Properties:
/// - dual(dual(nf)) == nf (involution)
/// - If nf represents relation R, dual(nf) represents the converse R^(-1)
pub fn dual_nf<C: ConstraintOps>(nf: &NF<C>, terms: &mut TermStore) -> NF<C> {
    let direct = collect_tensor(nf, terms);
    factor_tensor(direct.rhs, direct.lhs, direct.constraint, terms)
}


#[cfg(test)]
mod tests;


// ===== src/kernel/meet.rs =====
use crate::constraint::ConstraintOps;
use crate::nf::{collect_tensor, factor_tensor, NF};
use crate::term::TermStore;
#[cfg(feature = "tracing")]
use crate::trace::{debug_span, trace};

use super::util::{
    apply_subst_list, max_var_index_terms, remap_constraint_vars, shift_vars_list, unify_term_lists,
};

/// Compute the meet (intersection) of two NFs.
///
/// The meet represents the relation that satisfies BOTH a AND b.
/// For inputs, this means the input must match both a's and b's match patterns.
/// For outputs, this means the output must satisfy both a's and b's build patterns.
///
/// Returns None if the meet is empty (patterns are incompatible).
pub fn meet_nf<C: ConstraintOps>(a: &NF<C>, b: &NF<C>, terms: &mut TermStore) -> Option<NF<C>> {
    #[cfg(feature = "tracing")]
    let _span = debug_span!(
        "meet_nf",
        a_match_arity = a.match_pats.len(),
        a_build_arity = a.build_pats.len(),
        b_match_arity = b.match_pats.len(),
        b_build_arity = b.build_pats.len(),
    )
    .entered();

    if a.match_pats.len() != b.match_pats.len() || a.build_pats.len() != b.build_pats.len() {
        #[cfg(feature = "tracing")]
        trace!("meet_arity_mismatch");
        return None;
    }

    let rw1 = collect_tensor(a, terms);
    let mut rw2 = collect_tensor(b, terms);
    let b_max_var = max_var_index_terms(&rw2.lhs, terms).max(max_var_index_terms(&rw2.rhs, terms));

    let b_var_offset = max_var_index_terms(&rw1.lhs, terms)
        .max(max_var_index_terms(&rw1.rhs, terms))
        .map(|v| v + 1)
        .unwrap_or(0);

    if b_var_offset != 0 {
        rw2.lhs = shift_vars_list(&rw2.lhs, b_var_offset, terms);
        rw2.rhs = shift_vars_list(&rw2.rhs, b_var_offset, terms);
    }

    let mgu_match = match unify_term_lists(&rw1.lhs, &rw2.lhs, terms) {
        Some(mgu) => mgu,
        None => {
            #[cfg(feature = "tracing")]
            trace!("meet_match_unify_failed");
            return None;
        }
    };

    let unified_lhs = apply_subst_list(&rw1.lhs, &mgu_match, terms);
    let a_rhs_subst = apply_subst_list(&rw1.rhs, &mgu_match, terms);
    let b_rhs_subst = apply_subst_list(&rw2.rhs, &mgu_match, terms);

    let mgu_build = match unify_term_lists(&a_rhs_subst, &b_rhs_subst, terms) {
        Some(mgu) => mgu,
        None => {
            #[cfg(feature = "tracing")]
            trace!("meet_build_unify_failed");
            return None;
        }
    };

    let mut final_lhs = apply_subst_list(&unified_lhs, &mgu_build, terms);
    let mut final_rhs = apply_subst_list(&a_rhs_subst, &mgu_build, terms);

    let b_constraint =
        remap_constraint_vars(&b.drop_fresh.constraint, b_max_var, b_var_offset, terms);

    let combined = match a.drop_fresh.constraint.combine(&b_constraint) {
        Some(c) => c,
        None => {
            #[cfg(feature = "tracing")]
            trace!("meet_constraint_conflict");
            return None;
        }
    };
    let combined = combined.apply_subst(&mgu_match, terms);
    let combined = combined.apply_subst(&mgu_build, terms);

    let (normalized, subst_opt) = match combined.normalize(terms) {
        Some(result) => result,
        None => {
            #[cfg(feature = "tracing")]
            trace!("meet_constraint_unsat");
            return None;
        }
    };
    if let Some(subst) = subst_opt {
        final_lhs = apply_subst_list(&final_lhs, &subst, terms);
        final_rhs = apply_subst_list(&final_rhs, &subst, terms);
    }

    #[cfg(feature = "tracing")]
    trace!("meet_success");

    Some(factor_tensor(final_lhs, final_rhs, normalized, terms))
}


#[cfg(test)]
mod tests;


// ===== src/kernel/mod.rs =====
pub mod compose;
pub mod dual;
pub mod meet;
mod util;

pub use compose::compose_nf;
pub use dual::{dual_drop_fresh, dual_nf};
pub use meet::meet_nf;


// ===== src/kernel/util.rs =====
//! Shared utilities for kernel operations.
//!
//! This module contains helper functions used by both compose and meet operations.

use crate::nf::collect_vars_ordered;
use crate::subst::{apply_subst, Subst};
use crate::term::{Term, TermId, TermStore};
use crate::unify::unify;
use smallvec::SmallVec;

/// Find the maximum variable index in a list of patterns.
pub fn max_var_index_terms(pats: &[TermId], terms: &TermStore) -> Option<u32> {
    pats.iter()
        .flat_map(|&term| collect_vars_ordered(term, terms).into_iter())
        .max()
}

/// Shift all variables in a term by a given offset.
pub fn shift_vars(term: TermId, offset: u32, terms: &mut TermStore) -> TermId {
    match terms.resolve(term) {
        Some(Term::Var(idx)) => terms.var(idx + offset),
        Some(Term::App(func, children)) => {
            let new_children: SmallVec<[TermId; 4]> = children
                .iter()
                .map(|&c| shift_vars(c, offset, terms))
                .collect();
            terms.app(func, new_children)
        }
        None => term,
    }
}

/// Shift all variables in a list of patterns by a given offset.
pub fn shift_vars_list(
    pats: &[TermId],
    offset: u32,
    terms: &mut TermStore,
) -> SmallVec<[TermId; 1]> {
    if offset == 0 {
        return pats.iter().copied().collect();
    }
    pats.iter()
        .map(|&term| shift_vars(term, offset, terms))
        .collect()
}

/// Apply a substitution to a list of patterns.
pub fn apply_subst_list(
    pats: &[TermId],
    subst: &Subst,
    terms: &mut TermStore,
) -> SmallVec<[TermId; 1]> {
    pats.iter()
        .map(|&term| apply_subst(term, subst, terms))
        .collect()
}

/// Unify two lists of terms element-wise.
///
/// Returns the combined most general unifier if all pairs unify,
/// or None if any pair fails to unify.
pub fn unify_term_lists(left: &[TermId], right: &[TermId], terms: &mut TermStore) -> Option<Subst> {
    if left.len() != right.len() {
        return None;
    }

    let mut subst = Subst::new();
    for (&l, &r) in left.iter().zip(right.iter()) {
        let l_sub = apply_subst(l, &subst, terms);
        let r_sub = apply_subst(r, &subst, terms);
        let mgu = unify(l_sub, r_sub, terms)?;
        subst = compose_subst(&subst, &mgu, terms);
    }
    Some(subst)
}

/// Compose two substitutions.
///
/// The result applies `existing` first, then `new`.
pub fn compose_subst(existing: &Subst, new: &Subst, terms: &mut TermStore) -> Subst {
    let mut combined = Subst::new();
    for (var, term) in existing.iter() {
        let updated = apply_subst(term, new, terms);
        combined.bind(var, updated);
    }
    for (var, term) in new.iter() {
        combined.bind(var, term);
    }
    combined
}

/// Remap constraint variables by the given offset.
///
/// Returns the remapped constraint if offset is non-zero and there are variables,
/// otherwise returns a clone of the original.
pub fn remap_constraint_vars<C: crate::constraint::ConstraintOps>(
    constraint: &C,
    max_var: Option<u32>,
    offset: u32,
    terms: &mut TermStore,
) -> C {
    if offset == 0 {
        return constraint.clone();
    }
    match max_var {
        Some(max) => {
            let mut map = vec![None; max as usize + 1];
            for i in 0..=max {
                map[i as usize] = Some(i + offset);
            }
            constraint.remap_vars(&map, terms)
        }
        None => constraint.clone(),
    }
}


// ===== src/lib.rs =====
pub mod chr;
pub mod constraint;
pub mod drop_fresh;
pub mod engine;
pub mod factors;
pub mod join;
pub mod jupyter;
pub mod kernel;
pub mod metrics;
pub mod nf;
pub mod node;
pub mod parser;
pub mod queue;
pub mod rel;
pub mod repl;
pub mod subst;
pub mod symbol;
pub mod term;
pub mod trace;
pub mod unify;
pub mod work;

#[cfg(test)]
pub(crate) mod test_utils;


// ===== src/nf.rs =====
use crate::constraint::{ConstraintDisplay, ConstraintOps};
use crate::drop_fresh::DropFresh;
use crate::symbol::SymbolStore;
use crate::term::{format_term, Term, TermId, TermStore};
use smallvec::SmallVec;

/// Normal Form representation of a rewrite rule.
///
/// A rule `Rw lhs rhs` is factored into:
///   RwL [match_pats] ; DropFresh ; RwR [build_pats]
///
/// Where:
/// - RwL (match_pats): patterns to decompose input, extracting variables
/// - DropFresh: variable routing between LHS vars and RHS vars
/// - RwR (build_pats): patterns to construct output from variables
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct NF<C> {
    /// Patterns for matching input terms (RwL).
    /// Variables in these patterns are numbered 0..n-1 in order of first appearance.
    pub match_pats: SmallVec<[TermId; 1]>,
    /// Variable routing between match and build.
    pub drop_fresh: DropFresh<C>,
    /// Patterns for building output terms (RwR).
    /// Variables in these patterns are numbered 0..m-1 with shared vars in LHS order,
    /// followed by RHS-only vars in RHS order.
    pub build_pats: SmallVec<[TermId; 1]>,
}

/// Direct tensor rewrite form (lists of patterns with constraint).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RwT<C> {
    pub lhs: SmallVec<[TermId; 1]>,
    pub rhs: SmallVec<[TermId; 1]>,
    pub constraint: C,
}

impl<C> NF<C> {
    /// Create a new NF directly (assumes already normalized).
    pub fn new(
        match_pats: SmallVec<[TermId; 1]>,
        drop_fresh: DropFresh<C>,
        build_pats: SmallVec<[TermId; 1]>,
    ) -> Self {
        Self {
            match_pats,
            drop_fresh,
            build_pats,
        }
    }

    /// Create an identity NF (empty patterns, zero-arity DropFresh).
    ///
    /// This represents the identity relation that accepts any input
    /// and produces it unchanged.
    pub fn identity(constraint: C) -> Self {
        Self {
            match_pats: SmallVec::new(),
            drop_fresh: DropFresh::identity_with_constraint(0, constraint),
            build_pats: SmallVec::new(),
        }
    }
}

impl<C: ConstraintOps> NF<C> {
    /// Factor a single-term rule (lhs -> rhs) into normal form.
    ///
    /// This extracts variables, renumbers them, and computes the DropFresh
    /// that connects LHS variables to RHS variables.
    pub fn factor(lhs: TermId, rhs: TermId, constraint: C, terms: &mut TermStore) -> Self {
        // Step 1: Collect variables from each side
        let lhs_vars = collect_vars_ordered(lhs, terms);
        let rhs_vars = collect_vars_ordered(rhs, terms);

        let n = lhs_vars.len() as u32;
        let lhs_old_to_new = build_var_map(&lhs_vars);

        // Step 2: Renumber LHS
        let norm_lhs = if lhs_vars.is_empty() {
            lhs
        } else {
            apply_var_renaming(lhs, &lhs_old_to_new, terms)
        };

        // Step 3: Establish RHS variable order:
        // - shared vars in LHS order (preserves monotone routing)
        // - fresh vars appended in RHS order
        let rhs_set: std::collections::HashSet<u32> = rhs_vars.iter().copied().collect();
        let lhs_set: std::collections::HashSet<u32> = lhs_vars.iter().copied().collect();

        // Build constraint variable ordering
        let mut constraint_ordered: Vec<u32> = lhs_vars.clone();
        for &var in rhs_vars.iter() {
            if !lhs_set.contains(&var) {
                constraint_ordered.push(var);
            }
        }
        let mut seen: std::collections::HashSet<u32> = constraint_ordered.iter().copied().collect();
        let mut constraint_vars = Vec::new();
        constraint.collect_vars(terms, &mut constraint_vars);
        constraint_vars.sort_unstable();
        constraint_vars.dedup();
        for var in constraint_vars {
            if seen.insert(var) {
                constraint_ordered.push(var);
            }
        }
        let constraint_map = build_var_map(&constraint_ordered);
        let constraint = constraint.remap_vars(&constraint_map, terms);

        // Build RHS variable ordering
        let mut rhs_ordered: Vec<u32> = Vec::new();
        for &var in lhs_vars.iter() {
            if rhs_set.contains(&var) {
                rhs_ordered.push(var);
            }
        }
        for &var in rhs_vars.iter() {
            if !lhs_set.contains(&var) {
                rhs_ordered.push(var);
            }
        }

        let m = rhs_ordered.len() as u32;
        let rhs_old_to_new = build_var_map(&rhs_ordered);

        // Step 4: Renumber RHS
        let norm_rhs = if rhs_ordered.is_empty() {
            rhs
        } else {
            apply_var_renaming(rhs, &rhs_old_to_new, terms)
        };

        // Step 7: Build DropFresh by finding shared variables
        // For each LHS var position i, find if the original var appears in RHS
        // and at what position j in rhs_ordered. DropFresh connects (i, j) for shared vars.
        let mut rhs_pos: std::collections::HashMap<u32, u32> = std::collections::HashMap::new();
        for (pos, &var) in rhs_ordered.iter().enumerate() {
            rhs_pos.insert(var, pos as u32);
        }
        let mut drop_fresh_map: SmallVec<[(u32, u32); 4]> = SmallVec::new();

        for (i, &lhs_orig_var) in lhs_vars.iter().enumerate() {
            if let Some(&j) = rhs_pos.get(&lhs_orig_var) {
                drop_fresh_map.push((i as u32, j));
            }
        }

        let drop_fresh = DropFresh {
            in_arity: n,
            out_arity: m,
            map: drop_fresh_map,
            constraint,
        };

        Self {
            match_pats: smallvec::smallvec![norm_lhs],
            drop_fresh,
            build_pats: smallvec::smallvec![norm_rhs],
        }
    }
}

/// Collect a tensor NF into direct-rule form by pushing wiring into RHS vars.
pub fn collect_tensor<C: Clone>(nf: &NF<C>, terms: &mut TermStore) -> RwT<C> {
    let out_arity = nf.drop_fresh.out_arity as usize;
    let in_arity = nf.drop_fresh.in_arity;

    let mut rhs_map: Vec<Option<u32>> = vec![None; out_arity];
    for (i, j) in nf.drop_fresh.map.iter().copied() {
        if let Some(slot) = rhs_map.get_mut(j as usize) {
            *slot = Some(i);
        }
    }

    let mut next_var = in_arity;
    for slot in rhs_map.iter_mut() {
        if slot.is_none() {
            *slot = Some(next_var);
            next_var += 1;
        }
    }

    let rhs_direct = apply_var_renaming_list(&nf.build_pats, &rhs_map, terms);

    RwT {
        lhs: nf.match_pats.clone(),
        rhs: rhs_direct,
        constraint: nf.drop_fresh.constraint.clone(),
    }
}

/// Factor a tensor rewrite (lists of patterns) into NF.
pub fn factor_tensor<C: ConstraintOps>(
    lhs_pats: SmallVec<[TermId; 1]>,
    rhs_pats: SmallVec<[TermId; 1]>,
    constraint: C,
    terms: &mut TermStore,
) -> NF<C> {
    let constraint_map = constraint_var_renaming(&lhs_pats, &rhs_pats, &constraint, terms);
    let constraint = constraint.remap_vars(&constraint_map, terms);

    let lhs_vars = collect_vars_ordered_list(&lhs_pats, terms);
    let rhs_vars = collect_vars_ordered_list(&rhs_pats, terms);

    let n = lhs_vars.len() as u32;
    let lhs_old_to_new = build_var_map(&lhs_vars);

    let norm_lhs = if lhs_vars.is_empty() {
        lhs_pats.clone()
    } else {
        apply_var_renaming_list(&lhs_pats, &lhs_old_to_new, terms)
    };

    let rhs_set: std::collections::HashSet<u32> = rhs_vars.iter().copied().collect();
    let lhs_set: std::collections::HashSet<u32> = lhs_vars.iter().copied().collect();

    // Build RHS variable ordering: shared vars in LHS order, then RHS-only vars
    let mut rhs_ordered: Vec<u32> = Vec::new();
    for &var in lhs_vars.iter() {
        if rhs_set.contains(&var) {
            rhs_ordered.push(var);
        }
    }
    for &var in rhs_vars.iter() {
        if !lhs_set.contains(&var) {
            rhs_ordered.push(var);
        }
    }

    let m = rhs_ordered.len() as u32;
    let rhs_old_to_new = build_var_map(&rhs_ordered);

    let norm_rhs = if rhs_ordered.is_empty() {
        rhs_pats.clone()
    } else {
        apply_var_renaming_list(&rhs_pats, &rhs_old_to_new, terms)
    };

    // Build DropFresh by finding shared variables
    let mut rhs_pos: std::collections::HashMap<u32, u32> = std::collections::HashMap::new();
    for (pos, &var) in rhs_ordered.iter().enumerate() {
        rhs_pos.insert(var, pos as u32);
    }

    let mut drop_fresh_map: SmallVec<[(u32, u32); 4]> = SmallVec::new();
    for (i, &lhs_orig_var) in lhs_vars.iter().enumerate() {
        if let Some(&j) = rhs_pos.get(&lhs_orig_var) {
            drop_fresh_map.push((i as u32, j));
        }
    }

    let drop_fresh = DropFresh {
        in_arity: n,
        out_arity: m,
        map: drop_fresh_map,
        constraint,
    };

    NF {
        match_pats: norm_lhs,
        drop_fresh,
        build_pats: norm_rhs,
    }
}

/// Compute a renaming map for constraints based on direct-rule variable ordering:
/// LHS variables first (order of appearance), then RHS-only variables.
pub fn constraint_var_renaming<C: ConstraintOps>(
    lhs_pats: &[TermId],
    rhs_pats: &[TermId],
    constraint: &C,
    terms: &TermStore,
) -> Vec<Option<u32>> {
    let lhs_vars = collect_vars_ordered_list(lhs_pats, terms);
    let rhs_vars = collect_vars_ordered_list(rhs_pats, terms);
    let mut constraint_vars = Vec::new();
    constraint.collect_vars(terms, &mut constraint_vars);
    constraint_vars.sort_unstable();
    constraint_vars.dedup();
    combined_var_renaming_with_extra(&lhs_vars, &rhs_vars, &constraint_vars)
}

/// Compute a renaming map for constraints based on combined variable order:
/// LHS variables first (order of appearance), then RHS-only variables.
pub fn combined_var_renaming(lhs_vars: &[u32], rhs_vars: &[u32]) -> Vec<Option<u32>> {
    combined_var_renaming_with_extra(lhs_vars, rhs_vars, &[])
}

/// Compute a renaming map for constraints using LHS vars, RHS-only vars,
/// then any extra vars (e.g., constraint-only vars).
pub fn combined_var_renaming_with_extra(
    lhs_vars: &[u32],
    rhs_vars: &[u32],
    extra_vars: &[u32],
) -> Vec<Option<u32>> {
    let mut ordered: Vec<u32> = Vec::new();
    let mut seen: std::collections::HashSet<u32> = std::collections::HashSet::new();
    for &var in lhs_vars.iter() {
        if seen.insert(var) {
            ordered.push(var);
        }
    }
    for &var in rhs_vars.iter() {
        if seen.insert(var) {
            ordered.push(var);
        }
    }
    for &var in extra_vars.iter() {
        if seen.insert(var) {
            ordered.push(var);
        }
    }
    build_var_map(&ordered)
}

/// Build a variable renaming map from a list of original variable indices.
/// Maps old_idx -> new_idx where new_idx is the position in vars.
fn build_var_map(vars: &[u32]) -> Vec<Option<u32>> {
    if vars.is_empty() {
        return Vec::new();
    }
    let max_var = vars.iter().copied().max().unwrap_or(0) as usize;
    let mut old_to_new = vec![None; max_var + 1];
    for (new_idx, &old_idx) in vars.iter().enumerate() {
        old_to_new[old_idx as usize] = Some(new_idx as u32);
    }
    old_to_new
}

/// Collect variables from a term in order of first appearance.
/// Returns the list of original variable indices (unique).
pub fn collect_vars_ordered(term: TermId, terms: &TermStore) -> Vec<u32> {
    let mut vars = Vec::new();
    let mut seen = std::collections::HashSet::new();
    collect_vars_helper(term, terms, &mut vars, &mut seen);
    vars
}

/// Collect variables from a list of terms in order of first appearance.
pub fn collect_vars_ordered_list(terms_list: &[TermId], terms: &TermStore) -> Vec<u32> {
    let mut vars = Vec::new();
    let mut seen = std::collections::HashSet::new();
    for &term in terms_list {
        collect_vars_helper(term, terms, &mut vars, &mut seen);
    }
    vars
}

fn collect_vars_helper(
    term: TermId,
    terms: &TermStore,
    vars: &mut Vec<u32>,
    seen: &mut std::collections::HashSet<u32>,
) {
    match terms.resolve(term) {
        Some(Term::Var(idx)) => {
            if seen.insert(idx) {
                vars.push(idx);
            }
        }
        Some(Term::App(_, children)) => {
            for child in children {
                collect_vars_helper(child, terms, vars, seen);
            }
        }
        None => {}
    }
}

/// Renumber variables in a term to use consecutive indices starting at 0.
/// Returns the renumbered term and the mapping from new index to old index.
pub fn renumber_vars(term: TermId, terms: &mut TermStore) -> (TermId, Vec<u32>) {
    let vars = collect_vars_ordered(term, terms);

    if vars.is_empty() {
        return (term, vec![]);
    }

    // Build old_to_new mapping
    let max_var = vars.iter().copied().max().unwrap() as usize;
    let mut old_to_new = vec![None; max_var + 1];
    for (new_idx, &old_idx) in vars.iter().enumerate() {
        old_to_new[old_idx as usize] = Some(new_idx as u32);
    }

    let renumbered = apply_var_renaming(term, &old_to_new, terms);
    (renumbered, vars)
}

/// Renumber variables according to a given mapping.
/// The mapping maps old variable index to new variable index.
pub fn apply_var_renaming(
    term: TermId,
    old_to_new: &[Option<u32>],
    terms: &mut TermStore,
) -> TermId {
    match terms.resolve(term) {
        Some(Term::Var(idx)) => {
            let idx_usize = idx as usize;
            if idx_usize < old_to_new.len() {
                if let Some(new_idx) = old_to_new[idx_usize] {
                    return terms.var(new_idx);
                }
            }
            // Variable not in mapping - keep as is
            term
        }
        Some(Term::App(func, children)) => {
            let new_children: SmallVec<[TermId; 4]> = children
                .iter()
                .map(|&child| apply_var_renaming(child, old_to_new, terms))
                .collect();
            terms.app(func, new_children)
        }
        None => term,
    }
}

fn apply_var_renaming_list(
    terms_list: &[TermId],
    old_to_new: &[Option<u32>],
    terms: &mut TermStore,
) -> SmallVec<[TermId; 1]> {
    terms_list
        .iter()
        .map(|&term| apply_var_renaming(term, old_to_new, terms))
        .collect()
}

pub fn direct_rule_terms<C: Clone>(nf: &NF<C>, terms: &mut TermStore) -> Option<(TermId, TermId)> {
    if nf.match_pats.len() != 1 || nf.build_pats.len() != 1 {
        return None;
    }

    let lhs = nf.match_pats[0];
    let rhs = nf.build_pats[0];
    let out_arity = nf.drop_fresh.out_arity as usize;
    let in_arity = nf.drop_fresh.in_arity;

    let mut rhs_map: Vec<Option<u32>> = vec![None; out_arity];
    for (i, j) in nf.drop_fresh.map.iter().copied() {
        if let Some(slot) = rhs_map.get_mut(j as usize) {
            *slot = Some(i);
        }
    }

    let mut next_var = in_arity;
    for slot in rhs_map.iter_mut() {
        if slot.is_none() {
            *slot = Some(next_var);
            next_var += 1;
        }
    }

    let rhs_direct = apply_var_renaming(rhs, &rhs_map, terms);
    Some((lhs, rhs_direct))
}

pub fn format_nf<C: Clone + ConstraintDisplay>(
    nf: &NF<C>,
    terms: &mut TermStore,
    symbols: &SymbolStore,
) -> Result<String, String> {
    if nf.match_pats.is_empty() && nf.build_pats.is_empty() {
        return Ok("$0 -> $0".to_string());
    }

    let (lhs, rhs) = direct_rule_terms(nf, terms)
        .ok_or_else(|| "Cannot render non-unary relation".to_string())?;
    let lhs_str = format_term(lhs, terms, symbols)?;
    let rhs_str = format_term(rhs, terms, symbols)?;
    let constraint_str = nf.drop_fresh.constraint.fmt_constraints(terms, symbols)?;
    if let Some(cs) = constraint_str {
        Ok(format!("{} {{ {} }} -> {}", lhs_str, cs, rhs_str))
    } else {
        Ok(format!("{} -> {}", lhs_str, rhs_str))
    }
}


#[cfg(test)]
mod tests;


// ===== src/node.rs =====
//! Node - Search tree nodes for the evaluation engine.
//!
//! The Node enum represents the search tree structure.
//! Or nodes use rotation interleaving for fair search.
//! Work nodes embed active computations (Seq, And, Fix).

use crate::constraint::ConstraintOps;
use crate::nf::NF;
use crate::term::TermStore;
use crate::work::{Work, WorkStep};

/// Search tree node.
///
/// Represents a point in the search space:
/// - `Fail`: Dead end, no more answers
/// - `Or(left, right)`: Disjunction with rotation interleaving
/// - `Emit(nf, rest)`: Yield an answer, continue with rest
/// - `Work(work)`: Active computation (Seq, And, Fix)
#[derive(Clone, Debug)]
pub enum Node<C: ConstraintOps> {
    /// Failed/exhausted branch - no more answers.
    Fail,
    /// Disjunction: search left first, then rotate.
    /// Rotation: Or(left', right) -> Or(right, left')
    Or(Box<Node<C>>, Box<Node<C>>),
    /// Emit an answer and continue with the rest.
    Emit(NF<C>, Box<Node<C>>),
    /// Active work - computations that may emit, split, or complete.
    Work(Box<Work<C>>),
}

/// Result of stepping a Node one notch.
#[derive(Clone, Debug)]
pub enum NodeStep<C: ConstraintOps> {
    /// Produced an answer and the remaining node.
    Emit(NF<C>, Node<C>),
    /// No answer yet, but node updated (rotation or work progress).
    Continue(Node<C>),
    /// Exhausted - no more answers.
    Exhausted,
}

/// Step a node once using Or rotation and Work stepping.
pub fn step_node<C: ConstraintOps>(node: Node<C>, terms: &mut TermStore) -> NodeStep<C> {
    match node {
        Node::Fail => NodeStep::Exhausted,

        Node::Emit(nf, rest) => NodeStep::Emit(nf, *rest),

        Node::Or(left, right) => {
            let left_node = *left;
            match step_node(left_node, terms) {
                NodeStep::Emit(nf, new_left) => {
                    NodeStep::Emit(nf, Node::Or(right, Box::new(new_left)))
                }
                NodeStep::Exhausted => NodeStep::Continue(*right),
                NodeStep::Continue(new_left) => {
                    NodeStep::Continue(Node::Or(right, Box::new(new_left)))
                }
            }
        }

        Node::Work(mut work) => match work.step(terms) {
            WorkStep::Done => NodeStep::Continue(Node::Fail),
            WorkStep::Emit(nf, next_work) => NodeStep::Emit(nf, Node::Work(next_work)),
            WorkStep::Split(left_node, right_node) => {
                NodeStep::Continue(Node::Or(left_node, right_node))
            }
            WorkStep::More(next_work) => NodeStep::Continue(Node::Work(next_work)),
        },
    }
}


#[cfg(test)]
mod tests;


// ===== src/parser.rs =====
//! Parser for rwlog relation definitions.
//!
//! Syntax:
//! - `rel name { body }` - relation definition
//! - `pattern -> pattern` - rewrite rule (atomic relation)
//! - `|` - Or (disjunction) - lowest precedence
//! - `;` - Seq (sequential composition)
//! - `&` - And (intersection/conjunction) - highest precedence
//! - `[...]` - grouping for sequences
//! - `$var` - variable
//! - `atom` - lowercase identifier (nullary constructor)
//! - `@term` - term literal (identity relation at term)
//! - `(f x y ...)` - compound term

use crate::chr::{
    ArgExpr, BodyInstr, BodyProg, ChrProgram, ChrProgramBuilder, ChrState, GVal, GuardInstr,
    GuardProg, HeadPat, NoTheory, PatId, PredId, RVar,
};
use crate::constraint::ConstraintOps;
use crate::nf::NF;
use crate::rel::{Rel, RelId};
use crate::symbol::SymbolStore;
use crate::term::{TermId, TermStore};
use smallvec::SmallVec;
use std::collections::HashMap;
use std::sync::Arc;

/// Result of parsing a term - TermId plus variable info.
#[derive(Clone, Debug)]
pub struct ParsedTerm {
    pub term_id: crate::term::TermId,
    /// Variables in order of first occurrence.
    pub var_order: Vec<u32>,
}

#[derive(Clone, Debug)]
pub struct ConstraintCall {
    name: String,
    args: Vec<TermId>,
    position: usize,
}

#[derive(Clone, Debug)]
pub struct TheorySummary {
    pub name: String,
    pub predicates: usize,
    pub rules: usize,
}

pub trait ConstraintBuilder: Clone {
    type Constraint: ConstraintOps + Clone + Eq + Default + Send + Sync;

    fn empty_constraint(&self) -> Self::Constraint {
        Self::Constraint::default()
    }

    fn build_constraint(
        &mut self,
        calls: Vec<ConstraintCall>,
        terms: &mut TermStore,
    ) -> Result<Self::Constraint, ParseError>;

    fn parse_theory_def(
        &mut self,
        input: &str,
        symbols: &mut SymbolStore,
        terms: &mut TermStore,
    ) -> Result<TheorySummary, ParseError>;
}

#[derive(Clone, Debug, Default)]
pub struct NoConstraintBuilder;

impl ConstraintBuilder for NoConstraintBuilder {
    type Constraint = ();

    fn build_constraint(
        &mut self,
        calls: Vec<ConstraintCall>,
        _terms: &mut TermStore,
    ) -> Result<Self::Constraint, ParseError> {
        let pos = calls.first().map(|c| c.position).unwrap_or(0);
        Err(ParseError {
            message: "Constraints are not supported in this parser".to_string(),
            position: pos,
        })
    }

    fn parse_theory_def(
        &mut self,
        _input: &str,
        _symbols: &mut SymbolStore,
        _terms: &mut TermStore,
    ) -> Result<TheorySummary, ParseError> {
        Err(ParseError {
            message: "Theory blocks are not supported in this parser".to_string(),
            position: 0,
        })
    }
}

#[derive(Clone, Debug)]
pub struct ChrConstraintBuilder {
    builder: ChrProgramBuilder<NoTheory>,
    program: Arc<ChrProgram<NoTheory>>,
}

impl ChrConstraintBuilder {
    pub fn new() -> Self {
        let builder = ChrProgramBuilder::new(crate::chr::BuiltinRegistry::default());
        let program = builder.clone().build();
        Self { builder, program }
    }

    pub fn program(&self) -> Arc<ChrProgram<NoTheory>> {
        self.program.clone()
    }
}

impl Default for ChrConstraintBuilder {
    fn default() -> Self {
        Self::new()
    }
}

impl ConstraintBuilder for ChrConstraintBuilder {
    type Constraint = ChrState<NoTheory>;

    fn empty_constraint(&self) -> Self::Constraint {
        ChrState::new(self.program.clone(), ())
    }

    fn build_constraint(
        &mut self,
        calls: Vec<ConstraintCall>,
        terms: &mut TermStore,
    ) -> Result<Self::Constraint, ParseError> {
        let mut st = ChrState::new(self.program.clone(), ());
        for call in calls {
            let pred = self.program.pred_id(&call.name).ok_or_else(|| ParseError {
                message: format!("unknown constraint predicate '{}'", call.name),
                position: call.position,
            })?;
            let expected = self.program.preds[pred.0 as usize].arity as usize;
            if call.args.len() != expected {
                return Err(ParseError {
                    message: format!(
                        "constraint '{}' arity {} expects {} args, got {}",
                        call.name,
                        expected,
                        expected,
                        call.args.len()
                    ),
                    position: call.position,
                });
            }
            st.introduce(pred, &call.args, terms);
        }
        Ok(st)
    }

    fn parse_theory_def(
        &mut self,
        input: &str,
        symbols: &mut SymbolStore,
        terms: &mut TermStore,
    ) -> Result<TheorySummary, ParseError> {
        let summary = parse_chr_theory(input, &mut self.builder, symbols, terms)?;
        self.program = self.builder.clone().build();
        Ok(summary)
    }
}

/// Parser state.
pub struct Parser<B: ConstraintBuilder = NoConstraintBuilder> {
    symbols: SymbolStore,
    terms: TermStore,
    /// Named relations (for recursive calls).
    relations: HashMap<String, RelId>,
    /// Next available RelId.
    next_rel_id: RelId,
    constraints: B,
}

/// Parse error.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ParseError {
    pub message: String,
    pub position: usize,
}

impl std::fmt::Display for ParseError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "Parse error at position {}: {}",
            self.position, self.message
        )
    }
}

impl std::error::Error for ParseError {}

impl Parser<NoConstraintBuilder> {
    /// Create a new parser.
    pub fn new() -> Self {
        Self {
            symbols: SymbolStore::new(),
            terms: TermStore::new(),
            relations: HashMap::new(),
            next_rel_id: 0,
            constraints: NoConstraintBuilder,
        }
    }

    /// Create a parser with existing symbol and term stores.
    pub fn with_stores(symbols: SymbolStore, terms: TermStore) -> Self {
        Self {
            symbols,
            terms,
            relations: HashMap::new(),
            next_rel_id: 0,
            constraints: NoConstraintBuilder,
        }
    }
}

impl<B: ConstraintBuilder> Parser<B> {
    pub fn with_builder(builder: B) -> Self {
        Self {
            symbols: SymbolStore::new(),
            terms: TermStore::new(),
            relations: HashMap::new(),
            next_rel_id: 0,
            constraints: builder,
        }
    }

    pub fn with_stores_and_builder(symbols: SymbolStore, terms: TermStore, builder: B) -> Self {
        Self {
            symbols,
            terms,
            relations: HashMap::new(),
            next_rel_id: 0,
            constraints: builder,
        }
    }

    /// Get the symbol store.
    pub fn symbols(&self) -> &SymbolStore {
        &self.symbols
    }

    /// Get the term store.
    pub fn terms(&self) -> &TermStore {
        &self.terms
    }

    /// Take ownership of the term store, leaving a fresh one behind.
    pub fn take_terms(&mut self) -> TermStore {
        std::mem::take(&mut self.terms)
    }

    /// Restore the term store after temporary extraction.
    pub fn restore_terms(&mut self, terms: TermStore) {
        self.terms = terms;
    }

    /// Consume the parser and return the stores.
    pub fn into_stores(self) -> (SymbolStore, TermStore) {
        (self.symbols, self.terms)
    }

    /// Parse a term from a string.
    /// Returns the TermId and the variable order.
    pub fn parse_term(&self, input: &str) -> Result<ParsedTerm, ParseError> {
        let mut pos = 0;
        let mut var_map: HashMap<String, u32> = HashMap::new();
        let mut var_order: Vec<u32> = Vec::new();
        let term = self.parse_term_inner(input, &mut pos, &mut var_map, &mut var_order)?;
        skip_whitespace(input, &mut pos);
        if pos < input.len() {
            return Err(ParseError {
                message: "Unexpected characters after term".to_string(),
                position: pos,
            });
        }
        Ok(ParsedTerm {
            term_id: term,
            var_order,
        })
    }

    /// Parse a term, tracking variables.
    fn parse_term_inner(
        &self,
        input: &str,
        pos: &mut usize,
        var_map: &mut HashMap<String, u32>,
        var_order: &mut Vec<u32>,
    ) -> Result<crate::term::TermId, ParseError> {
        skip_whitespace(input, pos);

        if *pos >= input.len() {
            return Err(ParseError {
                message: "Unexpected end of input".to_string(),
                position: *pos,
            });
        }

        let ch = peek_char(input, *pos).unwrap();

        if ch == '$' {
            // Variable
            *pos += 1;
            let name = parse_identifier(input, pos)?;
            let var_id = if let Some(&id) = var_map.get(&name) {
                id
            } else {
                let id = var_map.len() as u32;
                var_map.insert(name, id);
                var_order.push(id);
                id
            };
            Ok(self.terms.var(var_id))
        } else if ch == '(' {
            // Compound term: (f args...)
            *pos += 1;
            skip_whitespace(input, pos);
            let functor = parse_identifier(input, pos)?;
            let sym = self.symbols.intern(&functor);

            let mut args: SmallVec<[crate::term::TermId; 4]> = SmallVec::new();
            loop {
                skip_whitespace(input, pos);
                if *pos >= input.len() {
                    return Err(ParseError {
                        message: "Unclosed parenthesis".to_string(),
                        position: *pos,
                    });
                }
                if peek_char(input, *pos).unwrap() == ')' {
                    *pos += 1;
                    break;
                }
                args.push(self.parse_term_inner(input, pos, var_map, var_order)?);
            }

            Ok(self.terms.app(sym, args))
        } else if ch.is_ascii_lowercase() || ch.is_ascii_digit() {
            // Atom (nullary constructor)
            let name = parse_identifier(input, pos)?;
            let sym = self.symbols.intern(&name);
            Ok(self.terms.app0(sym))
        } else {
            Err(ParseError {
                message: format!("Unexpected character: '{}'", ch),
                position: *pos,
            })
        }
    }

    /// Parse a rule: `lhs -> rhs`
    pub fn parse_rule(&mut self, input: &str) -> Result<NF<B::Constraint>, ParseError> {
        let mut pos = 0;
        let rule = self.parse_rule_inner(input, &mut pos)?;
        skip_whitespace(input, &mut pos);
        if pos < input.len() {
            return Err(ParseError {
                message: "Unexpected characters after rule".to_string(),
                position: pos,
            });
        }
        Ok(rule)
    }

    /// Parse a rule, returning an NF.
    fn parse_rule_inner(
        &mut self,
        input: &str,
        pos: &mut usize,
    ) -> Result<NF<B::Constraint>, ParseError> {
        let mut var_map: HashMap<String, u32> = HashMap::new();
        let mut var_order: Vec<u32> = Vec::new();

        // Parse LHS
        let lhs = self.parse_term_inner(input, pos, &mut var_map, &mut var_order)?;

        // Optional constraint block between lhs and arrow.
        skip_whitespace(input, pos);
        let constraint = if *pos < input.len() && peek_char(input, *pos) == Some('{') {
            self.parse_constraint_block(input, pos, &mut var_map, &mut var_order)?
        } else {
            self.constraints.empty_constraint()
        };

        // Expect ->
        skip_whitespace(input, pos);
        if !input[*pos..].starts_with("->") {
            return Err(ParseError {
                message: "Expected '->'".to_string(),
                position: *pos,
            });
        }
        *pos += 2;

        // Parse RHS with the same var_map (to share variables)
        let rhs = self.parse_term_inner(input, pos, &mut var_map, &mut var_order)?;

        Ok(NF::factor(lhs, rhs, constraint, &mut self.terms))
    }

    pub fn parse_theory_def(&mut self, input: &str) -> Result<TheorySummary, ParseError> {
        self.constraints
            .parse_theory_def(input, &mut self.symbols, &mut self.terms)
    }

    fn parse_constraint_block(
        &mut self,
        input: &str,
        pos: &mut usize,
        var_map: &mut HashMap<String, u32>,
        var_order: &mut Vec<u32>,
    ) -> Result<B::Constraint, ParseError> {
        if peek_char(input, *pos) != Some('{') {
            return Err(ParseError {
                message: "Expected '{' to start constraint block".to_string(),
                position: *pos,
            });
        }
        *pos += 1;

        let mut calls = Vec::new();
        loop {
            skip_whitespace(input, pos);
            if *pos >= input.len() {
                return Err(ParseError {
                    message: "Unterminated constraint block".to_string(),
                    position: *pos,
                });
            }
            if peek_char(input, *pos) == Some('}') {
                *pos += 1;
                break;
            }

            let call_pos = *pos;
            let (name, args) = self.parse_constraint_call(input, pos, var_map, var_order)?;
            calls.push(ConstraintCall {
                name,
                args,
                position: call_pos,
            });

            skip_whitespace(input, pos);
            if *pos >= input.len() {
                return Err(ParseError {
                    message: "Unterminated constraint block".to_string(),
                    position: *pos,
                });
            }
            match peek_char(input, *pos).unwrap() {
                ',' => {
                    *pos += 1;
                }
                '}' => {
                    *pos += 1;
                    break;
                }
                other => {
                    return Err(ParseError {
                        message: format!("Expected ',' or '}}', found '{}'", other),
                        position: *pos,
                    });
                }
            }
        }

        self.constraints.build_constraint(calls, &mut self.terms)
    }

    fn parse_constraint_call(
        &self,
        input: &str,
        pos: &mut usize,
        var_map: &mut HashMap<String, u32>,
        var_order: &mut Vec<u32>,
    ) -> Result<(String, Vec<TermId>), ParseError> {
        skip_whitespace(input, pos);
        if *pos >= input.len() {
            return Err(ParseError {
                message: "Unexpected end of input".to_string(),
                position: *pos,
            });
        }

        if peek_char(input, *pos) == Some('(') {
            *pos += 1;
            skip_whitespace(input, pos);
            let name = parse_identifier(input, pos)?;
            let mut args = Vec::new();
            loop {
                skip_whitespace(input, pos);
                if *pos >= input.len() {
                    return Err(ParseError {
                        message: "Unclosed constraint term".to_string(),
                        position: *pos,
                    });
                }
                if peek_char(input, *pos).unwrap() == ')' {
                    *pos += 1;
                    break;
                }
                let arg = self.parse_term_inner(input, pos, var_map, var_order)?;
                args.push(arg);
            }
            Ok((name, args))
        } else {
            let name = parse_identifier(input, pos)?;
            Ok((name, Vec::new()))
        }
    }

    /// Parse a relation body (the part inside `rel name { ... }`).
    pub fn parse_rel_body(&mut self, input: &str) -> Result<Rel<B::Constraint>, ParseError> {
        let mut pos = 0;
        let rel = self.parse_or_expr(input, &mut pos)?;
        skip_whitespace(input, &mut pos);
        if pos < input.len() {
            return Err(ParseError {
                message: format!(
                    "Unexpected characters after relation body: '{}'",
                    &input[pos..]
                ),
                position: pos,
            });
        }
        Ok(rel)
    }

    /// Parse an Or expression (lowest precedence).
    fn parse_or_expr(
        &mut self,
        input: &str,
        pos: &mut usize,
    ) -> Result<Rel<B::Constraint>, ParseError> {
        self.parse_or_expr_impl(input, pos, None)
    }

    /// Parse an Or expression, optionally stopping at a given character.
    fn parse_or_expr_impl(
        &mut self,
        input: &str,
        pos: &mut usize,
        stop_char: Option<char>,
    ) -> Result<Rel<B::Constraint>, ParseError> {
        let mut left = self.parse_seq_expr_impl(input, pos, stop_char)?;

        loop {
            skip_whitespace(input, pos);
            if *pos >= input.len() {
                break;
            }
            let ch = peek_char(input, *pos).unwrap();
            if stop_char == Some(ch) || ch != '|' {
                break;
            }
            *pos += 1;
            let right = self.parse_seq_expr_impl(input, pos, stop_char)?;
            left = Rel::Or(Arc::new(left), Arc::new(right));
        }

        Ok(left)
    }

    /// Parse a Seq expression, optionally stopping at a given character.
    fn parse_seq_expr_impl(
        &mut self,
        input: &str,
        pos: &mut usize,
        stop_char: Option<char>,
    ) -> Result<Rel<B::Constraint>, ParseError> {
        let mut factors: Vec<Arc<Rel<B::Constraint>>> = Vec::new();
        factors.push(Arc::new(self.parse_and_expr_impl(input, pos, stop_char)?));

        loop {
            skip_whitespace(input, pos);
            if *pos >= input.len() {
                break;
            }
            let ch = peek_char(input, *pos).unwrap();
            if stop_char == Some(ch) || ch == '|' || ch != ';' {
                break;
            }
            *pos += 1;
            factors.push(Arc::new(self.parse_and_expr_impl(input, pos, stop_char)?));
        }

        if factors.len() == 1 {
            Ok(unwrap_or_clone(factors.pop().unwrap()))
        } else {
            Ok(Rel::Seq(Arc::from(factors)))
        }
    }

    /// Parse an And expression, optionally stopping at a given character.
    fn parse_and_expr_impl(
        &mut self,
        input: &str,
        pos: &mut usize,
        stop_char: Option<char>,
    ) -> Result<Rel<B::Constraint>, ParseError> {
        let mut left = self.parse_primary_impl(input, pos, stop_char)?;

        loop {
            skip_whitespace(input, pos);
            if *pos >= input.len() {
                break;
            }
            let ch = peek_char(input, *pos).unwrap();
            if stop_char == Some(ch) || ch == '|' || ch == ';' || ch != '&' {
                break;
            }
            *pos += 1;
            let right = self.parse_primary_impl(input, pos, stop_char)?;
            left = Rel::And(Arc::new(left), Arc::new(right));
        }

        Ok(left)
    }

    /// Parse a primary expression (rule, call, or bracketed expr).
    fn parse_primary_impl(
        &mut self,
        input: &str,
        pos: &mut usize,
        stop_char: Option<char>,
    ) -> Result<Rel<B::Constraint>, ParseError> {
        skip_whitespace(input, pos);

        if *pos >= input.len() {
            return Err(ParseError {
                message: "Unexpected end of input".to_string(),
                position: *pos,
            });
        }

        let ch = peek_char(input, *pos).unwrap();

        if stop_char == Some(ch) {
            return Err(ParseError {
                message: format!("Unexpected '{}'", ch),
                position: *pos,
            });
        }

        if ch == '[' {
            // Bracketed sequence
            *pos += 1;
            let inner = self.parse_or_expr_impl(input, pos, Some(']'))?;
            skip_whitespace(input, pos);
            if *pos >= input.len() || peek_char(input, *pos).unwrap() != ']' {
                return Err(ParseError {
                    message: "Expected ']'".to_string(),
                    position: *pos,
                });
            }
            *pos += 1;
            Ok(inner)
        } else if ch == '@' {
            *pos += 1;
            let mut var_map: HashMap<String, u32> = HashMap::new();
            let mut var_order: Vec<u32> = Vec::new();
            let term = self.parse_term_inner(input, pos, &mut var_map, &mut var_order)?;
            let nf = NF::factor(
                term,
                term,
                self.constraints.empty_constraint(),
                &mut self.terms,
            );
            Ok(Rel::Atom(Arc::new(nf)))
        } else if ch == '$' || ch == '(' {
            // Rule starting with term
            let rule = self.parse_rule_inner(input, pos)?;
            Ok(Rel::Atom(Arc::new(rule)))
        } else if ch.is_ascii_lowercase() {
            // Could be atom (start of rule) or relation call
            let start_pos = *pos;
            let name = parse_identifier(input, pos)?;
            skip_whitespace(input, pos);

            // Check if this is followed by -> (making it a rule starting with an atom)
            if *pos < input.len() && input[*pos..].starts_with("->") {
                // It's a rule: restore position and parse as rule
                *pos = start_pos;
                let rule = self.parse_rule_inner(input, pos)?;
                Ok(Rel::Atom(Arc::new(rule)))
            } else {
                // It's a relation call
                if let Some(&rel_id) = self.relations.get(&name) {
                    Ok(Rel::Call(rel_id))
                } else {
                    // Unknown relation - allocate a new RelId
                    // This will be resolved when we parse the relation definition
                    let rel_id = self.next_rel_id;
                    self.next_rel_id += 1;
                    self.relations.insert(name, rel_id);
                    Ok(Rel::Call(rel_id))
                }
            }
        } else {
            Err(ParseError {
                message: format!("Unexpected character in primary: '{}'", ch),
                position: *pos,
            })
        }
    }

    /// Parse a complete relation definition.
    pub fn parse_rel_def(
        &mut self,
        input: &str,
    ) -> Result<(String, Rel<B::Constraint>), ParseError> {
        let mut pos = 0;
        skip_whitespace(input, &mut pos);

        // Expect 'rel'
        if !input[pos..].starts_with("rel") {
            return Err(ParseError {
                message: "Expected 'rel' keyword".to_string(),
                position: pos,
            });
        }
        pos += 3;

        // Parse name
        skip_whitespace(input, &mut pos);
        let name = parse_identifier(input, &mut pos)?;

        // Register the relation name if not already registered
        let rel_id = if let Some(&id) = self.relations.get(&name) {
            id
        } else {
            let id = self.next_rel_id;
            self.next_rel_id += 1;
            self.relations.insert(name.clone(), id);
            id
        };

        // Expect '{'
        skip_whitespace(input, &mut pos);
        if pos >= input.len() || peek_char(input, pos).unwrap() != '{' {
            return Err(ParseError {
                message: "Expected '{'".to_string(),
                position: pos,
            });
        }
        pos += 1;

        // Parse body
        let body = self.parse_rel_body_until_brace(input, &mut pos)?;

        // Expect '}'
        skip_whitespace(input, &mut pos);
        if pos >= input.len() || peek_char(input, pos).unwrap() != '}' {
            return Err(ParseError {
                message: "Expected '}'".to_string(),
                position: pos,
            });
        }
        // Wrap in Fix to enable recursion
        let rel = Rel::Fix(rel_id, Arc::new(body));

        Ok((name, rel))
    }

    /// Parse relation body until we hit a closing brace.
    fn parse_rel_body_until_brace(
        &mut self,
        input: &str,
        pos: &mut usize,
    ) -> Result<Rel<B::Constraint>, ParseError> {
        self.parse_or_expr_impl(input, pos, Some('}'))
    }
}

impl Parser<ChrConstraintBuilder> {
    pub fn with_chr() -> Self {
        Parser::with_builder(ChrConstraintBuilder::new())
    }
}

impl Default for Parser<NoConstraintBuilder> {
    fn default() -> Self {
        Self::new()
    }
}

fn peek_char(input: &str, pos: usize) -> Option<char> {
    input.as_bytes().get(pos).copied().map(|byte| byte as char)
}

fn unwrap_or_clone<T: Clone>(arc: Arc<T>) -> T {
    Arc::try_unwrap(arc).unwrap_or_else(|arc| (*arc).clone())
}

/// Skip whitespace and comments.
fn skip_whitespace(input: &str, pos: &mut usize) {
    while *pos < input.len() {
        let ch = peek_char(input, *pos).unwrap();
        if ch.is_ascii_whitespace() {
            *pos += 1;
        } else if ch == '#' {
            // Comment - skip to end of line
            while *pos < input.len() && peek_char(input, *pos).unwrap() != '\n' {
                *pos += 1;
            }
        } else {
            break;
        }
    }
}

fn parse_chr_theory(
    input: &str,
    builder: &mut ChrProgramBuilder<NoTheory>,
    symbols: &mut SymbolStore,
    terms: &mut TermStore,
) -> Result<TheorySummary, ParseError> {
    let mut pos = 0;
    skip_whitespace(input, &mut pos);
    if !input[pos..].starts_with("theory") {
        return Err(ParseError {
            message: "Expected 'theory' keyword".to_string(),
            position: pos,
        });
    }
    pos += "theory".len();
    skip_whitespace(input, &mut pos);
    let name = parse_identifier(input, &mut pos)?;

    skip_whitespace(input, &mut pos);
    if peek_char(input, pos) != Some('{') {
        return Err(ParseError {
            message: "Expected '{'".to_string(),
            position: pos,
        });
    }
    pos += 1;

    let body_start = pos;
    let mut depth = 1;
    while pos < input.len() {
        match peek_char(input, pos).unwrap() {
            '{' => depth += 1,
            '}' => {
                depth -= 1;
                if depth == 0 {
                    break;
                }
            }
            _ => {}
        }
        pos += 1;
    }
    if depth != 0 {
        return Err(ParseError {
            message: "Unterminated theory block".to_string(),
            position: pos,
        });
    }
    let body_end = pos;
    let body = &input[body_start..body_end];

    let mut predicates = 0usize;
    let mut rules = 0usize;

    for raw_line in body.lines() {
        let line = match raw_line.split_once('#') {
            Some((before, _)) => before.trim(),
            None => raw_line.trim(),
        };
        if line.is_empty() {
            continue;
        }
        let line = line.strip_suffix('.').unwrap_or(line).trim();
        if line.starts_with("constraint ") {
            let decl = line["constraint".len()..].trim();
            let (pred, arity) = decl.split_once('/').ok_or_else(|| ParseError {
                message: "Expected constraint declaration like name/arity".to_string(),
                position: 0,
            })?;
            let pred = pred.trim();
            let arity: u8 = arity.trim().parse().map_err(|_| ParseError {
                message: "Invalid constraint arity".to_string(),
                position: 0,
            })?;
            if builder.pred_id(pred).is_some() {
                return Err(ParseError {
                    message: format!("Duplicate constraint predicate '{}'", pred),
                    position: 0,
                });
            }
            builder.pred(pred, arity, Vec::new());
            predicates += 1;
            continue;
        }

        parse_chr_rule_line(line, builder, symbols, terms)?;
        rules += 1;
    }

    Ok(TheorySummary {
        name,
        predicates,
        rules,
    })
}

fn parse_chr_rule_line(
    line: &str,
    builder: &mut ChrProgramBuilder<NoTheory>,
    symbols: &mut SymbolStore,
    terms: &mut TermStore,
) -> Result<(), ParseError> {
    let op = if let Some(idx) = find_top_level_token(line, "<=>") {
        (idx, "<=>")
    } else if let Some(idx) = find_top_level_token(line, "==>") {
        (idx, "==>")
    } else {
        return Err(ParseError {
            message: "Expected '<=>' or '==>' in CHR rule".to_string(),
            position: 0,
        });
    };

    let (lhs, rhs) = line.split_at(op.0);
    let rhs = rhs[op.1.len()..].trim();
    let lhs = lhs.trim();

    let (kept, removed) = match op.1 {
        "==>" => (lhs, ""),
        "<=>" => {
            if let Some(idx) = find_top_level_token(lhs, "\\") {
                let (k, r) = lhs.split_at(idx);
                (k.trim(), r[1..].trim())
            } else {
                ("", lhs)
            }
        }
        _ => ("", ""),
    };

    if op.1 == "==>" && find_top_level_token(lhs, "\\").is_some() {
        return Err(ParseError {
            message: "Propagation rules cannot use \\".to_string(),
            position: 0,
        });
    }

    let mut rvars = HashMap::new();
    let kept_heads = parse_chr_head_list(kept, builder, symbols, &mut rvars)?;
    let removed_heads = parse_chr_head_list(removed, builder, symbols, &mut rvars)?;
    let (guard_src, body_src) = if let Some(idx) = find_top_level_token(rhs, "|") {
        let (g, b) = rhs.split_at(idx);
        (g.trim(), b[1..].trim())
    } else {
        ("", rhs)
    };
    if !guard_src.is_empty() && body_src.is_empty() {
        return Err(ParseError {
            message: "CHR guard must be followed by a body".to_string(),
            position: 0,
        });
    }

    let guard = parse_chr_guard(guard_src, builder, symbols, terms, &rvars)?;
    let body = parse_chr_body(body_src, builder, symbols, &mut rvars)?;

    builder.rule(kept_heads, removed_heads, guard, body, 0);
    Ok(())
}

fn parse_chr_head_list(
    input: &str,
    builder: &mut ChrProgramBuilder<NoTheory>,
    symbols: &mut SymbolStore,
    rvars: &mut HashMap<String, RVar>,
) -> Result<Vec<HeadPat>, ParseError> {
    let input = input.trim();
    if input.is_empty() {
        return Ok(Vec::new());
    }
    let parts = split_top_level_commas(input);
    let mut heads = Vec::new();
    for part in parts {
        let (pred, args) = parse_chr_constraint(part, builder, symbols, rvars)?;
        heads.push(HeadPat::new(pred, args));
    }
    Ok(heads)
}

fn parse_chr_body(
    input: &str,
    builder: &mut ChrProgramBuilder<NoTheory>,
    symbols: &mut SymbolStore,
    rvars: &mut HashMap<String, RVar>,
) -> Result<BodyProg, ParseError> {
    let input = input.trim();
    if input.is_empty() || input == "." || input == "true" {
        return Ok(BodyProg::new(Vec::new()));
    }
    if input == "fail" {
        return Ok(BodyProg::new(vec![BodyInstr::Fail]));
    }

    let parts = split_top_level_commas(input);
    let mut instrs = Vec::new();
    for part in parts {
        let (pred, args) = parse_chr_constraint(part, builder, symbols, rvars)?;
        let arg_exprs: Vec<ArgExpr> = args.into_iter().map(ArgExpr::Pat).collect();
        instrs.push(BodyInstr::AddChr {
            pred,
            args: arg_exprs.into_boxed_slice(),
        });
    }
    Ok(BodyProg::new(instrs))
}

fn parse_chr_guard(
    input: &str,
    builder: &mut ChrProgramBuilder<NoTheory>,
    symbols: &mut SymbolStore,
    terms: &mut TermStore,
    rvars: &HashMap<String, RVar>,
) -> Result<GuardProg, ParseError> {
    let input = input.trim();
    if input.is_empty() || input == "." || input == "true" {
        return Ok(GuardProg::empty());
    }

    let parts = split_top_level_commas(input);
    let mut instrs = Vec::new();
    for part in parts {
        instrs.push(parse_chr_guard_call(part, builder, symbols, terms, rvars)?);
    }
    Ok(GuardProg::new(instrs))
}

fn parse_chr_guard_call(
    input: &str,
    builder: &mut ChrProgramBuilder<NoTheory>,
    symbols: &mut SymbolStore,
    terms: &mut TermStore,
    rvars: &HashMap<String, RVar>,
) -> Result<GuardInstr, ParseError> {
    let mut pos = 0;
    skip_whitespace(input, &mut pos);
    if peek_char(input, pos) != Some('(') {
        return Err(ParseError {
            message: "Expected guard call like (eq $x z)".to_string(),
            position: pos,
        });
    }
    pos += 1;
    skip_whitespace(input, &mut pos);
    let name = parse_identifier(input, &mut pos)?;

    let instr = match name.as_str() {
        "eq" | "neq" => {
            let left = parse_chr_guard_val(input, &mut pos, symbols, terms, rvars)?;
            let right = parse_chr_guard_val(input, &mut pos, symbols, terms, rvars)?;
            skip_whitespace(input, &mut pos);
            if peek_char(input, pos) != Some(')') {
                return Err(ParseError {
                    message: "Expected ')' after guard arguments".to_string(),
                    position: pos,
                });
            }
            pos += 1;
            if name == "eq" {
                GuardInstr::Eq(left, right)
            } else {
                GuardInstr::Neq(left, right)
            }
        }
        "top" => {
            let target = parse_chr_guard_val(input, &mut pos, symbols, terms, rvars)?;
            skip_whitespace(input, &mut pos);
            let functor = parse_identifier(input, &mut pos)?;
            skip_whitespace(input, &mut pos);
            let arity_str = parse_identifier(input, &mut pos)?;
            let arity: u8 = arity_str.parse().map_err(|_| ParseError {
                message: "Invalid arity in top guard".to_string(),
                position: pos,
            })?;
            skip_whitespace(input, &mut pos);
            if peek_char(input, pos) != Some(')') {
                return Err(ParseError {
                    message: "Expected ')' after guard arguments".to_string(),
                    position: pos,
                });
            }
            pos += 1;
            GuardInstr::TopFunctor {
                t: target,
                f: symbols.intern(&functor),
                arity,
            }
        }
        "match" => {
            let pat = parse_chr_pat_term_bound(input, &mut pos, builder, symbols, rvars)?;
            let target = parse_chr_guard_val(input, &mut pos, symbols, terms, rvars)?;
            skip_whitespace(input, &mut pos);
            if peek_char(input, pos) != Some(')') {
                return Err(ParseError {
                    message: "Expected ')' after guard arguments".to_string(),
                    position: pos,
                });
            }
            pos += 1;
            GuardInstr::MatchPat { pat, t: target }
        }
        _ => {
            return Err(ParseError {
                message: format!("Unknown guard predicate '{}'", name),
                position: pos,
            });
        }
    };

    skip_whitespace(input, &mut pos);
    if pos < input.len() {
        return Err(ParseError {
            message: "Unexpected trailing characters in guard".to_string(),
            position: pos,
        });
    }
    Ok(instr)
}

fn parse_chr_guard_val(
    input: &str,
    pos: &mut usize,
    symbols: &mut SymbolStore,
    terms: &mut TermStore,
    rvars: &HashMap<String, RVar>,
) -> Result<GVal, ParseError> {
    skip_whitespace(input, pos);
    if *pos >= input.len() {
        return Err(ParseError {
            message: "Unexpected end of input".to_string(),
            position: *pos,
        });
    }
    let ch = peek_char(input, *pos).unwrap();
    if ch == '$' {
        *pos += 1;
        let name = parse_identifier(input, pos)?;
        let rv = rvars.get(&name).ok_or_else(|| ParseError {
            message: format!("Guard variable '${}' must be bound by a head", name),
            position: *pos,
        })?;
        Ok(GVal::RVar(*rv))
    } else {
        let term = parse_chr_const_term(input, pos, symbols, terms)?;
        Ok(GVal::Const(term))
    }
}

fn parse_chr_const_term(
    input: &str,
    pos: &mut usize,
    symbols: &mut SymbolStore,
    terms: &mut TermStore,
) -> Result<TermId, ParseError> {
    skip_whitespace(input, pos);
    if *pos >= input.len() {
        return Err(ParseError {
            message: "Unexpected end of input".to_string(),
            position: *pos,
        });
    }
    let ch = peek_char(input, *pos).unwrap();
    if ch == '$' {
        return Err(ParseError {
            message: "Guard constants cannot include rule variables".to_string(),
            position: *pos,
        });
    }
    if ch == '(' {
        *pos += 1;
        skip_whitespace(input, pos);
        let functor = parse_identifier(input, pos)?;
        let func = symbols.intern(&functor);
        let mut kids: SmallVec<[TermId; 4]> = SmallVec::new();
        loop {
            skip_whitespace(input, pos);
            if *pos >= input.len() {
                return Err(ParseError {
                    message: "Unclosed parenthesis".to_string(),
                    position: *pos,
                });
            }
            if peek_char(input, *pos).unwrap() == ')' {
                *pos += 1;
                break;
            }
            kids.push(parse_chr_const_term(input, pos, symbols, terms)?);
        }
        Ok(terms.app(func, kids))
    } else if ch.is_ascii_lowercase() || ch.is_ascii_digit() {
        let name = parse_identifier(input, pos)?;
        let func = symbols.intern(&name);
        Ok(terms.app0(func))
    } else {
        Err(ParseError {
            message: format!("Unexpected character: '{}'", ch),
            position: *pos,
        })
    }
}

fn parse_chr_constraint(
    input: &str,
    builder: &mut ChrProgramBuilder<NoTheory>,
    symbols: &mut SymbolStore,
    rvars: &mut HashMap<String, RVar>,
) -> Result<(PredId, Vec<PatId>), ParseError> {
    let mut pos = 0;
    skip_whitespace(input, &mut pos);
    let (name, args) = if peek_char(input, pos) == Some('(') {
        pos += 1;
        skip_whitespace(input, &mut pos);
        let name = parse_identifier(input, &mut pos)?;
        let mut args = Vec::new();
        loop {
            skip_whitespace(input, &mut pos);
            if pos >= input.len() {
                return Err(ParseError {
                    message: "Unclosed constraint term".to_string(),
                    position: pos,
                });
            }
            if peek_char(input, pos) == Some(')') {
                pos += 1;
                break;
            }
            args.push(parse_chr_pat_term(
                input, &mut pos, builder, symbols, rvars,
            )?);
        }
        (name, args)
    } else {
        (parse_identifier(input, &mut pos)?, Vec::new())
    };

    skip_whitespace(input, &mut pos);
    if pos < input.len() {
        return Err(ParseError {
            message: "Unexpected trailing characters in constraint".to_string(),
            position: pos,
        });
    }

    let pred = builder.pred_id(&name).ok_or_else(|| ParseError {
        message: format!("Unknown constraint predicate '{}'", name),
        position: 0,
    })?;
    let expected = builder.pred_arity(pred).map(|a| a as usize).unwrap_or(0);
    if args.len() != expected {
        return Err(ParseError {
            message: format!(
                "Constraint '{}' arity {} expects {} args, got {}",
                name,
                expected,
                expected,
                args.len()
            ),
            position: 0,
        });
    }
    Ok((pred, args))
}

/// Mode for parsing CHR pattern terms.
enum PatVarMode<'a> {
    /// Create new variables if not found in the map.
    Create(&'a mut HashMap<String, RVar>),
    /// Only allow existing bound variables (for guards).
    BoundOnly(&'a HashMap<String, RVar>),
}

fn parse_chr_pat_term_impl(
    input: &str,
    pos: &mut usize,
    builder: &mut ChrProgramBuilder<NoTheory>,
    symbols: &mut SymbolStore,
    mode: &mut PatVarMode<'_>,
) -> Result<PatId, ParseError> {
    skip_whitespace(input, pos);
    if *pos >= input.len() {
        return Err(ParseError {
            message: "Unexpected end of input".to_string(),
            position: *pos,
        });
    }
    let ch = peek_char(input, *pos).unwrap();
    if ch == '$' {
        *pos += 1;
        let name = parse_identifier(input, pos)?;
        let rv = match mode {
            PatVarMode::Create(rvars) => {
                let next_id = rvars.len() as u32;
                *rvars.entry(name).or_insert(RVar(next_id))
            }
            PatVarMode::BoundOnly(rvars) => *rvars.get(&name).ok_or_else(|| ParseError {
                message: format!("Guard variable '${}' must be bound by a head", name),
                position: *pos,
            })?,
        };
        Ok(builder.pat_var(rv))
    } else if ch == '(' {
        *pos += 1;
        skip_whitespace(input, pos);
        let functor = parse_identifier(input, pos)?;
        let sym = symbols.intern(&functor);
        let mut kids = Vec::new();
        loop {
            skip_whitespace(input, pos);
            if *pos >= input.len() {
                return Err(ParseError {
                    message: "Unclosed parenthesis".to_string(),
                    position: *pos,
                });
            }
            if peek_char(input, *pos).unwrap() == ')' {
                *pos += 1;
                break;
            }
            kids.push(parse_chr_pat_term_impl(input, pos, builder, symbols, mode)?);
        }
        Ok(builder.pat_app(sym, kids))
    } else if ch.is_ascii_lowercase() || ch.is_ascii_digit() {
        let name = parse_identifier(input, pos)?;
        let sym = symbols.intern(&name);
        Ok(builder.pat_app(sym, Vec::new()))
    } else {
        Err(ParseError {
            message: format!("Unexpected character: '{}'", ch),
            position: *pos,
        })
    }
}

fn parse_chr_pat_term(
    input: &str,
    pos: &mut usize,
    builder: &mut ChrProgramBuilder<NoTheory>,
    symbols: &mut SymbolStore,
    rvars: &mut HashMap<String, RVar>,
) -> Result<PatId, ParseError> {
    parse_chr_pat_term_impl(input, pos, builder, symbols, &mut PatVarMode::Create(rvars))
}

fn parse_chr_pat_term_bound(
    input: &str,
    pos: &mut usize,
    builder: &mut ChrProgramBuilder<NoTheory>,
    symbols: &mut SymbolStore,
    rvars: &HashMap<String, RVar>,
) -> Result<PatId, ParseError> {
    parse_chr_pat_term_impl(
        input,
        pos,
        builder,
        symbols,
        &mut PatVarMode::BoundOnly(rvars),
    )
}

fn split_top_level_commas(input: &str) -> Vec<&str> {
    let mut parts = Vec::new();
    let mut depth = 0i32;
    let mut start = 0usize;
    for (idx, ch) in input.char_indices() {
        match ch {
            '(' => depth += 1,
            ')' => depth -= 1,
            ',' if depth == 0 => {
                parts.push(input[start..idx].trim());
                start = idx + 1;
            }
            _ => {}
        }
    }
    if start < input.len() {
        parts.push(input[start..].trim());
    }
    parts.into_iter().filter(|p| !p.is_empty()).collect()
}

fn find_top_level_token(input: &str, token: &str) -> Option<usize> {
    let mut depth = 0i32;
    let mut idx = 0usize;
    while idx + token.len() <= input.len() {
        let ch = peek_char(input, idx).unwrap();
        if ch == '(' {
            depth += 1;
        } else if ch == ')' {
            depth -= 1;
        }
        if depth == 0 && input[idx..].starts_with(token) {
            return Some(idx);
        }
        idx += 1;
    }
    None
}

/// Parse an identifier (lowercase letters, digits, underscores).
fn parse_identifier(input: &str, pos: &mut usize) -> Result<String, ParseError> {
    let start = *pos;
    while *pos < input.len() {
        let ch = peek_char(input, *pos).unwrap();
        if ch.is_ascii_alphanumeric() || ch == '_' {
            *pos += 1;
        } else {
            break;
        }
    }

    if *pos == start {
        return Err(ParseError {
            message: "Expected identifier".to_string(),
            position: *pos,
        });
    }

    Ok(input[start..*pos].to_string())
}


#[cfg(test)]
mod tests;


// ===== src/queue.rs =====
use crate::nf::NF;
use crossbeam_channel::{Receiver, RecvTimeoutError, Sender, TryRecvError, TrySendError};
use std::collections::HashSet;
use std::hash::Hash;
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::Arc;
use std::sync::Mutex;
use std::time::Duration;

#[derive(Clone, Debug)]
pub struct QueueWaker {
    id: u64,
    epoch: Arc<AtomicU64>,
    tx: Sender<u64>,
}

#[derive(Clone, Debug)]
pub struct BlockedOn {
    waker: QueueWaker,
    epoch: u64,
}

impl QueueWaker {
    pub fn wake(&self) {
        self.epoch.fetch_add(1, Ordering::AcqRel);
        let _ = self.tx.send(self.id);
    }

    pub fn blocked_on(&self) -> BlockedOn {
        BlockedOn {
            waker: self.clone(),
            epoch: self.epoch(),
        }
    }

    pub fn epoch(&self) -> u64 {
        self.epoch.load(Ordering::Acquire)
    }

    pub fn id(&self) -> u64 {
        self.id
    }

    pub(crate) fn noop() -> Self {
        let (tx, _rx) = crossbeam_channel::unbounded();
        QueueWaker {
            id: 0,
            epoch: Arc::new(AtomicU64::new(0)),
            tx,
        }
    }
}

impl BlockedOn {
    pub fn id(&self) -> u64 {
        self.waker.id()
    }

    pub fn is_stale(&self) -> bool {
        self.epoch != self.waker.epoch()
    }

    pub fn waker(&self) -> QueueWaker {
        self.waker.clone()
    }
}

#[derive(Debug)]
pub struct WakeHub {
    next_id: AtomicU64,
    tx: Sender<u64>,
}

impl WakeHub {
    pub fn new() -> (Arc<Self>, crossbeam_channel::Receiver<u64>) {
        let (tx, rx) = crossbeam_channel::unbounded();
        let hub = Arc::new(WakeHub {
            next_id: AtomicU64::new(1),
            tx,
        });
        (hub, rx)
    }

    pub fn waker(&self) -> QueueWaker {
        let id = self.next_id.fetch_add(1, Ordering::AcqRel);
        QueueWaker {
            id,
            epoch: Arc::new(AtomicU64::new(0)),
            tx: self.tx.clone(),
        }
    }
}

#[derive(Clone)]
pub struct AnswerSender<C> {
    inner: Sender<NF<C>>,
    waker: QueueWaker,
}

pub struct AnswerReceiver<C> {
    inner: Receiver<NF<C>>,
    waker: QueueWaker,
}

impl<C> Drop for AnswerSender<C> {
    fn drop(&mut self) {
        self.waker.wake();
    }
}

impl<C> Drop for AnswerReceiver<C> {
    fn drop(&mut self) {
        self.waker.wake();
    }
}

impl<C> std::fmt::Debug for AnswerSender<C> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("AnswerSender").finish()
    }
}

impl<C> std::fmt::Debug for AnswerReceiver<C> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("AnswerReceiver").finish()
    }
}

pub struct AnswerQueue;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SinkResult {
    Accepted,
    Full,
    Closed,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum RecvResult<C> {
    Item(NF<C>),
    Empty,
    Closed,
}

impl AnswerQueue {
    pub fn bounded_with_waker<C>(
        capacity: usize,
        waker: QueueWaker,
    ) -> (AnswerSender<C>, AnswerReceiver<C>) {
        let (tx, rx) = crossbeam_channel::bounded(capacity);
        let sender = AnswerSender {
            inner: tx,
            waker: waker.clone(),
        };
        let receiver = AnswerReceiver { inner: rx, waker };
        (sender, receiver)
    }

    #[cfg(test)]
    pub fn bounded<C>(capacity: usize) -> (AnswerSender<C>, AnswerReceiver<C>) {
        Self::bounded_with_waker(capacity, QueueWaker::noop())
    }
}

impl<C> AnswerSender<C> {
    pub fn try_send(&self, nf: NF<C>) -> SinkResult {
        match self.inner.try_send(nf) {
            Ok(()) => {
                self.waker.wake();
                SinkResult::Accepted
            }
            Err(TrySendError::Full(_)) => SinkResult::Full,
            Err(TrySendError::Disconnected(_)) => SinkResult::Closed,
        }
    }

    pub fn blocked_on(&self) -> BlockedOn {
        self.waker.blocked_on()
    }
}

impl<C> AnswerReceiver<C> {
    pub fn recv_timeout(&self, timeout: Duration) -> RecvResult<C> {
        match self.inner.recv_timeout(timeout) {
            Ok(nf) => {
                self.waker.wake();
                RecvResult::Item(nf)
            }
            Err(RecvTimeoutError::Timeout) => RecvResult::Empty,
            Err(RecvTimeoutError::Disconnected) => RecvResult::Closed,
        }
    }

    pub fn try_recv(&self) -> RecvResult<C> {
        match self.inner.try_recv() {
            Ok(nf) => {
                self.waker.wake();
                RecvResult::Item(nf)
            }
            Err(TryRecvError::Empty) => RecvResult::Empty,
            Err(TryRecvError::Disconnected) => RecvResult::Closed,
        }
    }

    pub fn blocked_on(&self) -> BlockedOn {
        self.waker.blocked_on()
    }
}

pub enum AnswerSink<C> {
    Queue(AnswerSender<C>),
    DedupQueue {
        sender: AnswerSender<C>,
        seen: Arc<Mutex<HashSet<NF<C>>>>,
    },
    #[cfg(test)]
    Collector(Arc<Mutex<Vec<NF<C>>>>),
}

impl<C: Clone + Eq + Hash> AnswerSink<C> {
    pub fn push(&mut self, nf: NF<C>) -> SinkResult {
        match self {
            AnswerSink::Queue(sender) => sender.try_send(nf),
            AnswerSink::DedupQueue { sender, seen } => match seen.lock() {
                Ok(mut guard) => {
                    if guard.contains(&nf) {
                        return SinkResult::Accepted;
                    }
                    match sender.try_send(nf.clone()) {
                        SinkResult::Accepted => {
                            guard.insert(nf);
                            SinkResult::Accepted
                        }
                        other => other,
                    }
                }
                Err(_) => SinkResult::Closed,
            },
            #[cfg(test)]
            AnswerSink::Collector(out) => match out.lock() {
                Ok(mut guard) => {
                    guard.push(nf);
                    SinkResult::Accepted
                }
                Err(_) => SinkResult::Closed,
            },
        }
    }

    pub fn blocked_on(&self) -> Option<BlockedOn> {
        match self {
            AnswerSink::Queue(sender) => Some(sender.blocked_on()),
            AnswerSink::DedupQueue { sender, .. } => Some(sender.blocked_on()),
            #[cfg(test)]
            AnswerSink::Collector(_) => None,
        }
    }
}


#[cfg(test)]
mod tests;


// ===== src/rel.rs =====
//! Rel IR - Relation expressions for the direction-agnostic evaluation model.
//!
//! Rel replaces the old Goal enum with a more principled representation
//! that supports structural dual operations.

use crate::constraint::ConstraintOps;
use crate::kernel::dual_nf;
use crate::nf::NF;
use crate::term::TermStore;
use std::sync::Arc;

/// Identifier for recursive relation bindings (Fix/Call).
pub type RelId = u32;

/// Relation expression - the IR for evaluation.
///
/// Each variant represents a different way to combine relations:
/// - `Zero`: empty relation (always fails)
/// - `Atom(nf)`: single span (atomic relation from NF)
/// - `Or(a, b)`: union/disjunction
/// - `And(a, b)`: intersection/conjunction
/// - `Seq(xs)`: n-ary sequential composition
/// - `Fix(id, body)`: recursive binding (μ binder)
/// - `Call(id)`: recursive reference
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Rel<C> {
    /// Empty relation - always fails.
    Zero,
    /// Atomic relation from a single NF span.
    Atom(Arc<NF<C>>),
    /// Union (disjunction) of two relations.
    Or(Arc<Rel<C>>, Arc<Rel<C>>),
    /// Intersection (conjunction) of two relations.
    And(Arc<Rel<C>>, Arc<Rel<C>>),
    /// Sequential composition of relations.
    Seq(Arc<[Arc<Rel<C>>]>),
    /// Recursive binding: Fix(id, body) binds `id` to be used in `body`.
    Fix(RelId, Arc<Rel<C>>),
    /// Recursive reference to a Fix-bound relation.
    Call(RelId),
}

/// Compute the structural dual of a relation.
///
/// The dual of a relation R is its converse relation R^(-1).
/// If R relates input to output, dual(R) relates output to input.
///
/// Properties:
/// - dual(dual(r)) == r (involution)
/// - dual(Zero) = Zero
/// - dual(Atom(nf)) = Atom(dual_nf(nf, terms))
/// - dual(Or(a,b)) = Or(dual(a), dual(b)) (no swap)
/// - dual(And(a,b)) = And(dual(a), dual(b)) (no swap)
/// - dual(Seq([x0..xn])) = Seq([dual(xn)..dual(x0)]) (REVERSE and dual)
/// - dual(Fix(id, body)) = Fix(id, dual(body))
/// - dual(Call(id)) = Call(id)
pub fn dual<C: ConstraintOps>(rel: &Rel<C>, terms: &mut TermStore) -> Rel<C> {
    match rel {
        Rel::Zero => Rel::Zero,

        Rel::Atom(nf) => Rel::Atom(Arc::new(dual_nf(nf, terms))),

        Rel::Or(a, b) => Rel::Or(Arc::new(dual(a, terms)), Arc::new(dual(b, terms))),

        Rel::And(a, b) => Rel::And(Arc::new(dual(a, terms)), Arc::new(dual(b, terms))),

        Rel::Seq(xs) => {
            // CRITICAL: Reverse the sequence AND dual each element
            let dualed: Vec<Arc<Rel<C>>> = xs
                .iter()
                .rev() // Reverse order
                .map(|x| Arc::new(dual(x, terms))) // Dual each element
                .collect();
            Rel::Seq(Arc::from(dualed))
        }

        Rel::Fix(id, body) => Rel::Fix(*id, Arc::new(dual(body, terms))),

        Rel::Call(id) => Rel::Call(*id),
    }
}


#[cfg(test)]
mod tests;


// ===== src/subst.rs =====
use crate::term::{Term, TermId, TermStore};
use smallvec::SmallVec;

/// A substitution maps variable indices to terms.
/// Uses Vec<Option<TermId>> for dense local variables (0..n).
/// None means the variable is unbound (maps to itself).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Subst {
    bindings: Vec<Option<TermId>>,
}

impl Subst {
    /// Create an empty substitution.
    pub fn new() -> Self {
        Self {
            bindings: Vec::new(),
        }
    }

    /// Create a substitution with capacity for n variables.
    pub fn with_capacity(n: usize) -> Self {
        Self {
            bindings: vec![None; n],
        }
    }

    /// Bind a variable to a term.
    /// Extends the substitution if needed.
    pub fn bind(&mut self, var: u32, term: TermId) {
        let idx = var as usize;
        if idx >= self.bindings.len() {
            self.bindings.resize(idx + 1, None);
        }
        self.bindings[idx] = Some(term);
    }

    /// Get the binding for a variable, if any.
    pub fn get(&self, var: u32) -> Option<TermId> {
        let idx = var as usize;
        if idx < self.bindings.len() {
            self.bindings[idx]
        } else {
            None
        }
    }

    /// Check if a variable is bound.
    pub fn is_bound(&self, var: u32) -> bool {
        self.get(var).is_some()
    }

    /// Check if the substitution is empty (no bindings).
    pub fn is_empty(&self) -> bool {
        self.bindings.iter().all(|b| b.is_none())
    }

    /// Number of bound variables.
    pub fn len(&self) -> usize {
        self.bindings.iter().filter(|b| b.is_some()).count()
    }

    /// Iterator over (var_index, term_id) pairs for bound variables.
    pub fn iter(&self) -> impl Iterator<Item = (u32, TermId)> + '_ {
        self.bindings
            .iter()
            .enumerate()
            .filter_map(|(i, opt)| opt.map(|tid| (i as u32, tid)))
    }
}

impl Default for Subst {
    fn default() -> Self {
        Self::new()
    }
}

/// Apply a substitution to a term, returning a new term.
/// Variables bound in the substitution are replaced by their bound terms.
/// Unbound variables remain as variables.
/// Variable chains are followed iteratively to avoid stack overflow on cycles.
///
/// Uses explicit stack to avoid recursion.
pub fn apply_subst(term: TermId, subst: &Subst, terms: &mut TermStore) -> TermId {
    // Use a worklist to process terms depth-first
    // Stack contains (original term, children_processed)
    // Result stack collects processed terms

    let mut work_stack: Vec<(TermId, bool)> = vec![(term, false)];
    let mut result_stack: Vec<TermId> = Vec::new();
    let mut children_counts: Vec<usize> = Vec::new();

    while let Some((tid, children_done)) = work_stack.pop() {
        if children_done {
            // Children have been processed, now build the result
            let original = terms.resolve(tid);
            match original {
                Some(Term::App(func, children)) => {
                    let n = children.len();
                    let count = children_counts.pop().unwrap();
                    assert_eq!(n, count);

                    // Pop n results from result_stack
                    let new_children: SmallVec<[TermId; 4]> =
                        result_stack.drain(result_stack.len() - n..).collect();

                    let new_term = terms.app(func, new_children);
                    result_stack.push(new_term);
                }
                _ => {
                    // Var or None case already handled in first pass
                    unreachable!("Only App terms should have children_done=true");
                }
            }
        } else {
            // First visit to this term
            match terms.resolve(tid) {
                Some(Term::Var(_)) => {
                    // Follow variable chain iteratively
                    let resolved = resolve_var_chain(tid, subst, terms);
                    match terms.resolve(resolved) {
                        Some(Term::Var(_)) => {
                            // Ended at a variable (unbound or cycle)
                            result_stack.push(resolved);
                        }
                        Some(Term::App(_, children)) => {
                            if children.is_empty() {
                                result_stack.push(resolved);
                            } else {
                                // Need to process this App term
                                work_stack.push((resolved, true));
                                children_counts.push(children.len());
                                for child in children.iter().rev() {
                                    work_stack.push((*child, false));
                                }
                            }
                        }
                        None => {
                            result_stack.push(resolved);
                        }
                    }
                }
                Some(Term::App(_, children)) => {
                    if children.is_empty() {
                        // Nullary app - no children to process
                        result_stack.push(tid);
                    } else {
                        // Push back with children_done=true for later processing
                        work_stack.push((tid, true));
                        children_counts.push(children.len());
                        // Push children (in reverse order so leftmost processed first)
                        for child in children.iter().rev() {
                            work_stack.push((*child, false));
                        }
                    }
                }
                None => {
                    // Invalid term - just keep it
                    result_stack.push(tid);
                }
            }
        }
    }

    assert_eq!(result_stack.len(), 1);
    result_stack.pop().unwrap()
}

/// Follow a chain of variable substitutions until we hit a non-variable
/// or detect a cycle. Returns the final term in the chain.
fn resolve_var_chain(start: TermId, subst: &Subst, terms: &TermStore) -> TermId {
    let mut current = start;
    let mut visited = smallvec::SmallVec::<[u32; 8]>::new();

    loop {
        match terms.resolve(current) {
            Some(Term::Var(idx)) => {
                // Check for cycle
                if visited.contains(&idx) {
                    // Cycle detected - return current variable
                    return current;
                }
                visited.push(idx);

                // Check if bound
                if let Some(bound) = subst.get(idx) {
                    current = bound;
                } else {
                    // Unbound variable - end of chain
                    return current;
                }
            }
            Some(Term::App(_, _)) => {
                // Hit a non-variable term
                return current;
            }
            None => {
                return current;
            }
        }
    }
}


#[cfg(test)]
mod tests;


// ===== src/symbol.rs =====
use lasso::{Spur, ThreadedRodeo};

/// A unique identifier for a functor/constructor symbol.
/// This is an interned string ID for fast equality comparison.
pub type FuncId = Spur;

/// Thread-safe symbol store for interning constructor/functor names.
///
/// Guarantees:
/// - Same string always produces same FuncId
/// - Different strings always produce different FuncIds
/// - FuncId can be resolved back to the original string
pub struct SymbolStore {
    rodeo: ThreadedRodeo,
}

impl SymbolStore {
    /// Create a new empty symbol store.
    pub fn new() -> Self {
        Self {
            rodeo: ThreadedRodeo::new(),
        }
    }

    /// Intern a symbol string, returning its unique FuncId.
    /// If the symbol was already interned, returns the existing FuncId.
    pub fn intern(&self, name: &str) -> FuncId {
        self.rodeo.get_or_intern(name)
    }

    /// Resolve a FuncId back to its string representation.
    /// Returns None if the FuncId was not created by this store.
    pub fn resolve(&self, id: FuncId) -> Option<&str> {
        self.rodeo.try_resolve(&id)
    }

    /// Check if a symbol string has already been interned.
    pub fn contains(&self, name: &str) -> bool {
        self.rodeo.contains(name)
    }

    /// Get the FuncId for a symbol if it exists, without interning.
    pub fn get(&self, name: &str) -> Option<FuncId> {
        self.rodeo.get(name)
    }
}

impl Default for SymbolStore {
    fn default() -> Self {
        Self::new()
    }
}


#[cfg(test)]
mod tests;


// ===== src/term.rs =====
use crate::symbol::{FuncId, SymbolStore};
use hashbrown::HashMap;
use parking_lot::RwLock;
use rustc_hash::FxHasher;
use smallvec::SmallVec;
use std::hash::{Hash, Hasher};
use std::sync::atomic::{AtomicU32, Ordering};

/// Unique identifier for a term in the term store.
/// TermIds are stable and can be compared for equality.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct TermId(u32);

impl TermId {
    /// Get the raw u32 value (for debugging/display).
    pub fn raw(self) -> u32 {
        self.0
    }

    pub(crate) fn from_raw(raw: u32) -> Self {
        TermId(raw)
    }
}

/// A term is either a variable or a function application.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Term {
    /// A variable, identified by its de Bruijn-like index.
    Var(u32),
    /// A function application: functor applied to children.
    App(FuncId, SmallVec<[TermId; 4]>),
}

/// Number of shards for hashcons maps (power of 2 for fast modulo).
const NUM_SHARDS: usize = 16;

/// Thread-safe term store with hashconsing.
///
/// Guarantees:
/// - Structurally equal terms get the same TermId
/// - TermId can be resolved back to the term
/// - All terms (including variables) are hashconsed
pub struct TermStore {
    /// Central storage of all terms, indexed by TermId.
    nodes: RwLock<Vec<Term>>,
    /// Sharded hashcons maps for reducing contention.
    shards: [RwLock<HashMap<Term, TermId>>; NUM_SHARDS],
    /// Counter for generating unique TermIds.
    next_id: AtomicU32,
}

impl TermStore {
    /// Create a new empty term store.
    pub fn new() -> Self {
        // Initialize array of shards
        let shards = std::array::from_fn(|_| RwLock::new(HashMap::new()));
        Self {
            nodes: RwLock::new(Vec::new()),
            shards,
            next_id: AtomicU32::new(0),
        }
    }

    /// Intern a term, returning its TermId.
    /// If the term already exists, returns the existing TermId.
    fn intern(&self, term: Term) -> TermId {
        let shard_idx = Self::shard_index(&term);
        let shard = &self.shards[shard_idx];

        // Fast path: check if term exists (read lock)
        {
            let map = shard.read();
            if let Some(&id) = map.get(&term) {
                return id;
            }
        }

        // Slow path: need to insert (write lock)
        let mut map = shard.write();

        // Double-check after acquiring write lock
        if let Some(&id) = map.get(&term) {
            return id;
        }

        // Allocate new TermId and store term
        let id = TermId(self.next_id.fetch_add(1, Ordering::Relaxed));
        {
            let mut nodes = self.nodes.write();
            // Ensure the vector is large enough
            let idx = id.0 as usize;
            if nodes.len() <= idx {
                nodes.resize(idx + 1, Term::Var(0)); // placeholder
            }
            nodes[idx] = term.clone();
        }
        map.insert(term, id);
        id
    }

    /// Create a variable term.
    /// Variables are hashconsed: same index always returns same TermId.
    pub fn var(&self, index: u32) -> TermId {
        self.intern(Term::Var(index))
    }

    /// Create an application term.
    /// Hashconsed: same functor and children always returns same TermId.
    pub fn app(&self, func: FuncId, children: SmallVec<[TermId; 4]>) -> TermId {
        self.intern(Term::App(func, children))
    }

    /// Create a nullary (0-arity) application.
    pub fn app0(&self, func: FuncId) -> TermId {
        self.app(func, SmallVec::new())
    }

    /// Create a unary (1-arity) application.
    pub fn app1(&self, func: FuncId, child: TermId) -> TermId {
        self.app(func, smallvec::smallvec![child])
    }

    /// Create a binary (2-arity) application.
    pub fn app2(&self, func: FuncId, left: TermId, right: TermId) -> TermId {
        self.app(func, smallvec::smallvec![left, right])
    }

    /// Resolve a TermId to its term.
    /// Returns None if the TermId is invalid.
    pub fn resolve(&self, id: TermId) -> Option<Term> {
        let nodes = self.nodes.read();
        nodes.get(id.0 as usize).cloned()
    }

    /// Check if a term is a variable.
    pub fn is_var(&self, id: TermId) -> Option<u32> {
        match self.resolve(id)? {
            Term::Var(idx) => Some(idx),
            Term::App(_, _) => None,
        }
    }

    /// Check if a term is an application, returning functor and children.
    pub fn is_app(&self, id: TermId) -> Option<(FuncId, SmallVec<[TermId; 4]>)> {
        match self.resolve(id)? {
            Term::Var(_) => None,
            Term::App(f, children) => Some((f, children)),
        }
    }

    /// Get the shard index for a term (for hashconsing distribution).
    fn shard_index(term: &Term) -> usize {
        let mut hasher = FxHasher::default();
        term.hash(&mut hasher);
        (hasher.finish() as usize) % NUM_SHARDS
    }
}

pub fn format_term(
    term: TermId,
    terms: &TermStore,
    symbols: &SymbolStore,
) -> Result<String, String> {
    fn render(
        term: TermId,
        terms: &TermStore,
        symbols: &SymbolStore,
        out: &mut String,
    ) -> Result<(), String> {
        match terms.resolve(term) {
            Some(Term::Var(idx)) => {
                out.push('$');
                out.push_str(&idx.to_string());
                Ok(())
            }
            Some(Term::App(func, children)) => {
                let name = symbols
                    .resolve(func)
                    .ok_or_else(|| format!("Unknown symbol for func id {:?}", func))?;
                if children.is_empty() {
                    out.push_str(name);
                    Ok(())
                } else {
                    out.push('(');
                    out.push_str(name);
                    for child in children.iter() {
                        out.push(' ');
                        render(*child, terms, symbols, out)?;
                    }
                    out.push(')');
                    Ok(())
                }
            }
            None => Err(format!("Unknown term id {:?}", term)),
        }
    }

    let mut out = String::new();
    render(term, terms, symbols, &mut out)?;
    Ok(out)
}

impl Default for TermStore {
    fn default() -> Self {
        Self::new()
    }
}


#[cfg(test)]
mod tests;


// ===== src/unify.rs =====
use crate::subst::Subst;
use crate::term::{Term, TermId, TermStore};
use smallvec::SmallVec;

#[cfg(feature = "tracing")]
use crate::trace::{debug_span, trace};

/// Unify two terms, returning a most general unifier (MGU) if successful.
/// Returns None if the terms cannot be unified.
///
/// Uses an explicit worklist to avoid recursion.
/// Implements occurs-check to prevent infinite terms.
pub fn unify(t1: TermId, t2: TermId, terms: &TermStore) -> Option<Subst> {
    #[cfg(feature = "tracing")]
    let _span = debug_span!("unify", ?t1, ?t2).entered();

    let mut subst = Subst::new();
    let mut worklist: SmallVec<[(TermId, TermId); 32]> = SmallVec::new();
    worklist.push((t1, t2));

    while let Some((a, b)) = worklist.pop() {
        // Dereference variables through the substitution
        let a_deref = deref(a, &subst, terms);
        let b_deref = deref(b, &subst, terms);

        if a_deref == b_deref {
            // Same term - already unified
            continue;
        }

        match (terms.resolve(a_deref), terms.resolve(b_deref)) {
            (Some(Term::Var(idx_a)), Some(Term::Var(idx_b))) => {
                // Both variables - bind one to the other
                // Prefer binding higher-indexed to lower-indexed for consistency
                if idx_a < idx_b {
                    subst.bind(idx_b, a_deref);
                } else {
                    subst.bind(idx_a, b_deref);
                }
            }
            (Some(Term::Var(idx)), Some(Term::App(_, _))) => {
                // Variable vs App - occurs check then bind
                if occurs(idx, b_deref, &subst, terms) {
                    #[cfg(feature = "tracing")]
                    trace!(var = idx, "unify_occurs_check_failed");
                    return None; // Occurs check failed
                }
                subst.bind(idx, b_deref);
            }
            (Some(Term::App(_, _)), Some(Term::Var(idx))) => {
                // App vs Variable - occurs check then bind
                if occurs(idx, a_deref, &subst, terms) {
                    #[cfg(feature = "tracing")]
                    trace!(var = idx, "unify_occurs_check_failed");
                    return None; // Occurs check failed
                }
                subst.bind(idx, a_deref);
            }
            (Some(Term::App(f1, children1)), Some(Term::App(f2, children2))) => {
                // Both Apps - must have same functor and arity
                if f1 != f2 {
                    #[cfg(feature = "tracing")]
                    trace!("unify_functor_mismatch");
                    return None; // Different functors
                }
                if children1.len() != children2.len() {
                    #[cfg(feature = "tracing")]
                    trace!("unify_arity_mismatch");
                    return None; // Different arities
                }
                // Add children pairs to worklist
                for (c1, c2) in children1.iter().zip(children2.iter()) {
                    worklist.push((*c1, *c2));
                }
            }
            _ => {
                // One or both terms are invalid
                #[cfg(feature = "tracing")]
                trace!("unify_invalid_term");
                return None;
            }
        }
    }

    #[cfg(feature = "tracing")]
    trace!(bindings = subst.len(), "unify_success");

    Some(subst)
}

/// Dereference a term through the substitution.
/// If the term is a variable bound in the substitution, follow the chain.
fn deref(term: TermId, subst: &Subst, terms: &TermStore) -> TermId {
    let mut current = term;
    loop {
        match terms.resolve(current) {
            Some(Term::Var(idx)) => {
                if let Some(bound) = subst.get(idx) {
                    current = bound;
                } else {
                    return current;
                }
            }
            _ => return current,
        }
    }
}

/// Occurs check: does variable `var` occur in term `term`?
/// Used to prevent creating infinite (cyclic) terms.
fn occurs(var: u32, term: TermId, subst: &Subst, terms: &TermStore) -> bool {
    let mut stack: SmallVec<[TermId; 16]> = SmallVec::new();
    stack.push(term);

    while let Some(t) = stack.pop() {
        let t_deref = deref(t, subst, terms);
        match terms.resolve(t_deref) {
            Some(Term::Var(idx)) => {
                if idx == var {
                    return true;
                }
            }
            Some(Term::App(_, children)) => {
                for child in children.iter() {
                    stack.push(*child);
                }
            }
            None => {}
        }
    }

    false
}


#[cfg(test)]
mod tests;


// ===== src/work.rs =====
//! Work - Active work items for the evaluation engine.
//!
//! Work represents computations in progress. PipeWork handles
//! sequential composition (Seq) with outside-in boundary fusion.

use crate::constraint::ConstraintOps;
use crate::drop_fresh::DropFresh;
use crate::factors::Factors;
use crate::join::{AndJoiner, JoinStep};
use crate::kernel::{compose_nf, meet_nf};
use crate::nf::NF;
use crate::node::{step_node, Node, NodeStep};
use crate::queue::{
    AnswerQueue, AnswerReceiver, AnswerSender, BlockedOn, QueueWaker, RecvResult, SinkResult,
    WakeHub,
};
use crate::rel::{Rel, RelId};
use crate::term::{TermId, TermStore};
use dashmap::DashMap;
use parking_lot::Mutex;
use smallvec::SmallVec;
use std::collections::{HashSet, VecDeque};
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::Arc;

/// Active work items for evaluation.
#[derive(Clone, Debug)]
pub enum Work<C: ConstraintOps> {
    /// Sequential composition pipeline.
    Pipe(PipeWork<C>),
    /// Conjunction/intersection via fair diagonal join.
    Meet(MeetWork<C>),
    /// N-ary conjunction/intersection via fair diagonal join.
    AndGroup(AndGroup<C>),
    /// Tabled recursive call.
    Fix(FixWork<C>),
    /// Symmetric compose join for sequential composition.
    Compose(ComposeWork<C>),
    /// Receiver for joiner outputs (drives AndGroup producers).
    JoinReceiver(JoinReceiverWork<C>),
    /// Single atomic NF (emits once, then done).
    Atom(NF<C>),
    /// Completed - no more work.
    Done,
}

/// Result of stepping a work item.
#[derive(Clone, Debug)]
pub enum WorkStep<C: ConstraintOps> {
    /// Work exhausted, no answers.
    Done,
    /// Emit an answer, continue with more work.
    Emit(NF<C>, Box<Work<C>>),
    /// Fork into two search branches.
    Split(Box<Node<C>>, Box<Node<C>>),
    /// Continue with modified work.
    More(Box<Work<C>>),
}

/// Call handling mode for PipeWork.
#[derive(Clone, Debug)]
pub enum CallMode<C: ConstraintOps> {
    /// Normal call handling (tabling + producer).
    Normal,
    /// Replay-only for a specific CallKey (used during producer iterations).
    ReplayOnly(Box<CallKey<C>>),
}

fn collect_and_parts<C: ConstraintOps>(rel: Arc<Rel<C>>, out: &mut Vec<Arc<Rel<C>>>) {
    match rel.as_ref() {
        Rel::And(a, b) => {
            collect_and_parts(a.clone(), out);
            collect_and_parts(b.clone(), out);
        }
        _ => out.push(rel),
    }
}

fn flatten_and_parts<C: ConstraintOps>(rel: Arc<Rel<C>>) -> Vec<Arc<Rel<C>>> {
    let mut parts = Vec::new();
    collect_and_parts(rel, &mut parts);
    parts
}

fn wrap_rel_with_atoms<C: ConstraintOps>(
    rel: Arc<Rel<C>>,
    prefix: Option<NF<C>>,
    suffix: Option<NF<C>>,
) -> Rel<C> {
    if prefix.is_none() && suffix.is_none() {
        return rel.as_ref().clone();
    }

    let mut factors: Vec<Arc<Rel<C>>> = Vec::new();
    if let Some(nf) = prefix {
        factors.push(Arc::new(Rel::Atom(Arc::new(nf))));
    }
    factors.push(rel);
    if let Some(nf) = suffix {
        factors.push(Arc::new(Rel::Atom(Arc::new(nf))));
    }

    Rel::Seq(Arc::from(factors))
}

/// Convert a Rel to a Node tree with the given environment and tables.
pub fn rel_to_node<C: ConstraintOps>(rel: &Rel<C>, env: &Env<C>, tables: &Tables<C>) -> Node<C> {
    match rel {
        Rel::Zero => Node::Fail,

        Rel::Atom(nf) => Node::Emit(nf.as_ref().clone(), Box::new(Node::Fail)),

        Rel::Or(a, b) => Node::Or(
            Box::new(rel_to_node(a, env, tables)),
            Box::new(rel_to_node(b, env, tables)),
        ),

        Rel::And(a, b) => {
            let mut parts = Vec::new();
            collect_and_parts(a.clone(), &mut parts);
            collect_and_parts(b.clone(), &mut parts);
            if parts.is_empty() {
                return Node::Fail;
            }
            if parts.len() == 1 {
                return rel_to_node(parts[0].as_ref(), env, tables);
            }
            let nodes = parts
                .into_iter()
                .map(|part| rel_to_node(part.as_ref(), env, tables))
                .collect();
            Node::Work(boxed_work(Work::AndGroup(AndGroup::new(nodes))))
        }

        Rel::Seq(factors) => {
            let factors_rope = Factors::from_seq(factors.clone());
            let mut pipe = PipeWork::with_mid(factors_rope);
            pipe.env = env.clone();
            pipe.tables = tables.clone();
            Node::Work(boxed_work(Work::Pipe(pipe)))
        }

        Rel::Fix(id, body) => {
            let new_env = env.bind(*id, body.clone());
            rel_to_node(body, &new_env, tables)
        }

        Rel::Call(id) => match env.lookup(*id) {
            Some(_) => {
                let call_rel = Arc::new(rel.clone());
                let factors = Factors::from_seq(Arc::from(vec![call_rel]));
                let mut pipe = PipeWork::with_mid(factors);
                pipe.env = env.clone();
                pipe.tables = tables.clone();
                Node::Work(boxed_work(Work::Pipe(pipe)))
            }
            None => Node::Fail,
        },
    }
}

fn node_from_answers<C: ConstraintOps>(answers: &[NF<C>]) -> Node<C> {
    let mut node = Node::Fail;
    for nf in answers.iter().rev() {
        node = Node::Emit(nf.clone(), Box::new(node));
    }
    node
}

fn boxed_work<C: ConstraintOps>(work: Work<C>) -> Box<Work<C>> {
    Box::new(work)
}

fn boxed_node<C: ConstraintOps>(node: Node<C>) -> Box<Node<C>> {
    Box::new(node)
}

fn wrap_compose_with_prefix_suffix<C: ConstraintOps>(
    core: ComposeWork<C>,
    prefix: Option<NF<C>>,
    suffix: Option<NF<C>>,
) -> WorkStep<C> {
    let mut node = Node::Work(boxed_work(Work::Compose(core)));

    if let Some(prefix_nf) = prefix {
        let prefix_node = Node::Emit(prefix_nf, Box::new(Node::Fail));
        node = Node::Work(boxed_work(Work::Compose(ComposeWork::new(
            prefix_node, node,
        ))));
    }

    if let Some(suffix_nf) = suffix {
        let suffix_node = Node::Emit(suffix_nf, Box::new(Node::Fail));
        node = Node::Work(boxed_work(Work::Compose(ComposeWork::new(
            node, suffix_node,
        ))));
    }

    match node {
        Node::Work(work) => WorkStep::More(work),
        _ => WorkStep::Done,
    }
}

fn build_var_list(arity: u32, terms: &mut TermStore) -> SmallVec<[TermId; 1]> {
    let mut vars = SmallVec::new();
    for idx in 0..arity {
        vars.push(terms.var(idx));
    }
    vars
}

fn nf_rwl_iso<C: ConstraintOps>(nf: &NF<C>, terms: &mut TermStore) -> NF<C> {
    let in_arity = nf.drop_fresh.in_arity;
    NF::new(
        nf.match_pats.clone(),
        DropFresh::identity(in_arity),
        build_var_list(in_arity, terms),
    )
}

fn nf_rwr_iso<C: ConstraintOps>(nf: &NF<C>, terms: &mut TermStore) -> NF<C> {
    let out_arity = nf.drop_fresh.out_arity;
    NF::new(
        build_var_list(out_arity, terms),
        DropFresh::identity(out_arity),
        nf.build_pats.clone(),
    )
}

fn nf_left_prefix<C: ConstraintOps>(nf: &NF<C>, terms: &mut TermStore) -> NF<C> {
    let out_arity = nf.drop_fresh.out_arity;
    NF::new(
        nf.match_pats.clone(),
        nf.drop_fresh.clone(),
        build_var_list(out_arity, terms),
    )
}

fn nf_right_suffix<C: ConstraintOps>(nf: &NF<C>, terms: &mut TermStore) -> NF<C> {
    let in_arity = nf.drop_fresh.in_arity;
    NF::new(
        build_var_list(in_arity, terms),
        nf.drop_fresh.clone(),
        nf.build_pats.clone(),
    )
}

/// Pipeline work: sequential composition with boundary fusion.
///
/// Represents: left ; mid[0] ; mid[1] ; ... ; mid[n-1] ; right
///
/// Normalization absorbs Atoms at boundaries via compose_nf.
/// Or nodes in mid cause splits. Zero in mid annihilates.
///
/// Outside-in evaluation: alternates processing front/back to propagate
/// constraints before expanding recursion.
#[derive(Clone, Debug)]
pub struct PipeWork<C: ConstraintOps> {
    /// Left boundary (fused from front).
    pub left: Option<NF<C>>,
    /// Middle factors (remaining Rel elements).
    pub mid: Factors<C>,
    /// Right boundary (fused from back).
    pub right: Option<NF<C>>,
    /// Flip bit: alternates which end to process for outside-in evaluation.
    pub flip: bool,
    /// Environment for Fix bindings (RelId -> Rel body).
    pub env: Env<C>,
    /// Tables for call-context tabling.
    pub tables: Tables<C>,
    /// Call handling mode.
    pub call_mode: CallMode<C>,
}

struct PipeWorkBuilder<C: ConstraintOps> {
    left: Option<NF<C>>,
    mid: Factors<C>,
    right: Option<NF<C>>,
    flip: bool,
    env: Env<C>,
    tables: Tables<C>,
    call_mode: CallMode<C>,
}

impl<C: ConstraintOps> PipeWorkBuilder<C> {
    fn new() -> Self {
        Self {
            left: None,
            mid: Factors::new(),
            right: None,
            flip: false,
            env: Env::new(),
            tables: Tables::new(),
            call_mode: CallMode::Normal,
        }
    }

    fn left(mut self, left: Option<NF<C>>) -> Self {
        self.left = left;
        self
    }

    fn mid(mut self, mid: Factors<C>) -> Self {
        self.mid = mid;
        self
    }

    fn right(mut self, right: Option<NF<C>>) -> Self {
        self.right = right;
        self
    }

    fn env(mut self, env: Env<C>) -> Self {
        self.env = env;
        self
    }

    fn tables(mut self, tables: Tables<C>) -> Self {
        self.tables = tables;
        self
    }

    fn build(self) -> PipeWork<C> {
        PipeWork {
            left: self.left,
            mid: self.mid,
            right: self.right,
            flip: self.flip,
            env: self.env,
            tables: self.tables,
            call_mode: self.call_mode,
        }
    }
}

impl<C: ConstraintOps> Work<C> {
    /// Step this work item, returning the next state.
    pub fn step(&mut self, terms: &mut TermStore) -> WorkStep<C> {
        match self {
            Work::Pipe(pipe) => pipe.step(terms),
            Work::Meet(meet) => meet.step(terms),
            Work::AndGroup(group) => group.step(terms),
            Work::Fix(fix) => fix.step(terms),
            Work::Compose(compose) => compose.step(terms),
            Work::JoinReceiver(join) => join.step(terms),
            Work::Atom(nf) => {
                // Emit the NF once, then done
                let nf = nf.clone();
                WorkStep::Emit(nf, boxed_work(Work::Done))
            }
            Work::Done => WorkStep::Done,
        }
    }
}

impl<C: ConstraintOps> PipeWork<C> {
    fn builder() -> PipeWorkBuilder<C> {
        PipeWorkBuilder::new()
    }

    /// Create an empty pipe (represents identity and emits it).
    pub fn new() -> Self {
        Self::builder().build()
    }

    /// Create a pipe with only mid factors.
    pub fn with_mid(mid: Factors<C>) -> Self {
        Self::builder().mid(mid).build()
    }

    /// Create a pipe with boundaries and mid.
    pub fn with_boundaries(left: Option<NF<C>>, mid: Factors<C>, right: Option<NF<C>>) -> Self {
        Self::builder().left(left).mid(mid).right(right).build()
    }

    /// Create a pipe with full state including env and tables.
    pub fn with_env_and_tables(
        left: Option<NF<C>>,
        mid: Factors<C>,
        right: Option<NF<C>>,
        env: Env<C>,
        tables: Tables<C>,
    ) -> Self {
        Self::builder()
            .left(left)
            .mid(mid)
            .right(right)
            .env(env)
            .tables(tables)
            .build()
    }

    /// Create a pipe from a Rel expression with given env and tables.
    pub fn from_rel(rel: Rel<C>, env: Env<C>, tables: Tables<C>) -> Self {
        let mid = match &rel {
            Rel::Seq(factors) => Factors::from_seq(factors.clone()),
            _ => {
                // Single non-Seq rel becomes a single-element mid
                let factors: Arc<[Arc<Rel<C>>]> = Arc::from(vec![Arc::new(rel)]);
                Factors::from_seq(factors)
            }
        };
        Self::builder().mid(mid).env(env).tables(tables).build()
    }

    /// Create a producer pipe with boundaries as Atom factors in mid.
    /// The pipe will be: [Atom(left)?] ++ body_factors ++ [Atom(right)?]
    /// This ensures boundaries are visible for call-context key formation.
    pub fn from_rel_with_boundaries(
        rel: Rel<C>,
        left: Option<NF<C>>,
        right: Option<NF<C>>,
        env: Env<C>,
        tables: Tables<C>,
    ) -> Self {
        // Build mid factors: [left_atom?, body_factors..., right_atom?]
        let mut factors_vec: Vec<Arc<Rel<C>>> = Vec::new();

        // Add left boundary as Atom if present
        if let Some(left_nf) = left {
            factors_vec.push(Arc::new(Rel::Atom(Arc::new(left_nf))));
        }

        // Add body factors
        match &rel {
            Rel::Seq(body_factors) => {
                for f in body_factors.iter() {
                    factors_vec.push(f.clone());
                }
            }
            _ => {
                factors_vec.push(Arc::new(rel));
            }
        }

        // Add right boundary as Atom if present
        if let Some(right_nf) = right {
            factors_vec.push(Arc::new(Rel::Atom(Arc::new(right_nf))));
        }

        let factors: Arc<[Arc<Rel<C>>]> = Arc::from(factors_vec);
        let mid = Factors::from_seq(factors);

        Self::builder().mid(mid).env(env).tables(tables).build()
    }

    /// Check if the pipe is empty (no boundaries and no mid).
    pub fn is_empty(&self) -> bool {
        self.left.is_none() && self.mid.is_empty() && self.right.is_none()
    }

    /// Step this pipeline, returning the next state.
    ///
    /// Two-phase approach for direction-agnostic evaluation:
    /// - Phase A: Try to normalize (absorb atoms, flatten Seq, detect Zero) at BOTH ends
    /// - Phase B: When stuck, advance one end using alternating flip
    pub fn step(&mut self, terms: &mut TermStore) -> WorkStep<C> {
        loop {
            // Phase A: Check for empty mid
            if self.mid.is_empty() {
                return self.emit_boundaries(terms);
            }

            // Phase A: Try to normalize at either end
            match self.try_normalize_step(terms) {
                Ok(true) => continue,
                Ok(false) => {}
                Err(step) => return step,
            }

            // Phase A: Normalize adjacent atoms anywhere in mid
            match self.normalize_mid_atoms(terms) {
                Ok(true) => continue,
                Ok(false) => {}
                Err(step) => return step,
            }

            break;
        }

        // Phase B: Stuck on normalization - advance one end using flip.
        // Prefer advancing a non-Call end when the opposite end is a Call.
        let front_is_call = matches!(self.mid.front().map(|rel| rel.as_ref()), Some(Rel::Call(_)));
        let back_is_call = matches!(self.mid.back().map(|rel| rel.as_ref()), Some(Rel::Call(_)));

        let mut advance_back = self.flip;
        if advance_back && back_is_call && !front_is_call {
            advance_back = false;
        } else if !advance_back && front_is_call && !back_is_call {
            advance_back = true;
        }

        let result = if advance_back {
            self.advance_back(terms)
        } else {
            self.advance_front(terms)
        };
        self.flip = !self.flip; // Toggle for next step
        result
    }

    /// Emit the composed boundaries when mid is empty.
    fn emit_boundaries(&self, terms: &mut TermStore) -> WorkStep<C> {
        match (&self.left, &self.right) {
            (None, None) => {
                // Empty pipe - emit identity
                WorkStep::Emit(NF::identity(C::default()), boxed_work(Work::Done))
            }
            (Some(left), None) => {
                // Only left boundary
                WorkStep::Emit(left.clone(), boxed_work(Work::Done))
            }
            (None, Some(right)) => {
                // Only right boundary
                WorkStep::Emit(right.clone(), boxed_work(Work::Done))
            }
            (Some(left), Some(right)) => {
                // Compose left and right
                match compose_nf(left, right, terms) {
                    Some(composed) => WorkStep::Emit(composed, boxed_work(Work::Done)),
                    None => WorkStep::Done, // Composition failed
                }
            }
        }
    }

    /// Absorb an NF from the front into the left boundary.
    fn absorb_front(&mut self, nf: NF<C>, terms: &mut TermStore) -> bool {
        match &self.left {
            None => {
                // No left boundary, this NF becomes the left boundary
                self.left = Some(nf);
                true
            }
            Some(left) => {
                // Try to compose with left boundary
                match compose_nf(left, &nf, terms) {
                    Some(composed) => {
                        self.left = Some(composed);
                        true
                    }
                    None => {
                        // Composition failed - signal failure
                        false
                    }
                }
            }
        }
    }

    /// Absorb an NF from the back into the right boundary.
    fn absorb_back(&mut self, nf: NF<C>, terms: &mut TermStore) -> bool {
        match &self.right {
            None => {
                // No right boundary, this NF becomes the right boundary
                self.right = Some(nf);
                true
            }
            Some(right) => {
                // Try to compose: nf ; right
                match compose_nf(&nf, right, terms) {
                    Some(composed) => {
                        self.right = Some(composed);
                        true
                    }
                    None => {
                        // Composition failed - signal failure
                        false
                    }
                }
            }
        }
    }

    /// Split on an Or node at the front.
    fn split_or_front(&self, a: Arc<Rel<C>>, b: Arc<Rel<C>>) -> WorkStep<C> {
        // Create two pipes - one with branch a, one with branch b.
        // Both keep the same boundaries, env, tables, and remaining mid.

        // Left pipe: a followed by remaining mid
        let mut left_pipe = self.clone();
        left_pipe.mid.push_front_rel(a);

        // Right pipe: b followed by remaining mid
        let mut right_pipe = self.clone();
        right_pipe.mid.push_front_rel(b);

        WorkStep::Split(
            boxed_node(Node::Work(boxed_work(Work::Pipe(left_pipe)))),
            boxed_node(Node::Work(boxed_work(Work::Pipe(right_pipe)))),
        )
    }

    /// Split on an Or node at the back.
    fn split_or_back(&self, a: Arc<Rel<C>>, b: Arc<Rel<C>>) -> WorkStep<C> {
        // Create two pipes - one with branch a, one with branch b.
        // Both keep the same boundaries, env, tables, and remaining mid.

        // Left pipe: remaining mid followed by a
        let mut left_pipe = self.clone();
        left_pipe.mid.push_back_rel(a);

        // Right pipe: remaining mid followed by b
        let mut right_pipe = self.clone();
        right_pipe.mid.push_back_rel(b);

        WorkStep::Split(
            boxed_node(Node::Work(boxed_work(Work::Pipe(left_pipe)))),
            boxed_node(Node::Work(boxed_work(Work::Pipe(right_pipe)))),
        )
    }

    /// Try to normalize one step at either end.
    /// Returns Ok(true) if progress was made, Ok(false) if stuck,
    /// or Err(step) if normalization yields a terminal result.
    fn try_normalize_step(&mut self, terms: &mut TermStore) -> Result<bool, WorkStep<C>> {
        // Try front first
        if let Some(front) = self.mid.front().cloned() {
            match front.as_ref() {
                Rel::Zero => {
                    // Zero annihilates the pipe
                    return Err(WorkStep::Done);
                }
                Rel::Atom(nf) => {
                    self.mid.pop_front();
                    if self.absorb_front(nf.as_ref().clone(), terms) {
                        return Ok(true);
                    }
                    return Err(WorkStep::Done);
                }
                Rel::Seq(xs) => {
                    self.mid.pop_front();
                    self.mid.push_front_slice_from_seq(xs.clone());
                    return Ok(true);
                }
                _ => {}
            }
        }

        // Try back
        if let Some(back) = self.mid.back().cloned() {
            match back.as_ref() {
                Rel::Zero => {
                    // Zero annihilates the pipe
                    return Err(WorkStep::Done);
                }
                Rel::Atom(nf) => {
                    self.mid.pop_back();
                    if self.absorb_back(nf.as_ref().clone(), terms) {
                        return Ok(true);
                    }
                    return Err(WorkStep::Done);
                }
                Rel::Seq(xs) => {
                    self.mid.pop_back();
                    self.mid.push_back_slice_from_seq(xs.clone());
                    return Ok(true);
                }
                _ => {}
            }
        }

        // No progress possible
        Ok(false)
    }

    /// Normalize mid factors by flattening Seq and fusing adjacent atoms anywhere.
    fn normalize_mid_atoms(&mut self, terms: &mut TermStore) -> Result<bool, WorkStep<C>> {
        if self.mid.is_empty() {
            return Ok(false);
        }

        let mut factors = self.mid.to_vec();
        let mut changed = false;

        // Flatten nested Seq factors anywhere in the mid.
        loop {
            let mut flattened = Vec::new();
            let mut did_flatten = false;
            for factor in factors {
                match factor.as_ref() {
                    Rel::Seq(xs) => {
                        did_flatten = true;
                        for f in xs.iter() {
                            flattened.push(f.clone());
                        }
                    }
                    _ => flattened.push(factor),
                }
            }
            factors = flattened;
            if !did_flatten {
                break;
            }
            changed = true;
        }

        // Collapse And factors that are fully atomic into a single Atom via meet.
        for idx in 0..factors.len() {
            let rel = factors[idx].clone();
            let Rel::And(_, _) = rel.as_ref() else {
                continue;
            };
            let parts = flatten_and_parts(rel);
            let mut acc: Option<NF<C>> = None;
            let mut all_atoms = true;
            for part in parts {
                match part.as_ref() {
                    Rel::Atom(nf) => {
                        acc = match acc {
                            None => Some(nf.as_ref().clone()),
                            Some(prev) => meet_nf(&prev, nf.as_ref(), terms),
                        };
                        if acc.is_none() {
                            return Err(WorkStep::Done);
                        }
                    }
                    Rel::Zero => return Err(WorkStep::Done),
                    _ => {
                        all_atoms = false;
                        break;
                    }
                }
            }

            if all_atoms {
                if let Some(nf) = acc {
                    factors[idx] = Arc::new(Rel::Atom(Arc::new(nf)));
                    changed = true;
                }
            }
        }

        if factors.iter().any(|f| matches!(f.as_ref(), Rel::Zero)) {
            return Err(WorkStep::Done);
        }

        // Fuse adjacent Atom factors anywhere.
        let mut i = 0;
        while i + 1 < factors.len() {
            let left = factors[i].clone();
            let right = factors[i + 1].clone();
            if let (Rel::Atom(a), Rel::Atom(b)) = (left.as_ref(), right.as_ref()) {
                let Some(composed) = compose_nf(a, b, terms) else {
                    return Err(WorkStep::Done);
                };
                factors[i] = Arc::new(Rel::Atom(Arc::new(composed)));
                factors.remove(i + 1);
                changed = true;
                i = i.saturating_sub(1);
                continue;
            }
            i += 1;
        }

        if changed {
            let seq: Arc<[Arc<Rel<C>>]> = Arc::from(factors);
            self.mid = Factors::from_seq(seq);
        }

        Ok(changed)
    }

    /// Advance the front factor when stuck on normalization.
    fn advance_front(&mut self, terms: &mut TermStore) -> WorkStep<C> {
        let Some(front) = self.mid.front().cloned() else {
            return self.emit_boundaries(terms);
        };

        match front.as_ref() {
            Rel::Or(a, b) => {
                self.mid.pop_front();
                self.split_or_front(a.clone(), b.clone())
            }
            Rel::And(_, _) => {
                self.mid.pop_front();
                let parts = flatten_and_parts(front.clone());

                let (left_prefix, left_iso) = match &self.left {
                    Some(nf) => (Some(nf_left_prefix(nf, terms)), Some(nf_rwr_iso(nf, terms))),
                    None => (None, None),
                };

                let (right_suffix, right_iso) = if self.mid.is_empty() {
                    match &self.right {
                        Some(nf) => (
                            Some(nf_right_suffix(nf, terms)),
                            Some(nf_rwl_iso(nf, terms)),
                        ),
                        None => (None, None),
                    }
                } else {
                    (self.right.clone(), None)
                };

                let nodes = parts
                    .into_iter()
                    .map(|part| {
                        let wrapped =
                            wrap_rel_with_atoms(part, left_iso.clone(), right_iso.clone());
                        let mut part_pipe =
                            PipeWork::from_rel(wrapped, self.env.clone(), self.tables.clone());
                        part_pipe.call_mode = self.call_mode.clone();
                        Node::Work(boxed_work(Work::Pipe(part_pipe)))
                    })
                    .collect();
                let group = AndGroup::new(nodes);
                let left_node = Node::Work(boxed_work(Work::AndGroup(group)));

                let mut pipe = self.clone();
                pipe.left = None;
                pipe.right = if right_iso.is_some() { None } else { right_suffix.clone() };
                let right_node = Node::Work(boxed_work(Work::Pipe(pipe)));

                let core = ComposeWork::new(left_node, right_node);
                let outer_suffix = if right_iso.is_some() { right_suffix } else { None };
                wrap_compose_with_prefix_suffix(core, left_prefix, outer_suffix)
            }
            Rel::Fix(id, body) => {
                self.mid.pop_front();
                let use_left = true;
                let use_right = self.mid.is_empty();
                let call_left = if use_left { self.left.clone() } else { None };
                let call_right = if use_right { self.right.clone() } else { None };
                let bound_env = self.env.bind(*id, body.clone());

                let mut fix_pipe = PipeWork::from_rel_with_boundaries(
                    body.as_ref().clone(),
                    call_left,
                    call_right,
                    bound_env,
                    self.tables.clone(),
                );
                fix_pipe.call_mode = self.call_mode.clone();

                let fix_node = Node::Work(boxed_work(Work::Pipe(fix_pipe)));
                let mut pipe = self.clone();
                if use_left {
                    pipe.left = None;
                }
                if use_right {
                    pipe.right = None;
                }
                let left_node = fix_node;
                let right_node = Node::Work(boxed_work(Work::Pipe(pipe)));
                let compose = ComposeWork::new(left_node, right_node);
                WorkStep::More(boxed_work(Work::Compose(compose)))
            }
            Rel::Call(id) => {
                self.mid.pop_front();
                self.handle_call(*id, true)
            }
            // Atom/Zero/Seq should have been normalized in try_normalize_step
            _ => WorkStep::Done,
        }
    }

    /// Advance the back factor when stuck on normalization.
    fn advance_back(&mut self, terms: &mut TermStore) -> WorkStep<C> {
        let Some(back) = self.mid.back().cloned() else {
            return self.emit_boundaries(terms);
        };

        match back.as_ref() {
            Rel::Or(a, b) => {
                self.mid.pop_back();
                self.split_or_back(a.clone(), b.clone())
            }
            Rel::And(_, _) => {
                self.mid.pop_back();
                let parts = flatten_and_parts(back.clone());

                let (right_suffix, right_iso) = match &self.right {
                    Some(nf) => (
                        Some(nf_right_suffix(nf, terms)),
                        Some(nf_rwl_iso(nf, terms)),
                    ),
                    None => (None, None),
                };

                let (left_prefix, left_iso) = if self.mid.is_empty() {
                    match &self.left {
                        Some(nf) => (Some(nf_left_prefix(nf, terms)), Some(nf_rwr_iso(nf, terms))),
                        None => (None, None),
                    }
                } else {
                    (self.left.clone(), None)
                };

                let nodes = parts
                    .into_iter()
                    .map(|part| {
                        let wrapped =
                            wrap_rel_with_atoms(part, left_iso.clone(), right_iso.clone());
                        let mut part_pipe =
                            PipeWork::from_rel(wrapped, self.env.clone(), self.tables.clone());
                        part_pipe.call_mode = self.call_mode.clone();
                        Node::Work(boxed_work(Work::Pipe(part_pipe)))
                    })
                    .collect();
                let group = AndGroup::new(nodes);
                let right_node = Node::Work(boxed_work(Work::AndGroup(group)));

                let mut pipe = self.clone();
                pipe.right = None;
                pipe.left = if left_iso.is_some() { None } else { left_prefix.clone() };
                let left_node = Node::Work(boxed_work(Work::Pipe(pipe)));

                let core = ComposeWork::new(left_node, right_node);
                let outer_prefix = if left_iso.is_some() { left_prefix } else { None };
                wrap_compose_with_prefix_suffix(core, outer_prefix, right_suffix)
            }
            Rel::Fix(id, body) => {
                self.mid.pop_back();
                let use_left = self.mid.is_empty();
                let use_right = true;
                let call_left = if use_left { self.left.clone() } else { None };
                let call_right = if use_right { self.right.clone() } else { None };
                let bound_env = self.env.bind(*id, body.clone());

                let mut fix_pipe = PipeWork::from_rel_with_boundaries(
                    body.as_ref().clone(),
                    call_left,
                    call_right,
                    bound_env,
                    self.tables.clone(),
                );
                fix_pipe.call_mode = self.call_mode.clone();

                let fix_node = Node::Work(boxed_work(Work::Pipe(fix_pipe)));
                let mut pipe = self.clone();
                if use_left {
                    pipe.left = None;
                }
                if use_right {
                    pipe.right = None;
                }
                let left_node = Node::Work(boxed_work(Work::Pipe(pipe)));
                let right_node = fix_node;
                let compose = ComposeWork::new(left_node, right_node);
                WorkStep::More(boxed_work(Work::Compose(compose)))
            }
            Rel::Call(id) => {
                self.mid.pop_back();
                self.handle_call(*id, false)
            }
            // Atom/Zero/Seq should have been normalized in try_normalize_step
            _ => WorkStep::Done,
        }
    }

    /// Handle a Call by looking up in the environment and using tabling.
    fn handle_call(&mut self, id: RelId, absorb_front: bool) -> WorkStep<C> {
        let Some(binding) = self.env.lookup(id) else {
            return WorkStep::Done;
        };
        let use_left = if absorb_front {
            true
        } else {
            self.mid.is_empty()
        };
        let use_right = if absorb_front {
            self.mid.is_empty()
        } else {
            true
        };

        let call_left = if use_left { self.left.clone() } else { None };
        let call_right = if use_right { self.right.clone() } else { None };

        let key = CallKey::new(id, binding.id, call_left.clone(), call_right.clone());
        if let CallMode::ReplayOnly(replay_key) = &self.call_mode {
            if replay_key.as_ref() == &key {
                let table = match self.tables.lookup(&key) {
                    Some(table) => table,
                    None => return WorkStep::Done,
                };
                let snapshot = table.all_answers();
                let replay_node = node_from_answers(&snapshot);
                let mut pipe = self.clone();
                if use_left {
                    pipe.left = None;
                }
                if use_right {
                    pipe.right = None;
                }
                let (left_node, right_node) = if absorb_front {
                    (replay_node, Node::Work(boxed_work(Work::Pipe(pipe))))
                } else {
                    (Node::Work(boxed_work(Work::Pipe(pipe))), replay_node)
                };
                let compose = ComposeWork::new(left_node, right_node);
                return WorkStep::More(boxed_work(Work::Compose(compose)));
            }
        }

        let table = self.tables.get_or_create(key.clone());
        let snapshot = {
            let mut producer = table.producer.lock();
            if producer.spec.is_none() {
                producer.spec = Some(ProducerSpec {
                    key: key.clone(),
                    body: binding.body.clone(),
                    left: call_left.clone(),
                    right: call_right.clone(),
                    env: self.env.clone(),
                });
            }
            drop(producer);
            table.answers.lock().answers.clone()
        };

        let replay_node = node_from_answers(&snapshot);
        let fix = FixWork::new(key, table, snapshot.len(), self.tables.clone());
        let fix_node = Node::Work(boxed_work(Work::Fix(fix)));

        let gen_node = match replay_node {
            Node::Fail => fix_node,
            _ => Node::Or(Box::new(replay_node), Box::new(fix_node)),
        };

        let mut pipe = self.clone();
        if use_left {
            pipe.left = None;
        }
        if use_right {
            pipe.right = None;
        }

        let (left_node, right_node) = if absorb_front {
            (gen_node, Node::Work(boxed_work(Work::Pipe(pipe))))
        } else {
            (Node::Work(boxed_work(Work::Pipe(pipe))), gen_node)
        };
        let compose = ComposeWork::new(left_node, right_node);
        WorkStep::More(boxed_work(Work::Compose(compose)))
    }
}

impl<C: ConstraintOps> Default for PipeWork<C> {
    fn default() -> Self {
        Self {
            left: None,
            mid: Factors::new(),
            right: None,
            flip: false,
            env: Env::new(),
            tables: Tables::new(),
            call_mode: CallMode::Normal,
        }
    }
}

/// Compose work: symmetric join for sequential composition.
///
/// Represents: left ; right
///
/// Uses fair diagonal enumeration:
/// - Pull alternately from left/right nodes
/// - When a new answer arrives, compose with all seen from the other side
/// - Successful compositions are queued in pending
#[derive(Clone, Debug)]
enum ComposeCursor {
    Left {
        left_idx: usize,
        right_idx: usize,
        right_limit: usize,
    },
    Right {
        right_idx: usize,
        left_idx: usize,
        left_limit: usize,
    },
}

const COMPOSE_BATCH: usize = 1;

#[derive(Clone, Debug)]
pub struct ComposeWork<C: ConstraintOps> {
    /// Left search tree.
    pub left: Box<Node<C>>,
    /// Right search tree.
    pub right: Box<Node<C>>,
    /// Answers seen from left.
    pub seen_l: Vec<NF<C>>,
    /// Answers seen from right.
    pub seen_r: Vec<NF<C>>,
    /// Dedup set for left answers.
    seen_l_set: HashSet<NF<C>>,
    /// Dedup set for right answers.
    seen_r_set: HashSet<NF<C>>,
    /// Successful compositions waiting to be emitted.
    pub pending: VecDeque<NF<C>>,
    /// Dedup set for pending compositions.
    pending_set: HashSet<NF<C>>,
    /// Pending composition cursors.
    pair_queue: VecDeque<ComposeCursor>,
    /// If false, pull from left next; if true, pull from right.
    pub flip: bool,
}

impl<C: ConstraintOps> ComposeWork<C> {
    /// Create a new ComposeWork from two nodes.
    pub fn new(left: Node<C>, right: Node<C>) -> Self {
        Self {
            left: Box::new(left),
            right: Box::new(right),
            seen_l: Vec::new(),
            seen_r: Vec::new(),
            seen_l_set: HashSet::new(),
            seen_r_set: HashSet::new(),
            pending: VecDeque::new(),
            pending_set: HashSet::new(),
            pair_queue: VecDeque::new(),
            flip: false,
        }
    }

    fn take_self(&mut self) -> Self {
        std::mem::replace(self, ComposeWork::new(Node::Fail, Node::Fail))
    }

    fn push_pending(&mut self, nf: NF<C>) {
        if self.pending_set.insert(nf.clone()) {
            self.pending.push_back(nf);
        }
    }

    fn is_empty_identity(nf: &NF<C>) -> bool {
        nf.match_pats.is_empty()
            && nf.build_pats.is_empty()
            && nf.drop_fresh.in_arity == 0
            && nf.drop_fresh.out_arity == 0
    }

    fn compose_pair(
        left_nf: &NF<C>,
        right_nf: &NF<C>,
        terms: &mut TermStore,
    ) -> Option<NF<C>> {
        if Self::is_empty_identity(right_nf) {
            return Some(left_nf.clone());
        }
        if Self::is_empty_identity(left_nf) {
            return Some(right_nf.clone());
        }
        compose_nf(left_nf, right_nf, terms)
    }

    fn enqueue_pairs_left(&mut self, left_idx: usize) {
        let right_limit = self.seen_r.len();
        if right_limit == 0 {
            return;
        }
        self.pair_queue.push_back(ComposeCursor::Left {
            left_idx,
            right_idx: 0,
            right_limit,
        });
    }

    fn enqueue_pairs_right(&mut self, right_idx: usize) {
        let left_limit = self.seen_l.len();
        if left_limit == 0 {
            return;
        }
        self.pair_queue.push_back(ComposeCursor::Right {
            right_idx,
            left_idx: 0,
            left_limit,
        });
    }

    fn process_pair_queue(&mut self, terms: &mut TermStore) -> Option<NF<C>> {
        let Some(mut cursor) = self.pair_queue.pop_front() else {
            return None;
        };

        let mut steps = 0;
        loop {
            if steps >= COMPOSE_BATCH {
                break;
            }
            match &mut cursor {
                ComposeCursor::Left {
                    left_idx,
                    right_idx,
                    right_limit,
                } => {
                    if *right_idx >= *right_limit {
                        break;
                    }
                    let left_nf = &self.seen_l[*left_idx];
                    let right_nf = &self.seen_r[*right_idx];
                    if let Some(nf) = Self::compose_pair(left_nf, right_nf, terms) {
                        self.push_pending(nf);
                    }
                    *right_idx += 1;
                }
                ComposeCursor::Right {
                    right_idx,
                    left_idx,
                    left_limit,
                } => {
                    if *left_idx >= *left_limit {
                        break;
                    }
                    let left_nf = &self.seen_l[*left_idx];
                    let right_nf = &self.seen_r[*right_idx];
                    if let Some(nf) = Self::compose_pair(left_nf, right_nf, terms) {
                        self.push_pending(nf);
                    }
                    *left_idx += 1;
                }
            }
            steps += 1;
        }

        let cursor_done = match &cursor {
            ComposeCursor::Left {
                right_idx,
                right_limit,
                ..
            } => *right_idx >= *right_limit,
            ComposeCursor::Right {
                left_idx,
                left_limit,
                ..
            } => *left_idx >= *left_limit,
        };
        if !cursor_done {
            self.pair_queue.push_back(cursor);
        }

        if let Some(nf) = self.pending.pop_front() {
            self.pending_set.remove(&nf);
            return Some(nf);
        }

        None
    }

    /// Step this compose work, returning the next state.
    ///
    /// Step policy:
    /// 1. If pending non-empty: emit front
    /// 2. Alternate processing pair cursors and pulling new answers
    /// 3. Alternate pulling from left/right (flip)
    pub fn step(&mut self, terms: &mut TermStore) -> WorkStep<C> {
        if let Some(nf) = self.pending.pop_front() {
            self.pending_set.remove(&nf);
            return WorkStep::Emit(nf, boxed_work(Work::Compose(self.take_self())));
        }

        let left_exhausted = matches!(*self.left, Node::Fail);
        let right_exhausted = matches!(*self.right, Node::Fail);

        if let Some(nf) = self.process_pair_queue(terms) {
            return WorkStep::Emit(nf, boxed_work(Work::Compose(self.take_self())));
        }

        if left_exhausted && self.seen_l.is_empty() && self.pair_queue.is_empty() {
            return WorkStep::Done;
        }

        if right_exhausted && self.seen_r.is_empty() && self.pair_queue.is_empty() {
            return WorkStep::Done;
        }

        if left_exhausted && right_exhausted {
            if self.pair_queue.is_empty() {
                return WorkStep::Done;
            }
            return WorkStep::More(boxed_work(Work::Compose(self.take_self())));
        }

        let pull_from_right = if left_exhausted {
            true
        } else if right_exhausted {
            false
        } else {
            self.flip
        };

        if pull_from_right {
            self.pull_right(terms)
        } else {
            self.pull_left(terms)
        }
    }

    fn pull_left(&mut self, terms: &mut TermStore) -> WorkStep<C> {
        let current = std::mem::replace(&mut *self.left, Node::Fail);
        match step_node(current, terms) {
            NodeStep::Emit(nf, rest) => {
                *self.left = rest;
                if self.seen_l_set.insert(nf.clone()) {
                    let idx = self.seen_l.len();
                    self.seen_l.push(nf.clone());
                    self.enqueue_pairs_left(idx);
                }
                self.flip = true;
                if let Some(result) = self.pending.pop_front() {
                    self.pending_set.remove(&result);
                    WorkStep::Emit(result, boxed_work(Work::Compose(self.take_self())))
                } else {
                    WorkStep::More(boxed_work(Work::Compose(self.take_self())))
                }
            }
            NodeStep::Continue(rest) => {
                *self.left = rest;
                self.flip = true;
                WorkStep::More(boxed_work(Work::Compose(self.take_self())))
            }
            NodeStep::Exhausted => {
                *self.left = Node::Fail;
                self.flip = true;
                WorkStep::More(boxed_work(Work::Compose(self.take_self())))
            }
        }
    }

    fn pull_right(&mut self, terms: &mut TermStore) -> WorkStep<C> {
        let current = std::mem::replace(&mut *self.right, Node::Fail);
        match step_node(current, terms) {
            NodeStep::Emit(nf, rest) => {
                *self.right = rest;
                if self.seen_r_set.insert(nf.clone()) {
                    let idx = self.seen_r.len();
                    self.seen_r.push(nf.clone());
                    self.enqueue_pairs_right(idx);
                }
                self.flip = false;
                if let Some(result) = self.pending.pop_front() {
                    self.pending_set.remove(&result);
                    WorkStep::Emit(result, boxed_work(Work::Compose(self.take_self())))
                } else {
                    WorkStep::More(boxed_work(Work::Compose(self.take_self())))
                }
            }
            NodeStep::Continue(rest) => {
                *self.right = rest;
                self.flip = false;
                WorkStep::More(boxed_work(Work::Compose(self.take_self())))
            }
            NodeStep::Exhausted => {
                *self.right = Node::Fail;
                self.flip = false;
                WorkStep::More(boxed_work(Work::Compose(self.take_self())))
            }
        }
    }
}

/// Join receiver work: consume joiner outputs from a queue.
#[derive(Clone, Debug)]
pub struct JoinReceiverWork<C: ConstraintOps> {
    receiver: Arc<Mutex<AnswerReceiver<C>>>,
    blocked: Option<BlockedOn>,
}

impl<C: ConstraintOps> JoinReceiverWork<C> {
    pub fn new(receiver: AnswerReceiver<C>) -> Self {
        Self {
            receiver: Arc::new(Mutex::new(receiver)),
            blocked: None,
        }
    }

    pub fn blocked_on(&self) -> Option<BlockedOn> {
        self.blocked.clone()
    }

    pub fn step(&mut self, _terms: &mut TermStore) -> WorkStep<C> {
        let receiver = self.receiver.lock();
        match receiver.try_recv() {
            RecvResult::Item(nf) => {
                self.blocked = None;
                WorkStep::Emit(nf, boxed_work(Work::JoinReceiver(self.clone())))
            }
            RecvResult::Closed => WorkStep::Done,
            RecvResult::Empty => {
                self.blocked = Some(receiver.blocked_on());
                WorkStep::More(boxed_work(Work::JoinReceiver(self.clone())))
            }
        }
    }
}

/// AndGroup work: queue-backed join for n-ary conjunction/intersection.
///
/// Represents: And(r0, r1, ..., rn-1)
///
/// Each part runs as a producer that pushes answers into a bounded queue.
/// The joiner consumes those queues round-robin and emits meets into an output queue.
#[derive(Clone, Copy, Debug)]
pub struct AndGroupConfig {
    part_queue_capacity: usize,
    output_queue_capacity: usize,
}

impl Default for AndGroupConfig {
    fn default() -> Self {
        Self {
            part_queue_capacity: 1,
            output_queue_capacity: 1,
        }
    }
}

#[derive(Clone, Debug)]
struct AndProducer<C: ConstraintOps> {
    node: Node<C>,
    sender: Option<AnswerSender<C>>,
    pending: Option<NF<C>>,
    blocked: Option<BlockedOn>,
    done: bool,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum AndProducerStep {
    Progress,
    Blocked,
    Done,
}

impl<C: ConstraintOps> AndProducer<C> {
    fn new(node: Node<C>, sender: AnswerSender<C>) -> Self {
        Self {
            node,
            sender: Some(sender),
            pending: None,
            blocked: None,
            done: false,
        }
    }

    fn runnable(&self) -> bool {
        if self.done {
            return false;
        }
        self.blocked.as_ref().map_or(true, |b| b.is_stale())
    }

    fn close_sender(&mut self) {
        self.sender = None;
    }

    fn step(&mut self, terms: &mut TermStore) -> AndProducerStep {
        if self.done {
            return AndProducerStep::Done;
        }

        if let Some(blocked) = &self.blocked {
            if !blocked.is_stale() {
                return AndProducerStep::Blocked;
            }
        }

        if let Some(nf) = self.pending.take() {
            let Some(sender) = self.sender.as_ref() else {
                self.done = true;
                return AndProducerStep::Done;
            };
            match sender.try_send(nf.clone()) {
                SinkResult::Accepted => {
                    self.blocked = None;
                    return AndProducerStep::Progress;
                }
                SinkResult::Full => {
                    self.pending = Some(nf);
                    self.blocked = Some(sender.blocked_on());
                    return AndProducerStep::Blocked;
                }
                SinkResult::Closed => {
                    self.done = true;
                    self.close_sender();
                    return AndProducerStep::Done;
                }
            }
        }

        let current = std::mem::replace(&mut self.node, Node::Fail);
        match step_node(current, terms) {
            NodeStep::Emit(nf, rest) => {
                self.node = rest;
                let Some(sender) = self.sender.as_ref() else {
                    self.done = true;
                    return AndProducerStep::Done;
                };
                match sender.try_send(nf.clone()) {
                    SinkResult::Accepted => {
                        self.blocked = None;
                        AndProducerStep::Progress
                    }
                    SinkResult::Full => {
                        self.pending = Some(nf);
                        self.blocked = Some(sender.blocked_on());
                        AndProducerStep::Blocked
                    }
                    SinkResult::Closed => {
                        self.done = true;
                        self.close_sender();
                        AndProducerStep::Done
                    }
                }
            }
            NodeStep::Continue(rest) => {
                self.node = rest;
                if matches!(self.node, Node::Fail) {
                    self.done = true;
                    self.close_sender();
                    return AndProducerStep::Done;
                }
                self.blocked = None;
                AndProducerStep::Progress
            }
            NodeStep::Exhausted => {
                self.node = Node::Fail;
                self.done = true;
                self.close_sender();
                AndProducerStep::Done
            }
        }
    }
}

#[derive(Clone, Debug)]
pub struct AndGroup<C: ConstraintOps> {
    producers: Vec<AndProducer<C>>,
    joiner: Arc<Mutex<AndJoiner<C>>>,
    joiner_sink: AnswerSender<C>,
    joiner_blocked: Option<BlockedOn>,
    joiner_done: bool,
    output_receiver: Arc<Mutex<AnswerReceiver<C>>>,
    /// Round-robin turn index across producers + joiner.
    pub turn: usize,
}

impl<C: ConstraintOps> AndGroup<C> {
    /// Create a new AndGroup from part nodes.
    pub fn new(parts: Vec<Node<C>>) -> Self {
        Self::with_config(parts, AndGroupConfig::default())
    }

    pub fn with_config(parts: Vec<Node<C>>, config: AndGroupConfig) -> Self {
        let (hub, _rx) = WakeHub::new();
        let joiner_waker = hub.waker();
        let output_waker = hub.waker();

        let mut receivers = Vec::new();
        let mut producers = Vec::new();

        for part in parts {
            let (tx, rx) =
                AnswerQueue::bounded_with_waker(config.part_queue_capacity, joiner_waker.clone());
            receivers.push(rx);
            producers.push(AndProducer::new(part, tx));
        }

        let (out_tx, out_rx) =
            AnswerQueue::bounded_with_waker(config.output_queue_capacity, output_waker);

        let joiner = AndJoiner::from_state(
            receivers,
            vec![false; producers.len()],
            vec![Vec::new(); producers.len()],
            VecDeque::new(),
            0,
            joiner_waker,
        );

        Self {
            producers,
            joiner: Arc::new(Mutex::new(joiner)),
            joiner_sink: out_tx,
            joiner_blocked: None,
            joiner_done: false,
            output_receiver: Arc::new(Mutex::new(out_rx)),
            turn: 0,
        }
    }

    fn take_self(&mut self) -> Self {
        std::mem::replace(self, AndGroup::new(Vec::new()))
    }

    fn joiner_runnable(&self) -> bool {
        if self.joiner_done {
            return false;
        }
        self.joiner_blocked.as_ref().map_or(true, |b| b.is_stale())
    }

    fn poll_output(&mut self) -> Option<NF<C>> {
        let receiver = self.output_receiver.lock();
        match receiver.try_recv() {
            RecvResult::Item(nf) => Some(nf),
            RecvResult::Empty => None,
            RecvResult::Closed => {
                self.joiner_done = true;
                None
            }
        }
    }

    fn step_joiner(&mut self, terms: &mut TermStore) -> JoinStep {
        let mut joiner = self.joiner.lock();
        let mut sink = crate::queue::AnswerSink::Queue(self.joiner_sink.clone());
        match joiner.step(terms, &mut sink) {
            JoinStep::Progress => {
                self.joiner_blocked = None;
                JoinStep::Progress
            }
            JoinStep::Blocked(blocked) => {
                self.joiner_blocked = Some(blocked.clone());
                JoinStep::Blocked(blocked)
            }
            JoinStep::Done => {
                self.joiner_done = true;
                self.joiner_blocked = None;
                JoinStep::Done
            }
        }
    }

    /// Step this AndGroup, returning the next state.
    pub fn step(&mut self, terms: &mut TermStore) -> WorkStep<C> {
        if let Some(nf) = self.poll_output() {
            return WorkStep::Emit(nf, boxed_work(Work::AndGroup(self.take_self())));
        }

        if self.joiner_done {
            return WorkStep::Done;
        }

        let total = self.producers.len() + 1;
        if total == 0 {
            return WorkStep::Done;
        }

        for offset in 0..total {
            let idx = (self.turn + offset) % total;
            if idx == self.producers.len() {
                if !self.joiner_runnable() {
                    continue;
                }
                self.step_joiner(terms);
                self.turn = (idx + 1) % total;
                if let Some(nf) = self.poll_output() {
                    return WorkStep::Emit(nf, boxed_work(Work::AndGroup(self.take_self())));
                }
                return WorkStep::More(boxed_work(Work::AndGroup(self.take_self())));
            }

            if !self.producers[idx].runnable() {
                continue;
            }
            let _ = self.producers[idx].step(terms);
            self.turn = (idx + 1) % total;
            if let Some(nf) = self.poll_output() {
                return WorkStep::Emit(nf, boxed_work(Work::AndGroup(self.take_self())));
            }
            return WorkStep::More(boxed_work(Work::AndGroup(self.take_self())));
        }

        if self.joiner_done {
            WorkStep::Done
        } else {
            WorkStep::More(boxed_work(Work::AndGroup(self.take_self())))
        }
    }
}

/// Meet work: fair diagonal join for conjunction/intersection.
///
/// Represents: And(left_node, right_node)
///
/// Uses fair diagonal enumeration:
/// - Pull alternately from left and right nodes
/// - When a new answer arrives, meet with all seen from other side
/// - Successful meets are queued in pending
///
/// Step policy:
/// 1. If pending non-empty: emit front
/// 2. Alternate pulling from left/right (flip)
/// 3. When new answer arrives, meet with all seen from other side
/// 4. Push successful meets to pending
#[derive(Clone, Debug)]
pub struct MeetWork<C: ConstraintOps> {
    /// Left search tree (boxed to break recursive type cycle)
    pub left: Box<Node<C>>,
    /// Right search tree (boxed to break recursive type cycle)
    pub right: Box<Node<C>>,
    /// Answers seen from left (in insertion order)
    pub seen_l: Vec<NF<C>>,
    /// Answers seen from right (in insertion order)
    pub seen_r: Vec<NF<C>>,
    /// Dedup set for left answers
    seen_l_set: HashSet<NF<C>>,
    /// Dedup set for right answers
    seen_r_set: HashSet<NF<C>>,
    /// Successful meets waiting to be emitted
    pub pending: VecDeque<NF<C>>,
    /// If false, pull from left next; if true, pull from right
    pub flip: bool,
}

impl<C: ConstraintOps> MeetWork<C> {
    /// Create a new MeetWork from two nodes.
    pub fn new(left: Node<C>, right: Node<C>) -> Self {
        Self {
            left: Box::new(left),
            right: Box::new(right),
            seen_l: Vec::new(),
            seen_r: Vec::new(),
            seen_l_set: HashSet::new(),
            seen_r_set: HashSet::new(),
            pending: VecDeque::new(),
            flip: false,
        }
    }

    fn take_self(&mut self) -> Self {
        std::mem::replace(self, MeetWork::new(Node::Fail, Node::Fail))
    }

    /// Step this meet work, returning the next state.
    ///
    /// Step policy:
    /// 1. If pending non-empty: emit front
    /// 2. Alternate pulling from left/right (flip)
    /// 3. When new answer arrives, meet with all seen from other side
    /// 4. Push successful meets to pending
    pub fn step(&mut self, terms: &mut TermStore) -> WorkStep<C> {
        // Step 1: If pending has items, emit front
        if let Some(nf) = self.pending.pop_front() {
            return WorkStep::Emit(nf, boxed_work(Work::Meet(self.take_self())));
        }

        // Step 2: Check if both sides are exhausted
        let left_exhausted = matches!(*self.left, Node::Fail);
        let right_exhausted = matches!(*self.right, Node::Fail);

        if left_exhausted && right_exhausted {
            return WorkStep::Done;
        }

        // Step 3: Alternate pulling from left/right based on flip
        // If one side is exhausted, pull from the other
        let pull_from_right = if left_exhausted {
            true
        } else if right_exhausted {
            false
        } else {
            self.flip
        };

        if pull_from_right {
            self.pull_right(terms)
        } else {
            self.pull_left(terms)
        }
    }

    /// Pull from left node and meet with seen_r
    fn pull_left(&mut self, terms: &mut TermStore) -> WorkStep<C> {
        let current = std::mem::replace(&mut *self.left, Node::Fail);
        match step_node(current, terms) {
            NodeStep::Emit(nf, rest) => {
                *self.left = rest;
                if self.seen_l_set.insert(nf.clone()) {
                    self.seen_l.push(nf.clone());
                    for r_nf in self.seen_r.iter() {
                        if let Some(met) = meet_nf(&nf, r_nf, terms) {
                            if !self.pending.contains(&met) {
                                self.pending.push_back(met);
                            }
                        }
                    }
                }
                self.flip = true;
                if let Some(result) = self.pending.pop_front() {
                    WorkStep::Emit(result, boxed_work(Work::Meet(self.take_self())))
                } else {
                    WorkStep::More(boxed_work(Work::Meet(self.take_self())))
                }
            }
            NodeStep::Continue(rest) => {
                *self.left = rest;
                self.flip = true;
                WorkStep::More(boxed_work(Work::Meet(self.take_self())))
            }
            NodeStep::Exhausted => {
                *self.left = Node::Fail;
                self.flip = true;
                WorkStep::More(boxed_work(Work::Meet(self.take_self())))
            }
        }
    }

    /// Pull from right node and meet with seen_l
    fn pull_right(&mut self, terms: &mut TermStore) -> WorkStep<C> {
        let current = std::mem::replace(&mut *self.right, Node::Fail);
        match step_node(current, terms) {
            NodeStep::Emit(nf, rest) => {
                *self.right = rest;
                if self.seen_r_set.insert(nf.clone()) {
                    self.seen_r.push(nf.clone());
                    for l_nf in self.seen_l.iter() {
                        if let Some(met) = meet_nf(l_nf, &nf, terms) {
                            if !self.pending.contains(&met) {
                                self.pending.push_back(met);
                            }
                        }
                    }
                }
                self.flip = false;
                if let Some(result) = self.pending.pop_front() {
                    WorkStep::Emit(result, boxed_work(Work::Meet(self.take_self())))
                } else {
                    WorkStep::More(boxed_work(Work::Meet(self.take_self())))
                }
            }
            NodeStep::Continue(rest) => {
                *self.right = rest;
                self.flip = false;
                WorkStep::More(boxed_work(Work::Meet(self.take_self())))
            }
            NodeStep::Exhausted => {
                *self.right = Node::Fail;
                self.flip = false;
                WorkStep::More(boxed_work(Work::Meet(self.take_self())))
            }
        }
    }
}

// ============================================================================
// FixWork: Call-context tabling for recursive calls
// ============================================================================

type BindId = u64;

static NEXT_BIND_ID: AtomicU64 = AtomicU64::new(1);

#[derive(Clone, Debug)]
struct Binding<C: Clone> {
    id: BindId,
    body: Arc<Rel<C>>,
}

/// Environment for Fix bindings (RelId -> Rel body).
///
/// Uses persistent map for efficient cloning during search.
#[derive(Clone, Debug, Default)]
pub struct Env<C: Clone> {
    bindings: im::HashMap<RelId, Binding<C>>,
}

impl<C: Clone> Env<C> {
    /// Create an empty environment.
    pub fn new() -> Self {
        Self {
            bindings: im::HashMap::new(),
        }
    }

    /// Bind a RelId to a Rel body.
    pub fn bind(&self, id: RelId, body: Arc<Rel<C>>) -> Self {
        let binding = Binding {
            id: NEXT_BIND_ID.fetch_add(1, Ordering::Relaxed),
            body,
        };
        Self {
            bindings: self.bindings.update(id, binding),
        }
    }

    /// Look up a binding.
    fn lookup(&self, id: RelId) -> Option<&Binding<C>> {
        self.bindings.get(&id)
    }

    /// Check if a binding exists.
    pub fn contains(&self, id: RelId) -> bool {
        self.bindings.contains_key(&id)
    }
}

/// Key for call-context tabling.
///
/// Identifies a recursive call by its RelId and adjacent boundary constraints.
/// Two calls with the same key should share their tabled answers.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct CallKey<C: ConstraintOps> {
    /// The relation being called.
    pub rel: RelId,
    /// Unique binding id for the Fix scope.
    pub bind_id: BindId,
    /// Left boundary NF (if any).
    pub left: Option<NF<C>>,
    /// Right boundary NF (if any).
    pub right: Option<NF<C>>,
}

impl<C: ConstraintOps> CallKey<C> {
    /// Create a new CallKey.
    pub fn new(rel: RelId, bind_id: BindId, left: Option<NF<C>>, right: Option<NF<C>>) -> Self {
        Self {
            rel,
            bind_id,
            left,
            right,
        }
    }
}

/// State of a tabled call's producer.
#[derive(Clone, Debug, PartialEq)]
pub enum ProducerState {
    /// Producer hasn't started yet.
    NotStarted,
    /// Producer is currently running.
    Running,
    /// Producer has completed.
    Done,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ProducerStep {
    Progress,
    Blocked,
    Done,
}

/// Spec for rebuilding a producer iteration.
#[derive(Clone, Debug)]
pub struct ProducerSpec<C: ConstraintOps> {
    /// CallKey for ReplayOnly protection.
    pub key: CallKey<C>,
    /// Body of the Fix relation.
    pub body: Arc<Rel<C>>,
    /// Left boundary to apply for this call.
    pub left: Option<NF<C>>,
    /// Right boundary to apply for this call.
    pub right: Option<NF<C>>,
    /// Environment for resolving Fix bindings.
    pub env: Env<C>,
}

#[derive(Debug)]
struct TableAnswers<C: ConstraintOps> {
    answers: Vec<NF<C>>,
    seen: HashSet<NF<C>>,
    waker: QueueWaker,
}

#[derive(Debug)]
struct TableProducer<C: ConstraintOps> {
    state: ProducerState,
    producer: Option<Node<C>>,
    spec: Option<ProducerSpec<C>>,
    iteration_start_len: usize,
    producer_task_active: bool,
}

/// A table entry for a recursive call.
///
/// Stores the answers produced so far and the producer state.
#[derive(Debug)]
pub struct Table<C: ConstraintOps> {
    answers: Mutex<TableAnswers<C>>,
    producer: Mutex<TableProducer<C>>,
}

impl<C: ConstraintOps> Table<C> {
    /// Create a new empty table.
    pub fn new() -> Self {
        Self::with_waker(QueueWaker::noop())
    }

    pub fn with_waker(waker: QueueWaker) -> Self {
        Self {
            answers: Mutex::new(TableAnswers {
                answers: Vec::new(),
                seen: HashSet::new(),
                waker,
            }),
            producer: Mutex::new(TableProducer {
                state: ProducerState::NotStarted,
                producer: None,
                spec: None,
                iteration_start_len: 0,
                producer_task_active: false,
            }),
        }
    }

    /// Add an answer to the table.
    pub fn add_answer(&self, nf: NF<C>) -> bool {
        let mut answers = self.answers.lock();
        if answers.seen.insert(nf.clone()) {
            answers.answers.push(nf);
            answers.waker.wake();
            true
        } else {
            false
        }
    }

    /// Mark the producer as running.
    pub fn start_producer(
        &self,
        producer: Node<C>,
        spec: ProducerSpec<C>,
        iteration_start_len: usize,
    ) {
        let mut guard = self.producer.lock();
        guard.state = ProducerState::Running;
        guard.producer = Some(producer);
        guard.spec = Some(spec);
        guard.iteration_start_len = iteration_start_len;
    }

    /// Mark the producer as done.
    pub fn finish_producer(&self) {
        {
            let mut guard = self.producer.lock();
            guard.state = ProducerState::Done;
            guard.producer = None;
        }
        self.answers.lock().waker.wake();
    }

    /// Check if producer is done.
    pub fn is_done(&self) -> bool {
        self.producer.lock().state == ProducerState::Done
    }

    /// Check if producer is running.
    pub fn is_running(&self) -> bool {
        self.producer.lock().state == ProducerState::Running
    }

    pub fn producer_state(&self) -> ProducerState {
        self.producer.lock().state.clone()
    }

    pub fn producer_task_active(&self) -> bool {
        self.producer.lock().producer_task_active
    }

    pub fn set_producer_task_active(&self, active: bool) {
        self.producer.lock().producer_task_active = active;
    }

    pub fn try_mark_producer_active(&self) -> bool {
        let mut guard = self.producer.lock();
        if guard.producer_task_active || guard.state == ProducerState::Done || guard.spec.is_none()
        {
            false
        } else {
            guard.producer_task_active = true;
            true
        }
    }

    pub fn producer_spec_is_some(&self) -> bool {
        self.producer.lock().spec.is_some()
    }

    pub fn producer_spec_clone(&self) -> Option<ProducerSpec<C>> {
        self.producer.lock().spec.clone()
    }

    pub fn take_producer_node(&self) -> Option<Node<C>> {
        self.producer.lock().producer.take()
    }

    pub fn set_producer_node(&self, node: Node<C>) {
        self.producer.lock().producer = Some(node);
    }

    pub fn iteration_start_len(&self) -> usize {
        self.producer.lock().iteration_start_len
    }

    pub fn set_iteration_start_len(&self, len: usize) {
        self.producer.lock().iteration_start_len = len;
    }

    pub fn answers_len(&self) -> usize {
        self.answers.lock().answers.len()
    }

    pub fn answer_at(&self, index: usize) -> Option<NF<C>> {
        self.answers.lock().answers.get(index).cloned()
    }

    /// Get all answers.
    pub fn all_answers(&self) -> Vec<NF<C>> {
        self.answers.lock().answers.clone()
    }

    pub fn blocked_on(&self) -> BlockedOn {
        self.answers.lock().waker.blocked_on()
    }
}

#[cfg(test)]
impl<C: ConstraintOps> Table<C> {
    fn lock_answers_for_test(&self) -> parking_lot::MutexGuard<'_, TableAnswers<C>> {
        self.answers.lock()
    }

    fn try_lock_answers_for_test(&self) -> Option<parking_lot::MutexGuard<'_, TableAnswers<C>>> {
        self.answers.try_lock()
    }

    fn lock_producer_for_test(&self) -> parking_lot::MutexGuard<'_, TableProducer<C>> {
        self.producer.lock()
    }

    fn try_lock_producer_for_test(&self) -> Option<parking_lot::MutexGuard<'_, TableProducer<C>>> {
        self.producer.try_lock()
    }
}

impl<C: ConstraintOps> Default for Table<C> {
    fn default() -> Self {
        Self::new()
    }
}

pub fn step_table_producer<C: ConstraintOps>(
    table: &Arc<Table<C>>,
    terms: &mut TermStore,
    tables: &Tables<C>,
) -> ProducerStep {
    let state = table.producer_state();
    if state == ProducerState::Done {
        table.set_producer_task_active(false);
        return ProducerStep::Done;
    }

    if state == ProducerState::NotStarted {
        let Some(spec) = table.producer_spec_clone() else {
            table.finish_producer();
            table.set_producer_task_active(false);
            return ProducerStep::Done;
        };
        let mut producer_pipe = PipeWork::from_rel_with_boundaries(
            spec.body.as_ref().clone(),
            spec.left.clone(),
            spec.right.clone(),
            spec.env.clone(),
            tables.clone(),
        );
        producer_pipe.call_mode = CallMode::ReplayOnly(Box::new(spec.key.clone()));
        let producer_node = Node::Work(boxed_work(Work::Pipe(producer_pipe)));
        table.start_producer(producer_node, spec, table.answers_len());
    }

    let current = table.take_producer_node().unwrap_or(Node::Fail);

    let step = step_node(current, terms);
    match step {
        NodeStep::Emit(nf, rest) => {
            let _ = table.add_answer(nf);
            table.set_producer_node(rest);
            ProducerStep::Progress
        }
        NodeStep::Continue(rest) => {
            table.set_producer_node(rest);
            ProducerStep::Progress
        }
        NodeStep::Exhausted => {
            let has_new = table.answers_len() > table.iteration_start_len();
            if has_new {
                let Some(spec) = table.producer_spec_clone() else {
                    table.finish_producer();
                    table.set_producer_task_active(false);
                    return ProducerStep::Done;
                };
                let mut producer_pipe = PipeWork::from_rel_with_boundaries(
                    spec.body.as_ref().clone(),
                    spec.left.clone(),
                    spec.right.clone(),
                    spec.env.clone(),
                    tables.clone(),
                );
                producer_pipe.call_mode = CallMode::ReplayOnly(Box::new(spec.key.clone()));
                table.set_iteration_start_len(table.answers_len());
                table.set_producer_node(Node::Work(boxed_work(Work::Pipe(producer_pipe))));
                ProducerStep::Progress
            } else {
                table.finish_producer();
                table.set_producer_task_active(false);
                ProducerStep::Done
            }
        }
    }
}

type TableMap<C> = DashMap<CallKey<C>, Arc<Table<C>>>;

/// Collection of tables for call-context tabling.
///
/// Uses a shared concurrent map so all clones see the same tables.
#[derive(Clone, Debug)]
pub struct Tables<C: ConstraintOps> {
    map: Arc<TableMap<C>>,
    queue_bound: usize,
    wake_hub: Arc<WakeHub>,
}

impl<C: ConstraintOps> Tables<C> {
    /// Create an empty Tables collection.
    pub fn new() -> Self {
        Self::with_queue_bound(64)
    }

    pub fn with_queue_bound(queue_bound: usize) -> Self {
        let (wake_hub, _rx) = WakeHub::new();
        Self::with_queue_bound_and_waker(queue_bound, wake_hub)
    }

    pub fn with_queue_bound_and_waker(queue_bound: usize, wake_hub: Arc<WakeHub>) -> Self {
        Self {
            map: Arc::new(DashMap::new()),
            queue_bound: queue_bound.max(1),
            wake_hub,
        }
    }

    /// Look up a table by CallKey.
    pub fn lookup(&self, key: &CallKey<C>) -> Option<Arc<Table<C>>> {
        self.map.get(key).map(|entry| entry.value().clone())
    }

    /// Get or create a table for a CallKey.
    pub fn get_or_create(&self, key: CallKey<C>) -> Arc<Table<C>> {
        if let Some(table) = self.map.get(&key) {
            return table.value().clone();
        }
        let table = Arc::new(Table::with_waker(self.waker()));
        let entry = self.map.entry(key).or_insert(table.clone());
        entry.value().clone()
    }

    /// Check if a table exists for a CallKey.
    pub fn contains(&self, key: &CallKey<C>) -> bool {
        self.map.contains_key(key)
    }

    /// Get the number of tables.
    pub fn len(&self) -> usize {
        self.map.len()
    }

    /// Check if empty.
    pub fn is_empty(&self) -> bool {
        self.map.is_empty()
    }

    pub fn queue_bound(&self) -> usize {
        self.queue_bound
    }

    pub fn waker(&self) -> QueueWaker {
        self.wake_hub.waker()
    }
}

impl<C: ConstraintOps> Default for Tables<C> {
    fn default() -> Self {
        Self::new()
    }
}

/// FixWork: table handle that streams answers and steps the producer inline.
///
/// The producer runs in iterations. Each iteration evaluates the body with
/// replay-only calls for the current CallKey.
#[derive(Clone, Debug)]
pub struct FixWork<C: ConstraintOps> {
    /// The CallKey for this tabled call.
    pub key: CallKey<C>,
    /// Reference to the table.
    pub table: Arc<Table<C>>,
    /// Current answer index for this handle.
    pub answer_index: usize,
    /// Tables for nested calls.
    pub tables: Tables<C>,
}

impl<C: ConstraintOps> FixWork<C> {
    /// Create a new FixWork handle.
    pub fn new(
        key: CallKey<C>,
        table: Arc<Table<C>>,
        start_index: usize,
        tables: Tables<C>,
    ) -> Self {
        Self {
            key,
            table,
            answer_index: start_index,
            tables,
        }
    }

    /// Step this FixWork handle.
    pub fn step(&mut self, terms: &mut TermStore) -> WorkStep<C> {
        let _ = terms;
        if let Some(nf) = self.table.answer_at(self.answer_index) {
            self.answer_index += 1;
            return WorkStep::Emit(nf, boxed_work(Work::Fix(self.clone())));
        }

        if self.table.is_done() {
            return WorkStep::Done;
        }

        if !self.table.try_mark_producer_active() {
            if self.table.is_done() {
                return WorkStep::Done;
            }
            return WorkStep::More(boxed_work(Work::Fix(self.clone())));
        }

        let step = step_table_producer(&self.table, terms, &self.tables);
        self.table.set_producer_task_active(false);

        if let Some(nf) = self.table.answer_at(self.answer_index) {
            self.answer_index += 1;
            return WorkStep::Emit(nf, boxed_work(Work::Fix(self.clone())));
        }

        match step {
            ProducerStep::Done => WorkStep::Done,
            ProducerStep::Progress | ProducerStep::Blocked => {
                WorkStep::More(boxed_work(Work::Fix(self.clone())))
            }
        }
    }
}


#[cfg(test)]
mod tests;


