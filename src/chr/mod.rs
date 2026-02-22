use crate::constraint::ConstraintDisplay;
use crate::matching::unify_into;
use crate::nf::apply_var_renaming;
use crate::subst::{apply_subst, Subst};
use crate::symbol::FuncId;
use crate::term::{Term, TermId, TermReadGuard, TermStore};
use hashbrown::{HashMap, HashSet};
use smallvec::SmallVec;
use std::cell::RefCell;
use std::cmp::Ordering;
use std::collections::VecDeque;
use std::hash::{Hash, Hasher};
use std::sync::atomic::{AtomicU64, Ordering as AtomicOrdering};
use std::sync::Arc;

/// Thread-local cache for normalize_owned results.
///
/// Keyed by a fast hash of the pre-normalization ChrState (alive constraints
/// and their term arguments). The cache is invalidated when the TermStore
/// generation changes (indicating a new engine run with a fresh TermStore).
struct NormalizeCache {
    generation: u64,
    entries: HashMap<u64, Option<(ChrState, Option<Subst>)>>,
}

impl NormalizeCache {
    fn new() -> Self {
        Self {
            generation: u64::MAX,
            entries: HashMap::new(),
        }
    }
}

thread_local! {
    static NORMALIZE_CACHE: RefCell<NormalizeCache> = RefCell::new(NormalizeCache::new());
}

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

/// Pre-flattened match operation for cache-friendly linear pattern matching.
///
/// Instead of walking a PatNode tree via PatArena indirection at match time,
/// we pre-flatten each head's argument patterns into a contiguous array of
/// these ops at program construction time. This eliminates PatArena lookups,
/// SmallVec push/pop of (PatId, TermId) pairs, and PatNode dispatch during
/// the hot matching loop.
#[derive(Clone, Debug)]
pub enum FlatMatchOp {
    /// Push the next root term from the head argument list onto the work stack.
    PushRoot,
    /// Pop a term, check it is App(f, children) with the given arity.
    /// If match: push children in reverse onto work stack (for pre-order).
    /// If mismatch: fail immediately.
    CheckApp(FuncId, u8),
    /// Pop a term, bind it to the given RVar.
    BindVar(RVar),
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

/// Flatten a head pattern's argument list into a contiguous array of FlatMatchOps.
///
/// For each arg PatId, emits a PushRoot followed by a pre-order traversal of the
/// pattern tree. The result is a single linear sequence that can match all args
/// of a head in one tight loop.
fn flatten_head_pat(pats: &PatArena, args: &[PatId]) -> Box<[FlatMatchOp]> {
    let mut ops = Vec::new();
    for &arg in args {
        ops.push(FlatMatchOp::PushRoot);
        flatten_pat_preorder(pats, arg, &mut ops);
    }
    ops.into_boxed_slice()
}

/// Emit FlatMatchOps for a single pattern node in pre-order.
fn flatten_pat_preorder(pats: &PatArena, pat: PatId, ops: &mut Vec<FlatMatchOp>) {
    match pats.get(pat) {
        PatNode::RVar(rv) => {
            ops.push(FlatMatchOp::BindVar(*rv));
        }
        PatNode::App { f, kids } => {
            ops.push(FlatMatchOp::CheckApp(*f, kids.len() as u8));
            for kid in kids.iter() {
                flatten_pat_preorder(pats, *kid, ops);
            }
        }
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

    /// Grow internal vectors if needed to accommodate `n_rvars` slots.
    pub fn ensure_capacity(&mut self, n_rvars: u32) {
        let n = n_rvars as usize;
        if n > self.stamp.len() {
            self.stamp.resize(n, 0);
            self.val.resize(n, TermId::from_raw(0));
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

pub(crate) fn match_pat_nobind(
    pats: &PatArena,
    terms: &TermStore,
    pat: PatId,
    term: TermId,
    env: &RVarEnv,
) -> bool {
    let guard = terms.read_lock();
    match_pat_nobind_locked(pats, &guard, pat, term, env)
}

#[inline]
fn match_pat_nobind_locked(
    pats: &PatArena,
    guard: &TermReadGuard<'_>,
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
            PatNode::App { f, kids } => {
                // Handle inline nullary: check functor match with no children.
                if t.is_inline_nullary() {
                    if kids.is_empty() {
                        let func_raw = t.inline_nullary_func_raw();
                        if func_raw != f.into_inner().get() {
                            return false;
                        }
                        // Match: nullary pattern vs nullary inline term, same functor.
                    } else {
                        return false; // nullary term vs non-nullary pattern
                    }
                } else {
                    match guard.get(t) {
                        Some(Term::App(tf, tks)) => {
                            if *f != *tf || kids.len() != tks.len() {
                                return false;
                            }
                            for (cp, ct) in kids.iter().zip(tks.iter()) {
                                stack.push((*cp, *ct));
                            }
                        }
                        _ => return false,
                    }
                }
            }
        }
    }
    true
}

#[derive(Copy, Clone)]
pub struct Builtin {
    pub arity: u8,
    pub guard: fn(&Subst, &TermStore, &[TermId]) -> bool,
    pub add: fn(&mut Subst, &TermStore, &[TermId]) -> bool,
}

#[derive(Clone, Default)]
pub struct BuiltinRegistry {
    pub builtins: Vec<Builtin>,
}

impl std::fmt::Debug for Builtin {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Builtin")
            .field("arity", &self.arity)
            .finish()
    }
}

impl std::fmt::Debug for BuiltinRegistry {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("BuiltinRegistry")
            .field("builtins_len", &self.builtins.len())
            .finish()
    }
}

impl BuiltinRegistry {
    pub fn get(&self, id: BuiltinId) -> &Builtin {
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

    pub fn eval(
        &self,
        pats: &PatArena,
        terms: &TermStore,
        eq_subst: &Subst,
        reg: &BuiltinRegistry,
        env: &RVarEnv,
    ) -> bool {
        for ins in self.code.iter() {
            let ok = match ins {
                GuardInstr::Eq(a, b) => {
                    let (ta, tb) = match eval_gval_pair(env, *a, *b) {
                        Some(pair) => pair,
                        None => return false,
                    };
                    ta == tb
                }
                GuardInstr::Neq(a, b) => {
                    let (ta, tb) = match eval_gval_pair(env, *a, *b) {
                        Some(pair) => pair,
                        None => return false,
                    };
                    ta != tb
                }
                GuardInstr::TopFunctor { t, f, arity } => {
                    let tt = match eval_gval(env, *t) {
                        Some(x) => x,
                        None => return false,
                    };
                    terms.with_term(tt, |resolved| match resolved {
                        Some(Term::App(tf, kids)) => *tf == *f && kids.len() == (*arity as usize),
                        _ => false,
                    })
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
                    (b.guard)(eq_subst, terms, &av)
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

    pub fn exec(
        &self,
        pats: &PatArena,
        terms: &mut TermStore,
        reg: &BuiltinRegistry,
        env: &RVarEnv,
        st: &mut ChrState,
    ) -> bool {
        let program = Arc::clone(&st.program);
        let d = st.data_mut();
        self.exec_with_data(pats, terms, reg, env, &program, d)
    }

    fn exec_with_data(
        &self,
        pats: &PatArena,
        terms: &mut TermStore,
        reg: &BuiltinRegistry,
        env: &RVarEnv,
        program: &ChrProgram,
        data: &mut ChrStateData,
    ) -> bool {
        for ins in self.code.iter() {
            match ins {
                BodyInstr::AddChr { pred, args } => {
                    let av = match collect_args(args, pats, terms, env) {
                        Some(v) => v,
                        None => return false,
                    };
                    let cid = Cid(data.next_cid);
                    data.next_cid = data.next_cid.saturating_add(1);
                    let specs = &program.preds[pred.0 as usize].index_specs;
                    data.store.add_chr(cid, *pred, &av, terms, specs);
                    data.agenda.push_back(cid);
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
                    if !(b.add)(&mut data.eq_subst, terms, &av) {
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

pub(crate) fn instantiate_pat(
    pats: &PatArena,
    terms: &mut TermStore,
    env: &RVarEnv,
    root: PatId,
) -> Option<TermId> {
    let mut stack: SmallVec<[(PatId, usize); 8]> = SmallVec::new();
    stack.push((root, 0));
    let mut out: SmallVec<[TermId; 8]> = SmallVec::new();
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

    /// Create a lightweight stub that won't be used for index lookups.
    /// Avoids allocating HashMap entries for each IndexSpec.
    fn new_stub() -> Self {
        Self {
            all: Vec::new(),
            indexes: Vec::new(),
        }
    }

    fn insert(&mut self, cid: Cid, args: &[TermId], terms: &TermStore, specs: &[IndexSpec]) {
        self.all.push(cid);
        for (i, spec) in specs.iter().enumerate() {
            match (spec, &mut self.indexes[i]) {
                (IndexSpec::PredOnly, _) => {}
                (IndexSpec::ArgTerm(pos), IndexData::ArgTerm(map)) => {
                    let p = *pos as usize;
                    if p < args.len() {
                        map.entry(args[p]).or_default().push(cid);
                    }
                }
                (IndexSpec::ArgTopFunctor(pos), IndexData::ArgTopFunctor(map)) => {
                    let p = *pos as usize;
                    if p < args.len() {
                        terms.with_term(args[p], |resolved| {
                            if let Some(Term::App(f, _)) = resolved {
                                map.entry(*f).or_default().push(cid);
                            }
                        });
                    }
                }
                (IndexSpec::ArgPairTerm(a, b), IndexData::ArgPairTerm(map)) => {
                    let ia = *a as usize;
                    let ib = *b as usize;
                    if ia < args.len() && ib < args.len() {
                        let key = (args[ia], args[ib]);
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
    pub arg_start: u32,
    pub arg_count: u16,
    pub alive: bool,
}

#[derive(Clone, Debug)]
pub struct ChrStore {
    pub inst: Vec<CInstance>,
    pub all_args: Vec<TermId>,
    pub preds: Vec<PredStore>,
    pub alive_count: u32,
    pub dead_count: u32,
    /// When true, PredStore indexes are not populated because the program
    /// uses only single-head simplification rules that never read them.
    skip_indexes: bool,
}

impl ChrStore {
    pub const fn const_empty() -> Self {
        Self {
            inst: Vec::new(),
            all_args: Vec::new(),
            preds: Vec::new(),
            alive_count: 0,
            dead_count: 0,
            skip_indexes: false,
        }
    }

    /// Get the args slice for a CInstance.
    #[inline]
    pub fn args(&self, inst: &CInstance) -> &[TermId] {
        let start = inst.arg_start as usize;
        let end = start + inst.arg_count as usize;
        &self.all_args[start..end]
    }

    /// Get a mutable args slice for a CInstance.
    #[inline]
    pub fn args_mut(&mut self, inst: &CInstance) -> &mut [TermId] {
        let start = inst.arg_start as usize;
        let end = start + inst.arg_count as usize;
        &mut self.all_args[start..end]
    }

    pub fn new(preds: &[PredDecl], skip_indexes: bool) -> Self {
        let pred_stores: Vec<PredStore> = if skip_indexes {
            (0..preds.len()).map(|_| PredStore::new_stub()).collect()
        } else {
            preds
                .iter()
                .map(|p| PredStore::new(&p.index_specs))
                .collect()
        };
        Self {
            inst: Vec::new(),
            all_args: Vec::new(),
            preds: pred_stores,
            alive_count: 0,
            dead_count: 0,
            skip_indexes,
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
        let arg_start = self.all_args.len() as u32;
        let arg_count = args.len() as u16;
        self.all_args.extend_from_slice(args);
        let inst = CInstance {
            cid,
            pred,
            arg_start,
            arg_count,
            alive: true,
        };
        self.inst.push(inst);
        if !self.skip_indexes {
            let args_slice =
                &self.all_args[arg_start as usize..(arg_start as usize + arg_count as usize)];
            let pred_store = &mut self.preds[pred.0 as usize];
            pred_store.insert(cid, args_slice, terms, specs);
        }
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
        if self.skip_indexes {
            // Still recount alive/dead but skip all index construction.
            self.alive_count = 0;
            self.dead_count = 0;
            for inst in self.inst.iter() {
                if inst.alive {
                    self.alive_count += 1;
                } else {
                    self.dead_count += 1;
                }
            }
            return;
        }
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
                let args = &self.all_args
                    [inst.arg_start as usize..(inst.arg_start as usize + inst.arg_count as usize)];
                self.preds[pred.0 as usize].insert(inst.cid, args, terms, specs);
            } else {
                self.dead_count += 1;
            }
        }
    }

    /// Index only constraints starting from `from` position.
    /// Assumes indexes for constraints before `from` are already up-to-date.
    fn index_from(&mut self, from: usize, preds: &[PredDecl], terms: &TermStore) {
        for inst in self.inst[from..].iter() {
            if inst.alive {
                if !self.skip_indexes {
                    let pred = inst.pred;
                    let specs = &preds[pred.0 as usize].index_specs;
                    let args = &self.all_args[inst.arg_start as usize
                        ..(inst.arg_start as usize + inst.arg_count as usize)];
                    self.preds[pred.0 as usize].insert(inst.cid, args, terms, specs);
                }
                self.alive_count += 1;
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

#[derive(Debug, Clone)]
pub struct Rule {
    pub rid: RuleId,
    pub n_rvars: u32,
    pub heads: Box<[HeadPat]>,
    /// Pre-flattened match ops per head, indexed by head position.
    /// Each inner `Box<[FlatMatchOp]>` is a contiguous sequence of ops
    /// that matches all args of that head in a single linear scan.
    pub head_flat_ops: Box<[Box<[FlatMatchOp]>]>,
    pub guard: GuardProg,
    pub body: BodyProg,
    pub priority: i32,
    pub is_propagation: bool,
    pub occs: Box<[Occurrence]>,
    pub removed_mask: u64,
}

#[derive(Clone, Debug)]
pub struct OccRef {
    pub rid: RuleId,
    pub occ: u16,
}

/// First-argument functor-indexed trigger dispatch table.
///
/// For each predicate, partitions rule occurrences by the top-level functor
/// of the anchor head's first argument pattern:
/// - `by_functor[f]` → rules whose first arg pattern is `App(f, ...)`
/// - `fallback` → rules whose first arg is a variable (matches anything),
///   or rules with arity-0 heads (no argument to index on)
///
/// At dispatch time, a constraint `pred(t, ...)` looks up `t`'s top functor
/// and tries only `by_functor[f] ++ fallback`, skipping rules that cannot match.
#[derive(Clone, Debug)]
pub struct IndexedTriggers {
    pub by_functor: HashMap<FuncId, Vec<OccRef>>,
    pub fallback: Vec<OccRef>,
}

#[derive(Debug, Clone)]
pub struct ChrProgram {
    pub preds: Box<[PredDecl]>,
    pub rules: Box<[Rule]>,
    pub triggers: Vec<IndexedTriggers>,
    pub pats: PatArena,
    pub builtins: BuiltinRegistry,
    pub pred_names: HashMap<String, PredId>,
    pub program_id: u64,
    pub max_rvars: u32,
    /// True iff every rule in the program has exactly one head and is a
    /// simplification rule (not propagation).  When set, `solve_to_fixpoint`
    /// uses a specialised inline loop that avoids Vec allocations, SearchCtx
    /// construction, and propagation-token handling.
    pub all_single_head_simplification: bool,
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
pub struct ChrProgramBuilder {
    preds: Vec<PredDecl>,
    pred_names: HashMap<String, PredId>,
    rules: Vec<RuleDraft>,
    pats: PatArena,
    builtins: BuiltinRegistry,
}

impl Default for ChrProgramBuilder {
    fn default() -> Self {
        Self::new()
    }
}

impl ChrProgramBuilder {
    pub fn new() -> Self {
        let mut builtins = BuiltinRegistry::default();
        // BuiltinId(0): equality — `$x = $y` in rule bodies calls unify_into.
        builtins.builtins.push(Builtin {
            arity: 2,
            guard: |_eq_subst, _terms, args| args[0] == args[1],
            add: |eq_subst, terms, args| {
                let guard = terms.read_lock();
                unify_into(eq_subst, args[0], args[1], &guard)
            },
        });
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

    pub fn build(self) -> Arc<ChrProgram> {
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

            // Pre-flatten each head's arg patterns into contiguous match ops.
            let head_flat_ops: Box<[Box<[FlatMatchOp]>]> = heads
                .iter()
                .map(|head| flatten_head_pat(&self.pats, &head.args))
                .collect::<Vec<_>>()
                .into_boxed_slice();

            rules.push(Rule {
                rid: RuleId(idx as u32),
                n_rvars,
                heads: heads.into_boxed_slice(),
                head_flat_ops,
                guard: draft.guard,
                body: draft.body,
                priority: draft.priority,
                is_propagation,
                occs,
                removed_mask,
            });
        }

        let max_rvars = rules.iter().map(|r| r.n_rvars).max().unwrap_or(0);

        let all_single_head_simplification = !rules.is_empty()
            && rules
                .iter()
                .all(|r| r.heads.len() == 1 && !r.is_propagation);

        // Build first-argument indexed trigger tables.
        let mut triggers: Vec<IndexedTriggers> = (0..self.preds.len())
            .map(|_| IndexedTriggers {
                by_functor: HashMap::new(),
                fallback: Vec::new(),
            })
            .collect();

        for rule in rules.iter() {
            for (occ_idx, occ) in rule.occs.iter().enumerate() {
                let head = &rule.heads[occ.anchor_head as usize];
                let occ_ref = OccRef {
                    rid: rule.rid,
                    occ: occ_idx as u16,
                };
                let trig = &mut triggers[head.pred.0 as usize];

                // Index by the top-level functor of the first argument pattern.
                if let Some(first_arg) = head.args.first() {
                    match self.pats.get(*first_arg) {
                        PatNode::App { f, .. } => {
                            trig.by_functor.entry(*f).or_default().push(occ_ref);
                        }
                        PatNode::RVar(_) => {
                            trig.fallback.push(occ_ref);
                        }
                    }
                } else {
                    // Arity-0 head: no argument to index on.
                    trig.fallback.push(occ_ref);
                }
            }
        }

        // Sort each bucket by priority.
        for trig in triggers.iter_mut() {
            for bucket in trig.by_functor.values_mut() {
                bucket.sort_by(|a, b| occ_ref_order(a, b, &rules));
            }
            trig.fallback.sort_by(|a, b| occ_ref_order(a, b, &rules));
        }

        Arc::new(ChrProgram {
            preds: self.preds.into_boxed_slice(),
            rules: rules.into_boxed_slice(),
            triggers,
            pats: self.pats,
            builtins: self.builtins,
            pred_names: self.pred_names,
            program_id,
            max_rvars,
            all_single_head_simplification,
        })
    }
}

fn occ_ref_order(a: &OccRef, b: &OccRef, rules: &[Rule]) -> Ordering {
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

    /// Create an empty token store for programs where tokens are never used.
    /// This avoids allocating N empty HashSets that will never be accessed.
    fn empty() -> Self {
        Self { fired: Vec::new() }
    }
}

pub struct ChrStateData {
    pub(crate) store: ChrStore,
    /// Accumulated equality substitution from builtin `$x = $y` in rule bodies.
    /// Transient: only non-empty during `normalize_owned_uncached` between
    /// `solve_to_fixpoint` and the extract+apply step. Always empty in
    /// freeze/thaw/combine/remap/collect_vars contexts.
    pub(crate) eq_subst: Subst,
    pub(crate) tokens: TokenStore,
    pub(crate) next_cid: u32,
    pub(crate) agenda: VecDeque<Cid>,
    pub(crate) failed: bool,
    /// Constraints with `cid.0 < fixpoint_watermark` are already at CHR fixpoint
    /// and do not need to be re-enqueued for agenda processing.
    pub(crate) fixpoint_watermark: u32,
    /// Cached flag: true when every alive constraint arg has `is_ground()` set.
    /// When true, apply_subst/remap_vars can skip the expensive ChrStateData
    /// clone + arg walk because no variable can change.
    pub(crate) all_args_ground: bool,
}

impl Clone for ChrStateData {
    fn clone(&self) -> Self {
        Self {
            store: self.store.clone(),
            eq_subst: self.eq_subst.clone(),
            tokens: self.tokens.clone(),
            next_cid: self.next_cid,
            agenda: self.agenda.clone(),
            failed: self.failed,
            fixpoint_watermark: self.fixpoint_watermark,
            all_args_ground: self.all_args_ground,
        }
    }
}

impl ChrStateData {
    /// Recompute the `all_args_ground` flag by checking all alive constraint args.
    fn recompute_all_args_ground(&mut self) {
        self.all_args_ground = self.store.inst.iter().all(|inst| {
            if !inst.alive {
                return true;
            }
            self.store.args(inst).iter().all(|arg| arg.is_ground())
        });
    }
}

pub struct ChrState {
    pub program: Arc<ChrProgram>,
    data: Option<Arc<ChrStateData>>,
}

impl Clone for ChrState {
    fn clone(&self) -> Self {
        Self {
            program: self.program.clone(),
            data: self.data.clone(),
        }
    }
}

impl ChrState {
    #[inline]
    pub fn data(&self) -> Option<&ChrStateData> {
        self.data.as_deref()
    }

    #[inline]
    pub fn data_mut(&mut self) -> &mut ChrStateData {
        let program = &self.program;
        let arc = self.data.get_or_insert_with(|| {
            let tokens = if program.all_single_head_simplification {
                TokenStore::empty()
            } else {
                TokenStore::new(program.rules.len())
            };
            Arc::new(ChrStateData {
                store: ChrStore::new(&program.preds, program.all_single_head_simplification),
                eq_subst: Subst::default(),
                tokens,
                next_cid: 0,
                agenda: VecDeque::new(),
                failed: false,
                fixpoint_watermark: 0,
                all_args_ground: true, // empty store has no args
            })
        });
        Arc::make_mut(arc)
    }

    #[inline]
    pub fn store(&self) -> &ChrStore {
        static EMPTY_STORE: ChrStore = ChrStore::const_empty();
        match &self.data {
            Some(d) => &d.store,
            None => &EMPTY_STORE,
        }
    }

    #[inline]
    pub fn has_data(&self) -> bool {
        self.data.is_some()
    }

    pub fn new(program: Arc<ChrProgram>) -> Self {
        let skip_idx = program.all_single_head_simplification;
        let tokens = if skip_idx {
            TokenStore::empty()
        } else {
            TokenStore::new(program.rules.len())
        };
        Self {
            data: Some(Arc::new(ChrStateData {
                store: ChrStore::new(&program.preds, skip_idx),
                eq_subst: Subst::default(),
                tokens,
                next_cid: 0,
                agenda: VecDeque::new(),
                failed: false,
                fixpoint_watermark: 0,
                all_args_ground: true, // empty store has no args
            })),
            program,
        }
    }

    pub fn introduce(&mut self, pred: PredId, args: &[TermId], terms: &TermStore) -> Cid {
        let program = &self.program;
        let arc = self.data.get_or_insert_with(|| {
            let tokens = if program.all_single_head_simplification {
                TokenStore::empty()
            } else {
                TokenStore::new(program.rules.len())
            };
            Arc::new(ChrStateData {
                store: ChrStore::new(&program.preds, program.all_single_head_simplification),
                eq_subst: Subst::default(),
                tokens,
                next_cid: 0,
                agenda: VecDeque::new(),
                failed: false,
                fixpoint_watermark: 0,
                all_args_ground: true,
            })
        });
        let d = Arc::make_mut(arc);
        let cid = Cid(d.next_cid);
        d.next_cid = d.next_cid.saturating_add(1);
        let specs = &program.preds[pred.0 as usize].index_specs;
        d.store.add_chr(cid, pred, args, terms, specs);
        // Update all_args_ground: if it was true and new args have non-ground terms, set to false
        if d.all_args_ground && !args.iter().all(|a| a.is_ground()) {
            d.all_args_ground = false;
        }
        d.agenda.push_back(cid);
        cid
    }

    pub fn solve_to_fixpoint(&mut self, terms: &mut TermStore) -> bool {
        let d = match self.data.as_mut() {
            Some(arc) => Arc::make_mut(arc),
            None => return true,
        };
        if d.failed {
            return false;
        }

        if self.program.all_single_head_simplification {
            Self::solve_to_fixpoint_single_head(&self.program, d, terms);
        } else {
            Self::solve_to_fixpoint_general(&self.program, d, terms);
        }
        !d.failed
    }

    /// General solve_to_fixpoint for programs with multi-head or propagation rules.
    fn solve_to_fixpoint_general(
        program: &ChrProgram,
        d: &mut ChrStateData,
        terms: &mut TermStore,
    ) {
        let mut env = RVarEnv::new(program.max_rvars);
        while let Some(cid) = d.agenda.pop_front() {
            if !Self::is_alive_in(&d.store, cid) {
                continue;
            }
            let inst = &d.store.inst[cid.0 as usize];
            let pred = inst.pred;
            let indexed = &program.triggers[pred.0 as usize];

            let inst_args = d.store.args(inst);
            let first_arg_functor: Option<FuncId> = inst_args.first().and_then(|tid| {
                terms.with_term(*tid, |t| match t? {
                    Term::App(f, _) => Some(*f),
                    Term::Var(_) => None,
                })
            });

            let indexed_occs = first_arg_functor
                .and_then(|f| indexed.by_functor.get(&f))
                .map(|v| v.as_slice())
                .unwrap_or(&[]);

            let mut fired = false;
            for occ_ref in indexed_occs.iter().chain(indexed.fallback.iter()) {
                if let Some(tuple) = Self::find_match_by_ids_reuse(
                    program,
                    d,
                    occ_ref.rid,
                    occ_ref.occ,
                    cid,
                    terms,
                    &mut env,
                ) {
                    if !Self::apply_rule_by_id_reuse(
                        program,
                        d,
                        occ_ref.rid,
                        &tuple,
                        terms,
                        &mut env,
                    ) {
                        d.failed = true;
                        return;
                    }
                    fired = true;
                    break;
                }
            }
            let _ = fired;
        }
    }

    /// Specialized solve_to_fixpoint for programs where ALL rules are single-head
    /// simplification rules.  Avoids Vec allocations for chosen/tuple arrays,
    /// SearchCtx construction, search_steps_inner recursion, and propagation
    /// token handling.
    fn solve_to_fixpoint_single_head(
        program: &ChrProgram,
        d: &mut ChrStateData,
        terms: &mut TermStore,
    ) {
        let mut env = RVarEnv::new(program.max_rvars);
        while let Some(cid) = d.agenda.pop_front() {
            if !Self::is_alive_in(&d.store, cid) {
                continue;
            }
            let inst = &d.store.inst[cid.0 as usize];
            let pred = inst.pred;
            let indexed = &program.triggers[pred.0 as usize];

            let inst_args = d.store.args(inst);
            let first_arg_functor: Option<FuncId> = inst_args.first().and_then(|tid| {
                terms.with_term(*tid, |t| match t? {
                    Term::App(f, _) => Some(*f),
                    Term::Var(_) => None,
                })
            });

            let indexed_occs = first_arg_functor
                .and_then(|f| indexed.by_functor.get(&f))
                .map(|v| v.as_slice())
                .unwrap_or(&[]);

            for occ_ref in indexed_occs.iter().chain(indexed.fallback.iter()) {
                let rule = &program.rules[occ_ref.rid.0 as usize];
                let occ = &rule.occs[occ_ref.occ as usize];
                let anchor_idx = occ.anchor_head as usize;
                let anchor_head = &rule.heads[anchor_idx];
                let anchor_flat = &rule.head_flat_ops[anchor_idx];

                env.ensure_capacity(rule.n_rvars);
                env.reset();

                let inst_ref = &d.store.inst[cid.0 as usize];
                let inst_ref_args = d.store.args(inst_ref);
                if !match_head(
                    terms,
                    anchor_head,
                    anchor_flat,
                    inst_ref,
                    inst_ref_args,
                    &mut env,
                ) {
                    continue;
                }

                // Single-head: no join steps.  Evaluate guard directly.
                if !rule
                    .guard
                    .eval(&program.pats, terms, &d.eq_subst, &program.builtins, &env)
                {
                    continue;
                }

                // Single-head simplification: always mark dead (removed_mask bit 0
                // is always set for single-head simplification rules).
                d.store.mark_dead(cid);

                // Execute body with inline matching: new constraints created
                // by the body are matched against rules before being stored,
                // avoiding the store/agenda roundtrip for matched constraints.
                if !exec_body_inline(
                    &rule.body,
                    &program.pats,
                    terms,
                    &program.builtins,
                    &env,
                    program,
                    d,
                ) {
                    d.failed = true;
                    return;
                }
                break;
            }
        }
    }
}

struct SearchCtx<'a> {
    program: &'a ChrProgram,
    data: &'a ChrStateData,
    rule: &'a Rule,
    occ: &'a Occurrence,
    terms: &'a TermStore,
}

impl ChrState {
    /// Find a match for a rule occurrence using a pre-allocated `RVarEnv`.
    fn find_match_by_ids_reuse(
        program: &ChrProgram,
        data: &ChrStateData,
        rid: RuleId,
        occ_idx: u16,
        active: Cid,
        terms: &TermStore,
        env: &mut RVarEnv,
    ) -> Option<Vec<Cid>> {
        let rule = &program.rules[rid.0 as usize];
        let occ = &rule.occs[occ_idx as usize];
        env.ensure_capacity(rule.n_rvars);
        env.reset();
        let mut chosen: Vec<Option<Cid>> = vec![None; rule.heads.len()];
        let anchor_idx = occ.anchor_head as usize;
        let anchor_head = &rule.heads[anchor_idx];
        let anchor_flat = &rule.head_flat_ops[anchor_idx];
        let inst = &data.store.inst[active.0 as usize];
        let inst_args = data.store.args(inst);
        if !match_head(terms, anchor_head, anchor_flat, inst, inst_args, env) {
            return None;
        }
        chosen[occ.anchor_head as usize] = Some(active);
        let ctx = SearchCtx {
            program,
            data,
            rule,
            occ,
            terms,
        };
        Self::search_steps_inner(&ctx, 0, env, &mut chosen)
    }

    /// Apply a matched rule. The `env` must already contain the variable
    /// bindings produced by `find_match_by_ids_reuse` — we skip re-matching
    /// heads since those bindings are still live in the env.
    fn apply_rule_by_id_reuse(
        program: &ChrProgram,
        data: &mut ChrStateData,
        rid: RuleId,
        tuple: &[Cid],
        terms: &mut TermStore,
        env: &mut RVarEnv,
    ) -> bool {
        let rule = &program.rules[rid.0 as usize];
        let removed_mask = rule.removed_mask;

        if rule.is_propagation {
            let token = TokenKey::from_cids(tuple.to_vec());
            data.tokens.fired[rid.0 as usize].insert(token);
        }

        for (i, cid) in tuple.iter().copied().enumerate() {
            if (removed_mask & (1u64 << i)) != 0 {
                data.store.mark_dead(cid);
            }
        }

        // env already has correct bindings from find_match_by_ids_reuse —
        // no reset or re-matching needed.

        rule.body
            .exec_with_data(&program.pats, terms, &program.builtins, env, program, data)
    }

    fn search_steps_inner(
        ctx: &SearchCtx<'_>,
        step_idx: usize,
        env: &mut RVarEnv,
        chosen: &mut Vec<Option<Cid>>,
    ) -> Option<Vec<Cid>> {
        if step_idx == ctx.occ.steps.len() {
            if !ctx.rule.guard.eval(
                &ctx.program.pats,
                ctx.terms,
                &ctx.data.eq_subst,
                &ctx.program.builtins,
                env,
            ) {
                return None;
            }
            let tuple: Vec<Cid> = chosen.iter().map(|c| c.expect("head cid")).collect();
            if ctx.rule.is_propagation {
                let token = TokenKey::from_cids(tuple.clone());
                if ctx.data.tokens.fired[ctx.rule.rid.0 as usize].contains(&token) {
                    return None;
                }
            }
            return Some(tuple);
        }

        let step = &ctx.occ.steps[step_idx];
        let cands = Self::candidates_for_step_inner(&ctx.data.store, step, env);
        for &cid in cands.iter() {
            if !Self::is_alive_in(&ctx.data.store, cid) || chosen.iter().any(|c| c == &Some(cid)) {
                continue;
            }
            let trail = env.trail_len();
            let head_idx = step.head as usize;
            let head = &ctx.rule.heads[head_idx];
            let flat_ops = &ctx.rule.head_flat_ops[head_idx];
            let inst = &ctx.data.store.inst[cid.0 as usize];
            let inst_args = ctx.data.store.args(inst);
            if match_head(ctx.terms, head, flat_ops, inst, inst_args, env) {
                chosen[step.head as usize] = Some(cid);
                if let Some(tuple) = Self::search_steps_inner(ctx, step_idx + 1, env, chosen) {
                    return Some(tuple);
                }
                chosen[step.head as usize] = None;
            }
            env.unwind(trail);
        }
        None
    }

    fn candidates_for_step_inner<'a>(
        store: &'a ChrStore,
        step: &JoinStep,
        env: &RVarEnv,
    ) -> &'a [Cid] {
        static EMPTY: [Cid; 0] = [];
        let pred_store = &store.preds[step.pred.0 as usize];
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

    #[inline]
    fn is_alive_in(store: &ChrStore, cid: Cid) -> bool {
        matches!(
            store.inst.get(cid.0 as usize),
            Some(inst) if inst.alive
        )
    }

    /// Apply substitution to all alive constraint args.
    /// Returns `true` if any constraint arg actually changed.
    fn apply_subst_to_data(data: &mut ChrStateData, subst: &Subst, terms: &mut TermStore) -> bool {
        let mut changed = false;
        for i in 0..data.store.inst.len() {
            let inst = &data.store.inst[i];
            if inst.alive {
                let start = inst.arg_start as usize;
                let end = start + inst.arg_count as usize;
                for arg in data.store.all_args[start..end].iter_mut() {
                    if arg.is_ground() {
                        continue;
                    }
                    let new_arg = apply_subst(*arg, subst, terms);
                    if new_arg != *arg {
                        *arg = new_arg;
                        changed = true;
                    }
                }
            }
        }
        changed
    }

    fn enqueue_all_alive_in(data: &mut ChrStateData) {
        data.agenda.clear();
        for (idx, inst) in data.store.inst.iter().enumerate() {
            if inst.alive {
                data.agenda.push_back(Cid(idx as u32));
            }
        }
    }

    /// Enqueue only constraints at or above the fixpoint watermark.
    /// Constraints below the watermark are already at CHR fixpoint.
    fn enqueue_above_watermark(data: &mut ChrStateData) {
        data.agenda.clear();
        let start = data.fixpoint_watermark as usize;
        for inst in data.store.inst[start..].iter() {
            if inst.alive {
                data.agenda.push_back(inst.cid);
            }
        }
    }
}

fn match_head(
    terms: &TermStore,
    head: &HeadPat,
    flat_ops: &[FlatMatchOp],
    inst: &CInstance,
    inst_args: &[TermId],
    env: &mut RVarEnv,
) -> bool {
    if head.pred != inst.pred {
        return false;
    }
    if head.args.len() != inst_args.len() {
        return false;
    }
    let guard = terms.read_lock();
    match_flat_ops(flat_ops, &guard, inst_args, env)
}

/// Like `match_head` but takes `pred` and `args` directly instead of a
/// `CInstance`.  Used for inline matching before storing constraints.
#[inline(always)]
fn match_head_direct(
    terms: &TermStore,
    head: &HeadPat,
    flat_ops: &[FlatMatchOp],
    pred: PredId,
    args: &[TermId],
    env: &mut RVarEnv,
) -> bool {
    if head.pred != pred {
        return false;
    }
    if head.args.len() != args.len() {
        return false;
    }
    let guard = terms.read_lock();
    match_flat_ops(flat_ops, &guard, args, env)
}

/// Try to match a newly-created constraint against triggered rules inline,
/// before storing it. If a rule matches, execute its body recursively (DFS).
/// Returns `Ok(true)` if a rule matched and fired, `Ok(false)` if no rule
/// matched (caller should store the constraint), or `Err(())` if a body
/// execution failed (propagate failure).
fn try_inline_match(
    pred: PredId,
    args: &[TermId],
    terms: &mut TermStore,
    program: &ChrProgram,
    data: &mut ChrStateData,
    env: &mut RVarEnv,
) -> Result<bool, ()> {
    let indexed = &program.triggers[pred.0 as usize];

    let first_arg_functor: Option<FuncId> = args.first().and_then(|tid| {
        terms.with_term(*tid, |t| match t? {
            Term::App(f, _) => Some(*f),
            Term::Var(_) => None,
        })
    });

    let indexed_occs = first_arg_functor
        .and_then(|f| indexed.by_functor.get(&f))
        .map(|v| v.as_slice())
        .unwrap_or(&[]);

    for occ_ref in indexed_occs.iter().chain(indexed.fallback.iter()) {
        let rule = &program.rules[occ_ref.rid.0 as usize];
        let occ = &rule.occs[occ_ref.occ as usize];
        let anchor_idx = occ.anchor_head as usize;
        let anchor_head = &rule.heads[anchor_idx];
        let anchor_flat = &rule.head_flat_ops[anchor_idx];

        env.ensure_capacity(rule.n_rvars);
        env.reset();

        if !match_head_direct(terms, anchor_head, anchor_flat, pred, args, env) {
            continue;
        }

        if !rule
            .guard
            .eval(&program.pats, terms, &data.eq_subst, &program.builtins, env)
        {
            continue;
        }

        // Rule fires! Execute body with inline matching (recursive DFS).
        // The constraint never needs to be stored or killed.
        if !exec_body_inline(
            &rule.body,
            &program.pats,
            terms,
            &program.builtins,
            env,
            program,
            data,
        ) {
            return Err(());
        }
        return Ok(true);
    }
    Ok(false)
}

/// Execute a rule body, trying to match each new `AddChr` constraint inline
/// before storing it. This is the DFS variant used during single-head
/// simplification to avoid the store/agenda roundtrip for matched constraints.
fn exec_body_inline(
    body: &BodyProg,
    pats: &PatArena,
    terms: &mut TermStore,
    reg: &BuiltinRegistry,
    env: &RVarEnv,
    program: &ChrProgram,
    data: &mut ChrStateData,
) -> bool {
    // We need a separate env for inline matching (the caller's env must not
    // be clobbered). Allocate once and reuse across AddChr instructions.
    let mut match_env = RVarEnv::new(program.max_rvars);
    for ins in body.code.iter() {
        match ins {
            BodyInstr::AddChr { pred, args } => {
                let av = match collect_args(args, pats, terms, env) {
                    Some(v) => v,
                    None => return false,
                };

                match try_inline_match(*pred, &av, terms, program, data, &mut match_env) {
                    Ok(true) => {
                        // Rule matched and fired inline; constraint consumed.
                    }
                    Ok(false) => {
                        // No rule matched; store the constraint but do NOT
                        // push to agenda (we already tried all rules).
                        let cid = Cid(data.next_cid);
                        data.next_cid = data.next_cid.saturating_add(1);
                        let specs = &program.preds[pred.0 as usize].index_specs;
                        data.store.add_chr(cid, *pred, &av, terms, specs);
                    }
                    Err(()) => return false,
                }
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
                if !(b.add)(&mut data.eq_subst, terms, &av) {
                    return false;
                }
            }
            BodyInstr::Fail => return false,
        }
    }
    true
}

/// Execute a pre-flattened match op sequence against a list of root terms.
///
/// The ops were produced by `flatten_head_pat` and encode a pre-order traversal
/// of all arg patterns with PushRoot ops separating each arg's segment.
#[inline(always)]
fn match_flat_ops(
    ops: &[FlatMatchOp],
    guard: &TermReadGuard<'_>,
    args: &[TermId],
    env: &mut RVarEnv,
) -> bool {
    let mut stack: SmallVec<[TermId; 8]> = SmallVec::new();
    let mut arg_iter = args.iter();
    for op in ops {
        match op {
            FlatMatchOp::PushRoot => {
                // Safety: flatten_head_pat emits exactly one PushRoot per arg,
                // and we checked args.len() == head.args.len() above.
                let t = *arg_iter.next().unwrap();
                stack.push(t);
            }
            FlatMatchOp::CheckApp(f, n) => {
                let t = stack.pop().unwrap();
                // Handle inline nullary: check functor match with no children.
                if t.is_inline_nullary() {
                    if *n != 0 || t.inline_nullary_func_raw() != f.into_inner().get() {
                        return false;
                    }
                    // Match: nullary CheckApp vs nullary inline term, same functor.
                } else {
                    match guard.get(t) {
                        Some(Term::App(tf, tks)) if *tf == *f && tks.len() == *n as usize => {
                            // Push children in reverse for pre-order traversal.
                            for kid in tks.iter().rev() {
                                stack.push(*kid);
                            }
                        }
                        _ => return false,
                    }
                }
            }
            FlatMatchOp::BindVar(rv) => {
                let t = stack.pop().unwrap();
                if !env.bind(*rv, t) {
                    return false;
                }
            }
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

    fn into_vec(self) -> Vec<u8> {
        self.buf
    }
}

#[cfg(test)]
struct ByteReader<'a> {
    bs: &'a [u8],
    i: usize,
}

#[cfg(test)]
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

pub(crate) fn freeze_chr(st: &ChrState) -> Vec<u8> {
    let d = match &st.data {
        None => {
            let mut w = ByteWriter::new();
            w.push_u32(0);
            w.push_u32(0);
            w.push_u32(0);
            return w.into_vec();
        }
        Some(d) => d,
    };

    if d.store.alive_count == 0 {
        let mut w = ByteWriter::new();
        w.push_u32(0);
        w.push_u32(0);
        w.push_u32(0);
        return w.into_vec();
    }

    let mut alive: Vec<AliveRec> = Vec::new();
    for (i, inst) in d.store.inst.iter().enumerate() {
        if inst.alive {
            let args = d.store.args(inst);
            let mut sv: SmallVec<[TermId; 4]> = SmallVec::new();
            sv.extend_from_slice(args);
            alive.push(AliveRec {
                pred: inst.pred,
                args: sv,
                old_cid: i as u32,
            });
        }
    }

    alive.sort();

    let mut remap: Vec<u32> = vec![u32::MAX; d.store.inst.len()];
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

    // eq_subst is always empty when freezing; write 0-length marker.
    w.push_u32(0);

    let mut token_rules: Vec<(u32, Vec<TokenKey>)> = Vec::new();
    for (rid, set) in d.tokens.fired.iter().enumerate() {
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

#[cfg(test)]
pub(crate) fn thaw_chr(
    program: Arc<ChrProgram>,
    bytes: &[u8],
    terms: &TermStore,
) -> Option<ChrState> {
    let mut r = ByteReader::new(bytes);
    let n_constraints = r.read_u32()? as usize;
    let mut st = ChrState::new(program.clone());
    {
        let arc = st.data.as_mut().unwrap();
        Arc::make_mut(arc).store =
            ChrStore::new(&program.preds, program.all_single_head_simplification);
    }

    for _ in 0..n_constraints {
        let pred = PredId(r.read_u32()?);
        let arity = r.read_u32()? as usize;
        let mut args: Vec<TermId> = Vec::with_capacity(arity);
        for _ in 0..arity {
            args.push(TermId::from_raw(r.read_u32()?));
        }
        st.introduce(pred, &args, terms);
    }

    let d = Arc::make_mut(st.data.as_mut().unwrap());
    // Skip the builtin bytes (always empty, but need to advance the reader).
    let b_len = r.read_u32()? as usize;
    let _ = r.read_bytes(b_len)?;

    let n_token_rules = r.read_u32()? as usize;
    d.tokens = if program.all_single_head_simplification {
        TokenStore::empty()
    } else {
        TokenStore::new(program.rules.len())
    };
    for _ in 0..n_token_rules {
        let rid = r.read_u32()? as usize;
        let n_tokens = r.read_u32()? as usize;
        let set = d.tokens.fired.get_mut(rid)?;
        for _ in 0..n_tokens {
            let k = r.read_u32()? as usize;
            let mut sv: SmallVec<[Cid; 8]> = SmallVec::new();
            for _ in 0..k {
                sv.push(Cid(r.read_u32()?));
            }
            set.insert(TokenKey::from_cids(sv.into_vec()));
        }
    }

    d.agenda.clear();
    // Thawed state was frozen at fixpoint; mark all constraints as at fixpoint.
    d.fixpoint_watermark = d.next_cid;
    Some(st)
}

impl ChrProgram {
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
            max_rvars: 0,
            all_single_head_simplification: false,
        })
    }
}

impl Default for ChrState {
    fn default() -> Self {
        Self {
            program: ChrProgram::empty(),
            data: None,
        }
    }
}

impl PartialEq for ChrState {
    fn eq(&self, other: &Self) -> bool {
        if self.program.program_id != other.program.program_id {
            return false;
        }
        match (&self.data, &other.data) {
            (None, None) => true,
            _ => freeze_chr(self) == freeze_chr(other),
        }
    }
}

impl Eq for ChrState {}

impl Hash for ChrState {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.program.program_id.hash(state);
        if self.data.is_some() {
            freeze_chr(self).hash(state);
        }
    }
}

/// Run the full CHR normalization without caching. This is the uncached hot path
/// extracted from normalize_owned to keep the ConstraintOps impl clean.
fn normalize_owned_uncached(
    mut state: ChrState,
    terms: &mut TermStore,
) -> Option<(ChrState, Option<Subst>)> {
    {
        let preds = &state.program.preds;
        let sd = Arc::make_mut(state.data.as_mut().unwrap());
        let watermark = sd.fixpoint_watermark as usize;
        if watermark == 0 {
            sd.store.rebuild_indexes(preds, terms);
            ChrState::enqueue_all_alive_in(sd);
        } else {
            sd.store.index_from(watermark, preds, terms);
            ChrState::enqueue_above_watermark(sd);
        }
    }
    if !state.solve_to_fixpoint(terms) {
        return None;
    }

    let preds = &state.program.preds;
    let sd = Arc::make_mut(state.data.as_mut().unwrap());
    let subst = std::mem::take(&mut sd.eq_subst);
    let subst_opt = if subst.is_empty() {
        None
    } else {
        Some(subst.clone())
    };
    if !subst.is_empty() {
        let args_changed = ChrState::apply_subst_to_data(sd, &subst, terms);
        sd.store.rebuild_indexes(preds, terms);
        if args_changed {
            sd.fixpoint_watermark = 0;
        } else {
            sd.fixpoint_watermark = sd.next_cid;
        }
    } else {
        sd.fixpoint_watermark = sd.next_cid;
    }
    sd.agenda.clear();
    sd.recompute_all_args_ground();
    Some((state, subst_opt))
}

impl crate::constraint::ConstraintOps for ChrState {
    fn combine(&self, other: &Self) -> Option<Self> {
        if let Some(d) = &self.data {
            if d.failed {
                return None;
            }
        }
        if let Some(d) = &other.data {
            if d.failed {
                return None;
            }
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

        match (&self.data, &other.data) {
            (None, None) => Some(self.clone()),
            (None, Some(_)) => Some(other.clone()),
            (Some(_), None) => Some(self.clone()),
            (Some(_sd), Some(od)) => {
                let mut merged = self.clone();
                let md = Arc::make_mut(merged.data.as_mut().unwrap());
                md.agenda.clear();

                let mut remap: Vec<Option<Cid>> = vec![None; od.store.inst.len()];
                for (idx, inst) in od.store.inst.iter().enumerate() {
                    if !inst.alive {
                        continue;
                    }
                    let cid = Cid(md.next_cid);
                    md.next_cid = md.next_cid.saturating_add(1);
                    let other_args = od.store.args(inst);
                    let arg_start = md.store.all_args.len() as u32;
                    let arg_count = other_args.len() as u16;
                    md.store.all_args.extend_from_slice(other_args);
                    md.store.inst.push(CInstance {
                        cid,
                        pred: inst.pred,
                        arg_start,
                        arg_count,
                        alive: true,
                    });
                    remap[idx] = Some(cid);
                    md.store.alive_count += 1;
                }

                for (rid, set) in od.tokens.fired.iter().enumerate() {
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
                            md.tokens.fired[rid].insert(new_token);
                        }
                    }
                }

                Some(merged)
            }
        }
    }

    fn normalize(&self, terms: &mut TermStore) -> Option<(Self, Option<Subst>)> {
        self.clone().normalize_owned(terms)
    }

    fn normalize_owned(self, terms: &mut TermStore) -> Option<(Self, Option<Subst>)> {
        if self.data.is_none() {
            return Some((self, None));
        }
        if self.data.as_ref().unwrap().failed {
            return None;
        }

        // Compute a fast hash of the pre-normalization ChrState for cache lookup.
        // Includes: program_id, alive constraint predicates and their term args,
        // and fired propagation tokens (for propagation rule correctness).
        //
        // Per-constraint hashes are sorted before chaining to ensure order-independence
        // (the constraint store is a multiset) while avoiding the collision weakness
        // of commutative addition (where different multisets with the same sum collide).
        let state_hash = {
            let d = self.data.as_ref().unwrap();
            const MUL: u64 = 6364136223846793005;

            // Hash each alive constraint independently, collect into sorted array,
            // then chain-multiply for a collision-resistant order-independent hash.
            let mut per_constraint_hashes: SmallVec<[u64; 8]> = SmallVec::new();
            for inst in d.store.inst.iter() {
                if inst.alive {
                    // Per-constraint hash: order-dependent WITHIN a single constraint's
                    // predicate and args (which is correct — arg order matters).
                    let mut ch = inst.pred.0 as u64;
                    for arg in d.store.args(inst) {
                        ch = ch.wrapping_mul(MUL).wrapping_add(arg.raw() as u64);
                    }
                    per_constraint_hashes.push(ch);
                }
            }
            per_constraint_hashes.sort_unstable();

            let mut constraints_hash = 0u64;
            for ch in per_constraint_hashes {
                constraints_hash = constraints_hash.wrapping_mul(MUL).wrapping_add(ch);
            }

            // Final combination: alive_count, sorted constraint hash chain,
            // per-rule fired token counts, and program_id.
            let mut h = 0u64;
            h = h.wrapping_mul(MUL).wrapping_add(d.store.alive_count as u64);
            h = h.wrapping_mul(MUL).wrapping_add(constraints_hash);
            // Include fired token counts for propagation-rule correctness.
            for set in d.tokens.fired.iter() {
                h = h.wrapping_mul(MUL).wrapping_add(set.len() as u64);
            }
            h = h.wrapping_mul(MUL).wrapping_add(self.program.program_id);
            h
        };

        // Check the thread-local cache for a previously computed result.
        let generation = terms.generation();
        let cached = NORMALIZE_CACHE.with(|cache| {
            let mut c = cache.borrow_mut();
            if c.generation != generation {
                c.entries.clear();
                c.generation = generation;
            }
            c.entries.get(&state_hash).cloned()
        });

        if let Some(hit) = cached {
            return hit;
        }

        // Cache miss: run the full normalization.
        let result = normalize_owned_uncached(self, terms);

        // Store the result in the cache.
        NORMALIZE_CACHE.with(|cache| {
            let mut c = cache.borrow_mut();
            if c.generation == generation {
                c.entries.insert(state_hash, result.clone());
            }
        });

        result
    }

    fn combine_owned(mut self, other: Self) -> Option<Self> {
        if let Some(d) = &self.data {
            if d.failed {
                return None;
            }
        }
        if let Some(d) = &other.data {
            if d.failed {
                return None;
            }
        }
        if self.program.program_id != other.program.program_id {
            let self_empty = self.is_empty();
            let other_empty = other.is_empty();
            if self_empty && other_empty {
                return Some(if self.program.program_id <= other.program.program_id {
                    self
                } else {
                    other
                });
            }
            if self_empty {
                return Some(other);
            }
            if other_empty {
                return Some(self);
            }
            return None;
        }

        match (&self.data, &other.data) {
            (None, None) => Some(self),
            (None, Some(_)) => Some(other),
            (Some(_), None) => Some(self),
            (Some(_), Some(od)) => {
                // Reuse self's allocation instead of cloning.
                let md = Arc::make_mut(self.data.as_mut().unwrap());
                md.agenda.clear();

                let mut remap: Vec<Option<Cid>> = vec![None; od.store.inst.len()];
                for (idx, inst) in od.store.inst.iter().enumerate() {
                    if !inst.alive {
                        continue;
                    }
                    let cid = Cid(md.next_cid);
                    md.next_cid = md.next_cid.saturating_add(1);
                    let other_args = od.store.args(inst);
                    let arg_start = md.store.all_args.len() as u32;
                    let arg_count = other_args.len() as u16;
                    md.store.all_args.extend_from_slice(other_args);
                    md.store.inst.push(CInstance {
                        cid,
                        pred: inst.pred,
                        arg_start,
                        arg_count,
                        alive: true,
                    });
                    remap[idx] = Some(cid);
                    md.store.alive_count += 1;
                }

                // Update all_args_ground: if self was ground and other's alive args are all ground,
                // combined is still ground. Otherwise recompute.
                if md.all_args_ground && !od.all_args_ground {
                    md.all_args_ground = false;
                }

                for (rid, set) in od.tokens.fired.iter().enumerate() {
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
                            md.tokens.fired[rid].insert(new_token);
                        }
                    }
                }

                Some(self)
            }
        }
    }

    fn apply_subst(&self, subst: &Subst, terms: &mut TermStore) -> Self {
        let data_ref = match &self.data {
            Some(d) => d,
            None => return self.clone(),
        };
        if subst.is_empty() {
            return self.clone();
        }
        // If all constraint args are ground, no substitution can change anything.
        if data_ref.all_args_ground {
            return self.clone();
        }
        // Clone data directly to avoid self.clone() + Arc::make_mut double-clone.
        let mut data = data_ref.as_ref().clone();
        let args_changed = Self::apply_subst_to_data(&mut data, subst, terms);
        if args_changed {
            data.fixpoint_watermark = 0;
        }
        ChrState {
            program: self.program.clone(),
            data: Some(Arc::new(data)),
        }
    }

    fn remap_vars(&self, map: &[Option<u32>], terms: &mut TermStore) -> Self {
        let data_ref = match &self.data {
            Some(d) => d,
            None => return self.clone(),
        };
        // If all constraint args are ground, variable remapping cannot change anything.
        if data_ref.all_args_ground {
            return self.clone();
        }
        // Clone data directly to avoid self.clone() + Arc::make_mut double-clone.
        let mut data = data_ref.as_ref().clone();
        let preds = &self.program.preds;
        let mut args_changed = false;
        for i in 0..data.store.inst.len() {
            let inst = &data.store.inst[i];
            if inst.alive {
                let start = inst.arg_start as usize;
                let end = start + inst.arg_count as usize;
                for arg in data.store.all_args[start..end].iter_mut() {
                    let new_arg = apply_var_renaming(*arg, map, terms);
                    if new_arg != *arg {
                        *arg = new_arg;
                        args_changed = true;
                    }
                }
            }
        }
        if args_changed {
            data.store.rebuild_indexes(preds, terms);
            data.fixpoint_watermark = 0;
        }
        data.agenda.clear();
        ChrState {
            program: self.program.clone(),
            data: Some(Arc::new(data)),
        }
    }

    fn remap_and_apply_subst(
        &self,
        map: &[Option<u32>],
        subst: &Subst,
        terms: &mut TermStore,
    ) -> Self {
        let data_ref = match &self.data {
            Some(d) => d,
            None => return self.clone(),
        };
        // If all constraint args are ground, neither remap nor subst can change anything.
        if data_ref.all_args_ground {
            return self.clone();
        }
        // Clone data once instead of twice (remap_vars clone + apply_subst clone).
        let mut data = data_ref.as_ref().clone();
        let mut args_changed = false;
        for i in 0..data.store.inst.len() {
            let inst = &data.store.inst[i];
            if inst.alive {
                let start = inst.arg_start as usize;
                let end = start + inst.arg_count as usize;
                for arg in data.store.all_args[start..end].iter_mut() {
                    // Step 1: remap variable indices
                    let remapped = apply_var_renaming(*arg, map, terms);
                    // Step 2: apply substitution
                    let substituted = apply_subst(remapped, subst, terms);
                    if substituted != *arg {
                        *arg = substituted;
                        args_changed = true;
                    }
                }
            }
        }
        if args_changed {
            data.fixpoint_watermark = 0;
        }
        // Skip rebuild_indexes: normalize_owned will do this after combine.
        data.agenda.clear();
        ChrState {
            program: self.program.clone(),
            data: Some(Arc::new(data)),
        }
    }

    fn collect_vars(&self, terms: &TermStore, out: &mut Vec<u32>) {
        let d = match &self.data {
            Some(d) => d,
            None => return,
        };
        for inst in d.store.inst.iter() {
            if inst.alive {
                let args = d.store.args(inst);
                for arg in args.iter().copied() {
                    out.extend(crate::nf::collect_vars_ordered(arg, terms));
                }
            }
        }
    }

    fn is_empty(&self) -> bool {
        match &self.data {
            None => true,
            Some(d) => d.store.alive_count == 0,
        }
    }

    fn is_satisfiable(&self) -> bool {
        match &self.data {
            None => true,
            Some(d) => !d.failed,
        }
    }
}

impl ConstraintDisplay for ChrState {
    fn fmt_constraints(
        &self,
        terms: &mut TermStore,
        symbols: &crate::symbol::SymbolStore,
    ) -> Result<Option<String>, String> {
        let d = match &self.data {
            None => return Ok(None),
            Some(d) => d,
        };
        if d.store.alive_count == 0 {
            return Ok(None);
        }

        let mut parts = Vec::new();
        for inst in d.store.inst.iter().filter(|c| c.alive) {
            let pred_name = self.program.pred_name(inst.pred).unwrap_or("unknown");
            let args = d.store.args(inst);
            if args.is_empty() {
                parts.push(pred_name.to_string());
            } else {
                let mut s = String::new();
                s.push('(');
                s.push_str(pred_name);
                for arg in args.iter().copied() {
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
