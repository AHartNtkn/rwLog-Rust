use crate::symbol::{FuncId, SymbolStore};
use hashbrown::HashMap;
use parking_lot::RwLock;
use rustc_hash::{FxBuildHasher, FxHasher};
use smallvec::SmallVec;
use std::hash::{Hash, Hasher};
use std::sync::atomic::{AtomicU32, Ordering};

/// Tag bits (bits 31-30) encode TermId kind:
///   00 = Non-ground store reference (index in bits 0-29)
///   01 = Inline variable (var_index in bits 0-29)
///   10 = Ground store reference (index in bits 0-29)
///   11 = Inline nullary constant (FuncId raw value in bits 0-29)
const TAG_SHIFT: u32 = 30;
const TAG_MASK: u32 = 0b11 << TAG_SHIFT;
const PAYLOAD_MASK: u32 = !(TAG_MASK);

const TAG_STORE_NONGROUND: u32 = 0b00 << TAG_SHIFT;
const TAG_INLINE_VAR: u32 = 0b01 << TAG_SHIFT;
const TAG_STORE_GROUND: u32 = 0b10 << TAG_SHIFT;
const TAG_INLINE_NULLARY: u32 = 0b11 << TAG_SHIFT;

/// Bit 31 is set for ground terms (both ground store refs and inline nullaries).
const GROUND_BIT: u32 = 1 << 31;
/// Bit 30 is set for inline terms (both inline vars and inline nullaries).
const INLINE_BIT: u32 = 1 << 30;

/// Unique identifier for a term in the term store.
/// TermIds are stable and can be compared for equality.
///
/// Encoding uses the top 2 bits as a tag:
///   00 = Non-ground store reference
///   01 = Inline variable (pure arithmetic, no store access needed)
///   10 = Ground store reference
///   11 = Inline nullary constant (no store access needed)
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

    /// Get the storage index (strips both tag bits).
    /// Only valid for store references (non-inline TermIds).
    #[inline(always)]
    pub fn index(self) -> usize {
        (self.0 & PAYLOAD_MASK) as usize
    }

    /// Check if this term is ground (contains no variables).
    /// Ground terms are unaffected by any substitution or variable shift.
    /// True for ground store refs (tag 10) and inline nullaries (tag 11).
    #[inline(always)]
    pub fn is_ground(self) -> bool {
        self.0 & GROUND_BIT != 0
    }

    /// Check if this is an inline term (variable or nullary constant).
    /// Inline terms are not stored in the TermStore's nodes Vec.
    #[inline(always)]
    pub fn is_inline(self) -> bool {
        self.0 & INLINE_BIT != 0
    }

    /// Check if this is a store reference (not inline).
    #[inline(always)]
    pub fn is_store_ref(self) -> bool {
        self.0 & INLINE_BIT == 0
    }

    /// Check if this is an inline variable.
    #[inline(always)]
    pub fn is_inline_var(self) -> bool {
        self.0 & TAG_MASK == TAG_INLINE_VAR
    }

    /// Get the variable index from an inline variable TermId.
    /// Only valid when is_inline_var() returns true.
    #[inline(always)]
    pub fn inline_var_index(self) -> u32 {
        debug_assert!(self.is_inline_var());
        self.0 & PAYLOAD_MASK
    }

    /// Create an inline variable TermId.
    #[inline(always)]
    pub fn inline_var(idx: u32) -> Self {
        debug_assert!(
            idx <= PAYLOAD_MASK,
            "variable index too large for inline encoding"
        );
        TermId(TAG_INLINE_VAR | idx)
    }

    /// Check if this is an inline nullary constant.
    #[inline(always)]
    pub fn is_inline_nullary(self) -> bool {
        self.0 & TAG_MASK == TAG_INLINE_NULLARY
    }

    /// Get the FuncId from an inline nullary constant TermId.
    /// Only valid when is_inline_nullary() returns true.
    #[inline(always)]
    pub fn inline_nullary_func_raw(self) -> u32 {
        debug_assert!(self.is_inline_nullary());
        self.0 & PAYLOAD_MASK
    }

    /// Create an inline nullary constant TermId from a FuncId's raw value.
    #[inline(always)]
    pub fn inline_nullary(func_raw: u32) -> Self {
        debug_assert!(
            func_raw <= PAYLOAD_MASK,
            "FuncId too large for inline encoding"
        );
        TermId(TAG_INLINE_NULLARY | func_raw)
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
/// - Variables and nullary constants are encoded inline in TermId (no store access)
/// - Non-trivial App terms are hashconsed in the store
pub struct TermStore {
    /// Central storage of all terms, indexed by TermId (using index() to strip tag bits).
    /// Does NOT contain variables or nullary App entries (those are inline in TermId).
    pub(crate) nodes: RwLock<Vec<Term>>,
    /// Sharded hashcons maps for reducing contention. Uses FxHash for speed.
    shards: [RwLock<HashMap<Term, TermId, FxBuildHasher>>; NUM_SHARDS],
    /// Counter for generating unique TermIds.
    next_id: AtomicU32,
}

impl TermStore {
    /// Create a new empty term store.
    pub fn new() -> Self {
        // Initialize array of shards with FxHash
        let shards = std::array::from_fn(|_| RwLock::new(HashMap::with_hasher(FxBuildHasher)));
        Self {
            nodes: RwLock::new(Vec::new()),
            shards,
            next_id: AtomicU32::new(0),
        }
    }

    /// Intern a term, returning its TermId.
    /// If the term already exists, returns the existing TermId.
    /// Variables and nullary Apps are returned as inline TermIds without store insertion.
    fn intern(&self, term: Term) -> TermId {
        // Inline fast paths: variables and nullary constants are encoded directly in TermId.
        match &term {
            Term::Var(idx) => return TermId::inline_var(*idx),
            Term::App(func, children) if children.is_empty() => {
                return TermId::inline_nullary(func.into_inner().get());
            }
            _ => {}
        }

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

        // Allocate new raw index and store term
        let raw_index = self.next_id.fetch_add(1, Ordering::Relaxed);
        debug_assert!(
            raw_index & TAG_MASK == 0,
            "TermStore overflow: too many terms (>{} terms)",
            PAYLOAD_MASK
        );
        {
            let mut nodes = self.nodes.write();
            let idx = raw_index as usize;
            if nodes.len() <= idx {
                nodes.resize(idx + 1, Term::Var(0));
            }
            nodes[idx] = term.clone();
        }
        // Compute ground flag from children's TermId ground bits (zero cost).
        // At this point, term is guaranteed to be an App with at least one child.
        let is_ground = match &term {
            Term::App(_, children) => children.iter().all(|c| c.is_ground()),
            Term::Var(_) => unreachable!("variables are handled above"),
        };
        let id = TermId(
            raw_index
                | if is_ground {
                    TAG_STORE_GROUND
                } else {
                    TAG_STORE_NONGROUND
                },
        );
        map.insert(term, id);
        id
    }

    /// Create a variable term.
    /// Variables are always encoded inline: pure arithmetic, no store access.
    #[inline(always)]
    pub fn var(&self, index: u32) -> TermId {
        TermId::inline_var(index)
    }

    /// Create an application term.
    /// Nullary apps are encoded inline. Non-nullary apps are hashconsed.
    pub fn app(&self, func: FuncId, children: SmallVec<[TermId; 4]>) -> TermId {
        if children.is_empty() {
            return TermId::inline_nullary(func.into_inner().get());
        }
        self.intern(Term::App(func, children))
    }

    /// Create an application term from a slice of children.
    /// Avoids intermediate SmallVec allocation when children are already in a contiguous buffer.
    #[inline]
    pub fn app_from_slice(&self, func: FuncId, children: &[TermId]) -> TermId {
        if children.is_empty() {
            return TermId::inline_nullary(func.into_inner().get());
        }
        self.intern(Term::App(func, SmallVec::from_slice(children)))
    }

    /// Create a nullary (0-arity) application.
    #[inline(always)]
    pub fn app0(&self, func: FuncId) -> TermId {
        TermId::inline_nullary(func.into_inner().get())
    }

    /// Create a unary (1-arity) application.
    pub fn app1(&self, func: FuncId, child: TermId) -> TermId {
        self.app(func, smallvec::smallvec![child])
    }

    /// Create a binary (2-arity) application.
    pub fn app2(&self, func: FuncId, left: TermId, right: TermId) -> TermId {
        self.app(func, smallvec::smallvec![left, right])
    }

    /// Resolve a TermId to its term (cloning).
    /// Prefer `with_term` for read-only access to avoid cloning.
    pub fn resolve(&self, id: TermId) -> Option<Term> {
        if id.is_inline_var() {
            return Some(Term::Var(id.inline_var_index()));
        }
        if id.is_inline_nullary() {
            let func_raw = id.inline_nullary_func_raw();
            let func = Self::func_id_from_raw(func_raw)?;
            return Some(Term::App(func, SmallVec::new()));
        }
        let nodes = self.nodes.read();
        nodes.get(id.index()).cloned()
    }

    /// Access a term by reference without cloning.
    /// The closure receives `Option<&Term>` and must return before the lock is released.
    /// NOTE: For inline TermIds, this creates a temporary Term on the stack.
    #[inline]
    pub fn with_term<R>(&self, id: TermId, f: impl FnOnce(Option<&Term>) -> R) -> R {
        if id.is_inline_var() {
            let term = Term::Var(id.inline_var_index());
            return f(Some(&term));
        }
        if id.is_inline_nullary() {
            let func_raw = id.inline_nullary_func_raw();
            if let Some(func) = Self::func_id_from_raw(func_raw) {
                let term = Term::App(func, SmallVec::new());
                return f(Some(&term));
            }
            return f(None);
        }
        let nodes = self.nodes.read();
        f(nodes.get(id.index()))
    }

    /// Acquire a read lock on the term storage, returning a guard that allows
    /// zero-overhead term lookups. Use this for tight loops that resolve many terms.
    #[inline]
    pub fn read_lock(&self) -> TermReadGuard<'_> {
        TermReadGuard {
            data: self.nodes.read(),
        }
    }

    /// Check if a term is a variable.
    #[inline]
    pub fn is_var(&self, id: TermId) -> Option<u32> {
        if id.is_inline_var() {
            return Some(id.inline_var_index());
        }
        if id.is_inline_nullary() {
            return None;
        }
        let nodes = self.nodes.read();
        match nodes.get(id.index()) {
            Some(Term::Var(idx)) => Some(*idx),
            _ => None,
        }
    }

    /// Check if a term is an application, returning functor and children.
    pub fn is_app(&self, id: TermId) -> Option<(FuncId, SmallVec<[TermId; 4]>)> {
        if id.is_inline_var() {
            return None;
        }
        if id.is_inline_nullary() {
            let func = Self::func_id_from_raw(id.inline_nullary_func_raw())?;
            return Some((func, SmallVec::new()));
        }
        let nodes = self.nodes.read();
        match nodes.get(id.index()) {
            Some(Term::App(f, children)) => Some((*f, children.clone())),
            _ => None,
        }
    }

    /// Get a term by index without locking. Requires exclusive (`&mut`) access.
    ///
    /// Uses `RwLock::get_mut()` which is lock-free because exclusive access
    /// guarantees no other readers or writers exist.
    ///
    /// Returns None for inline TermIds (variables and nullary constants).
    /// Callers MUST check is_inline_var() / is_inline_nullary() first for
    /// hot-path code.
    #[inline]
    pub fn get_unlocked(&mut self, id: TermId) -> Option<&Term> {
        if id.is_inline() {
            return None;
        }
        self.nodes.get_mut().get(id.index())
    }

    /// Intern a term without locking. Requires exclusive (`&mut`) access.
    ///
    /// Uses `RwLock::get_mut()` on both nodes and shard maps, bypassing
    /// all lock acquire/release overhead.
    /// Variables and nullary Apps are returned as inline TermIds without store insertion.
    pub fn intern_unlocked(&mut self, term: Term) -> TermId {
        // Inline fast paths: variables and nullary constants.
        match &term {
            Term::Var(idx) => return TermId::inline_var(*idx),
            Term::App(func, children) if children.is_empty() => {
                return TermId::inline_nullary(func.into_inner().get());
            }
            _ => {}
        }

        let shard_idx = Self::shard_index(&term);

        // Fast path: check if term exists (no lock needed)
        if let Some(&id) = self.shards[shard_idx].get_mut().get(&term) {
            return id;
        }

        // Slow path: insert
        let raw_index = self.next_id.fetch_add(1, Ordering::Relaxed);
        debug_assert!(
            raw_index & TAG_MASK == 0,
            "TermStore overflow: too many terms (>{} terms)",
            PAYLOAD_MASK
        );
        let nodes = self.nodes.get_mut();
        let idx = raw_index as usize;
        if nodes.len() <= idx {
            nodes.resize(idx + 1, Term::Var(0));
        }
        nodes[idx] = term.clone();

        // At this point, term is guaranteed to be an App with at least one child.
        let is_ground = match &term {
            Term::App(_, children) => children.iter().all(|c| c.is_ground()),
            Term::Var(_) => unreachable!("variables are handled above"),
        };
        let id = TermId(
            raw_index
                | if is_ground {
                    TAG_STORE_GROUND
                } else {
                    TAG_STORE_NONGROUND
                },
        );
        self.shards[shard_idx].get_mut().insert(term, id);
        id
    }

    /// Create an application term from a slice without locking.
    /// Requires exclusive (`&mut`) access.
    #[inline]
    pub fn app_from_slice_unlocked(&mut self, func: FuncId, children: &[TermId]) -> TermId {
        if children.is_empty() {
            return TermId::inline_nullary(func.into_inner().get());
        }
        self.intern_unlocked(Term::App(func, SmallVec::from_slice(children)))
    }

    /// Create a variable term without locking. Requires exclusive (`&mut`) access.
    /// Pure arithmetic, no store access.
    #[inline(always)]
    pub fn var_unlocked(&mut self, index: u32) -> TermId {
        TermId::inline_var(index)
    }

    /// Convert a raw u32 FuncId value back to a FuncId (Spur).
    /// Returns None if the value is invalid (0 is not a valid NonZeroU32).
    #[inline]
    fn func_id_from_raw(raw: u32) -> Option<FuncId> {
        use lasso::Key;
        let nz = std::num::NonZeroU32::new(raw)?;
        // Spur::try_from_usize expects a 0-based index; Spur stores it as index+1 (NonZeroU32).
        // Since we stored func.into_inner().get() which is the NonZeroU32 value,
        // and Spur::into_usize() returns key-1, we need try_from_usize(raw-1).
        FuncId::try_from_usize(nz.get() as usize - 1)
    }

    /// Get the shard index for a term (for hashconsing distribution).
    fn shard_index(term: &Term) -> usize {
        let mut hasher = FxHasher::default();
        term.hash(&mut hasher);
        (hasher.finish() as usize) % NUM_SHARDS
    }
}

/// A read guard for the term storage that enables zero-overhead term lookups.
/// Holds the RwLock read guard for the duration of its lifetime, avoiding
/// per-lookup lock acquisition in tight loops.
pub struct TermReadGuard<'a> {
    data: parking_lot::RwLockReadGuard<'a, Vec<Term>>,
}

impl TermReadGuard<'_> {
    /// Resolve a TermId to a reference to its Term without cloning.
    /// Returns None for inline TermIds (variables and nullary constants).
    /// Callers must check is_inline_var() / is_inline_nullary() first for hot paths.
    #[inline]
    pub fn get(&self, id: TermId) -> Option<&Term> {
        if id.is_inline() {
            return None;
        }
        self.data.get(id.index())
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
        // Handle inline TermIds without store access.
        if term.is_inline_var() {
            out.push('$');
            out.push_str(&term.inline_var_index().to_string());
            return Ok(());
        }
        if term.is_inline_nullary() {
            let func = TermStore::func_id_from_raw(term.inline_nullary_func_raw())
                .ok_or_else(|| format!("Invalid inline nullary func raw {:?}", term))?;
            let name = symbols
                .resolve(func)
                .ok_or_else(|| format!("Unknown symbol for func id {:?}", func))?;
            out.push_str(name);
            return Ok(());
        }
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
mod tests {
    use super::*;
    use crate::symbol::SymbolStore;
    use crate::test_utils::setup;

    // ========== HAPPY PATH: VARIABLE TESTS ==========

    #[test]
    fn var_creates_term_id() {
        let (_, terms) = setup();
        let id = terms.var(0);
        // Should not panic
        let _ = id;
    }

    #[test]
    fn var_same_index_returns_same_id() {
        let (_, terms) = setup();
        let id1 = terms.var(42);
        let id2 = terms.var(42);
        assert_eq!(id1, id2, "Same variable index should return same TermId");
    }

    #[test]
    fn var_different_indices_return_different_ids() {
        let (_, terms) = setup();
        let id1 = terms.var(0);
        let id2 = terms.var(1);
        assert_ne!(
            id1, id2,
            "Different variable indices should return different TermIds"
        );
    }

    #[test]
    fn var_resolves_correctly() {
        let (_, terms) = setup();
        let id = terms.var(7);
        let resolved = terms.resolve(id);
        assert_eq!(
            resolved,
            Some(Term::Var(7)),
            "Variable should resolve to Term::Var with correct index"
        );
    }

    #[test]
    fn is_var_returns_index_for_variable() {
        let (_, terms) = setup();
        let id = terms.var(99);
        assert_eq!(
            terms.is_var(id),
            Some(99),
            "is_var should return the variable index"
        );
    }

    #[test]
    fn is_var_returns_none_for_app() {
        let (symbols, terms) = setup();
        let f = symbols.intern("F");
        let id = terms.app0(f);
        assert_eq!(
            terms.is_var(id),
            None,
            "is_var should return None for applications"
        );
    }

    // ========== HAPPY PATH: APPLICATION TESTS ==========

    #[test]
    fn app0_creates_nullary_term() {
        let (symbols, terms) = setup();
        let nil = symbols.intern("Nil");
        let id = terms.app0(nil);
        let resolved = terms.resolve(id);
        assert_eq!(
            resolved,
            Some(Term::App(nil, SmallVec::new())),
            "Nullary application should resolve correctly"
        );
    }

    #[test]
    fn app1_creates_unary_term() {
        let (symbols, terms) = setup();
        let succ = symbols.intern("Succ");
        let zero = symbols.intern("Zero");
        let zero_id = terms.app0(zero);
        let one_id = terms.app1(succ, zero_id);

        let resolved = terms.resolve(one_id);
        assert_eq!(
            resolved,
            Some(Term::App(succ, smallvec::smallvec![zero_id])),
            "Unary application should resolve correctly"
        );
    }

    #[test]
    fn app2_creates_binary_term() {
        let (symbols, terms) = setup();
        let pair = symbols.intern("Pair");
        let a = terms.var(0);
        let b = terms.var(1);
        let pair_id = terms.app2(pair, a, b);

        let resolved = terms.resolve(pair_id);
        assert_eq!(
            resolved,
            Some(Term::App(pair, smallvec::smallvec![a, b])),
            "Binary application should resolve correctly"
        );
    }

    #[test]
    fn app_with_many_children() {
        let (symbols, terms) = setup();
        let tuple = symbols.intern("Tuple5");
        let children: SmallVec<[TermId; 4]> = (0..5).map(|i| terms.var(i)).collect();
        let id = terms.app(tuple, children.clone());

        let resolved = terms.resolve(id);
        assert_eq!(
            resolved,
            Some(Term::App(tuple, children)),
            "Application with many children should resolve correctly"
        );
    }

    #[test]
    fn is_app_returns_functor_and_children() {
        let (symbols, terms) = setup();
        let cons = symbols.intern("Cons");
        let x = terms.var(0);
        let y = terms.var(1);
        let id = terms.app2(cons, x, y);

        let result = terms.is_app(id);
        assert_eq!(
            result,
            Some((cons, smallvec::smallvec![x, y])),
            "is_app should return functor and children"
        );
    }

    #[test]
    fn is_app_returns_none_for_var() {
        let (_, terms) = setup();
        let id = terms.var(0);
        assert_eq!(
            terms.is_app(id),
            None,
            "is_app should return None for variables"
        );
    }

    // ========== HAPPY PATH: HASHCONSING TESTS ==========

    #[test]
    fn hashcons_same_nullary_app() {
        let (symbols, terms) = setup();
        let nil = symbols.intern("Nil");
        let id1 = terms.app0(nil);
        let id2 = terms.app0(nil);
        assert_eq!(
            id1, id2,
            "Same nullary application should be hashconsed to same TermId"
        );
    }

    #[test]
    fn hashcons_same_app_with_children() {
        let (symbols, terms) = setup();
        let cons = symbols.intern("Cons");
        let x = terms.var(0);
        let y = terms.var(1);

        let id1 = terms.app2(cons, x, y);
        let id2 = terms.app2(cons, x, y);
        assert_eq!(
            id1, id2,
            "Same application with same children should be hashconsed"
        );
    }

    #[test]
    fn hashcons_different_functor_different_id() {
        let (symbols, terms) = setup();
        let f = symbols.intern("F");
        let g = symbols.intern("G");
        let x = terms.var(0);

        let id1 = terms.app1(f, x);
        let id2 = terms.app1(g, x);
        assert_ne!(id1, id2, "Different functors should give different TermIds");
    }

    #[test]
    fn hashcons_different_children_different_id() {
        let (symbols, terms) = setup();
        let f = symbols.intern("F");
        let x = terms.var(0);
        let y = terms.var(1);

        let id1 = terms.app1(f, x);
        let id2 = terms.app1(f, y);
        assert_ne!(
            id1, id2,
            "Same functor but different children should give different TermIds"
        );
    }

    #[test]
    fn hashcons_child_order_matters() {
        let (symbols, terms) = setup();
        let pair = symbols.intern("Pair");
        let a = terms.var(0);
        let b = terms.var(1);

        let id1 = terms.app2(pair, a, b);
        let id2 = terms.app2(pair, b, a);
        assert_ne!(
            id1, id2,
            "Different child order should give different TermIds"
        );
    }

    #[test]
    fn hashcons_nested_terms() {
        let (symbols, terms) = setup();
        let f = symbols.intern("F");
        let g = symbols.intern("G");
        let x = terms.var(0);

        // Build G(x) twice
        let gx1 = terms.app1(g, x);
        let gx2 = terms.app1(g, x);
        assert_eq!(gx1, gx2, "G(x) should be hashconsed");

        // Build F(G(x)) twice
        let fgx1 = terms.app1(f, gx1);
        let fgx2 = terms.app1(f, gx2);
        assert_eq!(fgx1, fgx2, "F(G(x)) should be hashconsed");
    }

    // ========== HAPPY PATH: COMPLEX TERM CONSTRUCTION ==========

    #[test]
    fn build_natural_number() {
        let (symbols, terms) = setup();
        let zero = symbols.intern("Zero");
        let succ = symbols.intern("Succ");

        // Build the number 3 = Succ(Succ(Succ(Zero)))
        let n0 = terms.app0(zero);
        let n1 = terms.app1(succ, n0);
        let n2 = terms.app1(succ, n1);
        let n3 = terms.app1(succ, n2);

        // Verify structure
        assert_eq!(terms.is_app(n0), Some((zero, SmallVec::new())));
        assert_eq!(terms.is_app(n1), Some((succ, smallvec::smallvec![n0])));
        assert_eq!(terms.is_app(n2), Some((succ, smallvec::smallvec![n1])));
        assert_eq!(terms.is_app(n3), Some((succ, smallvec::smallvec![n2])));
    }

    #[test]
    fn build_list() {
        let (symbols, terms) = setup();
        let nil = symbols.intern("Nil");
        let cons = symbols.intern("Cons");

        // Build [x, y, z] = Cons(x, Cons(y, Cons(z, Nil)))
        let x = terms.var(0);
        let y = terms.var(1);
        let z = terms.var(2);
        let empty = terms.app0(nil);
        let list_z = terms.app2(cons, z, empty);
        let list_yz = terms.app2(cons, y, list_z);
        let list_xyz = terms.app2(cons, x, list_yz);

        // Verify head
        let (f, children) = terms.is_app(list_xyz).unwrap();
        assert_eq!(symbols.resolve(f), Some("Cons"));
        assert_eq!(children[0], x);
        assert_eq!(children[1], list_yz);
    }

    #[test]
    fn build_lambda_term() {
        let (symbols, terms) = setup();
        let app_sym = symbols.intern("App");
        let lam = symbols.intern("Lam");

        // Build: Lam(App(Var(1), Var(0)))  -- \x. x applied to bound var
        let v0 = terms.var(0);
        let v1 = terms.var(1);
        let application = terms.app2(app_sym, v1, v0);
        let lambda = terms.app1(lam, application);

        let (f, children) = terms.is_app(lambda).unwrap();
        assert_eq!(symbols.resolve(f), Some("Lam"));
        assert_eq!(children[0], application);
    }

    // ========== HAPPY PATH: LARGE SCALE TESTS ==========

    #[test]
    fn many_distinct_terms() {
        let (symbols, terms) = setup();
        let f = symbols.intern("F");

        // Create 1000 distinct terms F(Var(i))
        let ids: Vec<_> = (0u32..1000)
            .map(|i| {
                let v = terms.var(i);
                terms.app1(f, v)
            })
            .collect();

        // All should be distinct
        let id_set: std::collections::HashSet<_> = ids.iter().copied().collect();
        assert_eq!(id_set.len(), 1000, "All 1000 terms should be distinct");
    }

    #[test]
    fn many_hashconsed_terms() {
        let (symbols, terms) = setup();
        let f = symbols.intern("F");
        let x = terms.var(0);

        // Create F(x) 1000 times - should all be same TermId
        let ids: Vec<_> = (0..1000).map(|_| terms.app1(f, x)).collect();

        let first = ids[0];
        assert!(
            ids.iter().all(|&id| id == first),
            "All 1000 copies of F(x) should have same TermId"
        );
    }

    // ========== UNHAPPY PATH / EDGE CASE TESTS ==========

    #[test]
    fn resolve_invalid_store_ref() {
        let (_, terms) = setup();
        // Create a store-ref TermId that doesn't exist in this store
        // Tag 00 (non-ground store ref) with a large index
        let invalid_id = TermId(999999);
        // 999999 has bit 30=0, bit 31=0 => TAG_STORE_NONGROUND => store ref
        let resolved = terms.resolve(invalid_id);
        assert_eq!(
            resolved, None,
            "Resolving invalid store ref TermId should return None"
        );
    }

    #[test]
    fn var_max_index() {
        let (_, terms) = setup();
        // Inline vars use 30 bits, so max index is PAYLOAD_MASK
        let max_idx = PAYLOAD_MASK;
        let id = terms.var(max_idx);
        let resolved = terms.resolve(id);
        assert_eq!(
            resolved,
            Some(Term::Var(max_idx)),
            "Max inline variable index should work"
        );
    }

    #[test]
    fn var_zero_index() {
        let (_, terms) = setup();
        let id = terms.var(0);
        let resolved = terms.resolve(id);
        assert_eq!(
            resolved,
            Some(Term::Var(0)),
            "Zero variable index should work"
        );
    }

    // ========== THREAD SAFETY TESTS ==========

    #[test]
    fn concurrent_var_creation() {
        use std::sync::Arc;
        use std::thread;

        let terms = Arc::new(TermStore::new());
        let mut handles = vec![];

        // 10 threads all create var(42)
        for _ in 0..10 {
            let terms_clone = Arc::clone(&terms);
            handles.push(thread::spawn(move || terms_clone.var(42)));
        }

        let ids: Vec<_> = handles.into_iter().map(|h| h.join().unwrap()).collect();

        // All should be same
        let first = ids[0];
        assert!(
            ids.iter().all(|&id| id == first),
            "Concurrent var(42) should all return same TermId"
        );
    }

    #[test]
    fn concurrent_app_creation() {
        use std::sync::Arc;
        use std::thread;

        let symbols = Arc::new(SymbolStore::new());
        let terms = Arc::new(TermStore::new());
        let f = symbols.intern("F");
        let x = terms.var(0);

        let mut handles = vec![];

        // 10 threads all create F(x)
        for _ in 0..10 {
            let terms_clone = Arc::clone(&terms);
            handles.push(thread::spawn(move || terms_clone.app1(f, x)));
        }

        let ids: Vec<_> = handles.into_iter().map(|h| h.join().unwrap()).collect();

        // All should be same due to hashconsing
        let first = ids[0];
        assert!(
            ids.iter().all(|&id| id == first),
            "Concurrent F(x) should all return same TermId"
        );
    }

    #[test]
    fn concurrent_different_terms() {
        use std::sync::Arc;
        use std::thread;

        let symbols = Arc::new(SymbolStore::new());
        let terms = Arc::new(TermStore::new());
        let f = symbols.intern("F");

        let mut handles = vec![];

        // 10 threads each create F(Var(i))
        for i in 0u32..10 {
            let terms_clone = Arc::clone(&terms);
            handles.push(thread::spawn(move || {
                let v = terms_clone.var(i);
                terms_clone.app1(f, v)
            }));
        }

        let ids: Vec<_> = handles.into_iter().map(|h| h.join().unwrap()).collect();

        // All should be different
        let id_set: std::collections::HashSet<_> = ids.iter().copied().collect();
        assert_eq!(
            id_set.len(),
            10,
            "Concurrent different terms should all be distinct"
        );
    }
}
