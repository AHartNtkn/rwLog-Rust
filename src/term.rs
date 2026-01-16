use crate::symbol::{FuncId, SymbolStore};
use hashbrown::HashMap;
use parking_lot::RwLock;
use rustc_hash::FxHasher;
use smallvec::SmallVec;
use std::hash::{Hash, Hasher};
use std::sync::atomic::{AtomicU32, Ordering};

/// Unique identifier for a term in the term store.
/// TermIds are stable and can be compared for equality.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct TermId(u32);

impl TermId {
    /// Get the raw u32 value (for debugging/display).
    pub fn raw(self) -> u32 {
        self.0
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
mod tests {
    use super::*;
    use crate::symbol::SymbolStore;

    // Helper to create a test environment
    fn setup() -> (SymbolStore, TermStore) {
        (SymbolStore::new(), TermStore::new())
    }

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
        assert_eq!(
            id1, id2,
            "Same variable index should return same TermId"
        );
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
        assert_ne!(
            id1, id2,
            "Different functors should give different TermIds"
        );
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
        let ids: Vec<_> = (0u32..1000).map(|i| {
            let v = terms.var(i);
            terms.app1(f, v)
        }).collect();

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
    fn resolve_invalid_term_id() {
        let (_, terms) = setup();
        // Create a TermId that doesn't exist in this store
        let invalid_id = TermId(999999);
        let resolved = terms.resolve(invalid_id);
        assert_eq!(
            resolved, None,
            "Resolving invalid TermId should return None"
        );
    }

    #[test]
    fn var_max_index() {
        let (_, terms) = setup();
        let id = terms.var(u32::MAX);
        let resolved = terms.resolve(id);
        assert_eq!(
            resolved,
            Some(Term::Var(u32::MAX)),
            "Max u32 variable index should work"
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
            id_set.len(), 10,
            "Concurrent different terms should all be distinct"
        );
    }
}
