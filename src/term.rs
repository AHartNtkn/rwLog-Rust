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
