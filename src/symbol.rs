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
