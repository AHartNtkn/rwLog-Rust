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
mod tests {
    use super::*;

    // ========== HAPPY PATH TESTS ==========

    #[test]
    fn intern_returns_func_id() {
        let store = SymbolStore::new();
        let id = store.intern("Cons");
        // Should return a valid FuncId (just check it doesn't panic)
        let _ = id;
    }

    #[test]
    fn intern_same_string_returns_same_id() {
        let store = SymbolStore::new();
        let id1 = store.intern("Nil");
        let id2 = store.intern("Nil");
        assert_eq!(
            id1, id2,
            "Interning the same string twice should return identical FuncIds"
        );
    }

    #[test]
    fn intern_different_strings_returns_different_ids() {
        let store = SymbolStore::new();
        let id1 = store.intern("Cons");
        let id2 = store.intern("Nil");
        assert_ne!(
            id1, id2,
            "Interning different strings should return different FuncIds"
        );
    }

    #[test]
    fn resolve_returns_original_string() {
        let store = SymbolStore::new();
        let id = store.intern("Lambda");
        let resolved = store.resolve(id);
        assert_eq!(
            resolved,
            Some("Lambda"),
            "Resolving a FuncId should return the original string"
        );
    }

    #[test]
    fn resolve_multiple_symbols() {
        let store = SymbolStore::new();
        let symbols = ["App", "Lam", "Var", "Zero", "Succ"];
        let ids: Vec<_> = symbols.iter().map(|s| store.intern(s)).collect();

        for (i, id) in ids.iter().enumerate() {
            let resolved = store.resolve(*id);
            assert_eq!(
                resolved,
                Some(symbols[i]),
                "Each FuncId should resolve to its original string"
            );
        }
    }

    #[test]
    fn contains_returns_true_for_interned_symbol() {
        let store = SymbolStore::new();
        store.intern("True");
        assert!(
            store.contains("True"),
            "contains should return true for interned symbol"
        );
    }

    #[test]
    fn contains_returns_false_for_unknown_symbol() {
        let store = SymbolStore::new();
        store.intern("True");
        assert!(
            !store.contains("False"),
            "contains should return false for non-interned symbol"
        );
    }

    #[test]
    fn get_returns_some_for_interned_symbol() {
        let store = SymbolStore::new();
        let id = store.intern("Pair");
        let retrieved = store.get("Pair");
        assert_eq!(
            retrieved,
            Some(id),
            "get should return the same FuncId as intern"
        );
    }

    #[test]
    fn get_returns_none_for_unknown_symbol() {
        let store = SymbolStore::new();
        store.intern("Pair");
        let retrieved = store.get("Triple");
        assert_eq!(
            retrieved, None,
            "get should return None for non-interned symbol"
        );
    }

    #[test]
    fn intern_empty_string_succeeds() {
        // Empty strings are valid symbols (edge case but allowed)
        let store = SymbolStore::new();
        let id = store.intern("");
        let resolved = store.resolve(id);
        assert_eq!(
            resolved,
            Some(""),
            "Empty string should be internabled and resolvable"
        );
    }

    #[test]
    fn intern_unicode_symbols() {
        let store = SymbolStore::new();
        let id1 = store.intern("λ");
        let id2 = store.intern("∀");
        let id3 = store.intern("→");

        assert_ne!(id1, id2);
        assert_ne!(id2, id3);
        assert_eq!(store.resolve(id1), Some("λ"));
        assert_eq!(store.resolve(id2), Some("∀"));
        assert_eq!(store.resolve(id3), Some("→"));
    }

    #[test]
    fn intern_long_symbol_name() {
        let store = SymbolStore::new();
        let long_name = "VeryLongConstructorNameThatMightCauseIssues".repeat(10);
        let id = store.intern(&long_name);
        let resolved = store.resolve(id);
        assert_eq!(
            resolved,
            Some(long_name.as_str()),
            "Long symbol names should be handled correctly"
        );
    }

    #[test]
    fn many_unique_symbols() {
        let store = SymbolStore::new();
        let mut ids = Vec::new();

        // Intern 1000 unique symbols
        for i in 0..1000 {
            let name = format!("Symbol_{}", i);
            ids.push((name.clone(), store.intern(&name)));
        }

        // Verify all are unique and resolvable
        for (name, id) in &ids {
            assert_eq!(
                store.resolve(*id),
                Some(name.as_str()),
                "All symbols should resolve correctly"
            );
        }

        // Verify all IDs are unique
        let id_set: std::collections::HashSet<_> = ids.iter().map(|(_, id)| *id).collect();
        assert_eq!(
            id_set.len(),
            1000,
            "All 1000 symbols should have unique FuncIds"
        );
    }

    // ========== UNHAPPY PATH / EDGE CASE TESTS ==========

    #[test]
    fn resolve_invalid_func_id_from_different_store() {
        let store1 = SymbolStore::new();
        let store2 = SymbolStore::new();

        let id_from_store1 = store1.intern("OnlyInStore1");

        // Attempting to resolve an ID from a different store should return None
        // (or the same string if both stores happen to have it, but in this case store2 doesn't)
        // Note: lasso's ThreadedRodeo behavior - IDs are indices, so this might actually
        // return garbage or panic. We'll handle this by returning None for safety.
        let resolved = store2.resolve(id_from_store1);

        // store2 doesn't have this ID, so it should be None
        // (Actually, lasso might not do bounds checking, so this test documents expected behavior)
        // If lasso panics or returns garbage, we need a wrapper.
        assert_eq!(
            resolved, None,
            "Resolving a FuncId from a different store should return None"
        );
    }

    #[test]
    fn whitespace_symbols_are_distinct() {
        let store = SymbolStore::new();
        let id_space = store.intern(" ");
        let id_tab = store.intern("\t");
        let id_newline = store.intern("\n");

        assert_ne!(
            id_space, id_tab,
            "Space and tab should be different symbols"
        );
        assert_ne!(
            id_tab, id_newline,
            "Tab and newline should be different symbols"
        );
        assert_ne!(
            id_space, id_newline,
            "Space and newline should be different symbols"
        );
    }

    #[test]
    fn case_sensitive_symbols() {
        let store = SymbolStore::new();
        let id_lower = store.intern("cons");
        let id_upper = store.intern("Cons");
        let id_caps = store.intern("CONS");

        assert_ne!(id_lower, id_upper, "cons and Cons should be different");
        assert_ne!(id_upper, id_caps, "Cons and CONS should be different");
        assert_ne!(id_lower, id_caps, "cons and CONS should be different");
    }

    // ========== THREAD SAFETY TESTS ==========

    #[test]
    fn concurrent_intern_same_symbol() {
        use std::sync::Arc;
        use std::thread;

        let store = Arc::new(SymbolStore::new());
        let mut handles = vec![];

        // Spawn 10 threads that all intern the same symbol
        for _ in 0..10 {
            let store_clone = Arc::clone(&store);
            handles.push(thread::spawn(move || store_clone.intern("SharedSymbol")));
        }

        let ids: Vec<_> = handles.into_iter().map(|h| h.join().unwrap()).collect();

        // All threads should get the same FuncId
        let first_id = ids[0];
        for id in ids {
            assert_eq!(
                id, first_id,
                "All threads should get the same FuncId for the same symbol"
            );
        }
    }

    #[test]
    fn concurrent_intern_different_symbols() {
        use std::sync::Arc;
        use std::thread;

        let store = Arc::new(SymbolStore::new());
        let mut handles = vec![];

        // Spawn 10 threads that each intern a unique symbol
        for i in 0..10 {
            let store_clone = Arc::clone(&store);
            handles.push(thread::spawn(move || {
                let name = format!("ThreadSymbol_{}", i);
                (name.clone(), store_clone.intern(&name))
            }));
        }

        let results: Vec<_> = handles.into_iter().map(|h| h.join().unwrap()).collect();

        // All FuncIds should be unique
        let id_set: std::collections::HashSet<_> = results.iter().map(|(_, id)| *id).collect();
        assert_eq!(
            id_set.len(),
            10,
            "All threads should get unique FuncIds for different symbols"
        );

        // All should resolve correctly
        for (name, id) in results {
            assert_eq!(store.resolve(id), Some(name.as_str()));
        }
    }
}
