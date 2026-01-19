use crate::drop_fresh::DropFresh;
use crate::nf::NF;
use crate::symbol::SymbolStore;
use crate::term::TermStore;
use smallvec::SmallVec;

pub(crate) fn setup() -> (SymbolStore, TermStore) {
    (SymbolStore::new(), TermStore::new())
}

pub(crate) fn make_ground_nf(name: &str, symbols: &SymbolStore, terms: &TermStore) -> NF<()> {
    let sym = symbols.intern(name);
    let term = terms.app0(sym);
    NF::new(
        SmallVec::from_slice(&[term]),
        DropFresh::identity(0),
        SmallVec::from_slice(&[term]),
    )
}

pub(crate) fn make_rule_nf(
    from: &str,
    to: &str,
    symbols: &SymbolStore,
    terms: &TermStore,
) -> NF<()> {
    let from_sym = symbols.intern(from);
    let to_sym = symbols.intern(to);
    let from_term = terms.app0(from_sym);
    let to_term = terms.app0(to_sym);
    NF::new(
        SmallVec::from_slice(&[from_term]),
        DropFresh::identity(0),
        SmallVec::from_slice(&[to_term]),
    )
}
