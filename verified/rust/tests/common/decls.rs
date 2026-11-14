//! Declarations the tests of the sorts share, and the symbols and names
//! they are written with.

use super::sorts::*;

// Symbols.
pub const Z: u32 = 0;
pub const SU: u32 = 1;
pub const PR: u32 = 2;
pub const F: u32 = 3;
pub const K: u32 = 6;
pub const A: u32 = 7;

// Names.
pub const UNIT: Name = 100;
pub const NAT: Name = 101;
pub const VOID: Name = 102;
pub const TWO: Name = 103;
pub const BOX: Name = 104;
pub const PAIR: Name = 105;
pub const MIX: Name = 106;
pub const C2: Name = 107;
pub const C3: Name = 108;
pub const SUC: Name = 109;
pub const ANY: Name = 110;

pub const G: u32 = 4;

pub fn z() -> P {
    pf(Z, vec![])
}
pub fn a() -> P {
    pf(A, vec![])
}
pub fn su(p: P) -> P {
    pf(SU, vec![p])
}
pub fn f2(p: P, q: P) -> P {
    pf(F, vec![p, q])
}
pub fn k1(p: P) -> P {
    pf(K, vec![p])
}
pub fn pr(p: P, q: P) -> P {
    pf(PR, vec![p, q])
}

pub fn one(f: u32, args: Vec<Option<Name>>) -> Def {
    Def { cases: vec![(f, args)], rest: None }
}

/// `unit` is `z`; `nat` is `z` or `s` of a `nat`; `void` is `s` of a `void`,
/// which nothing is; `two` is the pair of two `unit`; `box` is `k` of a
/// `nat`; `pair` is the pair of two `nat`; `mix` is `g` of a `unit` and a
/// `nat`; `c2` is `k` of a `box` and `c3` is `k` of a `c2`; `suc` is `s` of a
/// `nat`; `any` is `z` or anything else but `a`.
pub fn wf() -> Vec<(Name, Def)> {
    vec![
        (UNIT, one(Z, vec![])),
        (NAT, Def { cases: vec![(Z, vec![]), (SU, vec![Some(NAT)])], rest: None }),
        (VOID, one(SU, vec![Some(VOID)])),
        (TWO, one(PR, vec![Some(UNIT), Some(UNIT)])),
        (BOX, one(K, vec![Some(NAT)])),
        (PAIR, one(PR, vec![Some(NAT), Some(NAT)])),
        (MIX, one(G, vec![Some(UNIT), Some(NAT)])),
        (C2, one(K, vec![Some(BOX)])),
        (C3, one(K, vec![Some(C2)])),
        (SUC, one(SU, vec![Some(NAT)])),
        (ANY, Def { cases: vec![(Z, vec![])], rest: Some((vec![(A, 0)], None)) }),
    ]
}
