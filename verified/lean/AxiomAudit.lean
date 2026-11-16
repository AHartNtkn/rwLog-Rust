import RwLogVerified
import RwLog.Lib.Audit

/-!
# Audit of the verified Rust

Checked by the build, for every module of the generated Lean (`RwlogCore`)
and of the proofs about it (`RwLogVerified`), with nothing listed by hand
(`lean/RwLog/Lib/Audit.lean`): every file of both is in the build, and no
declaration depends on an axiom other than Lean's three standard ones
(`propext`, `Classical.choice`, `Quot.sound`). A proof that picks up
`sorryAx` or a new axiom fails the build.
-/

#audit_library RwLogVerified RwlogCore
