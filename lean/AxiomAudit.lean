import RwLog

/-!
# Audit of the whole library

Checked by the build, for every module of the library, with nothing listed by
hand (`RwLog/Lib/Audit.lean`):

* every file under `RwLog/` is imported by the root `RwLog.lean`, so no file
  is out of the build;
* no declaration depends on an axiom other than Lean's three standard ones
  (`propext`, `Classical.choice`, `Quot.sound`). A proof that picks up
  `sorryAx` or a new axiom fails the build;
* the layers shared by every rung import no machine: the specification, the
  kernel, the span layer, the libraries, the constraint domain and the rung
  framework import only each other. A part of an engine with its contract,
  and a composition theorem, go in `Rungs/Framework` and so cannot rest on
  one engine.
-/

#audit_library RwLog

#shared_layers RwLog.Trusted RwLog.Kernel RwLog.SpanLayer RwLog.Lib RwLog.Sorts
  RwLog.Rungs.Framework
