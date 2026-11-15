import RwLog.Rungs.R005.Sorts

/-!
# What R005 pays on the inputs of `SYMMETRIC_ENGINE_SIMULATION.md`

The note asks whether the engine of `SYMMETRIC_ENGINE.md` stays within a
polynomial of R005. These checks record R005's side of each comparison, on
R005 as it is written against the derivation kernel, at the domain of sorts
with nothing charged (`Engine.atSorts`): the ticks are the engine's own and
those of the operations on nodes. The engine's side is
`scripts/symmetric_engine_tables.py`.

The figures in the note are those of R005 at the tag `epoch-1`, a machine
with other charges and a step that did more in a round; they are in this file
at commit `326b608` and are reproduced by `scripts/r005_interpreter.py check`.
Only growth is compared in the note, and it is the same here: every run below
halts, after a number of steps linear in the parameter.

* `clash`: `p ; q` where every answer of `p` ends in `t _` and every answer of
  `q` begins with `u _`. Both tables are infinite. R005 halts in its fifth
  step, by unfolding. `clashId` is the same with an identity span at the
  end of `p` and at the start of `q`, so that the last span of one and the
  first span of the other say nothing.
* `deep`: `p ; q` with `p = (z -> (b z)) | p ; ($x -> (a $x))` and
  `q = ((a (e $x)) -> $x) | ((b $x) -> $x) ; q`. The answers of `p` end in
  `a^n (b z)` and those of `q` begin with `b^k (a (e _))`, so `p ; q` relates
  nothing, and both tables are infinite. No answer of `p` meets an answer of
  `q`, but the last span of an answer of `p` alone does meet a first span of
  an answer of `q`, on either side: the clash is two spans deep. R005 halts,
  by unfolding. This is the input on which the symmetric engine with the
  interface check and no unfolding race never halts (the note, section 10).
* `down k`: `@(s^k z) ; q` with `q = ((s $x) -> $x) ; q | (z -> z)`. R005 halts
  after `3 * k + 7` steps at a polynomial cost.
* `ladder n`: `@(st nil) ; r_n` with `r_i = G ; (F ; r_(i-1))`. R005 halts after
  `2 * n + 10` steps for `n` from 1. Larger `n` do not evaluate in reasonable
  time here, so the growth is not settled by these numbers.
-/

namespace RwLog.Tests.Simulation

/-- Steps taken within the fuel, whether the machine halted, ticks paid. -/
def costOf (C : CostedRuntime) (P : Program) (q : Rel) (fuel : Nat) : Nat × Bool × Nat :=
  let rec go (s : C.State) : Nat → Nat → Nat → Nat × Bool × Nat
    | 0, i, acc => (i, false, acc)
    | f + 1, i, acc =>
      let r := C.step s
      match r.val with
      | .done _ => (i, true, acc + r.ticks)
      | .emit _ s' => go s' f (i + 1) (acc + r.ticks)
      | .progress _ s' => go s' f (i + 1) (acc + r.ticks)
  go (C.start P q) fuel 0 (C.init P q).ticks

def num : Nat → Pat
  | 0 => .sym "z"
  | n + 1 => .app (.sym "s") (num n)

/-- `$x -> n` for every number `n`. -/
def gen : Rel := .or (.span ⟨.var 0, .sym "z", []⟩)
  (.seq (.call "gen") (.span ⟨.var 0, .app (.sym "s") (.var 0), []⟩))

def idSpan : Rel := .span ⟨.var 0, .var 0, []⟩
def clashP : Program := ⟨[("gen", gen),
  ("p", .seq (.call "gen") (.span ⟨.var 0, .app (.sym "t") (.var 0), []⟩)),
  ("q", .seq (.span ⟨.app (.sym "u") (.var 0), .var 0, []⟩) (.call "gen")),
  ("pi", .seq (.call "p") idSpan), ("qi", .seq idSpan (.call "q"))], []⟩

def clash : Rel := .seq (.call "p") (.call "q")
def clashId : Rel := .seq (.call "pi") (.call "qi")

#guard costOf R005.engine.atSorts clashP clash 10 == (5, true, 21000)
#guard costOf R005.engine.atSorts clashP clashId 10 == (7, true, 65362)

def deepP : Program := ⟨[
  ("p", .or (.span ⟨.sym "z", .app (.sym "b") (.sym "z"), []⟩)
    (.seq (.call "p") (.span ⟨.var 0, .app (.sym "a") (.var 0), []⟩))),
  ("q", .or (.span ⟨.app (.sym "a") (.app (.sym "e") (.var 0)), .var 0, []⟩)
    (.seq (.span ⟨.app (.sym "b") (.var 0), .var 0, []⟩) (.call "q")))], []⟩

def deep : Rel := .seq (.call "p") (.call "q")

#guard costOf R005.engine.atSorts deepP deep 14 == (9, true, 109962)

def downP : Program :=
  ⟨[("q", .or (.seq (.span ⟨.app (.sym "s") (.var 0), .var 0, []⟩) (.call "q")) (.at_ (.sym "z")))], []⟩
def down (k : Nat) : Rel := .seq (.at_ (num k)) (.call "q")

#guard [1, 2, 3, 4, 6].map (fun k => costOf R005.engine.atSorts downP (down k) 60) ==
  [(10, true, 101405), (13, true, 169371), (16, true, 242289), (19, true, 529223),
    (25, true, 1169866)]

def st (x : Pat) : Pat := .app (.sym "st") x
def pr (x y : Pat) : Pat := .app (.app (.sym "pair") x) y
/-- `st s -> pair s n` for every number `n`. -/
def ladG : Rel := .or (.span ⟨st (.var 0), pr (.var 0) (.sym "z"), []⟩)
  (.seq (.call "G") (.span ⟨pr (.var 0) (.var 1), pr (.var 0) (.app (.sym "s") (.var 1)), []⟩))
/-- `pair s 0 -> st (c0 s) | pair s 1 -> st (c1 s)`. -/
def ladF : Rel := .or (.span ⟨pr (.var 0) (.sym "z"), st (.app (.sym "c0") (.var 0)), []⟩)
  (.span ⟨pr (.var 0) (.app (.sym "s") (.sym "z")), st (.app (.sym "c1") (.var 0)), []⟩)
def ladTarget : Nat → Pat
  | 0 => .sym "nil"
  | n + 1 => .app (.sym "c1") (ladTarget n)
def ladName (i : Nat) : Name := "r" ++ toString i
def ladDef (n : Nat) : Nat → Rel
  | 0 => .span ⟨st (ladTarget n), .sym "done", []⟩
  | i + 1 => .seq (.call "G") (.seq ladF (.call (ladName i)))
def ladP (n : Nat) : Program :=
  ⟨("G", ladG) :: (List.range (n + 1)).map (fun i => (ladName i, ladDef n i)), []⟩
def ladder (n : Nat) : Rel := .seq (.at_ (st (.sym "nil"))) (.call (ladName n))

#guard (List.range 4).map (fun n => costOf R005.engine.atSorts (ladP n) (ladder n) 40) ==
  [(5, true, 6591), (12, true, 445124), (14, true, 1192103), (16, true, 2587166)]

end RwLog.Tests.Simulation
