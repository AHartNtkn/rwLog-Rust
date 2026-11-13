import RwLog.Rungs.R005.Spec

/-!
# What R005 pays on the inputs of `SYMMETRIC_ENGINE_SIMULATION.md`

The note asks whether the engine of `SYMMETRIC_ENGINE.md` stays within a
polynomial of R005. These checks record R005's side of each comparison; the
engine's side is `scripts/symmetric_engine_tables.py`.

* `clash`: `p ; q` where every answer of `p` ends in `t _` and every answer of
  `q` begins with `u _`. Both tables are infinite. R005 halts in its second
  round, by unfolding. `clashId` is the same with an identity span at the
  end of `p` and at the start of `q`, so that the last span of one and the
  first span of the other say nothing.
* `down k`: `@(s^k z) ; q` with `q = ((s $x) -> $x) ; q | (z -> z)`. R005 halts
  after `k + 3` rounds at a polynomial cost.
* `ladder n`: `@(st nil) ; r_n` with `r_i = G ; (F ; r_(i-1))`. R005 halts after
  `n + 3` rounds. Larger `n` do not evaluate in reasonable time here, so the
  growth is not settled by these numbers.
-/

namespace RwLog.Tests.Simulation

/-- Steps taken within the fuel, whether the machine halted, ticks paid. -/
def costOf (C : CostedRuntime) (P : Program) (q : Rel) (fuel : Nat) : Nat × Bool × Nat :=
  let rec go (s : C.State) : Nat → Nat → Nat → Nat × Bool × Nat
    | 0, i, acc => (i, false, acc)
    | f + 1, i, acc =>
      let r := C.step s
      match r.val with
      | .done => (i, true, acc + r.ticks)
      | .emit _ s' => go s' f (i + 1) (acc + r.ticks)
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

#guard costOf R005.costed clashP clash 10 == (2, true, 3571)
#guard costOf R005.costed clashP clashId 10 == (3, true, 27340)

def downP : Program :=
  ⟨[("q", .or (.seq (.span ⟨.app (.sym "s") (.var 0), .var 0, []⟩) (.call "q")) (.at_ (.sym "z")))], []⟩
def down (k : Nat) : Rel := .seq (.at_ (num k)) (.call "q")

#guard [1, 2, 3, 4, 6, 8].map (fun k => costOf R005.costed downP (down k) 60) ==
  [(4, true, 70783), (5, true, 135988), (6, true, 278543), (7, true, 537596),
    (9, true, 821008), (11, true, 2329233)]

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

#guard (List.range 5).map (fun n => costOf R005.costed (ladP n) (ladder n) 40) ==
  [(3, true, 12788), (5, true, 265798), (6, true, 1304050), (7, true, 1400644), (8, true, 2975637)]

end RwLog.Tests.Simulation
