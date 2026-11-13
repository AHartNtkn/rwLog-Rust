/-
# What the Rust span operations compute, as terms

The Rust operations work in one namespace of variables: the first span is
renamed into the even variables (`lsub`), the second into the odd ones
(`rsub`), the equations are solved over `Nat`, and the answer is a term that
packs the resulting span (`packSpan`).

The specification tags the two spans with `Sum.inl` and `Sum.inr`, solves
over `Nat ⊕ Nat`, and renumbers with `RwLog.enc`, which is `2 v` on the left
and `2 v + 1` on the right. `compose_bridge` and `meet_bridge` say that the
two agree.
-/
import RwLog.Kernel.Span
import RwLogVerified.SolveCost

namespace RwLogVerified

open RwLog RwLog.Term
open RwLog.Eqns (solveOn solveOn_ren ren)

/-- A list of terms as a term. `z` is the symbol that ends a list. -/
def encList {V : Type} (z : Sym) : List (Term V) → Term V
  | [] => .sym z
  | t :: ts => .app t (encList z ts)

theorem encList_bind {V W : Type} (z : Sym) (σ : V → Term W) (c : List (Term V)) :
    (encList z c).bind σ = encList z (c.map (Term.bind σ)) := by
  induction c with
  | nil => rfl
  | cons t ts ih => simp only [encList, Term.bind_app, List.map_cons, ih]

theorem encList_rename {V W : Type} (z : Sym) (f : V → W) (c : List (Term V)) :
    (encList z c).rename f = encList z (c.map (Term.rename f)) :=
  encList_bind z _ c

theorem encList_inj {V : Type} (z : Sym) {c d : List (Term V)}
    (h : encList z c = encList z d) : c = d := by
  induction c generalizing d with
  | nil =>
    cases d with
    | nil => rfl
    | cons u us => cases h
  | cons t ts ih =>
    cases d with
    | nil => cases h
    | cons u us =>
      simp only [encList, Term.app.injEq] at h
      rw [h.1, ih h.2]

/-- A span as one term. -/
def packSpan (z : Sym) (sp : Span) : Pat := .app sp.l (.app sp.r (encList z sp.c))

/-- The first span's variables become the even variables. -/
def lsub : Nat → Pat := fun v => .var (2 * v)

/-- The second span's variables become the odd variables. -/
def rsub : Nat → Pat := fun v => .var (2 * v + 1)

/-- A span with a substitution applied. -/
def subSpan (sp : Span) (σ : Nat → Pat) : Span :=
  ⟨sp.l.bind σ, sp.r.bind σ, sp.c.map (Term.bind σ)⟩

theorem rename_app' {V W : Type} (f : V → W) (a b : Term V) :
    (Term.app a b).rename f = .app (a.rename f) (b.rename f) := rfl

theorem left_rename_enc (t : Pat) : (Pat.left t).rename RwLog.enc = t.bind lsub := by
  unfold Pat.left Term.rename
  rw [Term.bind_bind]
  apply Term.bind_congr
  intro v _
  simp [RwLog.enc, lsub]

theorem right_rename_enc (t : Pat) : (Pat.right t).rename RwLog.enc = t.bind rsub := by
  unfold Pat.right Term.rename
  rw [Term.bind_bind]
  apply Term.bind_congr
  intro v _
  simp [RwLog.enc, rsub]

theorem enc_injective : Function.Injective RwLog.enc := Equiv.injective _

theorem pack_finish (z : Sym) (θ : Nat ⊕ Nat → Term (Nat ⊕ Nat)) (l r : Term (Nat ⊕ Nat))
    (c : List (Term (Nat ⊕ Nat))) :
    ((Term.app l (.app r (encList z c))).bind θ).rename RwLog.enc =
      packSpan z (RwLog.finish θ l r c) := by
  simp only [packSpan, RwLog.finish, Term.bind_app, encList_bind, Term.rename, List.map_map]
  rfl

theorem store_rename (c₁ c₂ : Store) :
    (c₁.map Pat.left ++ c₂.map Pat.right).map (Term.rename RwLog.enc) =
      c₁.map (Term.bind lsub) ++ c₂.map (Term.bind rsub) := by
  simp only [List.map_append, List.map_map]
  congr 1
  · exact List.map_congr_left fun t _ => left_rename_enc t
  · exact List.map_congr_left fun t _ => right_rename_enc t

/-- Solving the renamed equation over `Nat` gives the specification's
composition, packed. -/
theorem compose_bridge (z : Sym) (x y : Span) :
    solveOn [(x.r.bind lsub, y.l.bind rsub)]
        (.app (x.l.bind lsub)
          (.app (y.r.bind rsub) (encList z (x.c.map (Term.bind lsub) ++ y.c.map (Term.bind rsub))))) =
      (x.compose y).map (packSpan z) := by
  have h := solveOn_ren enc_injective [(Pat.left x.r, Pat.right y.l)]
    (.app (Pat.left x.l) (.app (Pat.right y.r) (encList z (x.c.map Pat.left ++ y.c.map Pat.right))))
  simp only [Eqns.ren_cons, Eqns.ren_nil, rename_app', encList_rename, store_rename,
    left_rename_enc, right_rename_enc] at h
  rw [h]
  simp only [solveOn, Span.compose, Option.map_map]
  congr 1
  funext θ
  exact pack_finish z θ _ _ _

/-- Solving the two renamed equations over `Nat` gives the specification's
conjunction, packed. -/
theorem meet_bridge (z : Sym) (x y : Span) :
    solveOn [(x.l.bind lsub, y.l.bind rsub), (x.r.bind lsub, y.r.bind rsub)]
        (.app (x.l.bind lsub)
          (.app (x.r.bind lsub) (encList z (x.c.map (Term.bind lsub) ++ y.c.map (Term.bind rsub))))) =
      (x.meet y).map (packSpan z) := by
  have h := solveOn_ren enc_injective
    [(Pat.left x.l, Pat.right y.l), (Pat.left x.r, Pat.right y.r)]
    (.app (Pat.left x.l) (.app (Pat.left x.r) (encList z (x.c.map Pat.left ++ y.c.map Pat.right))))
  simp only [Eqns.ren_cons, Eqns.ren_nil, rename_app', encList_rename, store_rename,
    left_rename_enc, right_rename_enc] at h
  rw [h]
  simp only [solveOn, Span.meet, Option.map_map]
  congr 1
  funext θ
  exact pack_finish z θ _ _ _

end RwLogVerified
