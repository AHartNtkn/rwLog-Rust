/-
# A list of terms as a term

The store holds a list as a term: the applications of each member to the
rest, ended by the symbol `z`.
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

end RwLogVerified
