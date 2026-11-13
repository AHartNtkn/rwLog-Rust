/-
# Charged computations whose value is only described

`Costs m v c` (`CostCalculus.lean`) names the value of a charged computation.
`Spends m c Q` only says that the value satisfies `Q`, which is what is known
when part of the input is not known exactly: a machine whose oracle may
return one of several equivalent answers, say. The rules follow the shape of
the computation as those of `Costs` do, and bounds on the ticks of the
traversals in terms of a bound on each member are given alongside.
-/
import RwLog.Rungs.Framework.CostCalculus
import RwLog.Rungs.Framework.Cost

namespace RwLog

namespace Cost

variable {α β γ : Type}

/-- `m` spends at most `c` ticks and its value satisfies `Q`. -/
def Spends (m : Cost α) (c : Nat) (Q : α → Prop) : Prop := m.ticks ≤ c ∧ Q m.val

namespace Spends

theorem of_costs {m : Cost α} {v : α} {c : Nat} (h : Costs m v c) : Spends m c (· = v) :=
  ⟨h.2, h.1⟩

theorem pure {Q : α → Prop} {a : α} (h : Q a) : Spends (Pure.pure a) 0 Q := ⟨le_rfl, h⟩

theorem mono {m : Cost α} {c c' : Nat} {Q Q' : α → Prop} (h : Spends m c Q) (hc : c ≤ c')
    (hQ : ∀ a, Q a → Q' a) : Spends m c' Q' :=
  ⟨le_trans h.1 hc, hQ _ h.2⟩

theorem bind {m : Cost α} {f : α → Cost β} {c c' : Nat} {Q : α → Prop} {R : β → Prop}
    (h₁ : Spends m c Q) (h₂ : ∀ a, Q a → Spends (f a) c' R) : Spends (m >>= f) (c + c') R := by
  have h := h₂ m.val h₁.2
  exact ⟨by simp only [bind_ticks]; exact Nat.add_le_add h₁.1 h.1, h.2⟩

/-- A traversal relates each member to its image. -/
theorem mapL {f : α → Cost β} {Q : α → β → Prop} {c : Nat} :
    ∀ {xs : List α}, (∀ x ∈ xs, Spends (f x) c (Q x)) →
      Spends (mapL f xs) (xs.length * c) (List.Forall₂ Q xs)
  | [], _ => ⟨by simp [Cost.mapL], .nil⟩
  | x :: xs, h => by
    have hx := h x (by simp)
    have ih := mapL (xs := xs) fun y hy => h y (by simp [hy])
    refine ⟨?_, .cons hx.2 ih.2⟩
    have h1 := hx.1
    have h2 := ih.1
    simp only [Cost.mapL, bind_ticks, pure_ticks, List.length_cons, Nat.succ_mul]
    omega

/-- A traversal of two related lists side by side. -/
theorem mapL_zip {f : α × γ → Cost β} {R : α → γ → Prop} {Q : α → β → Prop} {c : Nat} :
    ∀ {xs : List α} {ys : List γ}, List.Forall₂ R xs ys →
      (∀ x y, x ∈ xs → R x y → Spends (f (x, y)) c (Q x)) →
      Spends (Cost.mapL f (xs.zip ys)) (xs.length * c) (List.Forall₂ Q xs)
  | _, _, .nil, _ => ⟨by simp [Cost.mapL], .nil⟩
  | _, _, .cons (a := x) (b := y) (l₁ := xs) (l₂ := ys) hxy hr, h => by
    have hx := h x y (by simp) hxy
    have ih := mapL_zip hr fun a b ha hab => h a b (by simp [ha]) hab
    refine ⟨?_, .cons hx.2 ih.2⟩
    have h1 := hx.1
    have h2 := ih.1
    simp only [List.zip_cons_cons, Cost.mapL, bind_ticks, pure_ticks, List.length_cons,
      Nat.succ_mul]
    omega

end Spends

/-! ## Ticks of the traversals, from a bound on each member -/

theorem sum_map_le_mul {f : α → Nat} {c : Nat} : ∀ {xs : List α}, (∀ x ∈ xs, f x ≤ c) →
    (xs.map f).sum ≤ xs.length * c
  | [], _ => by simp
  | x :: xs, h => by
    have hx := h x (by simp)
    have ih := sum_map_le_mul (xs := xs) fun y hy => h y (by simp [hy])
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.succ_mul]
    omega

theorem anyL_ticks_le_mul {f : α → Cost Bool} {c : Nat} {xs : List α}
    (h : ∀ x ∈ xs, (f x).ticks ≤ c) : (anyL f xs).ticks ≤ xs.length * c :=
  le_trans (anyL_ticks_le f xs) (sum_map_le_mul h)

theorem allL_ticks_le_mul {f : α → Cost Bool} {c : Nat} {xs : List α}
    (h : ∀ x ∈ xs, (f x).ticks ≤ c) : (allL f xs).ticks ≤ xs.length * c :=
  le_trans (allL_ticks_le f xs) (sum_map_le_mul h)

theorem findL_ticks_le_mul {f : α → Cost Bool} {c : Nat} {xs : List α}
    (h : ∀ x ∈ xs, (f x).ticks ≤ c) : (findL f xs).ticks ≤ xs.length * c :=
  le_trans (findL_ticks_le f xs) (sum_map_le_mul h)

theorem filterL_ticks_le_mul {f : α → Cost Bool} {c : Nat} {xs : List α}
    (h : ∀ x ∈ xs, (f x).ticks ≤ c) : (filterL f xs).ticks ≤ xs.length * c := by
  rw [filterL_ticks]; exact sum_map_le_mul h

theorem mapL_ticks_le_mul {f : α → Cost β} {c : Nat} {xs : List α}
    (h : ∀ x ∈ xs, (f x).ticks ≤ c) : (mapL f xs).ticks ≤ xs.length * c := by
  rw [mapL_ticks]; exact sum_map_le_mul h

theorem flatMapL_ticks_le_mul {f : α → Cost (List β)} {c : Nat} {xs : List α}
    (h : ∀ x ∈ xs, (f x).ticks ≤ c) : (flatMapL f xs).ticks ≤ xs.length * c := by
  rw [flatMapL_ticks]; exact sum_map_le_mul h

end Cost

end RwLog
