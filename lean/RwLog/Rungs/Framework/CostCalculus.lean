/-
# Reasoning about charged computations

`Costs m v c`: the charged computation `m` returns `v` and spends at most `c`
ticks. The rules below follow the shape of a computation written in the cost
monad, so the value and a bound on the cost of a long `do` block are found
together, one statement at a time. For the free list traversals of
`Trusted/Cost.lean` the value is the list function of the same name.
-/
import RwLog.Trusted.Cost

namespace RwLog

namespace Cost

variable {α β : Type}

/-- `m` returns `v` and spends at most `c` ticks. -/
def Costs (m : Cost α) (v : α) (c : Nat) : Prop := m.val = v ∧ m.ticks ≤ c

namespace Costs

theorem refl (m : Cost α) : Costs m m.val m.ticks := ⟨rfl, le_rfl⟩

theorem pure (a : α) : Costs (Pure.pure a) a 0 := ⟨rfl, le_rfl⟩

theorem tick (n : Nat) : Costs (Cost.tick n) () n := ⟨rfl, le_rfl⟩

theorem mono {m : Cost α} {v : α} {c c' : Nat} (h : Costs m v c) (hc : c ≤ c') : Costs m v c' :=
  ⟨h.1, le_trans h.2 hc⟩

theorem congr_val {m : Cost α} {v w : α} {c : Nat} (h : Costs m v c) (e : v = w) : Costs m w c :=
  e ▸ h

theorem bind {m : Cost α} {f : α → Cost β} {v : α} {w : β} {c c' : Nat}
    (h₁ : Costs m v c) (h₂ : Costs (f v) w c') : Costs (m >>= f) w (c + c') := by
  obtain ⟨rfl, h₁⟩ := h₁
  exact ⟨h₂.1, by simp only [bind_ticks]; exact Nat.add_le_add h₁ h₂.2⟩

theorem mapL {f : α → Cost β} {g : α → β} {c : Nat} :
    ∀ {xs : List α}, (∀ x ∈ xs, Costs (f x) (g x) c) → Costs (mapL f xs) (xs.map g) (xs.length * c)
  | [], _ => ⟨rfl, by simp [Cost.mapL]⟩
  | x :: xs, h => by
    have hx := h x (by simp)
    have ih := mapL (xs := xs) fun y hy => h y (by simp [hy])
    refine Costs.mono (c := c + (xs.length * c + 0)) ?_ ?_
    · exact bind hx (bind ih (pure _))
    · simp only [List.length_cons, Nat.add_zero, Nat.succ_mul]; omega

/-- `mapL` over the image of a list. -/
theorem mapL_map {γ : Type} {f : α → Cost β} {h : γ → α} {g : γ → β} {c : Nat} {l : List γ}
    (H : ∀ s ∈ l, Costs (f (h s)) (g s) c) : Costs (Cost.mapL f (l.map h)) (l.map g) (l.length * c) := by
  have := mapL (f := fun s => f (h s)) (g := g) (xs := l) H
  have e : ∀ l : List γ, Cost.mapL f (l.map h) = Cost.mapL (fun s => f (h s)) l := by
    intro l
    induction l with
    | nil => rfl
    | cons x xs ih => simp only [List.map_cons, Cost.mapL, ih]
  rw [e]; exact this

theorem flatMapL {f : α → Cost (List β)} {g : α → List β} {c : Nat} :
    ∀ {xs : List α}, (∀ x ∈ xs, Costs (f x) (g x) c) →
      Costs (flatMapL f xs) (xs.flatMap g) (xs.length * c)
  | [], _ => ⟨rfl, by simp [Cost.flatMapL]⟩
  | x :: xs, h => by
    have hx := h x (by simp)
    have ih := flatMapL (xs := xs) fun y hy => h y (by simp [hy])
    refine Costs.mono (c := c + (xs.length * c + 0)) ?_ ?_
    · exact bind hx (bind ih (pure _))
    · simp only [List.length_cons, Nat.add_zero, Nat.succ_mul]; omega

theorem filterL {f : α → Cost Bool} {g : α → Bool} {c : Nat} :
    ∀ {xs : List α}, (∀ x ∈ xs, Costs (f x) (g x) c) →
      Costs (filterL f xs) (xs.filter g) (xs.length * c)
  | [], _ => ⟨rfl, by simp [Cost.filterL]⟩
  | x :: xs, h => by
    have hx := h x (by simp)
    have ih := filterL (xs := xs) fun y hy => h y (by simp [hy])
    refine Costs.mono (c := c + (xs.length * c + 0)) ?_ ?_
    · rw [List.filter_cons]
      exact bind hx (bind ih (pure _))
    · simp only [List.length_cons, Nat.add_zero, Nat.succ_mul]; omega

theorem anyL {f : α → Cost Bool} {g : α → Bool} {c : Nat} :
    ∀ {xs : List α}, (∀ x ∈ xs, Costs (f x) (g x) c) →
      Costs (anyL f xs) (xs.any g) (xs.length * c)
  | [], _ => ⟨rfl, by simp [Cost.anyL]⟩
  | x :: xs, h => by
    have hx := h x (by simp)
    have ih := anyL (xs := xs) fun y hy => h y (by simp [hy])
    have hle : c + xs.length * c = (x :: xs).length * c := by
      simp only [List.length_cons, Nat.succ_mul]; omega
    rw [← hle, List.any_cons]
    refine bind hx ?_
    cases g x with
    | true => exact (pure true).mono (Nat.zero_le _)
    | false => simpa using ih

theorem allL {f : α → Cost Bool} {g : α → Bool} {c : Nat} :
    ∀ {xs : List α}, (∀ x ∈ xs, Costs (f x) (g x) c) →
      Costs (allL f xs) (xs.all g) (xs.length * c)
  | [], _ => ⟨rfl, by simp [Cost.allL]⟩
  | x :: xs, h => by
    have hx := h x (by simp)
    have ih := allL (xs := xs) fun y hy => h y (by simp [hy])
    have hle : c + xs.length * c = (x :: xs).length * c := by
      simp only [List.length_cons, Nat.succ_mul]; omega
    rw [← hle, List.all_cons]
    refine bind hx ?_
    cases g x with
    | true => simpa using ih
    | false => exact (pure false).mono (Nat.zero_le _)

theorem findL {f : α → Cost Bool} {g : α → Bool} {c : Nat} :
    ∀ {xs : List α}, (∀ x ∈ xs, Costs (f x) (g x) c) →
      Costs (findL f xs) (xs.find? g) (xs.length * c)
  | [], _ => ⟨rfl, by simp [Cost.findL]⟩
  | x :: xs, h => by
    have hx := h x (by simp)
    have ih := findL (xs := xs) fun y hy => h y (by simp [hy])
    have hle : c + xs.length * c = (x :: xs).length * c := by
      simp only [List.length_cons, Nat.succ_mul]; omega
    rw [← hle, List.find?_cons]
    refine bind hx ?_
    cases g x with
    | true => exact (pure (some x)).mono (Nat.zero_le _)
    | false => simpa using ih

/-- A fold whose steps keep an invariant of the accumulator. -/
theorem foldL {f : β → α → Cost β} {g : β → α → β} {c : Nat} (I : β → Prop) :
    ∀ {xs : List α} {b : β}, I b → (∀ b, I b → ∀ x ∈ xs, Costs (f b x) (g b x) c ∧ I (g b x)) →
      Costs (foldL f b xs) (xs.foldl g b) (xs.length * c)
  | [], _, _, _ => ⟨rfl, by simp [Cost.foldL]⟩
  | x :: xs, b, hb, h => by
    have hx := h b hb x (by simp)
    have ih := foldL I (xs := xs) hx.2 fun b' hb' y hy => h b' hb' y (by simp [hy])
    have hle : c + xs.length * c = (x :: xs).length * c := by
      simp only [List.length_cons, Nat.succ_mul]; omega
    rw [← hle]
    exact bind hx.1 ih

end Costs

end Cost

end RwLog
