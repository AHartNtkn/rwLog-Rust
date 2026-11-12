/-
# Rung R001: order and direction (the Symmetry group)

* `conv_trace`: running `conv q` is running `q` with every answer swapped,
  step for step and exactly. The two initial states have the same tables and
  differ only in `rootFlip`, and a round never reads `rootFlip` except to
  orient the root's new answers.
-/
import RwLog.Rungs.R001.Spec

namespace RwLog

namespace R001

/-! ## `conv_trace` -/

theorem orient_not (f : Bool) (xs : List Span) :
    orient (!f) xs = (orient f xs).map Span.swap := by
  cases f <;> simp [orient, Function.comp_def]

/-- Flipping the root's orientation leaves the tables alone. -/
theorem round_flip (st : State) :
    round ⟨st.P, st.tables, !st.rootFlip, st.depth⟩ =
      (⟨st.P, (round st).1.tables, !st.rootFlip, st.depth + 1⟩, (round st).2.map Span.swap) := by
  simp only [round, orient_not]

theorem step_flip (st : State) :
    step ⟨st.P, st.tables, !st.rootFlip, st.depth⟩ =
      match step st with
      | .emit as st' => .emit (as.map Span.swap) ⟨st'.P, st'.tables, !st'.rootFlip, st'.depth⟩
      | .done => .done := by
  unfold step
  by_cases h : st.finished = true
  · have h' : State.finished ⟨st.P, st.tables, !st.rootFlip, st.depth⟩ = true := h
    simp [h, h']
  · have h' : ¬ State.finished ⟨st.P, st.tables, !st.rootFlip, st.depth⟩ = true := h
    simp only [h, h', round_flip]
    simp [round]

/-- The state with the root's orientation flipped. -/
def State.flip (st : State) : State := ⟨st.P, st.tables, !st.rootFlip, st.depth⟩

theorem trace_succ (st : runtime.State) (n : Nat) :
    runtime.trace st (n + 1) =
      match runtime.step st with
      | .emit as s' => as :: runtime.trace s' n
      | .done => [] := by
  conv => lhs; unfold Runtime.trace
  cases runtime.step st <;> rfl

theorem trace_flip (st : State) (n : Nat) :
    runtime.trace (st.flip : runtime.State) n =
      (runtime.trace (st : runtime.State) n).map (·.map Span.swap) := by
  induction n generalizing st with
  | zero => rfl
  | succ n ih =>
    refine (trace_succ (st.flip : runtime.State) n).trans ?_
    refine Eq.trans ?_ (congrArg _ (trace_succ (st : runtime.State) n)).symm
    show (match step st.flip with
      | .emit as s' => as :: runtime.trace s' n
      | .done => []) = (match step st with
      | .emit as s' => as :: runtime.trace s' n
      | .done => []).map _
    rw [State.flip, step_flip]
    cases step st with
    | emit as st' => simp only [List.map_cons]; rw [← ih st']; rfl
    | done => rfl

theorem conv_trace : Obligation.conv_trace := by
  intro P q n
  have h : runtime.init P (.conv q) = State.flip (runtime.init P q) := by
    show State.ofGoal P ⟨none, .conv q, none⟩ = _
    simp only [State.ofGoal, Goal.norm, canon]
    rw [Goal.stripConv]
    rfl
  rw [h]
  exact trace_flip (runtime.init P q) n

/-! ## `relCmp` is a linear order -/

section Order

/-- Lexicographic transitivity, from the facts about the first components. -/
theorem then_isLE_trans {o₁ o₂ o₃ p₁ p₂ p₃ : Ordering}
    (hlt : o₁ = .lt → o₂ = .lt → o₃ = .lt)
    (heq₁ : o₁ = .eq → o₃ = o₂) (heq₂ : o₂ = .eq → o₃ = o₁)
    (hp : p₁.isLE → p₂.isLE → p₃.isLE) :
    (o₁.then p₁).isLE → (o₂.then p₂).isLE → (o₃.then p₃).isLE := by
  intro h₁ h₂
  rw [Ordering.isLE_then_iff_or] at h₁ h₂ ⊢
  rcases h₁ with h₁ | ⟨h₁, hp₁⟩ <;> rcases h₂ with h₂ | ⟨h₂, hp₂⟩
  · exact .inl (hlt h₁ h₂)
  · exact .inl ((heq₂ h₂).trans h₁)
  · exact .inl ((heq₁ h₁).trans h₂)
  · exact .inr ⟨(heq₁ h₁).trans h₂, hp hp₁ hp₂⟩

/-- A comparison with the three laws on given elements. -/
structure Lin {α : Type} (f : α → α → Ordering) (a b c : α) : Prop where
  swap_ab : f a b = (f b a).swap
  eq_ab : f a b = .eq → a = b
  eq_bc : f b c = .eq → b = c
  eq_ac : f a c = .eq → a = c
  trans : (f a b).isLE → (f b c).isLE → (f a c).isLE

theorem Lin.lt_trans {α : Type} {f : α → α → Ordering} {a b c : α} (h : Lin f a b c)
    (h₁ : f a b = .lt) (h₂ : f b c = .lt) : f a c = .lt := by
  have hle := h.trans (by rw [h₁]; rfl) (by rw [h₂]; rfl)
  cases hac : f a c with
  | lt => rfl
  | gt => rw [hac] at hle; cases hle
  | eq =>
    have := h.eq_ac hac; subst this
    rw [h.swap_ab, h₂] at h₁; cases h₁

theorem Lin.then {α : Type} {f : α → α → Ordering} {a b c : α} (h : Lin f a b c)
    {p₁ p₂ p₃ : Ordering} (hp : p₁.isLE → p₂.isLE → p₃.isLE) :
    ((f a b).then p₁).isLE → ((f b c).then p₂).isLE → ((f a c).then p₃).isLE :=
  then_isLE_trans h.lt_trans (fun e => by rw [h.eq_ab e]) (fun e => by rw [h.eq_bc e]) hp

theorem lin_of {α : Type} (f : α → α → Ordering) [Std.TransCmp f] [Std.LawfulEqCmp f]
    (a b c : α) : Lin f a b c :=
  ⟨Std.OrientedCmp.eq_swap, Std.LawfulEqCmp.eq_of_compare, Std.LawfulEqCmp.eq_of_compare,
    Std.LawfulEqCmp.eq_of_compare, Std.TransCmp.isLE_trans⟩

theorem patCmp_swap : ∀ a b : Pat, patCmp a b = (patCmp b a).swap
  | .var a, .var b => by simp only [patCmp]; exact Std.OrientedCmp.eq_swap
  | .var _, .sym _ => rfl
  | .var _, .app _ _ => rfl
  | .sym _, .var _ => rfl
  | .sym f, .sym g => by simp only [patCmp]; exact Std.OrientedCmp.eq_swap
  | .sym _, .app _ _ => rfl
  | .app _ _, .var _ => rfl
  | .app _ _, .sym _ => rfl
  | .app a b, .app c d => by
    simp only [patCmp, Ordering.swap_then, ← patCmp_swap]

theorem patCmp_eq : ∀ {a b : Pat}, patCmp a b = .eq → a = b
  | .var a, .var b, h => by
    simp only [patCmp] at h; rw [Std.LawfulEqCmp.eq_of_compare h]
  | .sym f, .sym g, h => by
    simp only [patCmp] at h; rw [Std.LawfulEqCmp.eq_of_compare h]
  | .app a b, .app c d, h => by
    simp only [patCmp, Ordering.then_eq_eq] at h
    rw [patCmp_eq h.1, patCmp_eq h.2]
  | .var _, .sym _, h | .var _, .app _ _, h | .sym _, .var _, h | .sym _, .app _ _, h
  | .app _ _, .var _, h | .app _ _, .sym _, h => by simp [patCmp] at h

theorem patCmp_trans : ∀ {a b c : Pat}, (patCmp a b).isLE → (patCmp b c).isLE → (patCmp a c).isLE
  | .var a, .var b, .var c, h₁, h₂ => by
    simp only [patCmp] at h₁ h₂ ⊢; exact Std.TransCmp.isLE_trans h₁ h₂
  | .sym a, .sym b, .sym c, h₁, h₂ => by
    simp only [patCmp] at h₁ h₂ ⊢; exact Std.TransCmp.isLE_trans h₁ h₂
  | .app a₁ a₂, .app b₁ b₂, .app c₁ c₂, h₁, h₂ => by
    simp only [patCmp] at h₁ h₂ ⊢
    exact (⟨patCmp_swap _ _, patCmp_eq, patCmp_eq, patCmp_eq, patCmp_trans⟩ :
      Lin patCmp a₁ b₁ c₁).then patCmp_trans h₁ h₂
  | .var _, .var _, .sym _, h₁, h₂ => by rfl
  | .var _, .var _, .app _ _, h₁, h₂ => by rfl
  | .var _, .sym _, .var _, h₁, h₂ => by cases h₂
  | .var _, .sym _, .sym _, h₁, h₂ => by rfl
  | .var _, .sym _, .app _ _, h₁, h₂ => by rfl
  | .var _, .app _ _, .var _, h₁, h₂ => by cases h₂
  | .var _, .app _ _, .sym _, h₁, h₂ => by rfl
  | .var _, .app _ _, .app _ _, h₁, h₂ => by rfl
  | .sym _, .var _, .var _, h₁, h₂ => by cases h₁
  | .sym _, .var _, .sym _, h₁, h₂ => by cases h₁
  | .sym _, .var _, .app _ _, h₁, h₂ => by rfl
  | .sym _, .sym _, .var _, h₁, h₂ => by cases h₂
  | .sym _, .sym _, .app _ _, h₁, h₂ => by rfl
  | .sym _, .app _ _, .var _, h₁, h₂ => by cases h₂
  | .sym _, .app _ _, .sym _, h₁, h₂ => by cases h₂
  | .sym _, .app _ _, .app _ _, h₁, h₂ => by rfl
  | .app _ _, .var _, .var _, h₁, h₂ => by cases h₁
  | .app _ _, .var _, .sym _, h₁, h₂ => by cases h₁
  | .app _ _, .var _, .app _ _, h₁, h₂ => by cases h₁
  | .app _ _, .sym _, .var _, h₁, h₂ => by cases h₁
  | .app _ _, .sym _, .sym _, h₁, h₂ => by cases h₁
  | .app _ _, .sym _, .app _ _, h₁, h₂ => by cases h₁
  | .app _ _, .app _ _, .var _, h₁, h₂ => by cases h₂
  | .app _ _, .app _ _, .sym _, h₁, h₂ => by cases h₂

instance : Std.TransCmp patCmp where
  eq_swap := patCmp_swap _ _
  isLE_trans := patCmp_trans

instance : Std.LawfulEqCmp patCmp where
  compare_self {a} := by
    have h := patCmp_swap a a
    cases hc : patCmp a a <;> rw [hc] at h <;> simp_all
  eq_of_compare := patCmp_eq

section List

variable {α : Type} (f : α → α → Ordering)

theorem listCmp_swap [Std.OrientedCmp f] : ∀ xs ys : List α, listCmp f xs ys = (listCmp f ys xs).swap
  | [], [] => rfl
  | [], _ :: _ => rfl
  | _ :: _, [] => rfl
  | x :: xs, y :: ys => by
    simp only [listCmp, Ordering.swap_then, ← Std.OrientedCmp.eq_swap, ← listCmp_swap xs ys]

theorem listCmp_eq [Std.LawfulEqCmp f] : ∀ {xs ys : List α}, listCmp f xs ys = .eq → xs = ys
  | [], [], _ => rfl
  | x :: xs, y :: ys, h => by
    simp only [listCmp, Ordering.then_eq_eq] at h
    rw [Std.LawfulEqCmp.eq_of_compare h.1, listCmp_eq h.2]
  | [], _ :: _, h | _ :: _, [], h => by simp [listCmp] at h

theorem listCmp_trans [Std.TransCmp f] [Std.LawfulEqCmp f] : ∀ {xs ys zs : List α},
    (listCmp f xs ys).isLE → (listCmp f ys zs).isLE → (listCmp f xs zs).isLE
  | [], [], _, _, h => h
  | [], _ :: _, [], _, h => by simp [listCmp] at h
  | [], _ :: _, _ :: _, _, _ => rfl
  | _ :: _, [], _, h, _ => by simp [listCmp] at h
  | _ :: _, _ :: _, [], _, h => by simp [listCmp] at h
  | x :: xs, y :: ys, z :: zs, h₁, h₂ => by
    simp only [listCmp] at h₁ h₂ ⊢
    exact (lin_of f x y z).then (listCmp_trans) h₁ h₂

instance listCmp_transCmp [Std.TransCmp f] [Std.LawfulEqCmp f] : Std.TransCmp (listCmp f) where
  eq_swap := listCmp_swap f _ _
  isLE_trans := listCmp_trans f

instance listCmp_lawful [Std.TransCmp f] [Std.LawfulEqCmp f] : Std.LawfulEqCmp (listCmp f) where
  compare_self {a} := by
    have h := listCmp_swap f a a
    cases hc : listCmp f a a <;> rw [hc] at h <;> simp_all
  eq_of_compare := listCmp_eq f

end List

theorem spanCmp_swap (a b : Span) : spanCmp a b = (spanCmp b a).swap := by
  simp only [spanCmp, Ordering.swap_then, ← Std.OrientedCmp.eq_swap]

theorem spanCmp_eq {a b : Span} (h : spanCmp a b = .eq) : a = b := by
  simp only [spanCmp, Ordering.then_eq_eq] at h
  obtain ⟨⟨h₁, h₂⟩, h₃⟩ := h
  cases a; cases b
  simp only at h₁ h₂ h₃
  rw [Std.LawfulEqCmp.eq_of_compare (cmp := patCmp) h₁, Std.LawfulEqCmp.eq_of_compare (cmp := patCmp) h₂,
    Std.LawfulEqCmp.eq_of_compare (cmp := listCmp patCmp) h₃]

theorem spanCmp_trans {a b c : Span} (h₁ : (spanCmp a b).isLE) (h₂ : (spanCmp b c).isLE) :
    (spanCmp a c).isLE := by
  simp only [spanCmp] at h₁ h₂ ⊢
  refine then_isLE_trans ?_ ?_ ?_ Std.TransCmp.isLE_trans h₁ h₂
  · intro e₁ e₂
    simp only [Ordering.then_eq_lt] at e₁ e₂ ⊢
    have L := lin_of patCmp a.l b.l c.l
    have R := lin_of patCmp a.r b.r c.r
    rcases e₁ with e₁ | ⟨e₁, f₁⟩ <;> rcases e₂ with e₂ | ⟨e₂, f₂⟩
    · exact .inl (L.lt_trans e₁ e₂)
    · rw [← L.eq_bc e₂]; exact .inl e₁
    · rw [L.eq_ab e₁]; exact .inl e₂
    · rw [L.eq_ab e₁, L.eq_bc e₂] at *
      exact .inr ⟨Std.ReflCmp.compare_self, R.lt_trans f₁ f₂⟩
  · intro e
    simp only [Ordering.then_eq_eq] at e
    rw [Std.LawfulEqCmp.eq_of_compare e.1, Std.LawfulEqCmp.eq_of_compare (cmp := patCmp) e.2]
  · intro e
    simp only [Ordering.then_eq_eq] at e
    rw [← Std.LawfulEqCmp.eq_of_compare e.1, ← Std.LawfulEqCmp.eq_of_compare (cmp := patCmp) e.2]

instance : Std.TransCmp spanCmp where
  eq_swap := spanCmp_swap _ _
  isLE_trans := spanCmp_trans

instance : Std.LawfulEqCmp spanCmp where
  compare_self {a} := by
    have h := spanCmp_swap a a
    cases hc : spanCmp a a <;> rw [hc] at h <;> simp_all
  eq_of_compare := spanCmp_eq

theorem relCmp_swap : ∀ a b : Rel, relCmp a b = (relCmp b a).swap
  | .zero, .span _ => rfl
  | .zero, .or _ _ => rfl
  | .zero, .and _ _ => rfl
  | .zero, .seq _ _ => rfl
  | .zero, .conv _ => rfl
  | .zero, .call _ => rfl
  | .span _, .zero => rfl
  | .span _, .or _ _ => rfl
  | .span _, .and _ _ => rfl
  | .span _, .seq _ _ => rfl
  | .span _, .conv _ => rfl
  | .span _, .call _ => rfl
  | .or _ _, .zero => rfl
  | .or _ _, .span _ => rfl
  | .or _ _, .and _ _ => rfl
  | .or _ _, .seq _ _ => rfl
  | .or _ _, .conv _ => rfl
  | .or _ _, .call _ => rfl
  | .and _ _, .zero => rfl
  | .and _ _, .span _ => rfl
  | .and _ _, .or _ _ => rfl
  | .and _ _, .seq _ _ => rfl
  | .and _ _, .conv _ => rfl
  | .and _ _, .call _ => rfl
  | .seq _ _, .zero => rfl
  | .seq _ _, .span _ => rfl
  | .seq _ _, .or _ _ => rfl
  | .seq _ _, .and _ _ => rfl
  | .seq _ _, .conv _ => rfl
  | .seq _ _, .call _ => rfl
  | .conv _, .zero => rfl
  | .conv _, .span _ => rfl
  | .conv _, .or _ _ => rfl
  | .conv _, .and _ _ => rfl
  | .conv _, .seq _ _ => rfl
  | .conv _, .call _ => rfl
  | .call _, .zero => rfl
  | .call _, .span _ => rfl
  | .call _, .or _ _ => rfl
  | .call _, .and _ _ => rfl
  | .call _, .seq _ _ => rfl
  | .call _, .conv _ => rfl
  | .zero, .zero => rfl
  | .span a, .span b => spanCmp_swap a b
  | .or a₁ a₂, .or b₁ b₂ => by
    simp only [relCmp, Ordering.swap_then, ← relCmp_swap]
  | .and a₁ a₂, .and b₁ b₂ => by
    simp only [relCmp, Ordering.swap_then, ← relCmp_swap]
  | .seq a₁ a₂, .seq b₁ b₂ => by
    simp only [relCmp, Ordering.swap_then, ← relCmp_swap]
  | .conv a, .conv b => relCmp_swap a b
  | .call a, .call b => by simp only [relCmp]; exact Std.OrientedCmp.eq_swap

theorem relCmp_eq : ∀ {a b : Rel}, relCmp a b = .eq → a = b
  | .zero, .span _, h => by cases h
  | .zero, .or _ _, h => by cases h
  | .zero, .and _ _, h => by cases h
  | .zero, .seq _ _, h => by cases h
  | .zero, .conv _, h => by cases h
  | .zero, .call _, h => by cases h
  | .span _, .zero, h => by cases h
  | .span _, .or _ _, h => by cases h
  | .span _, .and _ _, h => by cases h
  | .span _, .seq _ _, h => by cases h
  | .span _, .conv _, h => by cases h
  | .span _, .call _, h => by cases h
  | .or _ _, .zero, h => by cases h
  | .or _ _, .span _, h => by cases h
  | .or _ _, .and _ _, h => by cases h
  | .or _ _, .seq _ _, h => by cases h
  | .or _ _, .conv _, h => by cases h
  | .or _ _, .call _, h => by cases h
  | .and _ _, .zero, h => by cases h
  | .and _ _, .span _, h => by cases h
  | .and _ _, .or _ _, h => by cases h
  | .and _ _, .seq _ _, h => by cases h
  | .and _ _, .conv _, h => by cases h
  | .and _ _, .call _, h => by cases h
  | .seq _ _, .zero, h => by cases h
  | .seq _ _, .span _, h => by cases h
  | .seq _ _, .or _ _, h => by cases h
  | .seq _ _, .and _ _, h => by cases h
  | .seq _ _, .conv _, h => by cases h
  | .seq _ _, .call _, h => by cases h
  | .conv _, .zero, h => by cases h
  | .conv _, .span _, h => by cases h
  | .conv _, .or _ _, h => by cases h
  | .conv _, .and _ _, h => by cases h
  | .conv _, .seq _ _, h => by cases h
  | .conv _, .call _, h => by cases h
  | .call _, .zero, h => by cases h
  | .call _, .span _, h => by cases h
  | .call _, .or _ _, h => by cases h
  | .call _, .and _ _, h => by cases h
  | .call _, .seq _ _, h => by cases h
  | .call _, .conv _, h => by cases h
  | .zero, .zero, _ => rfl
  | .span a, .span b, h => by rw [spanCmp_eq h]
  | .or a₁ a₂, .or b₁ b₂, h => by
    simp only [relCmp, Ordering.then_eq_eq] at h
    rw [relCmp_eq h.1, relCmp_eq h.2]
  | .and a₁ a₂, .and b₁ b₂, h => by
    simp only [relCmp, Ordering.then_eq_eq] at h
    rw [relCmp_eq h.1, relCmp_eq h.2]
  | .seq a₁ a₂, .seq b₁ b₂, h => by
    simp only [relCmp, Ordering.then_eq_eq] at h
    rw [relCmp_eq h.1, relCmp_eq h.2]
  | .conv a, .conv b, h => by rw [relCmp_eq (a := a) (b := b) h]
  | .call a, .call b, h => by
    simp only [relCmp] at h; rw [Std.LawfulEqCmp.eq_of_compare h]

theorem relCmp_trans : ∀ {a b c : Rel}, (relCmp a b).isLE → (relCmp b c).isLE → (relCmp a c).isLE
  | .zero, .zero, .span _, h₁, h₂ => by rfl
  | .zero, .zero, .or _ _, h₁, h₂ => by rfl
  | .zero, .zero, .and _ _, h₁, h₂ => by rfl
  | .zero, .zero, .seq _ _, h₁, h₂ => by rfl
  | .zero, .zero, .conv _, h₁, h₂ => by rfl
  | .zero, .zero, .call _, h₁, h₂ => by rfl
  | .zero, .span _, .zero, h₁, h₂ => by cases h₂
  | .zero, .span _, .span _, h₁, h₂ => by rfl
  | .zero, .span _, .or _ _, h₁, h₂ => by rfl
  | .zero, .span _, .and _ _, h₁, h₂ => by rfl
  | .zero, .span _, .seq _ _, h₁, h₂ => by rfl
  | .zero, .span _, .conv _, h₁, h₂ => by rfl
  | .zero, .span _, .call _, h₁, h₂ => by rfl
  | .zero, .or _ _, .zero, h₁, h₂ => by cases h₂
  | .zero, .or _ _, .span _, h₁, h₂ => by rfl
  | .zero, .or _ _, .or _ _, h₁, h₂ => by rfl
  | .zero, .or _ _, .and _ _, h₁, h₂ => by rfl
  | .zero, .or _ _, .seq _ _, h₁, h₂ => by rfl
  | .zero, .or _ _, .conv _, h₁, h₂ => by rfl
  | .zero, .or _ _, .call _, h₁, h₂ => by rfl
  | .zero, .and _ _, .zero, h₁, h₂ => by cases h₂
  | .zero, .and _ _, .span _, h₁, h₂ => by rfl
  | .zero, .and _ _, .or _ _, h₁, h₂ => by rfl
  | .zero, .and _ _, .and _ _, h₁, h₂ => by rfl
  | .zero, .and _ _, .seq _ _, h₁, h₂ => by rfl
  | .zero, .and _ _, .conv _, h₁, h₂ => by rfl
  | .zero, .and _ _, .call _, h₁, h₂ => by rfl
  | .zero, .seq _ _, .zero, h₁, h₂ => by cases h₂
  | .zero, .seq _ _, .span _, h₁, h₂ => by rfl
  | .zero, .seq _ _, .or _ _, h₁, h₂ => by rfl
  | .zero, .seq _ _, .and _ _, h₁, h₂ => by rfl
  | .zero, .seq _ _, .seq _ _, h₁, h₂ => by rfl
  | .zero, .seq _ _, .conv _, h₁, h₂ => by rfl
  | .zero, .seq _ _, .call _, h₁, h₂ => by rfl
  | .zero, .conv _, .zero, h₁, h₂ => by cases h₂
  | .zero, .conv _, .span _, h₁, h₂ => by rfl
  | .zero, .conv _, .or _ _, h₁, h₂ => by rfl
  | .zero, .conv _, .and _ _, h₁, h₂ => by rfl
  | .zero, .conv _, .seq _ _, h₁, h₂ => by rfl
  | .zero, .conv _, .conv _, h₁, h₂ => by rfl
  | .zero, .conv _, .call _, h₁, h₂ => by rfl
  | .zero, .call _, .zero, h₁, h₂ => by cases h₂
  | .zero, .call _, .span _, h₁, h₂ => by rfl
  | .zero, .call _, .or _ _, h₁, h₂ => by rfl
  | .zero, .call _, .and _ _, h₁, h₂ => by rfl
  | .zero, .call _, .seq _ _, h₁, h₂ => by rfl
  | .zero, .call _, .conv _, h₁, h₂ => by rfl
  | .zero, .call _, .call _, h₁, h₂ => by rfl
  | .span _, .zero, .zero, h₁, h₂ => by cases h₁
  | .span _, .zero, .span _, h₁, h₂ => by cases h₁
  | .span _, .zero, .or _ _, h₁, h₂ => by rfl
  | .span _, .zero, .and _ _, h₁, h₂ => by rfl
  | .span _, .zero, .seq _ _, h₁, h₂ => by rfl
  | .span _, .zero, .conv _, h₁, h₂ => by rfl
  | .span _, .zero, .call _, h₁, h₂ => by rfl
  | .span _, .span _, .zero, h₁, h₂ => by cases h₂
  | .span _, .span _, .or _ _, h₁, h₂ => by rfl
  | .span _, .span _, .and _ _, h₁, h₂ => by rfl
  | .span _, .span _, .seq _ _, h₁, h₂ => by rfl
  | .span _, .span _, .conv _, h₁, h₂ => by rfl
  | .span _, .span _, .call _, h₁, h₂ => by rfl
  | .span _, .or _ _, .zero, h₁, h₂ => by cases h₂
  | .span _, .or _ _, .span _, h₁, h₂ => by cases h₂
  | .span _, .or _ _, .or _ _, h₁, h₂ => by rfl
  | .span _, .or _ _, .and _ _, h₁, h₂ => by rfl
  | .span _, .or _ _, .seq _ _, h₁, h₂ => by rfl
  | .span _, .or _ _, .conv _, h₁, h₂ => by rfl
  | .span _, .or _ _, .call _, h₁, h₂ => by rfl
  | .span _, .and _ _, .zero, h₁, h₂ => by cases h₂
  | .span _, .and _ _, .span _, h₁, h₂ => by cases h₂
  | .span _, .and _ _, .or _ _, h₁, h₂ => by rfl
  | .span _, .and _ _, .and _ _, h₁, h₂ => by rfl
  | .span _, .and _ _, .seq _ _, h₁, h₂ => by rfl
  | .span _, .and _ _, .conv _, h₁, h₂ => by rfl
  | .span _, .and _ _, .call _, h₁, h₂ => by rfl
  | .span _, .seq _ _, .zero, h₁, h₂ => by cases h₂
  | .span _, .seq _ _, .span _, h₁, h₂ => by cases h₂
  | .span _, .seq _ _, .or _ _, h₁, h₂ => by rfl
  | .span _, .seq _ _, .and _ _, h₁, h₂ => by rfl
  | .span _, .seq _ _, .seq _ _, h₁, h₂ => by rfl
  | .span _, .seq _ _, .conv _, h₁, h₂ => by rfl
  | .span _, .seq _ _, .call _, h₁, h₂ => by rfl
  | .span _, .conv _, .zero, h₁, h₂ => by cases h₂
  | .span _, .conv _, .span _, h₁, h₂ => by cases h₂
  | .span _, .conv _, .or _ _, h₁, h₂ => by rfl
  | .span _, .conv _, .and _ _, h₁, h₂ => by rfl
  | .span _, .conv _, .seq _ _, h₁, h₂ => by rfl
  | .span _, .conv _, .conv _, h₁, h₂ => by rfl
  | .span _, .conv _, .call _, h₁, h₂ => by rfl
  | .span _, .call _, .zero, h₁, h₂ => by cases h₂
  | .span _, .call _, .span _, h₁, h₂ => by cases h₂
  | .span _, .call _, .or _ _, h₁, h₂ => by rfl
  | .span _, .call _, .and _ _, h₁, h₂ => by rfl
  | .span _, .call _, .seq _ _, h₁, h₂ => by rfl
  | .span _, .call _, .conv _, h₁, h₂ => by rfl
  | .span _, .call _, .call _, h₁, h₂ => by rfl
  | .or _ _, .zero, .zero, h₁, h₂ => by cases h₁
  | .or _ _, .zero, .span _, h₁, h₂ => by cases h₁
  | .or _ _, .zero, .or _ _, h₁, h₂ => by cases h₁
  | .or _ _, .zero, .and _ _, h₁, h₂ => by rfl
  | .or _ _, .zero, .seq _ _, h₁, h₂ => by rfl
  | .or _ _, .zero, .conv _, h₁, h₂ => by rfl
  | .or _ _, .zero, .call _, h₁, h₂ => by rfl
  | .or _ _, .span _, .zero, h₁, h₂ => by cases h₁
  | .or _ _, .span _, .span _, h₁, h₂ => by cases h₁
  | .or _ _, .span _, .or _ _, h₁, h₂ => by cases h₁
  | .or _ _, .span _, .and _ _, h₁, h₂ => by rfl
  | .or _ _, .span _, .seq _ _, h₁, h₂ => by rfl
  | .or _ _, .span _, .conv _, h₁, h₂ => by rfl
  | .or _ _, .span _, .call _, h₁, h₂ => by rfl
  | .or _ _, .or _ _, .zero, h₁, h₂ => by cases h₂
  | .or _ _, .or _ _, .span _, h₁, h₂ => by cases h₂
  | .or _ _, .or _ _, .and _ _, h₁, h₂ => by rfl
  | .or _ _, .or _ _, .seq _ _, h₁, h₂ => by rfl
  | .or _ _, .or _ _, .conv _, h₁, h₂ => by rfl
  | .or _ _, .or _ _, .call _, h₁, h₂ => by rfl
  | .or _ _, .and _ _, .zero, h₁, h₂ => by cases h₂
  | .or _ _, .and _ _, .span _, h₁, h₂ => by cases h₂
  | .or _ _, .and _ _, .or _ _, h₁, h₂ => by cases h₂
  | .or _ _, .and _ _, .and _ _, h₁, h₂ => by rfl
  | .or _ _, .and _ _, .seq _ _, h₁, h₂ => by rfl
  | .or _ _, .and _ _, .conv _, h₁, h₂ => by rfl
  | .or _ _, .and _ _, .call _, h₁, h₂ => by rfl
  | .or _ _, .seq _ _, .zero, h₁, h₂ => by cases h₂
  | .or _ _, .seq _ _, .span _, h₁, h₂ => by cases h₂
  | .or _ _, .seq _ _, .or _ _, h₁, h₂ => by cases h₂
  | .or _ _, .seq _ _, .and _ _, h₁, h₂ => by rfl
  | .or _ _, .seq _ _, .seq _ _, h₁, h₂ => by rfl
  | .or _ _, .seq _ _, .conv _, h₁, h₂ => by rfl
  | .or _ _, .seq _ _, .call _, h₁, h₂ => by rfl
  | .or _ _, .conv _, .zero, h₁, h₂ => by cases h₂
  | .or _ _, .conv _, .span _, h₁, h₂ => by cases h₂
  | .or _ _, .conv _, .or _ _, h₁, h₂ => by cases h₂
  | .or _ _, .conv _, .and _ _, h₁, h₂ => by rfl
  | .or _ _, .conv _, .seq _ _, h₁, h₂ => by rfl
  | .or _ _, .conv _, .conv _, h₁, h₂ => by rfl
  | .or _ _, .conv _, .call _, h₁, h₂ => by rfl
  | .or _ _, .call _, .zero, h₁, h₂ => by cases h₂
  | .or _ _, .call _, .span _, h₁, h₂ => by cases h₂
  | .or _ _, .call _, .or _ _, h₁, h₂ => by cases h₂
  | .or _ _, .call _, .and _ _, h₁, h₂ => by rfl
  | .or _ _, .call _, .seq _ _, h₁, h₂ => by rfl
  | .or _ _, .call _, .conv _, h₁, h₂ => by rfl
  | .or _ _, .call _, .call _, h₁, h₂ => by rfl
  | .and _ _, .zero, .zero, h₁, h₂ => by cases h₁
  | .and _ _, .zero, .span _, h₁, h₂ => by cases h₁
  | .and _ _, .zero, .or _ _, h₁, h₂ => by cases h₁
  | .and _ _, .zero, .and _ _, h₁, h₂ => by cases h₁
  | .and _ _, .zero, .seq _ _, h₁, h₂ => by rfl
  | .and _ _, .zero, .conv _, h₁, h₂ => by rfl
  | .and _ _, .zero, .call _, h₁, h₂ => by rfl
  | .and _ _, .span _, .zero, h₁, h₂ => by cases h₁
  | .and _ _, .span _, .span _, h₁, h₂ => by cases h₁
  | .and _ _, .span _, .or _ _, h₁, h₂ => by cases h₁
  | .and _ _, .span _, .and _ _, h₁, h₂ => by cases h₁
  | .and _ _, .span _, .seq _ _, h₁, h₂ => by rfl
  | .and _ _, .span _, .conv _, h₁, h₂ => by rfl
  | .and _ _, .span _, .call _, h₁, h₂ => by rfl
  | .and _ _, .or _ _, .zero, h₁, h₂ => by cases h₁
  | .and _ _, .or _ _, .span _, h₁, h₂ => by cases h₁
  | .and _ _, .or _ _, .or _ _, h₁, h₂ => by cases h₁
  | .and _ _, .or _ _, .and _ _, h₁, h₂ => by cases h₁
  | .and _ _, .or _ _, .seq _ _, h₁, h₂ => by rfl
  | .and _ _, .or _ _, .conv _, h₁, h₂ => by rfl
  | .and _ _, .or _ _, .call _, h₁, h₂ => by rfl
  | .and _ _, .and _ _, .zero, h₁, h₂ => by cases h₂
  | .and _ _, .and _ _, .span _, h₁, h₂ => by cases h₂
  | .and _ _, .and _ _, .or _ _, h₁, h₂ => by cases h₂
  | .and _ _, .and _ _, .seq _ _, h₁, h₂ => by rfl
  | .and _ _, .and _ _, .conv _, h₁, h₂ => by rfl
  | .and _ _, .and _ _, .call _, h₁, h₂ => by rfl
  | .and _ _, .seq _ _, .zero, h₁, h₂ => by cases h₂
  | .and _ _, .seq _ _, .span _, h₁, h₂ => by cases h₂
  | .and _ _, .seq _ _, .or _ _, h₁, h₂ => by cases h₂
  | .and _ _, .seq _ _, .and _ _, h₁, h₂ => by cases h₂
  | .and _ _, .seq _ _, .seq _ _, h₁, h₂ => by rfl
  | .and _ _, .seq _ _, .conv _, h₁, h₂ => by rfl
  | .and _ _, .seq _ _, .call _, h₁, h₂ => by rfl
  | .and _ _, .conv _, .zero, h₁, h₂ => by cases h₂
  | .and _ _, .conv _, .span _, h₁, h₂ => by cases h₂
  | .and _ _, .conv _, .or _ _, h₁, h₂ => by cases h₂
  | .and _ _, .conv _, .and _ _, h₁, h₂ => by cases h₂
  | .and _ _, .conv _, .seq _ _, h₁, h₂ => by rfl
  | .and _ _, .conv _, .conv _, h₁, h₂ => by rfl
  | .and _ _, .conv _, .call _, h₁, h₂ => by rfl
  | .and _ _, .call _, .zero, h₁, h₂ => by cases h₂
  | .and _ _, .call _, .span _, h₁, h₂ => by cases h₂
  | .and _ _, .call _, .or _ _, h₁, h₂ => by cases h₂
  | .and _ _, .call _, .and _ _, h₁, h₂ => by cases h₂
  | .and _ _, .call _, .seq _ _, h₁, h₂ => by rfl
  | .and _ _, .call _, .conv _, h₁, h₂ => by rfl
  | .and _ _, .call _, .call _, h₁, h₂ => by rfl
  | .seq _ _, .zero, .zero, h₁, h₂ => by cases h₁
  | .seq _ _, .zero, .span _, h₁, h₂ => by cases h₁
  | .seq _ _, .zero, .or _ _, h₁, h₂ => by cases h₁
  | .seq _ _, .zero, .and _ _, h₁, h₂ => by cases h₁
  | .seq _ _, .zero, .seq _ _, h₁, h₂ => by cases h₁
  | .seq _ _, .zero, .conv _, h₁, h₂ => by rfl
  | .seq _ _, .zero, .call _, h₁, h₂ => by rfl
  | .seq _ _, .span _, .zero, h₁, h₂ => by cases h₁
  | .seq _ _, .span _, .span _, h₁, h₂ => by cases h₁
  | .seq _ _, .span _, .or _ _, h₁, h₂ => by cases h₁
  | .seq _ _, .span _, .and _ _, h₁, h₂ => by cases h₁
  | .seq _ _, .span _, .seq _ _, h₁, h₂ => by cases h₁
  | .seq _ _, .span _, .conv _, h₁, h₂ => by rfl
  | .seq _ _, .span _, .call _, h₁, h₂ => by rfl
  | .seq _ _, .or _ _, .zero, h₁, h₂ => by cases h₁
  | .seq _ _, .or _ _, .span _, h₁, h₂ => by cases h₁
  | .seq _ _, .or _ _, .or _ _, h₁, h₂ => by cases h₁
  | .seq _ _, .or _ _, .and _ _, h₁, h₂ => by cases h₁
  | .seq _ _, .or _ _, .seq _ _, h₁, h₂ => by cases h₁
  | .seq _ _, .or _ _, .conv _, h₁, h₂ => by rfl
  | .seq _ _, .or _ _, .call _, h₁, h₂ => by rfl
  | .seq _ _, .and _ _, .zero, h₁, h₂ => by cases h₁
  | .seq _ _, .and _ _, .span _, h₁, h₂ => by cases h₁
  | .seq _ _, .and _ _, .or _ _, h₁, h₂ => by cases h₁
  | .seq _ _, .and _ _, .and _ _, h₁, h₂ => by cases h₁
  | .seq _ _, .and _ _, .seq _ _, h₁, h₂ => by cases h₁
  | .seq _ _, .and _ _, .conv _, h₁, h₂ => by rfl
  | .seq _ _, .and _ _, .call _, h₁, h₂ => by rfl
  | .seq _ _, .seq _ _, .zero, h₁, h₂ => by cases h₂
  | .seq _ _, .seq _ _, .span _, h₁, h₂ => by cases h₂
  | .seq _ _, .seq _ _, .or _ _, h₁, h₂ => by cases h₂
  | .seq _ _, .seq _ _, .and _ _, h₁, h₂ => by cases h₂
  | .seq _ _, .seq _ _, .conv _, h₁, h₂ => by rfl
  | .seq _ _, .seq _ _, .call _, h₁, h₂ => by rfl
  | .seq _ _, .conv _, .zero, h₁, h₂ => by cases h₂
  | .seq _ _, .conv _, .span _, h₁, h₂ => by cases h₂
  | .seq _ _, .conv _, .or _ _, h₁, h₂ => by cases h₂
  | .seq _ _, .conv _, .and _ _, h₁, h₂ => by cases h₂
  | .seq _ _, .conv _, .seq _ _, h₁, h₂ => by cases h₂
  | .seq _ _, .conv _, .conv _, h₁, h₂ => by rfl
  | .seq _ _, .conv _, .call _, h₁, h₂ => by rfl
  | .seq _ _, .call _, .zero, h₁, h₂ => by cases h₂
  | .seq _ _, .call _, .span _, h₁, h₂ => by cases h₂
  | .seq _ _, .call _, .or _ _, h₁, h₂ => by cases h₂
  | .seq _ _, .call _, .and _ _, h₁, h₂ => by cases h₂
  | .seq _ _, .call _, .seq _ _, h₁, h₂ => by cases h₂
  | .seq _ _, .call _, .conv _, h₁, h₂ => by rfl
  | .seq _ _, .call _, .call _, h₁, h₂ => by rfl
  | .conv _, .zero, .zero, h₁, h₂ => by cases h₁
  | .conv _, .zero, .span _, h₁, h₂ => by cases h₁
  | .conv _, .zero, .or _ _, h₁, h₂ => by cases h₁
  | .conv _, .zero, .and _ _, h₁, h₂ => by cases h₁
  | .conv _, .zero, .seq _ _, h₁, h₂ => by cases h₁
  | .conv _, .zero, .conv _, h₁, h₂ => by cases h₁
  | .conv _, .zero, .call _, h₁, h₂ => by rfl
  | .conv _, .span _, .zero, h₁, h₂ => by cases h₁
  | .conv _, .span _, .span _, h₁, h₂ => by cases h₁
  | .conv _, .span _, .or _ _, h₁, h₂ => by cases h₁
  | .conv _, .span _, .and _ _, h₁, h₂ => by cases h₁
  | .conv _, .span _, .seq _ _, h₁, h₂ => by cases h₁
  | .conv _, .span _, .conv _, h₁, h₂ => by cases h₁
  | .conv _, .span _, .call _, h₁, h₂ => by rfl
  | .conv _, .or _ _, .zero, h₁, h₂ => by cases h₁
  | .conv _, .or _ _, .span _, h₁, h₂ => by cases h₁
  | .conv _, .or _ _, .or _ _, h₁, h₂ => by cases h₁
  | .conv _, .or _ _, .and _ _, h₁, h₂ => by cases h₁
  | .conv _, .or _ _, .seq _ _, h₁, h₂ => by cases h₁
  | .conv _, .or _ _, .conv _, h₁, h₂ => by cases h₁
  | .conv _, .or _ _, .call _, h₁, h₂ => by rfl
  | .conv _, .and _ _, .zero, h₁, h₂ => by cases h₁
  | .conv _, .and _ _, .span _, h₁, h₂ => by cases h₁
  | .conv _, .and _ _, .or _ _, h₁, h₂ => by cases h₁
  | .conv _, .and _ _, .and _ _, h₁, h₂ => by cases h₁
  | .conv _, .and _ _, .seq _ _, h₁, h₂ => by cases h₁
  | .conv _, .and _ _, .conv _, h₁, h₂ => by cases h₁
  | .conv _, .and _ _, .call _, h₁, h₂ => by rfl
  | .conv _, .seq _ _, .zero, h₁, h₂ => by cases h₁
  | .conv _, .seq _ _, .span _, h₁, h₂ => by cases h₁
  | .conv _, .seq _ _, .or _ _, h₁, h₂ => by cases h₁
  | .conv _, .seq _ _, .and _ _, h₁, h₂ => by cases h₁
  | .conv _, .seq _ _, .seq _ _, h₁, h₂ => by cases h₁
  | .conv _, .seq _ _, .conv _, h₁, h₂ => by cases h₁
  | .conv _, .seq _ _, .call _, h₁, h₂ => by rfl
  | .conv _, .conv _, .zero, h₁, h₂ => by cases h₂
  | .conv _, .conv _, .span _, h₁, h₂ => by cases h₂
  | .conv _, .conv _, .or _ _, h₁, h₂ => by cases h₂
  | .conv _, .conv _, .and _ _, h₁, h₂ => by cases h₂
  | .conv _, .conv _, .seq _ _, h₁, h₂ => by cases h₂
  | .conv _, .conv _, .call _, h₁, h₂ => by rfl
  | .conv _, .call _, .zero, h₁, h₂ => by cases h₂
  | .conv _, .call _, .span _, h₁, h₂ => by cases h₂
  | .conv _, .call _, .or _ _, h₁, h₂ => by cases h₂
  | .conv _, .call _, .and _ _, h₁, h₂ => by cases h₂
  | .conv _, .call _, .seq _ _, h₁, h₂ => by cases h₂
  | .conv _, .call _, .conv _, h₁, h₂ => by cases h₂
  | .conv _, .call _, .call _, h₁, h₂ => by rfl
  | .call _, .zero, .zero, h₁, h₂ => by cases h₁
  | .call _, .zero, .span _, h₁, h₂ => by cases h₁
  | .call _, .zero, .or _ _, h₁, h₂ => by cases h₁
  | .call _, .zero, .and _ _, h₁, h₂ => by cases h₁
  | .call _, .zero, .seq _ _, h₁, h₂ => by cases h₁
  | .call _, .zero, .conv _, h₁, h₂ => by cases h₁
  | .call _, .zero, .call _, h₁, h₂ => by cases h₁
  | .call _, .span _, .zero, h₁, h₂ => by cases h₁
  | .call _, .span _, .span _, h₁, h₂ => by cases h₁
  | .call _, .span _, .or _ _, h₁, h₂ => by cases h₁
  | .call _, .span _, .and _ _, h₁, h₂ => by cases h₁
  | .call _, .span _, .seq _ _, h₁, h₂ => by cases h₁
  | .call _, .span _, .conv _, h₁, h₂ => by cases h₁
  | .call _, .span _, .call _, h₁, h₂ => by cases h₁
  | .call _, .or _ _, .zero, h₁, h₂ => by cases h₁
  | .call _, .or _ _, .span _, h₁, h₂ => by cases h₁
  | .call _, .or _ _, .or _ _, h₁, h₂ => by cases h₁
  | .call _, .or _ _, .and _ _, h₁, h₂ => by cases h₁
  | .call _, .or _ _, .seq _ _, h₁, h₂ => by cases h₁
  | .call _, .or _ _, .conv _, h₁, h₂ => by cases h₁
  | .call _, .or _ _, .call _, h₁, h₂ => by cases h₁
  | .call _, .and _ _, .zero, h₁, h₂ => by cases h₁
  | .call _, .and _ _, .span _, h₁, h₂ => by cases h₁
  | .call _, .and _ _, .or _ _, h₁, h₂ => by cases h₁
  | .call _, .and _ _, .and _ _, h₁, h₂ => by cases h₁
  | .call _, .and _ _, .seq _ _, h₁, h₂ => by cases h₁
  | .call _, .and _ _, .conv _, h₁, h₂ => by cases h₁
  | .call _, .and _ _, .call _, h₁, h₂ => by cases h₁
  | .call _, .seq _ _, .zero, h₁, h₂ => by cases h₁
  | .call _, .seq _ _, .span _, h₁, h₂ => by cases h₁
  | .call _, .seq _ _, .or _ _, h₁, h₂ => by cases h₁
  | .call _, .seq _ _, .and _ _, h₁, h₂ => by cases h₁
  | .call _, .seq _ _, .seq _ _, h₁, h₂ => by cases h₁
  | .call _, .seq _ _, .conv _, h₁, h₂ => by cases h₁
  | .call _, .seq _ _, .call _, h₁, h₂ => by cases h₁
  | .call _, .conv _, .zero, h₁, h₂ => by cases h₁
  | .call _, .conv _, .span _, h₁, h₂ => by cases h₁
  | .call _, .conv _, .or _ _, h₁, h₂ => by cases h₁
  | .call _, .conv _, .and _ _, h₁, h₂ => by cases h₁
  | .call _, .conv _, .seq _ _, h₁, h₂ => by cases h₁
  | .call _, .conv _, .conv _, h₁, h₂ => by cases h₁
  | .call _, .conv _, .call _, h₁, h₂ => by cases h₁
  | .call _, .call _, .zero, h₁, h₂ => by cases h₂
  | .call _, .call _, .span _, h₁, h₂ => by cases h₂
  | .call _, .call _, .or _ _, h₁, h₂ => by cases h₂
  | .call _, .call _, .and _ _, h₁, h₂ => by cases h₂
  | .call _, .call _, .seq _ _, h₁, h₂ => by cases h₂
  | .call _, .call _, .conv _, h₁, h₂ => by cases h₂
  | .zero, .zero, .zero, _, _ => rfl
  | .span a, .span b, .span c, h₁, h₂ => spanCmp_trans h₁ h₂
  | .or a₁ a₂, .or b₁ b₂, .or c₁ c₂, h₁, h₂ => by
    simp only [relCmp] at h₁ h₂ ⊢
    exact (⟨relCmp_swap _ _, relCmp_eq, relCmp_eq, relCmp_eq, relCmp_trans⟩ :
      Lin relCmp a₁ b₁ c₁).then relCmp_trans h₁ h₂
  | .and a₁ a₂, .and b₁ b₂, .and c₁ c₂, h₁, h₂ => by
    simp only [relCmp] at h₁ h₂ ⊢
    exact (⟨relCmp_swap _ _, relCmp_eq, relCmp_eq, relCmp_eq, relCmp_trans⟩ :
      Lin relCmp a₁ b₁ c₁).then relCmp_trans h₁ h₂
  | .seq a₁ a₂, .seq b₁ b₂, .seq c₁ c₂, h₁, h₂ => by
    simp only [relCmp] at h₁ h₂ ⊢
    exact (⟨relCmp_swap _ _, relCmp_eq, relCmp_eq, relCmp_eq, relCmp_trans⟩ :
      Lin relCmp a₁ b₁ c₁).then relCmp_trans h₁ h₂
  | .conv a, .conv b, .conv c, h₁, h₂ => relCmp_trans (a := a) (b := b) (c := c) h₁ h₂
  | .call a, .call b, .call c, h₁, h₂ => by
    simp only [relCmp] at h₁ h₂ ⊢; exact Std.TransCmp.isLE_trans h₁ h₂

instance : Std.TransCmp relCmp where
  eq_swap := relCmp_swap _ _
  isLE_trans := relCmp_trans

instance : Std.LawfulEqCmp relCmp where
  compare_self {a} := by
    have h := relCmp_swap a a
    cases hc : relCmp a a <;> rw [hc] at h <;> simp_all
  eq_of_compare := relCmp_eq

end Order

/-! ## The canonical form forgets the order and grouping of `|` -/

section Canon

theorem pairwise_eraseDups {α : Type} [BEq α] [LawfulBEq α] {R : α → α → Prop} :
    ∀ (n : Nat) (l : List α), l.length ≤ n → l.Pairwise R →
      l.eraseDups.Pairwise (fun a b => R a b ∧ a ≠ b)
  | _, [], _, _ => by simp
  | n + 1, a :: as, hn, h => by
    rw [List.eraseDups_cons, List.pairwise_cons]
    rw [List.pairwise_cons] at h
    refine ⟨fun b hb => ?_, pairwise_eraseDups n _ ?_ (h.2.filter _)⟩
    · rw [List.mem_eraseDups, List.mem_filter] at hb
      refine ⟨h.1 b hb.1, fun e => ?_⟩
      subst e; simp at hb
    · exact (List.length_filter_le _ _).trans (by simp at hn; omega)
  | 0, _ :: _, hn, _ => by simp at hn

/-- `relCmp` as a Boolean `≤`. -/
theorem relLE_iff (a b : Rel) : (relCmp a b != .gt) = (relCmp a b).isLE := by
  cases relCmp a b <;> rfl

theorem mem_sortedBranches {xs : List Rel} {z : Rel} :
    z ∈ sortedBranches xs ↔ z ∈ xs ∧ z ≠ .zero := by
  simp [sortedBranches, List.mem_eraseDups, List.mem_mergeSort, List.mem_filter]

theorem pairwise_sortedBranches (xs : List Rel) :
    (sortedBranches xs).Pairwise fun a b => (relCmp a b != .gt) = true ∧ a ≠ b := by
  unfold sortedBranches
  refine pairwise_eraseDups _ _ le_rfl (List.pairwise_mergeSort ?_ ?_ _)
  · intro a b c h₁ h₂
    rw [relLE_iff] at h₁ h₂ ⊢
    exact relCmp_trans h₁ h₂
  · intro a b
    rw [relLE_iff, relLE_iff, relCmp_swap b a]
    cases relCmp a b <;> rfl

/-- `sortedBranches` depends only on which non-`0` branches occur. -/
theorem sortedBranches_eq {xs ys : List Rel} (h : ∀ z, z ≠ .zero → (z ∈ xs ↔ z ∈ ys)) :
    sortedBranches xs = sortedBranches ys := by
  have hx := pairwise_sortedBranches xs
  have hy := pairwise_sortedBranches ys
  refine List.Perm.eq_of_pairwise (le := fun a b => (relCmp a b != .gt) = true)
    (fun a b _ _ h₁ h₂ => ?_) (hx.imp fun h => h.1) (hy.imp fun h => h.1) ?_
  · rw [relLE_iff] at h₁ h₂
    rw [relCmp_swap] at h₁
    cases hc : relCmp b a with
    | eq => exact (relCmp_eq hc).symm
    | lt => rw [hc] at h₁; cases h₁
    | gt => rw [hc] at h₂; cases h₂
  · refine (List.perm_ext_iff_of_nodup (hx.imp fun h => h.2) (hy.imp fun h => h.2)).2 fun z => ?_
    rw [mem_sortedBranches, mem_sortedBranches]
    constructor
    · rintro ⟨hz, h0⟩; exact ⟨(h z h0).1 hz, h0⟩
    · rintro ⟨hz, h0⟩; exact ⟨(h z h0).2 hz, h0⟩

/-- Not a `|`. -/
def NotOr (e : Rel) : Prop := ∀ a b, e ≠ .or a b

theorem notOr_of_mem_orBranches : ∀ {e x : Rel}, x ∈ orBranches e → NotOr x
  | .or a b, x, h => by
    rw [orBranches, List.mem_append] at h
    exact h.elim notOr_of_mem_orBranches notOr_of_mem_orBranches
  | .zero, x, h | .span _, x, h | .and _ _, x, h | .seq _ _, x, h | .conv _, x, h | .call _, x, h => by
    simp only [orBranches, List.mem_singleton] at h; subst h; intro a b h; cases h

theorem orBranches_notOr {e : Rel} (h : NotOr e) : orBranches e = [e] := by
  cases e with
  | or a b => exact absurd rfl (h a b)
  | _ => rfl

theorem mem_orBranches_mkOr : ∀ {L : List Rel}, (∀ x ∈ L, NotOr x) →
    ∀ z, z ≠ .zero → (z ∈ orBranches (mkOr L) ↔ z ∈ L)
  | [], _, z, hz => by simp [mkOr, orBranches, hz]
  | [e], hL, z, _ => by
    rw [mkOr, orBranches_notOr (hL e (by simp))]
  | e :: e' :: es, hL, z, hz => by
    rw [show mkOr (e :: e' :: es) = .or e (mkOr (e' :: es)) from rfl, orBranches,
      orBranches_notOr (hL e (by simp)), List.mem_append,
      mem_orBranches_mkOr (fun x hx => hL x (List.mem_cons_of_mem _ hx)) z hz]
    simp

/-- The non-`0` branches of a canonical `|`. -/
theorem mem_orBranches_canon_or {a b : Rel} {z : Rel} (hz : z ≠ .zero) :
    z ∈ orBranches (canon (.or a b)) ↔ z ∈ orBranches (canon a) ∨ z ∈ orBranches (canon b) := by
  rw [canon, mem_orBranches_mkOr (fun x hx => ?_) z hz, mem_sortedBranches, List.mem_append]
  · simp [hz]
  · rw [mem_sortedBranches, List.mem_append] at hx
    exact hx.1.elim notOr_of_mem_orBranches notOr_of_mem_orBranches

theorem canon_or_comm (a b : Rel) : canon (.or a b) = canon (.or b a) := by
  simp only [canon]
  congr 1
  exact sortedBranches_eq fun z _ => by simp only [List.mem_append]; exact or_comm

theorem canon_or_assoc (a b c : Rel) : canon (.or (.or a b) c) = canon (.or a (.or b c)) := by
  conv => lhs; rw [canon]
  conv => rhs; rw [canon]
  congr 1
  refine sortedBranches_eq fun z hz => ?_
  simp only [List.mem_append, mem_orBranches_canon_or hz]
  exact or_assoc

end Canon

theorem or_comm_trace : Obligation.or_comm_trace := by
  intro P a b n
  show runtime.trace (State.ofGoal P ⟨none, .or a b, none⟩) n =
    runtime.trace (State.ofGoal P ⟨none, .or b a, none⟩) n
  simp only [State.ofGoal, Goal.norm, canon_or_comm a b]

theorem or_assoc : Obligation.or_assoc := by
  intro P a b c n
  show runtime.trace (State.ofGoal P ⟨none, .or (.or a b) c, none⟩) n =
    runtime.trace (State.ofGoal P ⟨none, .or a (.or b c), none⟩) n
  simp only [State.ofGoal, Goal.norm, canon_or_assoc a b c]

end R001

end RwLog
