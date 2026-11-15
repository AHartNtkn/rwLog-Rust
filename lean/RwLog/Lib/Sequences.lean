/-
# Sequences that cannot go on for ever

Facts about a sequence indexed by the natural numbers, each a way to say
that something happens only finitely often:

* a sequence of numbers that never rises is constant from some point
  (`eventually_const`);
* a sequence that never rises in a well-founded order does not fall
  infinitely often (`no_descent`);
* what happens infinitely often at one of finitely many places happens
  infinitely often at one of them (`infinitely_often_fin`);
* what holds from some point on at each of finitely many places holds at
  all of them from some point on (`eventually_forall_lt`,
  `eventually_forall_mem`).
-/
import Mathlib.Data.List.Basic

namespace RwLog

/-- A sequence of numbers that never rises from `a` on is constant from some
point on. -/
theorem eventually_const (f : Nat → Nat) (a : Nat) (h : ∀ r, a ≤ r → f (r + 1) ≤ f r) :
    ∃ r0, a ≤ r0 ∧ ∀ r, r0 ≤ r → f r = f r0 := by
  have mono : ∀ a', a ≤ a' → ∀ r, a' ≤ r → f r ≤ f a' := by
    intro a' ha' r hr
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hr
    induction d with
    | zero => exact Nat.le_refl _
    | succ d ih =>
      exact Nat.le_trans (h (a' + d) (by omega)) (ih (by omega))
  have key : ∀ v a', a ≤ a' → f a' = v → ∃ r0, a ≤ r0 ∧ ∀ r, r0 ≤ r → f r = f r0 := by
    intro v
    induction v using Nat.strongRecOn with
    | _ v ih =>
      intro a' ha' hv
      by_cases hc : ∀ r, a' ≤ r → f r = f a'
      · exact ⟨a', ha', hc⟩
      · obtain ⟨r, hc'⟩ := Classical.not_forall.1 hc
        obtain ⟨hr, hne⟩ := Classical.not_imp.1 hc'
        have hle := mono a' ha' r hr
        exact ih (f r) (by omega) r (Nat.le_trans ha' hr) rfl
  exact key (f a) a (Nat.le_refl _) rfl

/-- A sequence that from `a` on stays or falls in a well-founded order does
not fall infinitely often. -/
theorem no_descent {α : Type} (lt : α → α → Prop) (wf : WellFounded lt)
    (tr : ∀ x y z, lt x y → lt y z → lt x z) (f : Nat → α) (a : Nat)
    (hstep : ∀ r, a ≤ r → f (r + 1) = f r ∨ lt (f (r + 1)) (f r))
    (hinf : ∀ r', ∃ r, r' ≤ r ∧ lt (f (r + 1)) (f r)) : False := by
  have mono : ∀ a', a ≤ a' → ∀ r, a' ≤ r → f r = f a' ∨ lt (f r) (f a') := by
    intro a' ha' r hr
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hr
    induction d with
    | zero => exact .inl rfl
    | succ d ih =>
      rcases hstep (a' + d) (by omega) with e | l
      · rw [show a' + (d + 1) = a' + d + 1 from rfl, e]; exact ih (by omega)
      · rcases ih (by omega) with e | l'
        · rw [e] at l; exact .inr l
        · exact .inr (tr _ _ _ l l')
  have key : ∀ x a', a ≤ a' → f a' = x → False := by
    intro x
    induction x using wf.induction with
    | _ x ih =>
      intro a' ha' hx
      obtain ⟨r, hr, hl⟩ := hinf a'
      have hlt : lt (f (r + 1)) x := by
        rcases mono a' ha' r hr with e | l
        · rw [e, hx] at hl; exact hl
        · rw [hx] at l; exact tr _ _ _ hl l
      exact ih (f (r + 1)) hlt (r + 1) (by omega) rfl
  exact key (f a) a (Nat.le_refl _) rfl

/-- What happens infinitely often at one of the places below `L` happens
infinitely often at one of them. -/
theorem infinitely_often_fin (L : Nat) (Q : Nat → Nat → Prop)
    (h : ∀ r', ∃ r, r' ≤ r ∧ ∃ m, m < L ∧ Q r m) :
    ∃ m, m < L ∧ ∀ r', ∃ r, r' ≤ r ∧ Q r m := by
  by_contra hno
  have hb : ∀ m, m < L → ∃ b, ∀ r, b ≤ r → ¬ Q r m := by
    intro m hm
    by_contra hc
    refine hno ⟨m, hm, fun r' => ?_⟩
    by_contra hc'
    exact hc ⟨r', fun r hr hq => hc' ⟨r, hr, hq⟩⟩
  have hall : ∀ n, n ≤ L → ∃ b, ∀ m, m < n → ∀ r, b ≤ r → ¬ Q r m := by
    intro n
    induction n with
    | zero => exact fun _ => ⟨0, fun m hm => absurd hm (Nat.not_lt_zero m)⟩
    | succ n ih =>
      intro hn
      obtain ⟨b, hbn⟩ := ih (Nat.le_of_succ_le hn)
      obtain ⟨b', hb'⟩ := hb n hn
      refine ⟨max b b', fun m hm r hr => ?_⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 hm with hm | rfl
      · exact hbn m hm r (by omega)
      · exact hb' r (by omega)
  obtain ⟨b, hbL⟩ := hall L (Nat.le_refl _)
  obtain ⟨r, hr, m, hm, hq⟩ := h b
  exact hbL m hm r hr hq

/-- What holds from some point on at each of the places below `n` holds at
all of them from some point on. -/
theorem eventually_forall_lt (n : Nat) (Q : Nat → Nat → Prop)
    (h : ∀ m, m < n → ∃ T, ∀ r, T ≤ r → Q m r) : ∃ T, ∀ m, m < n → ∀ r, T ≤ r → Q m r := by
  induction n with
  | zero => exact ⟨0, fun m hm => absurd hm (Nat.not_lt_zero m)⟩
  | succ n ih =>
    obtain ⟨T, hT⟩ := ih fun m hm => h m (Nat.lt_succ_of_lt hm)
    obtain ⟨T', hT'⟩ := h n (Nat.lt_succ_self n)
    refine ⟨max T T', fun m hm r hr => ?_⟩
    rcases Nat.lt_succ_iff_lt_or_eq.1 hm with hm | rfl
    · exact hT m hm r (by omega)
    · exact hT' r (by omega)

/-- What holds from some point on of each member of a list holds of all of
them from some point on. -/
theorem eventually_forall_mem {α : Type} (l : List α) (Q : α → Nat → Prop)
    (h : ∀ x ∈ l, ∃ T, ∀ r, T ≤ r → Q x r) : ∃ T, ∀ x ∈ l, ∀ r, T ≤ r → Q x r := by
  induction l with
  | nil => exact ⟨0, fun x hx => nomatch hx⟩
  | cons a l ih =>
    obtain ⟨T, hT⟩ := ih fun x hx => h x (List.mem_cons_of_mem _ hx)
    obtain ⟨T', hT'⟩ := h a List.mem_cons_self
    refine ⟨max T T', fun x hx r hr => ?_⟩
    rcases List.mem_cons.1 hx with rfl | hx
    · exact hT' r (by omega)
    · exact hT x hx r (by omega)

end RwLog
