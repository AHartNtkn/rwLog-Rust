/-
# A solved exclusion from a solution of its equations

`solve` gives a most general solution of the equations of an exclusion as a
function on variables. A normal exclusion is a list of bindings in which an
alias binds the later variable, so the solution is first turned around:
each variable the solution leaves alone is renamed to the least variable the
solution sends to it (`rep`, `orient`), and the bindings of the variables
below the number of variables of the store are listed (`bindsOf`).

The result has the syntax of a normal exclusion (`pre_solved`) and the same
substitutions satisfy it as satisfy the equations (`unifies_solved`).
-/
import RwLog.Sorts.Solved

namespace RwLog
namespace Sorts

open Function

/-! ## What a solution leaves alone -/

section solve

variable {E : Eqns Nat} {μ : Nat → Pat}

/-- The variables in the values of a solution are left alone by it. -/
theorem solve_idem (h : solve E = some μ) (v : Nat) : ∀ w ∈ (μ v).vars, μ w = .var w := by
  obtain ⟨hu, hg⟩ := solve_some h
  have e : (μ v).bind μ = (μ v).bind Term.var := by rw [hg μ hu v, Term.bind_var_id]
  exact bind_agree e

/-- A solution with its variables filled in satisfies the equations. -/
theorem solve_ground (h : solve E = some μ) :
    Eqns.Unifies (fun v => (μ v).bind fun _ => (Term.sym "" : GTerm)) E := by
  intro p hp
  have := congrArg (Term.bind fun _ => (Term.sym "" : GTerm)) ((solve_some h).1 p hp)
  simpa [Term.bind_bind] using this

/-- A variable outside the equations is left alone. -/
theorem solve_var_of_not_mem (h : solve E = some μ) {v : Nat} (hv : v ∉ E.vars) :
    μ v = .var v := by
  by_contra hne
  have hnot : v ∉ (μ v).vars := fun hin => hne (solve_idem h v v hin)
  have hu := solve_ground h
  obtain ⟨g', hg'⟩ := exists_ne ((μ v).bind fun _ => (Term.sym "" : GTerm))
  have hu' : Eqns.Unifies
      (update (fun v => (μ v).bind fun _ => (Term.sym "" : GTerm)) v g') E :=
    unifies_congr (fun p hp w hw => by
      have : w ≠ v := fun e => hv (e ▸ List.mem_flatMap.2 ⟨p, hp, hw⟩)
      simp [update, this]) hu
  have h₁ := (solve_some h).2 _ hu' v
  have h₂ : (μ v).bind (update (fun v => (μ v).bind fun _ => (Term.sym "" : GTerm)) v g') =
      (μ v).bind (fun v => (μ v).bind fun _ => (Term.sym "" : GTerm)) :=
    Term.bind_congr fun w hw => by
      have : w ≠ v := fun e => hnot (e ▸ hw)
      simp [update, this]
  have h₃ := (solve_some h).2 _ hu v
  rw [h₂, h₃] at h₁
  simp only [update_self] at h₁
  exact hg' h₁.symm

/-- The variables in the value of a variable that is not left alone are
variables of the equations. -/
theorem solve_vars (h : solve E = some μ) {v w : Nat} (hw : w ∈ (μ v).vars)
    (hne : μ v ≠ .var v) : w ∈ E.vars := by
  by_contra hw'
  have hwv : w ≠ v := by
    rintro rfl
    exact hne (solve_idem h w w hw)
  have hu := solve_ground h
  obtain ⟨g', hg'⟩ := exists_ne ((μ w).bind fun _ => (Term.sym "" : GTerm))
  have hu' : Eqns.Unifies
      (update (fun v => (μ v).bind fun _ => (Term.sym "" : GTerm)) w g') E :=
    unifies_congr (fun p hp z hz => by
      have : z ≠ w := fun e => hw' (e ▸ List.mem_flatMap.2 ⟨p, hp, hz⟩)
      simp [update, this]) hu
  have h₁ := (solve_some h).2 _ hu' v
  have h₃ := (solve_some h).2 _ hu v
  have e : (μ v).bind (update (fun v => (μ v).bind fun _ => (Term.sym "" : GTerm)) w g') =
      (μ v).bind (fun v => (μ v).bind fun _ => (Term.sym "" : GTerm)) := by
    rw [h₁, h₃]; simp [update, hwv.symm]
  have := bind_agree e w hw
  simp only [update_self] at this
  exact hg' this

/-- The substitutions that satisfy the equations are the ones the solution
does not change. -/
theorem unifies_iff_solve (h : solve E = some μ) (σ : Nat → GTerm) :
    Eqns.Unifies σ E ↔ ∀ v, (μ v).bind σ = σ v := by
  refine ⟨fun hu => (solve_some h).2 σ hu, fun hf p hp => ?_⟩
  have := congrArg (Term.bind σ) ((solve_some h).1 p hp)
  simp only [Term.bind_bind] at this
  have e : (fun v => (μ v).bind σ) = σ := funext hf
  rwa [e] at this

end solve

/-! ## Turning aliases around -/

/-- The least variable below `k` that the solution sends to `w`. -/
def rep (k : Nat) (μ : Nat → Pat) (w : Nat) : Nat :=
  ((List.range k).find? fun v => μ v = .var w).getD w

/-- The solution with each variable it leaves alone renamed to the least
variable sent to it. -/
def orient (k : Nat) (μ : Nat → Pat) (v : Nat) : Pat :=
  (μ v).bind fun w => .var (rep k μ w)

/-- The bindings of a substitution on the variables below `k`. -/
def bindsOf (k : Nat) (ν : Nat → Pat) : Binds :=
  (List.range k).filterMap fun v => if ν v = .var v then none else some (v, ν v)

theorem rep_spec {k : Nat} {μ : Nat → Pat} {v w : Nat} (hv : v < k) (h : μ v = .var w) :
    rep k μ w ≤ v ∧ rep k μ w < k ∧ μ (rep k μ w) = .var w := by
  unfold rep
  cases hf : (List.range k).find? fun v => μ v = .var w with
  | none =>
    rw [List.find?_eq_none] at hf
    exact absurd h (by simpa using hf v (List.mem_range.2 hv))
  | some i =>
    rw [List.find?_range_eq_some] at hf
    obtain ⟨hi, hik, hmin⟩ := hf
    simp only [Option.getD_some]
    refine ⟨?_, List.mem_range.1 hik, by simpa using hi⟩
    by_contra hlt
    have := hmin v (by omega)
    simp [h] at this

theorem mem_bindsOf {k : Nat} {ν : Nat → Pat} {b : Nat × Pat} :
    b ∈ bindsOf k ν ↔ b.1 < k ∧ ν b.1 ≠ .var b.1 ∧ b.2 = ν b.1 := by
  simp only [bindsOf, List.mem_filterMap, List.mem_range]
  constructor
  · rintro ⟨v, hv, h⟩
    by_cases e : ν v = .var v
    · simp [e] at h
    · simp only [e, ↓reduceIte, Option.some.injEq] at h
      subst h
      exact ⟨hv, e, rfl⟩
  · rintro ⟨hk, hne, e⟩
    refine ⟨b.1, hk, ?_⟩
    simp only [hne, ↓reduceIte, Option.some.injEq]
    exact Prod.ext rfl e.symm

theorem sorted_bindsOf (k : Nat) (ν : Nat → Pat) :
    (bindsOf k ν).Pairwise fun a b => a.1 < b.1 := by
  refine List.Pairwise.filterMap _ ?_ List.pairwise_lt_range
  intro v w hvw b hb b' hb'
  have e : ∀ {u : Nat} {c : Nat × Pat},
      c ∈ (if ν u = .var u then none else some (u, ν u)) → c.1 = u := by
    intro u c hc
    by_cases h : ν u = .var u
    · simp [h] at hc
    · simp only [h, ↓reduceIte, Option.mem_def, Option.some.injEq] at hc
      rw [← hc]
  rw [e hb, e hb']
  exact hvw

theorem apply_bindsOf {k : Nat} {ν : Nat → Pat} {v : Nat} (hv : v < k) :
    PSubst.apply (bindsOf k ν) v = ν v := by
  by_cases e : ν v = .var v
  · rw [e]
    exact apply_of_not_mem fun b hb hbv => (mem_bindsOf.1 hb).2.1 (hbv ▸ e)
  · exact apply_of_mem (sorted_bindsOf k ν) (b := (v, ν v)) (mem_bindsOf.2 ⟨hv, e, rfl⟩)

/-! ## The solved exclusion -/

section solved

variable {E : Eqns Nat} {μ : Nat → Pat} {k : Nat}

/-- A variable the solution leaves alone is sent to its least alias, which
is left alone. -/
theorem orient_rep {w : Nat} (hw : w < k) (hfree : μ w = .var w) :
    orient k μ (rep k μ w) = .var (rep k μ w) := by
  unfold orient
  rw [(rep_spec hw hfree).2.2]
  rfl

theorem orient_vars (h : solve E = some μ) (hEv : ∀ v ∈ E.vars, v < k) {v y : Nat} (hv : v < k)
    (hy : y ∈ (orient k μ v).vars) :
    ∃ w, w < k ∧ μ w = .var w ∧ y = rep k μ w := by
  obtain ⟨w, hw, hyw⟩ := Term.vars_bind_mem hy
  simp only [Term.vars, List.mem_singleton] at hyw
  have hfree := solve_idem h v w hw
  refine ⟨w, ?_, hfree, hyw⟩
  by_cases e : μ v = .var v
  · rw [e] at hw
    simp only [Term.vars, List.mem_singleton] at hw
    subst hw; exact hv
  · exact hEv w (solve_vars h hw e)

/-- The oriented solution has the syntax of a normal exclusion. -/
theorem pre_solved (h : solve E = some μ) (hE : E.FO) (hEv : ∀ v ∈ E.vars, v < k) :
    Pre k (bindsOf k (orient k μ)) := by
  refine ⟨sorted_bindsOf _ _, fun b hb => (mem_bindsOf.1 hb).1, ?_, ?_, ?_⟩
  · intro b hb
    rw [(mem_bindsOf.1 hb).2.2]
    exact Term.fo_bind (solve_fo E hE μ h b.1) fun _ _ => rfl
  · intro b hb y hy
    obtain ⟨hbk, -, e⟩ := mem_bindsOf.1 hb
    rw [e] at hy
    obtain ⟨w, hw, hfree, rfl⟩ := orient_vars h hEv hbk hy
    refine ⟨(rep_spec hw hfree).2.1, fun b' hb' e' => ?_⟩
    have := (mem_bindsOf.1 hb').2.1
    rw [e'] at this
    exact this (orient_rep hw hfree)
  · intro b hb y hy
    obtain ⟨hbk, hne, e⟩ := mem_bindsOf.1 hb
    rw [e] at hy
    have hyne : y ≠ b.1 := fun e' => hne (e' ▸ hy)
    unfold orient at hy
    cases hμ : μ b.1 with
    | var w =>
      rw [hμ] at hy
      simp only [Term.bind, Term.var.injEq] at hy
      have := (rep_spec hbk hμ).1
      omega
    | sym f => rw [hμ] at hy; simp [Term.bind] at hy
    | app a c => rw [hμ] at hy; simp [Term.bind] at hy

/-- The oriented solution is satisfied by the substitutions that satisfy the
equations. -/
theorem unifies_solved (h : solve E = some μ) (hE : E.FO) (hEv : ∀ v ∈ E.vars, v < k)
    (σ : Nat → GTerm) :
    Eqns.Unifies σ (eqnsOf (bindsOf k (orient k μ))) ↔ Eqns.Unifies σ E := by
  have hpre := pre_solved h hE hEv
  have hin : ∀ v, v < k → ∀ w ∈ (μ v).vars, w < k ∧ μ w = .var w := by
    intro v hv w hw
    refine ⟨?_, solve_idem h v w hw⟩
    by_cases e : μ v = .var v
    · rw [e] at hw
      simp only [Term.vars, List.mem_singleton] at hw
      subst hw; exact hv
    · exact hEv w (solve_vars h hw e)
  have key : (∀ w, w < k → μ w = .var w → σ (rep k μ w) = σ w) →
      ∀ v, v < k → (orient k μ v).bind σ = (μ v).bind σ := by
    intro hK v hv
    unfold orient
    rw [Term.bind_bind]
    exact Term.bind_congr fun w hw => hK w (hin v hv w hw).1 (hin v hv w hw).2
  rw [unifies_eqnsOf hpre.sorted, unifies_iff_solve h]
  constructor
  · intro hA
    have hK : ∀ w, w < k → μ w = .var w → σ (rep k μ w) = σ w := by
      intro w hw hfree
      have := hA w
      rw [apply_bindsOf hw] at this
      unfold orient at this
      rw [hfree] at this
      exact this.symm
    intro v
    by_cases hv : v < k
    · have := hA v
      rw [apply_bindsOf hv, key hK v hv] at this
      exact this.symm
    · rw [solve_var_of_not_mem h fun hin' => hv (hEv v hin')]
      rfl
  · intro hB
    have hK : ∀ w, w < k → μ w = .var w → σ (rep k μ w) = σ w := by
      intro w hw hfree
      have := hB (rep k μ w)
      rw [(rep_spec hw hfree).2.2] at this
      exact this.symm
    intro v
    by_cases hv : v < k
    · rw [apply_bindsOf hv, key hK v hv]
      exact (hB v).symm
    · rw [hpre.apply_ge (by omega)]
      rfl

end solved

end Sorts
end RwLog
