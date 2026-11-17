/-
# The fan as a class

The members are the programs of `Fan.lean` with the input `h`; the rank of
the member with `m + 2` copies of the union is `m`, and its target is the
pair `(a, b)`. Here: the class is proper (`proper`), and the first rung has
paid `2 ^ k` before it covers a pair that needs the target of a member of
rank `k`, in any context (`below`): the lower clause of a separation
(`SeparatesOn.below`).
-/
import RwLog.Rungs.Symmetric.Fan
import RwLog.Rungs.Symmetric.Rung
import RwLog.Kernel.NormalFormSize
import RwLog.Kernel.NormalFormCalls
import RwLog.Kernel.NormalFormSpans

namespace RwLog

deriving instance DecidableEq for ProgramOf

namespace Symmetric

namespace Fan

/-- The greatest `m` up to the bound with `P` the member of rank `m`. -/
def findDown (P : Program) : Nat → Option Nat
  | 0 => if P = prog 0 then some 0 else none
  | k + 1 => if P = prog (k + 1) then some (k + 1) else findDown P k

theorem findDown_some {P : Program} : ∀ {k m : Nat}, findDown P k = some m → P = prog m
  | 0, m, h => by
    unfold findDown at h
    split at h
    · next e => cases h; exact e
    · cases h
  | k + 1, m, h => by
    unfold findDown at h
    split at h
    · next e => cases h; exact e
    · exact findDown_some h

theorem findDown_ge {P : Program} {m : Nat} (hP : P = prog m) :
    ∀ {k : Nat}, m ≤ k → ∃ m', findDown P k = some m' ∧ m ≤ m'
  | 0, h => by
    obtain rfl : m = 0 := by omega
    exact ⟨0, by simp [findDown, hP], Nat.le_refl _⟩
  | k + 1, h => by
    unfold findDown
    split
    · exact ⟨k + 1, rfl, h⟩
    · next hne =>
      have : m ≤ k := by
        rcases Nat.lt_or_ge k m with h' | h'
        · exact absurd (by rw [hP]; congr 1; omega) hne
        · exact h'
      exact findDown_ge hP this

/-- The rank of a program, if it is a member's. -/
def rankOf (P : Program) : Option Nat := findDown P P.size

/-- The pair `(a, b)`. -/
def target : GTerm × GTerm := (.sym "a", .sym "b")

/-- **The fan**: the members of `prog` with the input `h`, ranked by the
number of copies of the union past two, with the target `(a, b)`. -/
def cls : ProgClass where
  mem P r := decide (r = .call "h") && (rankOf P).isSome
  rank P _ := (rankOf P).getD 0
  tgt _ _ := [target]

theorem mem_cls {P : Program} {r : Rel} (h : cls.mem P r) :
    r = .call "h" ∧ P = prog (cls.rank P r) := by
  simp only [cls, Bool.and_eq_true, decide_eq_true_eq, Option.isSome_iff_exists] at h
  obtain ⟨hr, m, hm⟩ := h
  refine ⟨hr, ?_⟩
  show P = prog ((rankOf P).getD 0)
  rw [hm]
  exact findDown_some hm

/-! ## The size of a member -/

theorem size_Bn : ∀ m : Nat, (Bn m false).size = (m + 2) * ((U false).size + 1) - 1
  | 0 => rfl
  | m + 1 => by
    have e : Bn (m + 1) false = .seq (U false) (Bn m false) := rfl
    rw [e, RelOf.size, size_Bn m]
    have : (m + 1 + 2) * ((U false).size + 1) = (m + 2) * ((U false).size + 1) +
        ((U false).size + 1) := by ring
    have h1 : 0 < (m + 2) * ((U false).size + 1) := Nat.mul_pos (by omega) (by omega)
    omega

theorem size_prog (m : Nat) :
    (prog m).size = (prog 0).size - (Bn 0 false).size + (Bn m false).size := by
  have e : ∀ k, (prog k).size = (Bn k false).size + ((prog 0).size - (Bn 0 false).size) := by
    intro k
    simp [ProgramOf.size, prog, body, chain, mkSeq, Ud, RelOf.size, Sorts.size]
    omega
  rw [e m]
  omega

theorem le_size_prog (m : Nat) : m ≤ (prog m).size := by
  rw [size_prog]
  have h0 : (Bn 0 false).size ≤ (prog 0).size := by decide
  have h1 := size_Bn m
  have : m + 2 ≤ (m + 2) * ((U false).size + 1) := Nat.le_mul_of_pos_right _ (by omega)
  omega

theorem rank_prog (m : Nat) (r : Rel) : m ≤ cls.rank (prog m) r := by
  obtain ⟨m', h, hm⟩ := findDown_ge (P := prog m) rfl (le_size_prog m)
  show m ≤ (rankOf (prog m)).getD 0
  unfold rankOf
  rw [h]
  exact hm

theorem mem_prog (m : Nat) : cls.mem (prog m) (.call "h") = true := by
  obtain ⟨m', h, _⟩ := findDown_ge (P := prog m) rfl (le_size_prog m)
  simp [cls, rankOf, h]

/-! ## A member is well formed and relates its target -/

theorem wf_prog (m : Nat) : (prog m).WellFormed (.call "h") := by
  refine ⟨by simp [prog], ?_, Sorts.wellFormed_nil, ?_⟩
  · intro n hn
    simp [prog, body, cbody, calls_mkSeq, chain, RelOf.calls, I, Ud, cl, Bn, U] at hn ⊢
    tauto
  · intro s hs
    simp [prog, body, cbody, spans_mkSeq, chain, RelOf.spans, I, Ud, cl, Bn, U] at hs
    casesm* _ ∨ _ <;> subst_vars <;> decide

theorem related_prog (m : Nat) : target ∈ (prog m).pairs (.call "h") := by
  have hI : ∀ (t : GTerm) (ρ : Name → PRel), (t, t) ∈ denoteAt (prog m).sorts.interp ρ I := by
    intro t ρ
    show (t, t) ∈ idS.denAt _
    rw [denAt_idS]
    rfl
  have hc : ((.sym "b" : GTerm), (.sym "b" : GTerm)) ∈
      (prog m).meaningAt (prog m).sorts.interp "c" := by
    rw [ProgramOf.meaningAt_eq]
    exact .inl (hI _ _)
  show target ∈ (prog m).meaningAt (prog m).sorts.interp "h"
  rw [ProgramOf.meaningAt_eq]
  refine ⟨.sym "a", hI _ _, .sym "a", hI _ _, .sym "a", hI _ _, .sym "a", hI _ _, .sym "b",
    .inl ⟨fun _ => .sym "a", rfl, rfl, by simp [gS]⟩, hc⟩

/-- **The fan is a proper class**, with members of size linear in the rank. -/
theorem proper : cls.Proper fun k => 200 * (k + 1) ^ 1 where
  wf P r hm := by
    obtain ⟨rfl, hP⟩ := mem_cls hm
    rw [hP]
    exact wf_prog _
  size_le P r hm := by
    obtain ⟨rfl, hP⟩ := mem_cls hm
    generalize cls.rank P (.call "h") = k at hP ⊢
    rw [hP, size_prog, pow_one]
    have h1 := size_Bn k
    have h0 : (prog 0).size - (Bn 0 false).size ≤ 100 := by decide
    have hu : (U false).size + 1 ≤ 31 := by decide
    have h2 := Nat.mul_le_mul_left (k + 2) hu
    show _ + (RelOf.call "h" : Rel).size ≤ _
    simp only [RelOf.size]
    omega
  nonempty _ _ _ := by simp [cls]
  related P r hm x hx := by
    obtain ⟨rfl, hP⟩ := mem_cls hm
    obtain rfl : x = target := by simpa [cls] using hx
    rw [hP]
    exact related_prog _
  unbounded k := ⟨prog k, .call "h", mem_prog k, rank_prog k _⟩

/-- **The first rung has paid `2 ^ k` before it covers a pair that needs the
target of a member of rank `k`**, in any context, at a kernel that charges a
tick or more for a composition. -/
theorem below (κ : KernelRung)
    (hc : ∀ S (a b : κ.Rep S), 1 ≤ ((κ.kernel S).compose a b).ticks) (A : ArtifactStore)
    (P : Program) (r : Rel) (hm : cls.mem P r) (K : Context)
    (wf : (K.program P).WellFormed (K.query r)) (y : GTerm × GTerm)
    (hd : K.Demands P r P.sorts.interp {x | x ∈ cls.tgt P r} y) (n : Nat)
    (hcov : (rung1.machine κ A).Covered (K.program P) (K.query r) P.sorts.interp y n) :
    2 ^ cls.rank P r ≤ Resource.time.meter (rung1.machine κ A) (K.program P) (K.query r) n := by
  obtain ⟨rfl, hP⟩ := mem_cls hm
  generalize cls.rank P (.call "h") = k at hP ⊢
  subst hP
  have e : rung1.machine κ A =
      (((engine Unfold.raced @runsReader).costedAt κ.dom κ.kernel κ.refines).oriented).reLive
        (rung1.machine κ A).live := rfl
  rw [e] at hcov ⊢
  have h := paid κ.dom κ.kernel κ.refines κ.lawful hc k K wf hd
    (CostedRuntime.covered_reLive _ _ |>.1 hcov)
  refine le_trans (Nat.pow_le_pow_right (by omega) (Nat.le_succ k)) (le_of_le_of_eq h ?_)
  exact (CostedRuntime.paid_reLive _ _ _ _ _).symm

end Fan

end Symmetric

end RwLog
