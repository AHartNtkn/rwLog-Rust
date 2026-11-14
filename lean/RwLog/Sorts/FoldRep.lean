/-
# The folded store of a representative

A representative of the domain is a normal store over a pair
(`Sorts/Rep.lean`). The machine keeps its folded canonical store instead
(`FoldOf`, `Sorts/FoldRaw.lean`). The pair symbol is reserved for the
domain: when no sort has a case for it (`NoPair`), a pair is never a free
subterm, so the folded store of a representative is again a store over a
pair, it relates the same pairs, and its two sides are the same pattern
exactly when those of the representative are.
-/
import RwLog.Sorts.Rep
import RwLog.Sorts.FoldRaw

namespace RwLog
namespace Sorts

variable {S : Sorts}

/-- No sort has a case for the pair symbol with two arguments. -/
def NoPair (S : Sorts) : Prop :=
  ∀ n d, S.lookup n = some d → ∀ cs ∈ d.cases, ¬ (cs.1 = "" ∧ cs.2.length = 2)

/-- When no sort has a case for the pair symbol, a pair is not a free
subterm of a store that has a solution. -/
theorem not_free_tpair (hS : S.WellFormed) (hN : NoPair S) {s : Store}
    (hne : (s.Sol S).Nonempty) (a b : Pat) : ¬ Free S s (tpair a b) := by
  intro hF
  obtain ⟨C, hin, hout⟩ := hF.sem
  obtain ⟨σ, hσ⟩ := hne
  have hm := hin σ hσ
  have hall : ∀ g, MemC S C g → g.key = some ("", 2) := by
    intro g hg
    obtain ⟨σ', -, rfl, -⟩ := hout σ hσ g hg
    exact tpair_key _ _
  cases hs : sole S C [] with
  | none =>
    obtain ⟨t₁, t₂, h1, -, h2, -, hne⟩ := sole_none hS hs hm List.not_mem_nil
    exact hne ((hall t₁ h1).trans (hall t₂ h2).symm)
  | some key =>
    have hk : key = ("", 2) := by
      have := sole_sound hs hm List.not_mem_nil
      rw [hall _ hm] at this
      exact (Option.some.inj this).symm
    subst hk
    unfold sole at hs
    split at hs
    · cases hs
    · have hmem : (("", 2) : Sym × Nat) ∈ survivors S C [] := by
        rw [only_eq_some.1 hs]; exact Finset.mem_singleton_self _
      simp only [survivors, Finset.mem_filter, Finset.mem_union, List.filterMap_nil,
        List.toFinset_nil, Finset.notMem_empty, or_false] at hmem
      obtain ⟨n, -, d, hd, cs, hcs, h1, h2⟩ := mem_caseKeys.1 hmem.1
      exact hN n d hd cs hcs ⟨h1, h2⟩

/-- Terms with the same image under a renaming that is one to one on their
variables are the same. -/
theorem rename_injOn {V W : Type} (f : V → W) : ∀ t u : Term V,
    (∀ v ∈ t.vars, ∀ w ∈ u.vars, f v = f w → v = w) → t.rename f = u.rename f → t = u
  | .var x, .var y, h, e => by
    simp only [Term.rename, Term.bind, Term.var.injEq] at e
    rw [h x (by simp [Term.vars]) y (by simp [Term.vars]) e]
  | .var _, .sym _, _, e => by simp [Term.rename, Term.bind] at e
  | .var _, .app _ _, _, e => by simp [Term.rename, Term.bind] at e
  | .sym _, .var _, _, e => by simp [Term.rename, Term.bind] at e
  | .sym _, .sym _, _, e => by simpa [Term.rename, Term.bind] using e
  | .sym _, .app _ _, _, e => by simp [Term.rename, Term.bind] at e
  | .app _ _, .var _, _, e => by simp [Term.rename, Term.bind] at e
  | .app _ _, .sym _, _, e => by simp [Term.rename, Term.bind] at e
  | .app a b, .app c d, h, e => by
    simp only [Term.rename, Term.bind, Term.app.injEq] at e
    rw [rename_injOn f a c (fun v hv w hw => h v (by simp [Term.vars, hv]) w
        (by simp [Term.vars, hw])) e.1,
      rename_injOn f b d (fun v hv w hw => h v (by simp [Term.vars, hv]) w
        (by simp [Term.vars, hw])) e.2]

open Classical in
/-- The folded pattern of a store over a pair is a pair, and its two sides
are the same pattern exactly when those of the store are. -/
theorem foldPat_tpair (hS : S.WellFormed) (hN : NoPair S) {s : Store}
    (hne : (s.Sol S).Nonempty) {a b : Pat} (ht : s.t = tpair a b) :
    ∃ a' b', foldPat S s = tpair a' b' ∧ (a' = b' ↔ a = b) := by
  have hV : foldV S s s.t =
      tpair (if Free S s a then Term.var a else foldF S s a)
        (if Free S s b then Term.var b else foldF S s b) := by
    rw [ht]
    unfold foldV
    rw [ite_eq_right (not_free_tpair hS hN hne a b)]
    rfl
  have hjoin : ∀ p : Pat, (if Free S s p then Term.var p else foldF S s p).bind id = p := by
    intro p
    by_cases hf : Free S s p
    · rw [ite_eq_left hf]; rfl
    · rw [ite_eq_right hf, foldF_join]
  refine ⟨_, _, by unfold foldPat; rw [hV]; rfl, fun e => ?_, fun e => by rw [e]⟩
  have hAB := rename_injOn _ _ _ (fun v hv w hw e' => ?_) e
  · rw [← hjoin a, ← hjoin b, hAB]
  · have hmem : ∀ p, p ∈ (tpair (if Free S s a then Term.var a else foldF S s a)
        (if Free S s b then Term.var b else foldF S s b)).vars →
        p ∈ firsts (tpair (if Free S s a then Term.var a else foldF S s a)
          (if Free S s b then Term.var b else foldF S s b)).vars :=
      fun p hp => ((firsts_spec _).2.1 p).2 hp
    exact (List.idxOf_inj (hmem v (by rw [tpair_vars]; exact List.mem_append_left _ hv))).1 e'

/-- The folded canonical store of a normal store over a pair is a store over
a pair, and its two sides are the same pattern exactly when those of the
normal store are. -/
theorem FoldOf.pair (hS : S.WellFormed) (hN : NoPair S) {n r : Raw} (hn : n.Normal S)
    (h : FoldOf S n r) {a b : Pat} (ht : n.t = tpair a b) :
    ∃ a' b', r.t = tpair a' b' ∧ (a' = b' ↔ a = b) := by
  rw [h.2.2]
  exact foldPat_tpair hS hN (hn.sol_nonempty hS) ht

/-- The folded canonical store relates the pairs the normal store does. -/
theorem FoldOf.rel {n r : Raw} (h : FoldOf S n r) : r.rel S = n.rel S := by
  unfold Raw.rel
  rw [h.2.1]

/-- The sides of the folded canonical store of a representative: its pattern
is their pair, and they are the same pattern exactly when the sides of the
representative are. -/
theorem Rep.fold_sides (hN : NoPair S) (ρ : Rep S) {r : Raw} (h : FoldOf S ρ.1 r) :
    r.t = tpair r.sides.1 r.sides.2 ∧ (r.sides.1 = r.sides.2 ↔ ρ.1.sides.1 = ρ.1.sides.2) := by
  obtain ⟨a, b, hab⟩ := ρ.2.2.2
  obtain ⟨a', b', ht, hiff⟩ := h.pair ρ.wf hN ρ.normal hab
  rw [Raw.sides_of ht, Raw.sides_of hab]
  exact ⟨ht, hiff⟩

/-- Representatives with the same folded canonical store are the same. -/
theorem Rep.eq_of_fold {ρ ρ' : Rep S} {r : Raw} (h : FoldOf S ρ.1 r) (h' : FoldOf S ρ'.1 r) :
    ρ = ρ' :=
  Subtype.ext (FoldOf.inj ρ.wf ρ.normal ρ'.normal h h')

end Sorts
end RwLog
