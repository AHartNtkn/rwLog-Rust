/-
# Conjunctions of sorts

A variable can carry several sorts at once; their conjunction is again decided
by the root symbol. `memC_mk` is membership of a surface term in a
conjunction: every sort accepts the root, and every argument is in the
conjunction of the sorts its position is given.
-/
import RwLog.Sorts.Decl
import Mathlib.Data.Finset.Option
import Mathlib.Data.Finset.Union

namespace RwLog
namespace Sorts

/-- A conjunction of named sorts. The empty conjunction is every term. -/
abbrev Conj := Finset Name

/-- `t` is in every sort of `c`. -/
def MemC (S : Sorts) (c : Conj) (t : GTerm) : Prop := ∀ n ∈ c, mem S n t = true

instance (S : Sorts) (c : Conj) (t : GTerm) : Decidable (MemC S c t) := by
  unfold MemC; infer_instance

/-- Every sort of `c` accepts the root `f` with `k` arguments. -/
def Accepts (S : Sorts) (c : Conj) (f : Sym) (k : Nat) : Prop :=
  ∀ n ∈ c, (step S n f k).isSome = true

instance (S : Sorts) (c : Conj) (f : Sym) (k : Nat) : Decidable (Accepts S c f k) := by
  unfold Accepts; infer_instance

/-- The sorts required of argument `i` of a term with root `f` and `k`
arguments that is in `c`. -/
def kidC (S : Sorts) (c : Conj) (f : Sym) (k : Nat) (i : Nat) : Conj :=
  c.biUnion fun n =>
    match step S n f k with
    | some ks => (ks[i]?.join).toFinset
    | none => ∅

theorem mem_kidC {S : Sorts} {c : Conj} {f : Sym} {k i : Nat} {m : Name} :
    m ∈ kidC S c f k i ↔ ∃ n ∈ c, ∃ ks, step S n f k = some ks ∧ ks[i]? = some (some m) := by
  simp only [kidC, Finset.mem_biUnion]
  constructor
  · rintro ⟨n, hn, h⟩
    cases hs : step S n f k with
    | none => simp [hs] at h
    | some ks =>
      simp only [hs, Option.mem_toFinset, Option.mem_def] at h
      refine ⟨n, hn, ks, hs, ?_⟩
      cases hg : ks[i]? with
      | none => simp [hg] at h
      | some o => simp [hg] at h; simp [h]
  · rintro ⟨n, hn, ks, hs, hg⟩
    exact ⟨n, hn, by simp [hs, hg]⟩

theorem memC_mk {S : Sorts} {c : Conj} {f : Sym} {ts : List GTerm} :
    MemC S c (Term.mk f ts) ↔
      Accepts S c f ts.length ∧
        ∀ i (h : i < ts.length), MemC S (kidC S c f ts.length i) ts[i] := by
  constructor
  · intro h
    refine ⟨fun n hn => ?_, fun i hi m hm => ?_⟩
    · obtain ⟨ks, hs, _⟩ := mem_mk.mp (h n hn)
      simp [hs]
    · obtain ⟨n, hn, ks, hs, hg⟩ := mem_kidC.mp hm
      obtain ⟨ks', hs', hall⟩ := mem_mk.mp (h n hn)
      rw [hs] at hs'; cases hs'
      have := hall i hi
      simpa [hg, memO] using this
  · rintro ⟨hacc, hall⟩ n hn
    have := hacc n hn
    rw [Option.isSome_iff_exists] at this
    obtain ⟨ks, hs⟩ := this
    refine mem_mk.mpr ⟨ks, hs, fun i hi => ?_⟩
    cases hg : ks[i]? with
    | none => rfl
    | some o =>
      cases o with
      | none => rfl
      | some m =>
        have hm : m ∈ kidC S c f ts.length i := mem_kidC.mpr ⟨n, hn, ks, hs, hg⟩
        simpa [memO] using hall i hi m hm

/-- Every ground term is a surface term whose arguments are smaller. -/
theorem exists_mk : ∀ t : GTerm, ∃ f ts, t = Term.mk f ts ∧ ∀ u ∈ ts, u.size < t.size
  | .sym f => ⟨f, [], rfl, by simp⟩
  | .app a b => by
    obtain ⟨f, ts, rfl, hsz⟩ := exists_mk a
    refine ⟨f, ts ++ [b], by simp [Term.mk], ?_⟩
    intro u hu
    simp only [List.mem_append, List.mem_singleton] at hu
    simp only [Term.size]
    rcases hu with hu | rfl
    · have := hsz u hu; omega
    · omega

end Sorts
end RwLog
