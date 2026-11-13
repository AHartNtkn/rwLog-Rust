/-
# Rung zero terminates on every recursion-free query

`FinitelyNormalising` is the class rung zero is proved to stop on, but it is
phrased in terms of rung zero's own normalizer, so on its own it says little
more than "the run stops when its stopping test passes". This file connects it
to a class stated without reference to the engine, which is the day-one
requirement in the properties catalogue ("termination when the relation
unfolds finitely on its own, in practice recursion-free relations"):

* `CallTreeFinite P q`: some number of unfoldings leaves no call at all. This
  is the statement that the derivation tree of the query (every call
  unfolded) is finite. It mentions neither normalization nor matching.
* `RecursionFree P q`: the names reachable from the query can be ranked so
  that every call inside a reachable body goes to a strictly smaller rank,
  that is, the reachable call graph has no cycle.

`RecursionFree → CallTreeFinite → FinitelyNormalising`, so rung zero halts on
every recursion-free query (`terminates_recursionFree`).
-/
import RwLog.Rungs.R000.Properties

namespace RwLog

namespace R000

variable {P : Program}

/-- The query's call tree is finite: after `k` unfoldings no call is left. -/
def CallTreeFinite (P : Program) (q : Rel) : Prop :=
  ∃ k, (unfoldN P k q).calls = []

/-- The names reachable from the query through calls. -/
inductive Reaches (P : Program) (q : Rel) : Name → Prop
  | root {n : Name} : n ∈ q.calls → Reaches P q n
  | step {n m : Name} : Reaches P q n → m ∈ (P.body n).calls → Reaches P q m

/-- No recursion is reachable from the query: reachable names have a rank
that strictly decreases along every call. -/
def RecursionFree (P : Program) (q : Rel) : Prop :=
  ∃ r : Name → Nat, ∀ n m, Reaches P q n → m ∈ (P.body n).calls → r m < r n

theorem mem_calls_unfold {m : Name} :
    ∀ e : Rel, m ∈ (unfold P e).calls ↔ ∃ n ∈ e.calls, m ∈ (P.body n).calls
  | .zero => by simp [unfold, RelOf.calls]
  | .span _ => by simp [unfold, RelOf.calls]
  | .or a b | .and a b | .seq a b => by
    simp only [unfold, RelOf.calls, List.mem_append, mem_calls_unfold a, mem_calls_unfold b]
    constructor
    · rintro (⟨n, hn, h⟩ | ⟨n, hn, h⟩)
      · exact ⟨n, Or.inl hn, h⟩
      · exact ⟨n, Or.inr hn, h⟩
    · rintro ⟨n, hn | hn, h⟩
      · exact Or.inl ⟨n, hn, h⟩
      · exact Or.inr ⟨n, hn, h⟩
  | .conv a => by simp only [unfold, RelOf.calls, mem_calls_unfold a]
  | .call n => by simp [unfold, RelOf.calls]

theorem le_sum_of_mem {l : List Nat} {x : Nat} (h : x ∈ l) : x ≤ l.sum := by
  induction l with
  | nil => simp at h
  | cons y l ih =>
    rcases List.mem_cons.1 h with rfl | h
    · simp
    · have := ih h; simp; omega

theorem RecursionFree.callTreeFinite {q : Rel} (h : RecursionFree P q) : CallTreeFinite P q := by
  obtain ⟨r, hr⟩ := h
  let K := (q.calls.map r).sum + 1
  -- Every call left after `j` unfoldings is reachable and has rank below `K - j`.
  have inv : ∀ j, ∀ m ∈ (unfoldN P j q).calls, Reaches P q m ∧ r m + j < K := by
    intro j
    induction j with
    | zero =>
      intro m hm
      refine ⟨.root hm, ?_⟩
      have : r m ≤ (q.calls.map r).sum := le_sum_of_mem (List.mem_map_of_mem hm)
      simp only [K]; omega
    | succ j ih =>
      intro m hm
      rw [unfoldN_succ, mem_calls_unfold] at hm
      obtain ⟨n, hn, hm⟩ := hm
      obtain ⟨hreach, hlt⟩ := ih n hn
      have := hr n m hreach hm
      exact ⟨.step hreach hm, by omega⟩
  refine ⟨K, ?_⟩
  rcases hc : (unfoldN P K q).calls with _ | ⟨m, _⟩
  · rfl
  · have := (inv K m (by rw [hc]; exact List.mem_cons_self)).2
    omega

theorem joinSeq_callFree {p q r : List Rel} (hp : ∀ x ∈ p, x.calls = [])
    (hq : ∀ x ∈ q, x.calls = []) (h : joinSeq p q = some r) : ∀ x ∈ r, x.calls = [] := by
  unfold joinSeq at h
  split at h
  · rename_i a b q' _ hq'
    obtain ⟨c, -, rfl⟩ := Option.map_eq_some_iff.1 h
    intro x hx
    simp only [List.mem_append, List.mem_cons] at hx
    rcases hx with hx | rfl | hx
    · exact hp x (List.dropLast_subset _ hx)
    · rfl
    · exact hq x (List.mem_cons_of_mem _ hx)
  · cases h
    intro x hx
    rcases List.mem_append.1 hx with hx | hx
    · exact hp x hx
    · exact hq x hx

theorem mkAnd_callFree {p q r : List Rel} (hp : ∀ x ∈ p, x.calls = [])
    (hq : ∀ x ∈ q, x.calls = []) (h : mkAnd p q = some r) : ∀ x ∈ r, x.calls = [] := by
  unfold mkAnd at h
  split at h
  · obtain ⟨c, -, rfl⟩ := Option.map_eq_some_iff.1 h
    simp [RelOf.calls]
  · cases h
    simp only [List.mem_singleton, forall_eq, RelOf.calls, List.append_eq_nil_iff]
    exact ⟨(calls_toRel p).2 hp, (calls_toRel q).2 hq⟩

/-- Normalizing a call-free expression leaves only call-free products. -/
theorem norm_callFree : ∀ (neg : Bool) (e : Rel), e.calls = [] →
    ∀ p ∈ norm neg e, ∀ x ∈ p, x.calls = []
  | _, .zero, _, p, hp => by simp [norm] at hp
  | neg, .span s, _, p, hp => by
    simp only [norm, List.mem_singleton] at hp
    subst hp
    simp [RelOf.calls]
  | neg, .or a b, he, p, hp => by
    simp only [RelOf.calls, List.append_eq_nil_iff] at he
    rcases List.mem_append.1 hp with hp | hp
    · exact norm_callFree neg a he.1 p hp
    · exact norm_callFree neg b he.2 p hp
  | false, .seq a b, he, p, hp => by
    simp only [RelOf.calls, List.append_eq_nil_iff] at he
    simp only [norm, List.mem_flatMap, List.mem_filterMap] at hp
    obtain ⟨p₁, hp₁, p₂, hp₂, hj⟩ := hp
    exact joinSeq_callFree (norm_callFree false a he.1 p₁ hp₁) (norm_callFree false b he.2 p₂ hp₂) hj
  | true, .seq a b, he, p, hp => by
    simp only [RelOf.calls, List.append_eq_nil_iff] at he
    simp only [norm, List.mem_flatMap, List.mem_filterMap] at hp
    obtain ⟨p₁, hp₁, p₂, hp₂, hj⟩ := hp
    exact joinSeq_callFree (norm_callFree true b he.2 p₁ hp₁) (norm_callFree true a he.1 p₂ hp₂) hj
  | neg, .and a b, he, p, hp => by
    simp only [RelOf.calls, List.append_eq_nil_iff] at he
    simp only [norm, List.mem_flatMap, List.mem_filterMap] at hp
    obtain ⟨p₁, hp₁, p₂, hp₂, hj⟩ := hp
    exact mkAnd_callFree (norm_callFree neg a he.1 p₁ hp₁) (norm_callFree neg b he.2 p₂ hp₂) hj
  | neg, .conv a, he, p, hp => by
    simp only [norm] at hp
    exact norm_callFree (!neg) a he p hp
  | _, .call n, he, _, _ => by simp [RelOf.calls] at he

theorem CallTreeFinite.finitelyNormalising {q : Rel} (h : CallTreeFinite P q) :
    FinitelyNormalising P q := by
  obtain ⟨k, hk⟩ := h
  exact ⟨k, fun p hp => (calls_toRel p).2 (norm_callFree false _ hk p hp)⟩

/-- Rung zero halts on every query whose call tree is finite. -/
theorem terminates_callTreeFinite : runtime.TerminatesOn CallTreeFinite :=
  fun P q hw h => terminates P q hw h.finitelyNormalising

/-- Rung zero halts on every recursion-free query. -/
theorem terminates_recursionFree : runtime.TerminatesOn RecursionFree :=
  fun P q hw h => terminates P q hw h.callTreeFinite.finitelyNormalising

end R000

end RwLog
