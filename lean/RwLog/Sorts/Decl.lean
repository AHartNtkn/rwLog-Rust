/-
# Sort declarations and membership

A sort is a set of ground terms given by a grammar that is decided by the root
symbol. For a root symbol and a number of arguments, a declaration either has
a *case*, which names the sort of every argument (`none` is "any term"), or
falls to its *rest*: every symbol with no case is accepted unless it is listed
as excluded, with all its arguments in one sort (`none` is "any term"). A
declaration without a rest rejects every symbol that has no case.

Membership is computed by one pass over the curried term (`kids`), and is
characterised on surface terms `(f t₁ … tₙ)` by `mem_mk`.
-/
import RwLog.Trusted.Syntax

namespace RwLog
namespace Sorts

/-- One sort declaration. -/
structure SortDef where
  cases : List (Sym × List (Option Name))
  rest : Option (List (Sym × Nat) × Option Name)
  deriving DecidableEq, Repr

/-- The declared sorts of a program. -/
abbrev Decls := List (Name × SortDef)

/-- The sorts of the arguments of a term with root `f` and `n` arguments, when
the declaration accepts that root. -/
def SortDef.step (d : SortDef) (f : Sym) (n : Nat) : Option (List (Option Name)) :=
  match d.cases.find? (fun c => c.1 = f ∧ c.2.length = n) with
  | some c => some c.2
  | none =>
    match d.rest with
    | some (ex, k) => if (f, n) ∈ ex then none else some (List.replicate n k)
    | none => none

theorem SortDef.step_length {d : SortDef} {f : Sym} {n : Nat} {ks : List (Option Name)}
    (h : d.step f n = some ks) : ks.length = n := by
  unfold SortDef.step at h
  split at h
  · rename_i c hc
    have := List.find?_some hc
    simp only [decide_eq_true_eq] at this
    cases h; exact this.2
  · split at h
    · split at h
      · cases h
      · cases h; simp
    · cases h

/-- One step of a named sort; an undeclared name is the empty sort. -/
def step (S : Decls) (n : Name) (f : Sym) (k : Nat) : Option (List (Option Name)) :=
  (S.lookup n).bind fun d => d.step f k

theorem step_length {S : Decls} {n : Name} {f : Sym} {k : Nat} {ks : List (Option Name)}
    (h : step S n f k = some ks) : ks.length = k := by
  unfold step at h
  cases hd : S.lookup n with
  | none => simp [hd] at h
  | some d => simp [hd] at h; exact SortDef.step_length h

/-- The argument sorts of the surface term of which `t` is the function part
with `extra` arguments still to come, when sort `n` accepts everything read so
far. Membership of an argument is checked as it is passed. -/
def kids (S : Decls) : GTerm → Name → Nat → Option (List (Option Name))
  | .sym f, n, extra => step S n f extra
  | .app t u, n, extra =>
    match kids S t n (extra + 1) with
    | none => none
    | some ks =>
      match ks[ks.length - extra - 1]? with
      | none => none
      | some none => some ks
      | some (some m) => if (kids S u m 0).isSome then some ks else none

/-- `t` is a member of the sort named `n`. -/
def mem (S : Decls) (n : Name) (t : GTerm) : Bool := (kids S t n 0).isSome

/-- `t` is in the sort `k`, where `none` is the sort of all terms. -/
def memO (S : Decls) (k : Option Name) (t : GTerm) : Bool :=
  match k with
  | none => true
  | some m => mem S m t

theorem kids_length {S : Decls} : ∀ {t : GTerm} {n : Name} {extra : Nat} {ks : List (Option Name)},
    kids S t n extra = some ks → extra ≤ ks.length
  | .sym f, n, extra, ks, h => by
    simp only [kids] at h; exact Nat.le_of_eq (step_length h).symm
  | .app t u, n, extra, ks, h => by
    simp only [kids] at h
    split at h
    · cases h
    · rename_i ks' hk
      have := kids_length hk
      split at h
      · cases h
      · cases h; omega
      · split at h
        · cases h; omega
        · cases h

/-- Reading one more argument. -/
theorem kids_app {S : Decls} {t u : GTerm} {n : Name} {extra : Nat} {ks : List (Option Name)} :
    kids S (.app t u) n extra = some ks ↔
      kids S t n (extra + 1) = some ks ∧
        memO S (ks[ks.length - extra - 1]?.getD none) u = true := by
  simp only [kids]
  cases hk : kids S t n (extra + 1) with
  | none => simp
  | some ks' =>
    have hlen := kids_length hk
    have hlt : ks'.length - extra - 1 < ks'.length := by omega
    obtain ⟨o, hget⟩ : ∃ o, ks'[ks'.length - extra - 1]? = some o :=
      ⟨_, List.getElem?_eq_getElem hlt⟩
    constructor
    · intro h
      simp only [hget] at h
      cases o with
      | none =>
        simp only [Option.some.injEq] at h; subst h
        exact ⟨rfl, by simp [hget, memO]⟩
      | some m =>
        simp only at h
        by_cases hm : (kids S u m 0).isSome = true
        · simp only [hm, ite_true, Option.some.injEq] at h; subst h
          exact ⟨rfl, by simp [hget, memO, mem, hm]⟩
        · simp [hm] at h
    · rintro ⟨h1, h2⟩
      simp only [Option.some.injEq] at h1; subst h1
      simp only [hget]
      cases o with
      | none => rfl
      | some m =>
        simp only [hget, Option.getD_some, memO, mem] at h2
        simp [h2]

/-- Reading the arguments `args` after a function part `t`. -/
theorem kids_foldl {S : Decls} (n : Name) :
    ∀ (args : List GTerm) (t : GTerm) (extra : Nat) (ks : List (Option Name)),
      kids S (args.foldl .app t) n extra = some ks ↔
        kids S t n (extra + args.length) = some ks ∧
          ∀ i (h : i < args.length),
            memO S (ks[ks.length - extra - args.length + i]?.getD none) args[i] = true
  | [], t, extra, ks => by simp
  | a :: args, t, extra, ks => by
    rw [List.foldl_cons, kids_foldl n args (.app t a) extra ks, kids_app]
    have e1 : extra + args.length + 1 = extra + (a :: args).length := by simp; omega
    rw [e1]
    constructor
    · rintro ⟨⟨hk, h0⟩, hall⟩
      have hlen := kids_length hk
      simp only [List.length_cons] at hlen
      refine ⟨hk, ?_⟩
      intro i hi
      cases i with
      | zero =>
        have e : ks.length - extra - (a :: args).length + 0 = ks.length - (extra + args.length) - 1 := by
          simp only [List.length_cons]; omega
        rw [e]; simpa using h0
      | succ j =>
        have := hall j (by simpa using hi)
        have e : ks.length - extra - (a :: args).length + (j + 1) = ks.length - extra - args.length + j := by
          simp only [List.length_cons]; omega
        rw [e]; simpa using this
    · rintro ⟨hk, hall⟩
      have hlen := kids_length hk
      simp only [List.length_cons] at hlen
      refine ⟨⟨hk, ?_⟩, ?_⟩
      · have h0 := hall 0 (by simp)
        have e : ks.length - extra - (a :: args).length + 0 = ks.length - (extra + args.length) - 1 := by
          simp only [List.length_cons]; omega
        rw [e] at h0; simpa using h0
      · intro i hi
        have := hall (i + 1) (by simpa using hi)
        have e : ks.length - extra - (a :: args).length + (i + 1) = ks.length - extra - args.length + i := by
          simp only [List.length_cons]; omega
        rw [e] at this; simpa using this

/-- Membership of a surface term: the sort accepts the root, and every
argument is in the sort the root assigns to its position. -/
theorem mem_mk {S : Decls} {n : Name} {f : Sym} {ts : List GTerm} :
    mem S n (Term.mk f ts) = true ↔
      ∃ ks, step S n f ts.length = some ks ∧
        ∀ i (h : i < ts.length), memO S (ks[i]?.getD none) ts[i] = true := by
  unfold mem Term.mk
  rw [Option.isSome_iff_exists]
  constructor
  · rintro ⟨ks, h⟩
    rw [kids_foldl] at h
    simp only [kids, Nat.zero_add] at h
    refine ⟨ks, h.1, ?_⟩
    intro i hi
    have := h.2 i hi
    have hl := step_length h.1
    simpa [hl] using this
  · rintro ⟨ks, hs, hall⟩
    refine ⟨ks, ?_⟩
    rw [kids_foldl]
    simp only [kids, Nat.zero_add]
    refine ⟨hs, ?_⟩
    intro i hi
    have hl := step_length hs
    simpa [hl] using hall i hi

end Sorts
end RwLog
