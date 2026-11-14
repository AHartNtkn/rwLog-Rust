/-
# A normal store that is exponential in the declarations

The sorts `tower k` declare `k + 1` sorts: the numerals, and for each `j < k`
the pairs of two members of sort `j`. They are well formed (`tower_wf`): two
different sorts of the tower share no term and each is infinite. A member of
sort `k` is a full tree of pairs of depth `k` with a numeral at each of its
`2 ^ k` leaves (`T`).

The problem "`$x` is in sort `k`" is written with one variable and one sort.
Every normal store that denotes it has at least `2 ^ k` variables
(`blowup`), and the normal store is unique, so `Prob.norm` returns such a
store (`norm_blowup`). A variable of a normal store has two values with
different roots, so no variable can stand where every member has a pair;
below the pairs each leaf can be changed alone, so the leaves are distinct
variables.

So no program computes the normal store in time polynomial in the size of
the declarations and of the problem. What can be bounded is the time in
terms of the store returned.
-/
import RwLog.Sorts.Norm
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Card

namespace RwLog
namespace Sorts
namespace Blowup

/-! ## The terms -/

/-- The numeral `n`. -/
def num : Nat → GTerm
  | 0 => .sym "z"
  | n + 1 => .app (.sym "s") (num n)

/-- A pair. -/
def pr {V : Type} (a b : Term V) : Term V := .app (.app (.sym "pair") a) b

/-- The full trees of pairs of depth `j` with numerals at the leaves. -/
def T : Nat → GTerm → Prop
  | 0, g => ∃ n, g = num n
  | j + 1, g => ∃ a b, g = pr a b ∧ T j a ∧ T j b

/-- The tree of depth `j` with the numeral `n` at every leaf. -/
def full : Nat → Nat → GTerm
  | 0, n => num n
  | j + 1, n => pr (full j n) (full j n)

theorem T_full : ∀ j n, T j (full j n)
  | 0, n => ⟨n, rfl⟩
  | j + 1, n => ⟨_, _, rfl, T_full j n, T_full j n⟩

theorem num_inj : ∀ {n m : Nat}, num n = num m → n = m
  | 0, 0, _ => rfl
  | 0, m + 1, h => by simp [num] at h
  | n + 1, 0, h => by simp [num] at h
  | n + 1, m + 1, h => by
    simp only [num, Term.app.injEq, true_and] at h
    rw [num_inj h]

theorem full_inj : ∀ (j : Nat) {n m : Nat}, full j n = full j m → n = m
  | 0, _, _, h => num_inj h
  | j + 1, _, _, h => by
    simp only [full, pr, Term.app.injEq, true_and, and_self] at h
    exact full_inj j h

theorem T_infinite (j : Nat) : {g | T j g}.Infinite :=
  Set.infinite_of_injective_forall_mem (f := full j) (fun _ _ h => full_inj j h) (T_full j)

/-- A term is in one level of the tower at most. -/
theorem T_level : ∀ {j j' : Nat} {g : GTerm}, T j g → T j' g → j = j'
  | 0, 0, _, _, _ => rfl
  | 0, j' + 1, _, ⟨n, hn⟩, ⟨a, b, hg, _, _⟩ => by
    subst hn
    cases n <;> simp [num, pr] at hg
  | j + 1, 0, _, ⟨a, b, hg, _, _⟩, ⟨n, hn⟩ => by
    subst hn
    cases n <;> simp [num, pr] at hg
  | j + 1, j' + 1, _, ⟨a, b, hg, ha, _⟩, ⟨a', b', hg', ha', _⟩ => by
    subst hg
    simp only [pr, Term.app.injEq, true_and] at hg'
    rw [hg'.1] at ha
    rw [T_level ha ha']

theorem key_of_T {j : Nat} {g : GTerm} (h : T (j + 1) g) : g.key = some ("pair", 2) := by
  obtain ⟨a, b, rfl, -, -⟩ := h
  simp [Term.key, Term.spine, pr]

/-! ## The sorts -/

/-- The name of sort `j`. -/
def nm (j : Nat) : Name := String.ofList (List.replicate j 'p')

theorem nm_inj {i j : Nat} (h : nm i = nm j) : i = j := by
  have := congrArg String.length h
  simpa [nm] using this

/-- Sort 0 is the numerals; sort `j + 1` is the pairs of members of sort `j`. -/
def decl : Nat → SortDef
  | 0 => ⟨[("z", []), ("s", [some (nm 0)])], none⟩
  | j + 1 => ⟨[("pair", [some (nm j), some (nm j)])], none⟩

/-- The sorts `0` to `k`. -/
def tower : Nat → Sorts
  | 0 => [(nm 0, decl 0)]
  | k + 1 => (nm (k + 1), decl (k + 1)) :: tower k

theorem tower_length : ∀ k, (tower k).length = k + 1
  | 0 => rfl
  | k + 1 => by simp [tower, tower_length k]

theorem lookup_tower : ∀ (k : Nat) (n : Name) (d : SortDef),
    (tower k).lookup n = some d ↔ ∃ j, j ≤ k ∧ n = nm j ∧ d = decl j
  | 0, n, d => by
    simp only [tower, List.lookup_cons, List.lookup_nil]
    constructor
    · intro h
      split at h
      · next e => exact ⟨0, Nat.le_refl 0, by simpa using e, by simpa using h.symm⟩
      · cases h
    · rintro ⟨j, hj, rfl, rfl⟩
      obtain rfl : j = 0 := by omega
      simp
  | k + 1, n, d => by
    simp only [tower, List.lookup_cons]
    constructor
    · intro h
      split at h
      · next e => exact ⟨k + 1, Nat.le_refl _, by simpa using e, by simpa using h.symm⟩
      · obtain ⟨j, hj, e1, e2⟩ := (lookup_tower k n d).1 h
        exact ⟨j, by omega, e1, e2⟩
    · rintro ⟨j, hj, rfl, rfl⟩
      by_cases e : j = k + 1
      · subst e; simp
      · have hne : (nm j == nm (k + 1)) = false := by
          simp only [beq_eq_false_iff_ne, ne_eq]; exact fun h => e (nm_inj h)
        rw [hne]
        exact (lookup_tower k (nm j) (decl j)).2 ⟨j, by omega, rfl, rfl⟩

theorem step_zero {k : Nat} {f : Sym} {m : Nat} {ks : List (Option Name)} :
    step (tower k) (nm 0) f m = some ks ↔
      (f = "z" ∧ m = 0 ∧ ks = []) ∨ (f = "s" ∧ m = 1 ∧ ks = [some (nm 0)]) := by
  have hl : (tower k).lookup (nm 0) = some (decl 0) :=
    (lookup_tower k _ _).2 ⟨0, Nat.zero_le _, rfl, rfl⟩
  simp only [step, hl, Option.bind_some, SortDef.step, decl]
  by_cases h1 : f = "z" ∧ m = 0
  · obtain ⟨rfl, rfl⟩ := h1
    simp [List.find?, eq_comm]
  · by_cases h2 : f = "s" ∧ m = 1
    · obtain ⟨rfl, rfl⟩ := h2
      simp [List.find?, eq_comm]
    · have e1 : ¬ ("z" = f ∧ 0 = m) := fun h => h1 ⟨h.1.symm, h.2.symm⟩
      have e2 : ¬ ("s" = f ∧ 1 = m) := fun h => h2 ⟨h.1.symm, h.2.symm⟩
      simp only [List.find?]
      rw [show decide ("z" = f ∧ ([] : List (Option Name)).length = m) = false from
          decide_eq_false e1,
        show decide ("s" = f ∧ [some (nm 0)].length = m) = false from decide_eq_false e2]
      constructor
      · intro h; cases h
      · rintro (⟨a, b, -⟩ | ⟨a, b, -⟩)
        exacts [(h1 ⟨a, b⟩).elim, (h2 ⟨a, b⟩).elim]

theorem step_succ {k j : Nat} (hj : j + 1 ≤ k) {f : Sym} {m : Nat} {ks : List (Option Name)} :
    step (tower k) (nm (j + 1)) f m = some ks ↔
      f = "pair" ∧ m = 2 ∧ ks = [some (nm j), some (nm j)] := by
  have hl : (tower k).lookup (nm (j + 1)) = some (decl (j + 1)) :=
    (lookup_tower k _ _).2 ⟨j + 1, hj, rfl, rfl⟩
  simp only [step, hl, Option.bind_some, SortDef.step, decl]
  by_cases h1 : f = "pair" ∧ m = 2
  · obtain ⟨rfl, rfl⟩ := h1
    simp [List.find?, eq_comm]
  · have e1 : ¬ ("pair" = f ∧ 2 = m) := fun h => h1 ⟨h.1.symm, h.2.symm⟩
    simp only [List.find?]
    rw [show decide ("pair" = f ∧ [some (nm j), some (nm j)].length = m) = false from
      decide_eq_false e1]
    constructor
    · intro h; cases h
    · rintro ⟨a, b, -⟩
      exact (h1 ⟨a, b⟩).elim

/-- Sort `j` of the tower holds the trees of depth `j`. -/
theorem mem_tower {k : Nat} : ∀ (N : Nat) (g : GTerm) (j : Nat), g.size ≤ N → j ≤ k →
    (mem (tower k) (nm j) g = true ↔ T j g) := by
  intro N
  induction N with
  | zero =>
    intro g j hN
    cases g <;> simp [Term.size] at hN
  | succ N IH =>
    intro g j hN hj
    obtain ⟨f, ts, rfl, hsz⟩ := exists_mk g
    rw [mem_mk]
    cases j with
    | zero =>
      constructor
      · rintro ⟨ks, hs, hall⟩
        rcases step_zero.1 hs with ⟨rfl, hm, rfl⟩ | ⟨rfl, hm, rfl⟩
        · obtain rfl : ts = [] := List.length_eq_zero_iff.1 hm
          exact ⟨0, rfl⟩
        · obtain ⟨u, rfl⟩ := List.length_eq_one_iff.1 hm
          have hu := hall 0 (by simp)
          simp only [List.getElem?_cons_zero, Option.getD_some, List.getElem_cons_zero,
            memO] at hu
          have hlt := hsz u (by simp)
          obtain ⟨n, rfl⟩ := (IH u 0 (by omega) hj).1 hu
          exact ⟨n + 1, rfl⟩
      · rintro ⟨n, hn⟩
        cases n with
        | zero =>
          obtain ⟨rfl, rfl⟩ := Term.mk_inj (ys := []) hn
          exact ⟨[], step_zero.2 (.inl ⟨rfl, rfl, rfl⟩), by simp⟩
        | succ n =>
          obtain ⟨rfl, rfl⟩ := Term.mk_inj (ys := [num n]) hn
          refine ⟨[some (nm 0)], step_zero.2 (.inr ⟨rfl, rfl, rfl⟩), ?_⟩
          intro i hi
          obtain rfl : i = 0 := by simpa using hi
          have hlt := hsz (num n) (by simp)
          simpa [memO] using (IH (num n) 0 (by omega) hj).2 ⟨n, rfl⟩
    | succ j =>
      constructor
      · rintro ⟨ks, hs, hall⟩
        obtain ⟨rfl, hm, rfl⟩ := (step_succ hj).1 hs
        obtain ⟨a, b, rfl⟩ := List.length_eq_two.1 hm
        have ha := hall 0 (by simp)
        have hb := hall 1 (by simp)
        simp only [List.getElem?_cons_zero, Option.getD_some, List.getElem_cons_zero,
          memO] at ha
        simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.getD_some,
          List.getElem_cons_succ, List.getElem_cons_zero, memO] at hb
        have hla := hsz a (by simp)
        have hlb := hsz b (by simp)
        exact ⟨a, b, rfl, (IH a j (by omega) (by omega)).1 ha, (IH b j (by omega) (by omega)).1 hb⟩
      · rintro ⟨a, b, hg, ha, hb⟩
        obtain ⟨rfl, rfl⟩ := Term.mk_inj (ys := [a, b]) hg
        refine ⟨[some (nm j), some (nm j)], (step_succ hj).2 ⟨rfl, rfl, rfl⟩, ?_⟩
        have hla := hsz a (by simp)
        have hlb := hsz b (by simp)
        have ma := (IH a j (by omega) (by omega)).2 ha
        have mb := (IH b j (by omega) (by omega)).2 hb
        intro i hi
        have : i = 0 ∨ i = 1 := by simp at hi; omega
        rcases this with rfl | rfl
        · simpa [memO] using ma
        · simpa [memO] using mb

theorem mem_tower_iff {k j : Nat} (hj : j ≤ k) (g : GTerm) :
    mem (tower k) (nm j) g = true ↔ T j g :=
  mem_tower g.size g j (Nat.le_refl _) hj

/-- The tower is well formed: the terms in all of some of its sorts are none
or infinitely many. -/
theorem tower_wf (k : Nat) : (tower k).WellFormed := by
  intro ns
  by_cases h : ∃ j, j ≤ k ∧ ∀ n ∈ ns, n = nm j
  · obtain ⟨j, hj, hall⟩ := h
    refine .inr (.inr ((T_infinite j).mono ?_))
    intro g hg n hn
    rw [hall n hn]
    exact mem_iff_Mem.1 ((mem_tower_iff hj g).2 hg)
  · refine .inl (Set.eq_empty_iff_forall_notMem.2 fun g hg => h ?_)
    have key : ∀ n ∈ ns, ∃ j, j ≤ k ∧ n = nm j ∧ T j g := by
      intro n hn
      have hm := hg n hn
      have hd : ∃ d, (tower k).lookup n = some d := by
        cases hm with
        | case hl _ _ _ => exact ⟨_, hl⟩
        | rest hl _ _ _ _ => exact ⟨_, hl⟩
      obtain ⟨d, hd⟩ := hd
      obtain ⟨j, hj, rfl, -⟩ := (lookup_tower k n d).1 hd
      exact ⟨j, hj, rfl, (mem_tower_iff hj g).1 (mem_iff_Mem.2 hm)⟩
    cases ns with
    | nil => exact ⟨0, Nat.zero_le _, by simp⟩
    | cons n₀ ns =>
      obtain ⟨j₀, hj₀, rfl, hT₀⟩ := key n₀ (by simp)
      refine ⟨j₀, hj₀, fun n hn => ?_⟩
      obtain ⟨j, -, rfl, hT⟩ := key n hn
      rw [T_level hT hT₀]

/-! ## The leaves of a pattern that denotes the trees are distinct variables -/

/-- The first part of a pair. -/
def pl : Pat → Pat
  | .app (.app _ a) _ => a
  | t => t

/-- The second part of a pair. -/
def pr2 : Pat → Pat
  | .app _ b => b
  | t => t

/-- A pattern all of whose values are trees of depth `j + 1`, and whose
variables each have two values with different roots, is a pair. -/
theorem is_pair {Sg : Set (Nat → GTerm)} {V : Finset Nat}
    (htight : ∀ v ∈ V, ∃ σ ∈ Sg, ∃ σ' ∈ Sg, (σ v).key ≠ (σ' v).key) (hne : Sg.Nonempty)
    {j : Nat} {u : Pat} (hv : ∀ v ∈ u.vars, v ∈ V) (hT : ∀ σ ∈ Sg, T (j + 1) (u.bind σ)) :
    u = pr (pl u) (pr2 u) := by
  obtain ⟨σ₀, hσ₀⟩ := hne
  have same : ∀ v ∈ V, ∀ key, (∀ σ ∈ Sg, (σ v).key = some key) → False := by
    intro v hvV key hk
    obtain ⟨σ, hσ, σ', hσ', hne⟩ := htight v hvV
    exact hne ((hk σ hσ).trans (hk σ' hσ').symm)
  cases u with
  | var v =>
    exact (same v (hv v (by simp [Term.vars])) ("pair", 2) fun σ hσ => key_of_T (hT σ hσ)).elim
  | sym f =>
    obtain ⟨a, b, e, -, -⟩ := hT σ₀ hσ₀
    simp [pr] at e
  | app p q =>
    cases p with
    | var v =>
      refine (same v (hv v (by simp [Term.vars])) ("pair", 1) fun σ hσ => ?_).elim
      obtain ⟨a, b, e, -, -⟩ := hT σ hσ
      simp only [Term.bind_app, Term.bind_var, pr, Term.app.injEq] at e
      rw [e.1]; simp [Term.key, Term.spine]
    | sym f =>
      obtain ⟨a, b, e, -, -⟩ := hT σ₀ hσ₀
      simp [pr] at e
    | app p' a' =>
      cases p' with
      | var v =>
        refine (same v (hv v (by simp [Term.vars])) ("pair", 0) fun σ hσ => ?_).elim
        obtain ⟨a, b, e, -, -⟩ := hT σ hσ
        simp only [Term.bind_app, Term.bind_var, pr, Term.app.injEq] at e
        rw [e.1.1]; simp [Term.key, Term.spine]
      | sym f =>
        obtain ⟨a, b, e, -, -⟩ := hT σ₀ hσ₀
        simp only [Term.bind_app, Term.bind_sym, pr, Term.app.injEq, Term.sym.injEq] at e
        rw [e.1.1]; rfl
      | app _ _ =>
        obtain ⟨a, b, e, -, -⟩ := hT σ₀ hσ₀
        simp [pr] at e

/-- Patterns whose values are, independently, all the trees of depth `j`, and
whose variables each have two values with different roots, have `2 ^ j`
variables each. -/
theorem frontier {Sg : Set (Nat → GTerm)} {V : Finset Nat}
    (htight : ∀ v ∈ V, ∃ σ ∈ Sg, ∃ σ' ∈ Sg, (σ v).key ≠ (σ' v).key) :
    ∀ (j : Nat) (ι : Type) [Fintype ι] (us : ι → Pat),
      (∀ i, ∀ v ∈ (us i).vars, v ∈ V) → (∀ σ ∈ Sg, ∀ i, T j ((us i).bind σ)) →
      (∀ gs : ι → GTerm, (∀ i, T j (gs i)) → ∃ σ ∈ Sg, ∀ i, (us i).bind σ = gs i) →
      2 ^ j * Fintype.card ι ≤ V.card := by
  intro j
  induction j with
  | zero =>
    intro ι _ us hv _ hall
    classical
    obtain ⟨σ₀, -, h₀⟩ := hall (fun _ => num 0) fun _ => ⟨0, rfl⟩
    have h1 : ∀ i, ∃ σ ∈ Sg, ∀ i', (us i').bind σ = if i' = i then num 1 else num 0 := fun i =>
      hall (fun i' => if i' = i then num 1 else num 0) fun i' => by
        by_cases e : i' = i
        · exact ⟨1, by simp [e]⟩
        · exact ⟨0, by simp [e]⟩
    have hvar : ∀ i, ∃ x, us i = .var x := by
      intro i
      obtain ⟨σ, -, hσ⟩ := h1 i
      have e₀ := h₀ i
      have e₁ := hσ i
      simp only [↓reduceIte] at e₁
      cases hu : us i with
      | var x => exact ⟨x, rfl⟩
      | sym f => rw [hu] at e₁; simp [num] at e₁
      | app p q => rw [hu] at e₀; simp [num] at e₀
    choose x hx using hvar
    have hinj : Function.Injective x := by
      intro i i' e
      by_contra hne
      obtain ⟨σ, -, hσ⟩ := h1 i
      have e₁ := hσ i
      have e₂ := hσ i'
      rw [hx] at e₁ e₂
      have hne' : ¬ i' = i := Ne.symm hne
      simp only [Term.bind_var, ↓reduceIte, hne'] at e₁ e₂
      rw [e] at e₁
      have := num_inj (e₁.symm.trans e₂)
      omega
    have := Finset.card_le_card_of_injOn x (s := Finset.univ) (t := V)
      (fun i _ => hv i (x i) (by rw [hx]; simp [Term.vars])) fun a _ b _ h => hinj h
    simpa using this
  | succ j IH =>
    intro ι _ us hv hT hall
    have hne : Sg.Nonempty := by
      obtain ⟨σ, hσ, -⟩ := hall (fun _ => full (j + 1) 0) fun _ => T_full _ _
      exact ⟨σ, hσ⟩
    have hp : ∀ i, us i = pr (pl (us i)) (pr2 (us i)) := fun i =>
      is_pair htight hne (hv i) fun σ hσ => hT σ hσ i
    let us' : ι × Bool → Pat := fun p => if p.2 then pl (us p.1) else pr2 (us p.1)
    have key := IH (ι × Bool) us' ?_ ?_ ?_
    · have : Fintype.card (ι × Bool) = Fintype.card ι * 2 := by simp
      rw [this] at key
      rw [Nat.pow_succ, Nat.mul_assoc, Nat.mul_comm 2]
      exact key
    · rintro ⟨i, b⟩ v hvv
      refine hv i v ?_
      rw [hp i]
      cases b
      · simp only [us', Bool.false_eq_true, ↓reduceIte] at hvv
        simp [pr, Term.vars, hvv]
      · simp only [us', ↓reduceIte] at hvv
        simp [pr, Term.vars, hvv]
    · rintro σ hσ ⟨i, b⟩
      obtain ⟨a, c, e, ha, hc⟩ := hT σ hσ i
      rw [hp i] at e
      simp only [pr, Term.bind_app, Term.bind_sym, Term.app.injEq, true_and] at e
      cases b
      · simp only [us', Bool.false_eq_true, ↓reduceIte]; rw [e.2]; exact hc
      · simp only [us', ↓reduceIte]; rw [e.1]; exact ha
    · intro gs hgs
      obtain ⟨σ, hσ, h⟩ := hall (fun i => pr (gs (i, true)) (gs (i, false))) fun i =>
        ⟨_, _, rfl, hgs _, hgs _⟩
      refine ⟨σ, hσ, ?_⟩
      rintro ⟨i, b⟩
      have e := h i
      rw [hp i] at e
      simp only [pr, Term.bind_app, Term.bind_sym, Term.app.injEq, true_and] at e
      cases b
      · simp only [us', Bool.false_eq_true, ↓reduceIte]; exact e.2
      · simp only [us', ↓reduceIte]; exact e.1

/-! ## The normal store -/

/-- "`$x` is in sort `k`". -/
def prob (k : Nat) : Prob := ⟨.var 0, [], [(nm k, .var 0)], []⟩

theorem prob_fo (k : Nat) : (prob k).FO where
  t := rfl
  e := by intro p hp; simp [prob] at hp
  a := by intro a ha; simp only [prob, List.mem_singleton] at ha; subst ha; rfl
  x := by intro E hE; simp [prob] at hE

theorem prob_den (k : Nat) : (prob k).Den (tower k) = {g | T k g} := by
  ext g
  simp only [Prob.Den, Prob.Sol, prob, Set.mem_ofPred_eq, List.mem_singleton, forall_eq,
    Term.bind_var, List.not_mem_nil, false_imp_iff, implies_true, and_true]
  constructor
  · rintro ⟨σ, ⟨-, hm⟩, rfl⟩
    exact (mem_tower_iff (Nat.le_refl k) _).1 hm
  · intro hg
    exact ⟨fun _ => g, ⟨by simp [Eqns.Unifies], (mem_tower_iff (Nat.le_refl k) _).2 hg⟩, rfl⟩

/-- Every normal store that denotes the members of sort `k` of the tower has
`2 ^ k` variables at least. -/
theorem blowup (k : Nat) {r : Raw} (hr : r.Normal (tower k))
    (hden : r.store.Den (tower k) = {g | T k g}) : 2 ^ k ≤ r.c.length := by
  have key := frontier (Sg := r.store.Sol (tower k)) (V := Finset.range r.c.length)
    (fun v hv => hr.two v (Finset.mem_range.1 hv)) k Unit (fun _ => r.t)
    (fun _ v hv => Finset.mem_range.2 ((hr.len v).1 hv))
    (fun σ hσ _ => by
      have : r.t.bind σ ∈ r.store.Den (tower k) := ⟨σ, hσ, rfl⟩
      rw [hden] at this; exact this)
    (fun gs hgs => by
      have : gs () ∈ r.store.Den (tower k) := by rw [hden]; exact hgs ()
      obtain ⟨σ, hσ, e⟩ := this
      exact ⟨σ, hσ, fun _ => e.symm⟩)
  simpa using key

/-- The normal store of "`$x` is in sort `k`" over the `k + 1` sorts of the
tower has `2 ^ k` variables at least. -/
theorem norm_blowup (k : Nat) :
    ∃ r, (prob k).norm (tower k) (tower_wf k) = some r ∧ 2 ^ k ≤ r.c.length := by
  obtain ⟨r, hr, hden⟩ := Prob.normal (tower_wf k) (prob_fo k)
    (by rw [prob_den]; exact ⟨_, T_full k 0⟩)
  exact ⟨r, Prob.norm_unique (tower_wf k) (prob_fo k) hr hden,
    blowup k hr (hden.trans (prob_den k))⟩

end Blowup
end Sorts
end RwLog
