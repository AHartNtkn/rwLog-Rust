/-
# The constraint domain of sorts

`dom S` is the constraint domain (`Trusted/Domain.lean`) whose
representatives are the normal stores over a pair (`Rep S`,
`Sorts/Rep.lean`). Each operation builds the problem of its result and
returns its normal store (`Rep.of`, by `Prob.norm`). That is *the*
representative of the relation the operation names: there is at most one
(`Rep.ext_rel`), and there is one whenever the relation holds of some pair
(`exists_rep`). `dom_rep`, `dom_compose`, `dom_meet` and `dom_rightBound`
state each operation by the relation it represents (`Rep.mk?`), and the laws
are proved from those. Another program for an operation is correct when it
returns a normal store with the right denotation.

`dom_lawful`: for well-formed sorts the domain satisfies every law, in the
interpretation of the sorts.
-/
import RwLog.Sorts.Rep

namespace RwLog
namespace Sorts

open Function

variable {S : Sorts}

/-! ## Problems from one store and from two -/

/-- The problem of a raw store with another pattern. -/
def Raw.prob (r : Raw) (t : Pat) : Prob := ⟨t, [], r.atoms id, r.excl id⟩

theorem Raw.prob_sol (r : Raw) (t : Pat) (σ : Nat → GTerm) :
    σ ∈ (r.prob t).Sol S ↔ σ ∈ r.store.Sol S := by
  have h := r.sol_shift (S := S) id σ
  rw [comp_id] at h
  rw [← h]
  exact ⟨fun h' => h'.2, fun h' => ⟨fun p hp => by simp [Raw.prob] at hp, h'⟩⟩

/-- The problem of two raw stores, the variables of the second moved above
those of the first. -/
def Raw.prob₂ (a b : Raw) (t : Pat) (e : Eqns Nat) : Prob :=
  ⟨t, e, a.atoms id ++ b.atoms (· + a.c.length), a.excl id ++ b.excl (· + a.c.length)⟩

theorem Raw.prob₂_sol (a b : Raw) (t : Pat) (e : Eqns Nat) (σ : Nat → GTerm) :
    σ ∈ (a.prob₂ b t e).Sol S ↔
      Eqns.Unifies σ e ∧ σ ∈ a.store.Sol S ∧ σ ∘ (· + a.c.length) ∈ b.store.Sol S := by
  have h₁ := a.sol_shift (S := S) id σ
  have h₂ := b.sol_shift (S := S) (· + a.c.length) σ
  rw [comp_id] at h₁
  rw [← h₁, ← h₂]
  show (_ ∧ (∀ x ∈ _ ++ _, _) ∧ ∀ E ∈ _ ++ _, _) ↔ _
  rw [List.forall_mem_append, List.forall_mem_append]
  tauto

namespace Rep

/-- The left side. -/
def l (ρ : Rep S) : Pat := ρ.1.sides.1

/-- The right side. -/
def r (ρ : Rep S) : Pat := ρ.1.sides.2

theorem t_eq (ρ : Rep S) : ρ.1.t = tpair ρ.l ρ.r := by
  obtain ⟨a, b, hab⟩ := ρ.2.2.2
  rw [l, r, Raw.sides_of hab]; exact hab

theorem rel_eq (ρ : Rep S) :
    ρ.1.rel S = {p | ∃ σ ∈ ρ.1.store.Sol S, p.1 = ρ.l.bind σ ∧ p.2 = ρ.r.bind σ} :=
  Raw.rel_eq ρ.t_eq

theorem l_fo (ρ : Rep S) : ρ.l.firstOrder = true := by
  have := ρ.normal.fo; rw [ρ.t_eq, tpair_fo, Bool.and_eq_true] at this; exact this.1

theorem r_fo (ρ : Rep S) : ρ.r.firstOrder = true := by
  have := ρ.normal.fo; rw [ρ.t_eq, tpair_fo, Bool.and_eq_true] at this; exact this.2

theorem l_vars (ρ : Rep S) : ∀ v ∈ ρ.l.vars, v < ρ.1.c.length := fun v hv =>
  (ρ.normal.len v).1 (by rw [ρ.t_eq, tpair_vars]; exact List.mem_append_left _ hv)

theorem r_vars (ρ : Rep S) : ∀ v ∈ ρ.r.vars, v < ρ.1.c.length := fun v hv =>
  (ρ.normal.len v).1 (by rw [ρ.t_eq, tpair_vars]; exact List.mem_append_right _ hv)

theorem prob_fo (ρ : Rep S) {u w : Pat} (hu : u.firstOrder = true) (hw : w.firstOrder = true) :
    (ρ.1.prob (tpair u w)).FO :=
  ⟨by show (tpair u w).firstOrder = true; rw [tpair_fo, hu, hw]; rfl,
    fun p hp => by simp [Raw.prob] at hp, ρ.1.atoms_fo id, Raw.excl_fo ρ.normal id⟩

/-- The pairs the problem of a representative with another pair of patterns
denotes. -/
theorem prob_den (ρ : Rep S) (u w : Pat) :
    {p : GTerm × GTerm | tpair p.1 p.2 ∈ (ρ.1.prob (tpair u w)).Den S} =
      {p | ∃ σ ∈ ρ.1.store.Sol S, p.1 = u.bind σ ∧ p.2 = w.bind σ} := by
  ext p
  constructor
  · rintro ⟨σ, hσ, e⟩
    exact ⟨σ, (ρ.1.prob_sol _ σ).1 hσ, tpair_inj e⟩
  · rintro ⟨σ, hσ, e₁, e₂⟩
    exact ⟨σ, (ρ.1.prob_sol _ σ).2 hσ, by
      show _ = (tpair u w).bind σ
      rw [tpair_bind, e₁, e₂]⟩

/-- The representative of a pair of first-order patterns over the solutions
of a representative. -/
def one (ρ : Rep S) (u w : Pat) (hu : u.firstOrder = true) (hw : w.firstOrder = true) :
    Option (Rep S) :=
  Rep.of ρ.wf (ρ.1.prob (tpair u w)) (ρ.prob_fo hu hw) ⟨u, w, rfl⟩

theorem one_eq (ρ : Rep S) {u w : Pat} (hu : u.firstOrder = true) (hw : w.firstOrder = true) :
    ρ.one u w hu hw =
      Rep.mk? S {p | ∃ σ ∈ ρ.1.store.Sol S, p.1 = u.bind σ ∧ p.2 = w.bind σ} := by
  rw [one, Rep.of_eq, prob_den]

/-- A pair of first-order patterns over the solutions of a representative
has a representative. -/
theorem exists_one (ρ : Rep S) {u w : Pat} (hu : u.firstOrder = true) (hw : w.firstOrder = true) :
    ∃ ρ' : Rep S, ρ'.1.rel S =
      {p | ∃ σ ∈ ρ.1.store.Sol S, p.1 = u.bind σ ∧ p.2 = w.bind σ} := by
  obtain ⟨σ₀, hσ₀⟩ := ρ.normal.sol_nonempty ρ.wf
  obtain ⟨ρ', h⟩ := exists_rep ρ.wf (ρ.prob_fo hu hw) rfl
    ⟨_, σ₀, (ρ.1.prob_sol _ σ₀).2 hσ₀, rfl⟩
  exact ⟨ρ', h.trans (ρ.prob_den u w)⟩

/-- The substitution that is `σ₁` on the variables of the first of two
representatives and `σ₂` on those of the second, moved above them. -/
def join (a : Rep S) (σ₁ σ₂ : Nat → GTerm) : Nat → GTerm :=
  fun v => if v < a.1.c.length then σ₁ v else σ₂ (v - a.1.c.length)

theorem join_shift (a : Rep S) (σ₁ σ₂ : Nat → GTerm) :
    a.join σ₁ σ₂ ∘ (· + a.1.c.length) = σ₂ := by
  funext v
  simp [join]

theorem join_sol (a : Rep S) {σ₁ : Nat → GTerm} (σ₂ : Nat → GTerm) (h : σ₁ ∈ a.1.store.Sol S) :
    a.join σ₁ σ₂ ∈ a.1.store.Sol S :=
  Raw.Normal.sol_congr a.normal (fun v hv => by simp [join, hv]) h

theorem join_bind (a : Rep S) (σ₁ σ₂ : Nat → GTerm) {q : Pat}
    (hq : ∀ v ∈ q.vars, v < a.1.c.length) : q.bind (a.join σ₁ σ₂) = q.bind σ₁ :=
  Term.bind_congr fun v hv => by simp [join, hq v hv]

theorem join_rename (a : Rep S) (σ₁ σ₂ : Nat → GTerm) (q : Pat) :
    (q.rename (· + a.1.c.length)).bind (a.join σ₁ σ₂) = q.bind σ₂ := by
  rw [rename_bind, join_shift]

theorem prob₂_fo (a b : Rep S) {u w : Pat} {e : Eqns Nat} (hu : u.firstOrder = true)
    (hw : w.firstOrder = true) (he : e.FO) : (a.1.prob₂ b.1 (tpair u w) e).FO := by
  refine ⟨by show (tpair u w).firstOrder = true; rw [tpair_fo, hu, hw]; rfl, he, ?_, ?_⟩
  · intro x hx
    rcases List.mem_append.1 hx with hx | hx
    · exact a.1.atoms_fo _ x hx
    · exact b.1.atoms_fo _ x hx
  · intro E hE
    rcases List.mem_append.1 hE with hE | hE
    · exact Raw.excl_fo a.normal _ E hE
    · exact Raw.excl_fo b.normal _ E hE

/-- The pairs the problem of two representatives with equations and a pair of
patterns denotes. -/
theorem prob₂_den (a b : Rep S) (u w : Pat) (e : Eqns Nat) :
    {p : GTerm × GTerm | tpair p.1 p.2 ∈ (a.1.prob₂ b.1 (tpair u w) e).Den S} =
      {p | ∃ σ, (Eqns.Unifies σ e ∧ σ ∈ a.1.store.Sol S ∧
        σ ∘ (· + a.1.c.length) ∈ b.1.store.Sol S) ∧ p.1 = u.bind σ ∧ p.2 = w.bind σ} := by
  ext p
  constructor
  · rintro ⟨σ, hσ, e'⟩
    exact ⟨σ, (Raw.prob₂_sol _ _ _ _ σ).1 hσ, tpair_inj e'⟩
  · rintro ⟨σ, hσ, e₁, e₂⟩
    exact ⟨σ, (Raw.prob₂_sol _ _ _ _ σ).2 hσ, by
      show _ = (tpair u w).bind σ
      rw [tpair_bind, e₁, e₂]⟩

/-- The representative of a pair of first-order patterns over the pairs of
solutions of two representatives that satisfy first-order equations. -/
def two (a b : Rep S) (u w : Pat) (e : Eqns Nat) (hu : u.firstOrder = true)
    (hw : w.firstOrder = true) (he : e.FO) : Option (Rep S) :=
  Rep.of a.wf (a.1.prob₂ b.1 (tpair u w) e) (a.prob₂_fo b hu hw he) ⟨u, w, rfl⟩

theorem two_eq (a b : Rep S) {u w : Pat} {e : Eqns Nat} (hu : u.firstOrder = true)
    (hw : w.firstOrder = true) (he : e.FO) :
    a.two b u w e hu hw he = Rep.mk? S {p | ∃ σ, (Eqns.Unifies σ e ∧ σ ∈ a.1.store.Sol S ∧
      σ ∘ (· + a.1.c.length) ∈ b.1.store.Sol S) ∧ p.1 = u.bind σ ∧ p.2 = w.bind σ} := by
  rw [two, Rep.of_eq, prob₂_den]

/-- A pair of first-order patterns over the solutions of two representatives
that satisfy first-order equations has a representative, if some pair of
solutions satisfies the equations. -/
theorem exists_two (a b : Rep S) {u w : Pat} {e : Eqns Nat} (hu : u.firstOrder = true)
    (hw : w.firstOrder = true) (he : e.FO)
    (hne : ∃ σ, Eqns.Unifies σ e ∧ σ ∈ a.1.store.Sol S ∧ σ ∘ (· + a.1.c.length) ∈ b.1.store.Sol S) :
    ∃ ρ : Rep S, ρ.1.rel S = {p | ∃ σ, (Eqns.Unifies σ e ∧ σ ∈ a.1.store.Sol S ∧
      σ ∘ (· + a.1.c.length) ∈ b.1.store.Sol S) ∧ p.1 = u.bind σ ∧ p.2 = w.bind σ} := by
  obtain ⟨σ₀, hσ₀⟩ := hne
  obtain ⟨ρ, h⟩ := exists_rep a.wf (a.prob₂_fo b hu hw he) rfl
    ⟨_, σ₀, (Raw.prob₂_sol _ _ _ _ σ₀).2 hσ₀, rfl⟩
  exact ⟨ρ, h.trans (a.prob₂_den b u w e)⟩

/-! ## The representative of each operation exists -/

theorem swap_key (ρ : Rep S) :
    {p : GTerm × GTerm | ∃ σ ∈ ρ.1.store.Sol S, p.1 = ρ.r.bind σ ∧ p.2 = ρ.l.bind σ} =
      (ρ.1.rel S).inv := by
  rw [ρ.rel_eq]
  ext p
  constructor
  · rintro ⟨σ, hσ, e₁, e₂⟩; exact ⟨σ, hσ, e₂, e₁⟩
  · rintro ⟨σ, hσ, e₁, e₂⟩; exact ⟨σ, hσ, e₂, e₁⟩

theorem exists_swap (ρ : Rep S) : ∃ ρ' : Rep S, ρ'.1.rel S = (ρ.1.rel S).inv := by
  obtain ⟨ρ', h⟩ := ρ.exists_one ρ.r_fo ρ.l_fo
  exact ⟨ρ', h.trans ρ.swap_key⟩

theorem right_key (ρ : Rep S) :
    {p : GTerm × GTerm | ∃ σ ∈ ρ.1.store.Sol S, p.1 = ρ.r.bind σ ∧ p.2 = ρ.r.bind σ} =
      {p | p.2 = p.1 ∧ ∃ x, (x, p.1) ∈ ρ.1.rel S} := by
  rw [ρ.rel_eq]
  ext p
  constructor
  · rintro ⟨σ, hσ, e₁, e₂⟩; exact ⟨e₂.trans e₁.symm, _, σ, hσ, rfl, e₁⟩
  · rintro ⟨e, x, σ, hσ, -, e₂⟩; exact ⟨σ, hσ, e₂, e.trans e₂⟩

theorem exists_right (ρ : Rep S) :
    ∃ ρ' : Rep S, ρ'.1.rel S = {p | p.2 = p.1 ∧ ∃ x, (x, p.1) ∈ ρ.1.rel S} := by
  obtain ⟨ρ', h⟩ := ρ.exists_one ρ.r_fo ρ.r_fo
  exact ⟨ρ', h.trans ρ.right_key⟩

theorem comp_fo (a b : Rep S) :
    Eqns.FO [(a.r, b.l.rename (· + a.1.c.length))] := fun q hq => by
  rw [List.mem_singleton] at hq; subst hq
  exact ⟨a.r_fo, rename_fo b.l_fo _⟩

theorem comp_key (a b : Rep S) :
    (a.1.rel S).comp (b.1.rel S) =
    {p | ∃ σ, (Eqns.Unifies σ [(a.r, b.l.rename (· + a.1.c.length))] ∧ σ ∈ a.1.store.Sol S ∧
      σ ∘ (· + a.1.c.length) ∈ b.1.store.Sol S) ∧
      p.1 = a.l.bind σ ∧ p.2 = (b.r.rename (· + a.1.c.length)).bind σ} := by
  rw [a.rel_eq, b.rel_eq]
  ext p
  constructor
  · rintro ⟨m, ⟨σ₁, hσ₁, e₁, e₂⟩, σ₂, hσ₂, e₃, e₄⟩
    refine ⟨a.join σ₁ σ₂, ⟨?_, a.join_sol σ₂ hσ₁, by rw [a.join_shift]; exact hσ₂⟩, ?_, ?_⟩
    · intro q hq
      rw [List.mem_singleton] at hq; subst hq
      show a.r.bind _ = (b.l.rename _).bind _
      rw [a.join_bind _ _ a.r_vars, a.join_rename]
      exact e₂.symm.trans e₃
    · rw [a.join_bind _ _ a.l_vars]; exact e₁
    · rw [a.join_rename]; exact e₄
  · rintro ⟨σ, ⟨hu, h₁, h₂⟩, e₁, e₂⟩
    have hm := hu _ List.mem_cons_self
    simp only [rename_bind] at hm e₂
    exact ⟨a.r.bind σ, ⟨σ, h₁, e₁, rfl⟩, _, h₂, hm, e₂⟩

theorem exists_comp (a b : Rep S) (hne : ((a.1.rel S).comp (b.1.rel S)).Nonempty) :
    ∃ ρ : Rep S, ρ.1.rel S = (a.1.rel S).comp (b.1.rel S) := by
  rw [a.comp_key b] at hne ⊢
  obtain ⟨p, σ, hσ, -⟩ := hne
  exact a.exists_two b a.l_fo (rename_fo b.r_fo _) (a.comp_fo b) ⟨σ, hσ⟩

theorem meet_fo (a b : Rep S) :
    Eqns.FO [(a.l, b.l.rename (· + a.1.c.length)), (a.r, b.r.rename (· + a.1.c.length))] :=
  fun q hq => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact ⟨a.l_fo, rename_fo b.l_fo _⟩
    · exact ⟨a.r_fo, rename_fo b.r_fo _⟩

theorem meet_key (a b : Rep S) :
    a.1.rel S ∩ b.1.rel S =
    {p | ∃ σ, (Eqns.Unifies σ [(a.l, b.l.rename (· + a.1.c.length)),
        (a.r, b.r.rename (· + a.1.c.length))] ∧ σ ∈ a.1.store.Sol S ∧
      σ ∘ (· + a.1.c.length) ∈ b.1.store.Sol S) ∧ p.1 = a.l.bind σ ∧ p.2 = a.r.bind σ} := by
  rw [a.rel_eq, b.rel_eq]
  ext p
  constructor
  · rintro ⟨⟨σ₁, hσ₁, e₁, e₂⟩, σ₂, hσ₂, e₃, e₄⟩
    refine ⟨a.join σ₁ σ₂, ⟨?_, a.join_sol σ₂ hσ₁, by rw [a.join_shift]; exact hσ₂⟩, ?_, ?_⟩
    · intro q hq
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl
      · show a.l.bind _ = (b.l.rename _).bind _
        rw [a.join_bind _ _ a.l_vars, a.join_rename]
        exact e₁.symm.trans e₃
      · show a.r.bind _ = (b.r.rename _).bind _
        rw [a.join_bind _ _ a.r_vars, a.join_rename]
        exact e₂.symm.trans e₄
    · rw [a.join_bind _ _ a.l_vars]; exact e₁
    · rw [a.join_bind _ _ a.r_vars]; exact e₂
  · rintro ⟨σ, ⟨hu, h₁, h₂⟩, e₁, e₂⟩
    have hm₁ := hu _ List.mem_cons_self
    have hm₂ := hu _ (List.mem_cons_of_mem _ List.mem_cons_self)
    simp only [rename_bind] at hm₁ hm₂
    exact ⟨⟨σ, h₁, e₁, e₂⟩, _, h₂, e₁.trans hm₁, e₂.trans hm₂⟩

theorem exists_meet (a b : Rep S) (hne : (a.1.rel S ∩ b.1.rel S).Nonempty) :
    ∃ ρ : Rep S, ρ.1.rel S = a.1.rel S ∩ b.1.rel S := by
  rw [a.meet_key b] at hne ⊢
  obtain ⟨p, σ, hσ, -⟩ := hne
  exact a.exists_two b a.l_fo a.r_fo (a.meet_fo b) ⟨σ, hσ⟩

end Rep

/-! ## A span as written -/

/-- The sort a constraint puts a pattern in. -/
def atomOf : Pat → List (Name × Pat)
  | .app (.sym n) p => [(n, p)]
  | _ => []

/-- The exclusion a constraint is; a constraint that is neither a sort nor a
disequality never holds, and is the exclusion of no equations. -/
def exclOf : Pat → List (Eqns Nat)
  | .app (.sym _) _ => []
  | .app (.app (.sym f) p) q => if f = neSym then [[(p, q)]] else [[]]
  | _ => [[]]

theorem con_holds (c : Pat) (hc : c.isAtom = true) (σ : Nat → GTerm) :
    c.bind σ ∈ S.interp ↔
      (∀ a ∈ atomOf c, mem S a.1 (a.2.bind σ) = true) ∧ ∀ E ∈ exclOf c, ¬ Eqns.Unifies σ E := by
  have nil : Eqns.Unifies σ ([] : Eqns Nat) := fun p hp => by simp at hp
  cases c with
  | var v => simp [Term.isAtom] at hc
  | sym f =>
    simp only [Term.bind, exclOf, List.mem_singleton, forall_eq]
    exact ⟨fun h => h.elim, fun h => h.2 nil⟩
  | app c₁ q =>
    cases c₁ with
    | var w => simp [Term.isAtom, Term.firstOrder] at hc
    | sym n =>
      simp only [atomOf, exclOf, List.mem_singleton, forall_eq, List.not_mem_nil,
        IsEmpty.forall_iff, implies_true, and_true]
      exact mem_iff_Mem.symm
    | app c₂ p =>
      cases c₂ with
      | var w => simp [Term.isAtom, Term.firstOrder] at hc
      | sym f =>
        by_cases hf : f = neSym
        · subst hf
          simp only [atomOf, exclOf, List.not_mem_nil, IsEmpty.forall_iff, implies_true,
            true_and, ite_true, List.mem_singleton, forall_eq]
          constructor
          · intro h hu
            exact h.2 (hu (p, q) List.mem_cons_self)
          · intro h
            refine ⟨rfl, fun e => h fun x hx => ?_⟩
            rw [List.mem_singleton] at hx; subst hx; exact e
        · simp only [atomOf, exclOf, hf, ite_false, List.not_mem_nil, IsEmpty.forall_iff,
            implies_true, true_and, List.mem_singleton, forall_eq]
          exact ⟨fun h => absurd h.1 hf, fun h => absurd nil h⟩
      | app c₃ c₄ =>
        simp only [atomOf, exclOf, List.not_mem_nil, IsEmpty.forall_iff, implies_true,
          true_and, List.mem_singleton, forall_eq]
        exact ⟨fun h => h.elim, fun h => absurd nil h⟩

theorem atomOf_fo {c : Pat} (hc : c.isAtom = true) : ∀ a ∈ atomOf c, a.2.firstOrder = true := by
  intro a ha
  cases c with
  | var v => simp [atomOf] at ha
  | sym f => simp [atomOf] at ha
  | app c₁ q =>
    cases c₁ with
    | sym n =>
      simp only [atomOf, List.mem_singleton] at ha; subst ha
      simpa [Term.isAtom, Term.firstOrder] using hc
    | var w => simp [atomOf] at ha
    | app c₂ p => simp [atomOf] at ha

theorem exclOf_fo {c : Pat} (hc : c.isAtom = true) : ∀ E ∈ exclOf c, E.FO := by
  have nil : Eqns.FO ([] : Eqns Nat) := fun p hp => by simp at hp
  intro E hE
  cases c with
  | var v => simp only [exclOf, List.mem_singleton] at hE; subst hE; exact nil
  | sym f => simp only [exclOf, List.mem_singleton] at hE; subst hE; exact nil
  | app c₁ q =>
    cases c₁ with
    | sym n => simp [exclOf] at hE
    | var w => simp only [exclOf, List.mem_singleton] at hE; subst hE; exact nil
    | app c₂ p =>
      cases c₂ with
      | var w => simp only [exclOf, List.mem_singleton] at hE; subst hE; exact nil
      | app c₃ c₄ => simp only [exclOf, List.mem_singleton] at hE; subst hE; exact nil
      | sym f =>
        simp only [exclOf] at hE
        split at hE
        · rw [List.mem_singleton] at hE; subst hE
          intro x hx
          rw [List.mem_singleton] at hx; subst hx
          simpa [Term.isAtom, Term.firstOrder] using hc
        · rw [List.mem_singleton] at hE; subst hE; exact nil

/-- The problem of a span as written. -/
def spanProb (s : Span) : Prob := ⟨tpair s.l s.r, [], s.c.flatMap atomOf, s.c.flatMap exclOf⟩

theorem spanProb_fo {s : Span} (hfo : s.firstOrder = true) : (spanProb s).FO := by
  simp only [Span.firstOrder, Bool.and_eq_true, List.all_eq_true] at hfo
  obtain ⟨⟨hl, hr⟩, hc⟩ := hfo
  refine ⟨by show (tpair s.l s.r).firstOrder = true; rw [tpair_fo, hl, hr]; rfl,
    fun p hp => by simp [spanProb] at hp, ?_, ?_⟩
  · intro a ha
    obtain ⟨c, hcm, ha⟩ := List.mem_flatMap.1 ha
    exact atomOf_fo (hc c hcm) a ha
  · intro E hE
    obtain ⟨c, hcm, hE⟩ := List.mem_flatMap.1 hE
    exact exclOf_fo (hc c hcm) E hE

/-- The problem of a first-order span denotes the pairs the span relates. -/
theorem spanProb_den {s : Span} (hfo : s.firstOrder = true) :
    {p : GTerm × GTerm | tpair p.1 p.2 ∈ (spanProb s).Den S} = s.denAt S.interp := by
  simp only [Span.firstOrder, Bool.and_eq_true, List.all_eq_true] at hfo
  obtain ⟨-, hc⟩ := hfo
  have hsol : ∀ σ : Nat → GTerm, σ ∈ (spanProb s).Sol S ↔ ∀ c ∈ s.c, c.bind σ ∈ S.interp := by
    intro σ
    constructor
    · rintro ⟨-, ha, hx⟩ c hcm
      exact (con_holds c (hc c hcm) σ).2
        ⟨fun a h => ha a (List.mem_flatMap.2 ⟨c, hcm, h⟩),
          fun E h => hx E (List.mem_flatMap.2 ⟨c, hcm, h⟩)⟩
    · intro h
      refine ⟨fun p hp => by simp [spanProb] at hp, fun a ha => ?_, fun E hE => ?_⟩
      · obtain ⟨c, hcm, ha⟩ := List.mem_flatMap.1 ha
        exact ((con_holds c (hc c hcm) σ).1 (h c hcm)).1 a ha
      · obtain ⟨c, hcm, hE⟩ := List.mem_flatMap.1 hE
        exact ((con_holds c (hc c hcm) σ).1 (h c hcm)).2 E hE
  ext p
  constructor
  · rintro ⟨σ, hσ, e⟩
    obtain ⟨e₁, e₂⟩ := tpair_inj e
    exact ⟨σ, e₁, e₂, (hsol σ).1 hσ⟩
  · rintro ⟨σ, e₁, e₂, hσ⟩
    exact ⟨σ, (hsol σ).2 hσ, by show _ = (tpair s.l s.r).bind σ; rw [tpair_bind, e₁, e₂]⟩

/-- A first-order span that relates some pair has a representative. -/
theorem exists_span (hS : S.WellFormed) (s : Span) (hfo : s.firstOrder = true)
    (hne : (s.denAt S.interp).Nonempty) : ∃ ρ : Rep S, ρ.1.rel S = s.denAt S.interp := by
  obtain ⟨p, hp⟩ := hne
  rw [← spanProb_den (S := S) hfo] at hp ⊢
  exact exists_rep hS (spanProb_fo hfo) rfl ⟨_, hp⟩

/-! ## The domain -/

/-- There is no representative when the sorts are not well formed. -/
theorem Rep.mk?_of_not_wf (h : ¬ S.WellFormed) (X : PRel) : Rep.mk? S X = none := by
  cases hm : Rep.mk? S X with
  | none => rfl
  | some ρ => exact absurd ρ.wf h

namespace Rep

/-- The converse of a representative. -/
def conv (ρ : Rep S) : Rep S := (ρ.one ρ.r ρ.l ρ.r_fo ρ.l_fo).getD ρ

theorem conv_eq (ρ : Rep S) : ρ.conv = (Rep.mk? S (ρ.1.rel S).inv).getD ρ := by
  rw [conv, one_eq, swap_key]

/-- The composition of two representatives. -/
def compose (a b : Rep S) : Option (Rep S) :=
  a.two b a.l (b.r.rename (· + a.1.c.length)) [(a.r, b.l.rename (· + a.1.c.length))]
    a.l_fo (rename_fo b.r_fo _) (a.comp_fo b)

theorem compose_eq (a b : Rep S) :
    a.compose b = Rep.mk? S ((a.1.rel S).comp (b.1.rel S)) := by
  rw [compose, two_eq, ← comp_key]

/-- The meet of two representatives. -/
def meet (a b : Rep S) : Option (Rep S) :=
  a.two b a.l a.r [(a.l, b.l.rename (· + a.1.c.length)), (a.r, b.r.rename (· + a.1.c.length))]
    a.l_fo a.r_fo (a.meet_fo b)

theorem meet_eq (a b : Rep S) : a.meet b = Rep.mk? S (a.1.rel S ∩ b.1.rel S) := by
  rw [meet, two_eq, ← meet_key]

/-- The right interface of a representative. -/
def right (ρ : Rep S) : Option (Rep S) := ρ.one ρ.r ρ.r ρ.r_fo ρ.r_fo

theorem right_eq (ρ : Rep S) :
    ρ.right = Rep.mk? S {p | p.2 = p.1 ∧ ∃ x, (x, p.1) ∈ ρ.1.rel S} := by
  rw [right, one_eq, right_key]

end Rep

/-- The representative of a span as written. -/
def repOf (S : Sorts) (s : Span) : Option (Rep S) :=
  if hS : S.WellFormed then
    if hfo : s.firstOrder = true then
      Rep.of hS (spanProb s) (spanProb_fo hfo) ⟨s.l, s.r, rfl⟩
    else none
  else none

theorem repOf_eq (s : Span) :
    repOf S s = if s.firstOrder then Rep.mk? S (s.denAt S.interp) else none := by
  unfold repOf
  by_cases hS : S.WellFormed
  · by_cases hfo : s.firstOrder = true
    · simp only [hS, hfo, ↓reduceDIte, ↓reduceIte]
      rw [Rep.of_eq, spanProb_den hfo]
    · simp [hS, hfo]
  · simp only [hS, ↓reduceDIte]
    split
    · exact (Rep.mk?_of_not_wf hS _).symm
    · rfl

instance (S : Sorts) : Answer (Rep S) where
  den _ ρ := ρ.1.rel S
  swap ρ := ρ.conv
  den_swap _ ρ := by
    obtain ⟨ρ', h⟩ := ρ.exists_swap
    rw [Rep.conv_eq, ← h, Rep.mk?_rel]; rfl

/-- The constraint domain of the sorts `S`. Each operation computes the
normal store of a problem (`Prob.norm`), which is the one representative of
the pairs the operation is to relate. -/
def dom (S : Sorts) : Domain (Rep S) where
  rep s := repOf S s
  compose a b := a.compose b
  meet a b := a.meet b
  rightBound a := a.right
  isBound b := decide (b.l = b.r)
  covers a b := decide (a.meet b = some b)

theorem dom_rep (s : Span) :
    (dom S).rep s = if s.firstOrder then Rep.mk? S (s.denAt S.interp) else none := repOf_eq s

theorem dom_compose (a b : Rep S) :
    (dom S).compose a b = Rep.mk? S ((a.1.rel S).comp (b.1.rel S)) := a.compose_eq b

theorem dom_meet (a b : Rep S) : (dom S).meet a b = Rep.mk? S (a.1.rel S ∩ b.1.rel S) :=
  a.meet_eq b

theorem dom_rightBound (a : Rep S) :
    (dom S).rightBound a = Rep.mk? S {p | p.2 = p.1 ∧ ∃ x, (x, p.1) ∈ a.1.rel S} := a.right_eq

/-- The right interface of a representative is always a representative. -/
theorem rightBound_isSome (a : Rep S) : ((dom S).rightBound a).isSome = true := by
  obtain ⟨ρ', h⟩ := a.exists_right
  rw [dom_rightBound, ← h, Rep.mk?_rel]; rfl

/-- The right interface relates only right ends of a pair: it is exact. -/
theorem dom_rightBound_end (a b : Rep S) (h : (dom S).rightBound a = some b) :
    ∀ p ∈ Answer.den S.interp b, ∃ x, (x, p.1) ∈ Answer.den S.interp a := by
  intro p hp
  have hb : b.1.rel S = _ := Rep.mk?_some (dom_rightBound a ▸ h)
  have hp' : p ∈ b.1.rel S := hp
  rw [hb] at hp'
  exact hp'.2

/-- A representative always has a right interface, so with none every term
is a right end of a pair. -/
theorem dom_rightBound_none (a : Rep S) (h : (dom S).rightBound a = none) :
    ∀ z, ∃ x, (x, z) ∈ Answer.den S.interp a := by
  have := rightBound_isSome a
  rw [h] at this
  cases this

/-- L51. For well-formed sorts the domain satisfies the laws of a constraint
domain in the interpretation of the sorts. -/
theorem dom_lawful (hS : S.WellFormed) : (dom S).Lawful S.interp where
  live ρ := ρ.rel_nonempty
  canon a b h := Rep.ext_rel h
  rep_some s ρ h := by
    rw [dom_rep] at h
    split at h
    · exact Rep.mk?_some h
    · cases h
  rep_none s hfo h := by
    rw [dom_rep] at h
    simp only [hfo, ite_true] at h
    refine Set.not_nonempty_iff_eq_empty.1 fun hne => ?_
    obtain ⟨ρ, hρ⟩ := exists_span hS s hfo hne
    exact Rep.mk?_none h ρ hρ
  compose_some a b c h := Rep.mk?_some (dom_compose a b ▸ h)
  compose_none a b h := Set.not_nonempty_iff_eq_empty.1 fun hne => by
    obtain ⟨ρ, hρ⟩ := a.exists_comp b hne
    exact Rep.mk?_none (dom_compose a b ▸ h) ρ hρ
  meet_some a b c h := Rep.mk?_some (dom_meet a b ▸ h)
  meet_none a b h := Set.not_nonempty_iff_eq_empty.1 fun hne => by
    obtain ⟨ρ, hρ⟩ := a.exists_meet b hne
    exact Rep.mk?_none (dom_meet a b ▸ h) ρ hρ
  isBound_sub b hb p hp := by
    have e : b.l = b.r := by simpa [dom] using hb
    have hp' : p ∈ b.1.rel S := hp
    rw [b.rel_eq] at hp'
    obtain ⟨σ, -, e₁, e₂⟩ := hp'
    rw [e₁, e₂, e]
  rightBound_isBound a b h := by
    have hb : b.1.rel S = _ := Rep.mk?_some (dom_rightBound a ▸ h)
    show decide (b.l = b.r) = true
    rw [decide_eq_true_eq]
    by_contra hne
    obtain ⟨τ, hτ⟩ := exists_sep hne
    obtain ⟨σ, hσ, hD⟩ := b.normal.rich b.wf [(b.l, b.r)] (by
      intro p hp
      rw [List.mem_singleton] at hp; subst hp
      refine ⟨fun v hv => ?_, τ, hτ⟩
      rcases List.mem_append.1 hv with hv | hv
      · exact b.l_vars v hv
      · exact b.r_vars v hv)
    have hm : (b.l.bind σ, b.r.bind σ) ∈ b.1.rel S := by
      rw [b.rel_eq]; exact ⟨σ, hσ, rfl, rfl⟩
    rw [hb] at hm
    exact hD _ List.mem_cons_self hm.1.symm
  rightBound_mem a b h x y hxy := by
    have hb : b.1.rel S = _ := Rep.mk?_some (dom_rightBound a ▸ h)
    show (y, y) ∈ b.1.rel S
    rw [hb]; exact ⟨rfl, x, hxy⟩
  rightBound_end := dom_rightBound_end
  rightBound_none := dom_rightBound_none
  covers_iff a b := by
    show decide (a.meet b = some b) = true ↔ b.1.rel S ⊆ a.1.rel S
    rw [decide_eq_true_eq, Rep.meet_eq]
    constructor
    · intro h
      have := Rep.mk?_some h
      intro p hp
      rw [this] at hp; exact hp.1
    · intro h
      have : a.1.rel S ∩ b.1.rel S = b.1.rel S := Set.inter_eq_right.2 h
      rw [this, Rep.mk?_rel]

end Sorts
end RwLog
