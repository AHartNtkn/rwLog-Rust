/-
# Constraint conformance cases, stated against the specification

The conformance cases from the Rust interpreter review
(`conformance/rust-interpreter-findings.md`, cases 2 and 4) that involve
constraints, stated per model where the answer is a family over models
(`c4_pin_at`, `c4_pinKeep_at`), and through the display projection
`ProgramOf.obs` (the pairs some model relates) where a pair is ruled out in
every model or kept in an intended one. They check that the
specification itself gives the intended answers, independently of any engine:

* a constraint no model allows removes the pair (`c2_nonzero_z`,
  `c2_different_pair_zz`, `c4_neq_self`, `c4_eq_and_neq`);
* a constraint some model allows keeps the pair, so the semantics does not
  remove too much (`c2_nonzero_sz`, `different_alone`; the model is the
  intended one, `stdModel`);
* constraints from different spans meet in the same model, so a multi-head
  rule can rule out a composition although each span alone is satisfiable
  (`stores_combine_across_seq`);
* an equation in a rule body restricts the span to the instances where it
  holds (`c4_pin`).

The theory is the case file's `eq_neq` in the agreed rule language (heads
only, no guards): the two guarded `nonzero` rules become
`(nonzero z) <=> fail.`.

Under the declarative reading a rule is an equivalence, so
`(pin $x) <=> $x = z.` already states that `(pin z)` holds. Writing the head
back, `(pin $x) <=> $x = z, (pin z).`, is not a restatement: it makes
`(pin z) ↔ (pin z)`, so it no longer forces `(pin z)`, and it gains the
models without any `pin` atom (`pinKeep_models_iff`). Whether a firing keeps
or drops `(pin z)` from a store is a question about how an engine computes,
not about what the program means.
-/
import RwLog.Theory.Firing

namespace RwLog.Conformance

open Term

def pv (n : Nat) : Pat := .var n
def ps (f : Sym) : Pat := .sym f
def pa (f : Sym) (args : List Pat) : Pat := Term.mk f args

/-- `eq_neq` from the case file, guards removed. -/
def eqNeq : Theory := [
  ⟨[pa "eq" [pv 0, pv 0]], .conj [] []⟩,
  ⟨[pa "eq" [ps "z", pa "s" [pv 0]]], .fail⟩,
  ⟨[pa "eq" [pa "s" [pv 0], ps "z"]], .fail⟩,
  ⟨[pa "eq" [pa "s" [pv 0], pa "s" [pv 1]]], .conj [] [pa "eq" [pv 0, pv 1]]⟩,
  ⟨[pa "neq" [pv 0, pv 0]], .fail⟩,
  ⟨[pa "neq" [ps "z", pa "s" [pv 0]]], .conj [] []⟩,
  ⟨[pa "neq" [pa "s" [pv 0], ps "z"]], .conj [] []⟩,
  ⟨[pa "neq" [pa "s" [pv 0], pa "s" [pv 1]]], .conj [] [pa "neq" [pv 0, pv 1]]⟩,
  ⟨[pa "eq" [pv 0, pv 1], pa "neq" [pv 0, pv 1]], .fail⟩,
  ⟨[pa "nonzero" [ps "z"]], .fail⟩]

theorem eqNeq_wellFormed : ∀ ρ ∈ eqNeq, ρ.WellFormed := by decide

def prog : Program := ⟨[], eqNeq⟩

/-- `[$q -> $q]` -/
def idQ : Rel := .rw (pv 0) (pv 0)
/-- `rel nonzero_ok { $x { (nonzero $x) } -> $x }` -/
def nonzeroOk : Rel := .rw (pv 0) (pv 0) [pa "nonzero" [pv 0]]
/-- `rel different { (pair $x $y) { (neq $x $y) } -> (pair $x $y) }` -/
def different : Rel :=
  .rw (pa "pair" [pv 0, pv 1]) (pa "pair" [pv 0, pv 1]) [pa "neq" [pv 0, pv 1]]

/-! ## Ground terms -/

def gz : GTerm := .sym "z"
def gs (t : GTerm) : GTerm := Term.mk "s" [t]
def gpair (a b : GTerm) : GTerm := Term.mk "pair" [a, b]
def gc (f : Sym) (args : List GTerm) : GTerm := Term.mk f args

theorem bind_mk {V W : Type} (σ : V → Term W) (f : Sym) (args : List (Term V)) :
    (Term.mk f args).bind σ = Term.mk f (args.map (Term.bind σ)) := by
  unfold Term.mk
  suffices ∀ (acc : Term V), (args.foldl Term.app acc).bind σ =
      (args.map (Term.bind σ)).foldl Term.app (acc.bind σ) by exact this _
  induction args with
  | nil => intro; rfl
  | cons x xs ih => intro acc; simp [ih]

theorem mk_eq_mk {V : Type} {f g : Sym} {xs ys : List (Term V)} :
    Term.mk f xs = Term.mk g ys ↔ f = g ∧ xs = ys :=
  ⟨Term.mk_inj, fun ⟨h₁, h₂⟩ => h₁ ▸ h₂ ▸ rfl⟩

theorem mk_ne_sym {V : Type} {f g : Sym} {x : Term V} {xs : List (Term V)} :
    Term.mk f (x :: xs) ≠ Term.sym g := by
  intro h
  have := congrArg Term.spine h
  simp [Term.spine_mk, Term.spine] at this

theorem sym_ne_mk {V : Type} {f g : Sym} {x : Term V} {xs : List (Term V)} :
    Term.sym g ≠ Term.mk f (x :: xs) := fun h => mk_ne_sym h.symm

/-- A rule of the theory holds in every model. -/
theorem rule {T : Theory} {M : Interp} (hM : T.Model M) {ρ : TRule} (hρ : ρ ∈ T)
    (hw : ρ.WellFormed) (σ : Nat → GTerm) :
    (∀ h ∈ ρ.heads, h.bind σ ∈ M) ↔ ρ.body.HoldsAt M σ :=
  (TRule.holdsIn_iff hw).1 (hM ρ hρ) σ

/-! ## The intended model of `eq_neq` -/

/-- `eq` is syntactic equality, `neq` is its negation, and `nonzero` holds
of every term other than `z`. -/
def stdModel : Interp :=
  {x | (∃ a, x = gc "eq" [a, a]) ∨ (∃ a b, a ≠ b ∧ x = gc "neq" [a, b]) ∨
    (∃ a, a ≠ gz ∧ x = gc "nonzero" [a])}

theorem mem_stdModel {x : GTerm} : x ∈ stdModel ↔ (∃ a, x = gc "eq" [a, a]) ∨
    (∃ a b, a ≠ b ∧ x = gc "neq" [a, b]) ∨ (∃ a, a ≠ gz ∧ x = gc "nonzero" [a]) := Iff.rfl

theorem stdModel_model : eqNeq.Model stdModel := by
  intro ρ hρ
  rw [TRule.holdsIn_iff (eqNeq_wellFormed ρ hρ)]
  intro σ
  simp only [eqNeq, List.mem_cons, List.not_mem_nil, or_false] at hρ
  rcases hρ with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [Body.HoldsAt, mem_stdModel, pa, ps, pv, gc, gz, bind_mk, mk_eq_mk, mk_ne_sym, sym_ne_mk]
  exact fun h => h.symm

/-! ## Case 2: a constraint is checked against the theory, not guessed -/

/-- `[$q -> $q] ; nonzero_ok ; @z` is empty. -/
theorem c2_nonzero_z : prog.obs (.seq idQ (.seq nonzeroOk (.at_ (ps "z")))) = ∅ := by
  apply Set.eq_empty_of_forall_notMem
  rintro ⟨a, b⟩ ⟨M, hM, m, -, m', ⟨σ, -, h₁, hc⟩, ⟨τ, h₂, -, -⟩⟩
  have hz := (rule hM (ρ := ⟨[pa "nonzero" [ps "z"]], .fail⟩) (by simp [prog, eqNeq]) (by decide)
    (fun _ => gz)).1
  apply hz
  simp only [ps, Term.bind_sym] at h₂
  have := hc _ List.mem_cons_self
  simp only [pa, pv, bind_mk, List.map, Term.bind_var] at this
  simp only [pv, Term.bind_var] at h₁
  simpa [pa, ps, bind_mk, ← h₁, h₂] using this

/-- `[$q -> $q] ; different ; @(pair z z)` is empty. -/
theorem c2_different_pair_zz :
    prog.obs (.seq idQ (.seq different (.at_ (pa "pair" [ps "z", ps "z"])))) = ∅ := by
  apply Set.eq_empty_of_forall_notMem
  rintro ⟨a, b⟩ ⟨M, hM, m, -, m', ⟨σ, -, h₁, hc⟩, ⟨τ, h₂, -, -⟩⟩
  have hn := (rule hM (ρ := ⟨[pa "neq" [pv 0, pv 0]], .fail⟩) (by simp [prog, eqNeq]) (by decide)
    (fun _ => gz)).1
  apply hn
  simp only [pa, ps, pv, bind_mk, List.map, Term.bind_var, Term.bind_sym] at h₁ h₂
  rw [h₂, mk_eq_mk] at h₁
  simp only [List.cons.injEq, true_and, and_true] at h₁
  have := hc _ List.mem_cons_self
  simp only [pa, pv, bind_mk, List.map, Term.bind_var] at this
  simpa [pa, pv, gz, bind_mk, ← h₁.1, ← h₁.2] using this

/-- `[$q -> $q] ; nonzero_ok ; @(s z)` relates `(s z)` to itself. -/
theorem c2_nonzero_sz :
    (gs gz, gs gz) ∈ prog.obs (.seq idQ (.seq nonzeroOk (.at_ (pa "s" [ps "z"])))) := by
  refine ⟨stdModel, stdModel_model, gs gz, ⟨fun _ => gs gz, ?_, ?_, ?_⟩, gs gz,
    ⟨fun _ => gs gz, ?_, ?_, ?_⟩, ⟨fun _ => gz, ?_, ?_, ?_⟩⟩ <;>
    simp [mem_stdModel, pa, pv, ps, gs, gc, gz, bind_mk, mk_eq_mk, mk_ne_sym]

/-! ## Case 4: a rule's own unsatisfiable constraints denote nothing -/

/-- `$x { (neq $x $x) } -> $x` is empty. -/
theorem c4_neq_self : prog.obs (.rw (pv 0) (pv 0) [pa "neq" [pv 0, pv 0]]) = ∅ := by
  apply Set.eq_empty_of_forall_notMem
  rintro ⟨a, b⟩ ⟨M, hM, σ, -, -, hc⟩
  exact (rule hM (ρ := ⟨[pa "neq" [pv 0, pv 0]], .fail⟩) (by simp [prog, eqNeq]) (by decide) σ).1
    (by simpa using hc)

/-- `(pair $x $y) { (eq $x $y), (neq $x $y) } -> $x` is empty. -/
theorem c4_eq_and_neq :
    prog.obs (.rw (pa "pair" [pv 0, pv 1]) (pv 0) [pa "eq" [pv 0, pv 1], pa "neq" [pv 0, pv 1]]) =
      ∅ := by
  apply Set.eq_empty_of_forall_notMem
  rintro ⟨a, b⟩ ⟨M, hM, σ, -, -, hc⟩
  exact (rule hM (ρ := ⟨[pa "eq" [pv 0, pv 1], pa "neq" [pv 0, pv 1]], .fail⟩)
    (by simp [prog, eqNeq]) (by decide) σ).1 (by simpa using hc)

/-- `(pair $x $y) { (neq $x $y) } -> $x` alone relates `(pair z (s z))` to `z`. -/
theorem different_alone :
    (gpair gz (gs gz), gz) ∈
      prog.obs (.rw (pa "pair" [pv 0, pv 1]) (pv 0) [pa "neq" [pv 0, pv 1]]) := by
  refine ⟨stdModel, stdModel_model, fun n => if n = 0 then gz else gs gz, ?_, ?_, ?_⟩ <;>
    simp [mem_stdModel, pa, pv, gpair, gs, gc, gz, bind_mk, mk_eq_mk, sym_ne_mk]

/-- `[(pair $x $y) { (eq $x $y) } -> (pair $x $y)] ; [(pair $x $y) { (neq $x $y) } -> $x]`
is empty: each span's constraint holds in some model alone, but `;` asks for
both in the same model, and `(eq $x $y), (neq $x $y) <=> fail` rules that
out. -/
theorem stores_combine_across_seq :
    prog.obs (.seq (.rw (pa "pair" [pv 0, pv 1]) (pa "pair" [pv 0, pv 1]) [pa "eq" [pv 0, pv 1]])
      (.rw (pa "pair" [pv 0, pv 1]) (pv 0) [pa "neq" [pv 0, pv 1]])) = ∅ := by
  apply Set.eq_empty_of_forall_notMem
  rintro ⟨a, b⟩ ⟨M, hM, m, ⟨σ₁, -, hm₁, hc₁⟩, ⟨σ₂, hm₂, -, hc₂⟩⟩
  simp only [pa, pv, bind_mk, List.map, Term.bind_var] at hm₁ hm₂
  rw [hm₁, mk_eq_mk] at hm₂
  simp only [List.cons.injEq, true_and, and_true] at hm₂
  have he := hc₁ _ List.mem_cons_self
  have hn := hc₂ _ List.mem_cons_self
  simp only [pa, pv, bind_mk, List.map, Term.bind_var] at he hn
  rw [← hm₂.1, ← hm₂.2] at hn
  exact (rule hM (ρ := ⟨[pa "eq" [pv 0, pv 1], pa "neq" [pv 0, pv 1]], .fail⟩)
    (by simp [prog, eqNeq]) (by decide) σ₁).1 (by simp [pa, pv, bind_mk, he, hn])

/-! ## Case 4: an equation in a rule body restricts the span

`(pin $x) <=> $x = z.` makes `(pin a)` hold exactly when `a` is `z`. -/

/-- `theory pin { (pin $x) <=> $x = z. }` -/
def pinTheory : Theory := [⟨[pa "pin" [pv 0]], .conj [(pv 0, ps "z")] []⟩]

theorem pinTheory_wellFormed : ∀ ρ ∈ pinTheory, ρ.WellFormed := by decide

def pinProg : Program := ⟨[], pinTheory⟩

/-- The models of `pin` are the interpretations in which `(pin a)` holds
exactly for `a = z`. -/
theorem pin_models_iff (M : Interp) :
    pinTheory.Model M ↔ ∀ a, gc "pin" [a] ∈ M ↔ a = gz := by
  constructor
  · intro hM a
    have := rule hM (ρ := ⟨[pa "pin" [pv 0]], .conj [(pv 0, ps "z")] []⟩) (by simp [pinTheory]) (by decide)
      (fun _ => a)
    simpa [Body.HoldsAt, pa, pv, ps, gc, gz, bind_mk] using this
  · intro h ρ hρ
    rw [TRule.holdsIn_iff (pinTheory_wellFormed ρ hρ)]
    intro σ
    simp only [pinTheory, List.mem_singleton] at hρ
    subst hρ
    simpa [Body.HoldsAt, pa, pv, ps, gc, gz, bind_mk] using h (σ 0)

/-- `(pair $x $y) { (pin $x) } -> $y` means exactly `(pair z $y) -> $y`. -/
theorem c4_pin :
    pinProg.obs (.rw (pa "pair" [pv 0, pv 1]) (pv 1) [pa "pin" [pv 0]]) =
      {p | ∃ b, p = (gpair gz b, b)} := by
  ext ⟨a, b⟩
  constructor
  · rintro ⟨M, hM, σ, rfl, rfl, hc⟩
    have hz := ((pin_models_iff M).1 hM (σ 0)).1 (by simpa [pa, pv, gc, bind_mk] using hc)
    exact ⟨σ 1, by simp [gpair, pa, pv, bind_mk, hz]⟩
  · rintro ⟨b, hb⟩
    simp only [Prod.mk.injEq] at hb
    obtain ⟨rfl, rfl⟩ := hb
    refine ⟨{gc "pin" [gz]}, (pin_models_iff _).2 fun a => by simp [gc, mk_eq_mk],
      fun n => if n = 0 then gz else b, ?_, ?_, ?_⟩ <;>
      simp [gpair, gc, pa, pv, bind_mk]

/-- In every model of `pin`, `(pair $x $y) { (pin $x) } -> $y` relates exactly
`(pair z b)` to `b`. -/
theorem c4_pin_at (M : Interp) (hM : pinTheory.Model M) :
    pinProg.semAt M (.rw (pa "pair" [pv 0, pv 1]) (pv 1) [pa "pin" [pv 0]]) =
      {p | ∃ b, p = (gpair gz b, b)} := by
  ext ⟨a, b⟩
  constructor
  · rintro ⟨σ, rfl, rfl, hc⟩
    have hz := ((pin_models_iff M).1 hM (σ 0)).1 (by simpa [pa, pv, gc, bind_mk] using hc)
    exact ⟨σ 1, by simp [gpair, pa, pv, bind_mk, hz]⟩
  · rintro ⟨b, hb⟩
    simp only [Prod.mk.injEq] at hb
    obtain ⟨rfl, rfl⟩ := hb
    have hp : Term.mk "pin" [gz] ∈ M := ((pin_models_iff M).1 hM gz).2 rfl
    refine ⟨fun n => if n = 0 then gz else b, ?_, ?_, ?_⟩ <;>
      simp [gpair, pa, pv, bind_mk, hp]

/-! ## Writing the head back is weaker, not the same

`(pin $x) <=> $x = z, (pin z).` reads: `(pin a)` holds exactly when `a` is
`z` and `(pin z)` holds. For `a = z` that is `(pin z) ↔ (pin z)`, which says
nothing, so this theory has two kinds of model: those where `(pin z)` holds
and those where no `pin` atom holds at all (`pinKeep_models_iff`). The empty
interpretation is a model of it but not of `pin` (`pinKeep_model_empty`,
`pin_not_model_empty`). Per model, the span is empty in the models without
`(pin z)` (`c4_pinKeep_at`); only the display projection `obs`, which asks
for some model, is unchanged (`c4_pinKeep`). -/

/-- `theory pin_keep { (pin $x) <=> $x = z, (pin z). }` -/
def pinKeep : Theory := [⟨[pa "pin" [pv 0]], .conj [(pv 0, ps "z")] [pa "pin" [ps "z"]]⟩]

theorem pinKeep_wellFormed : ∀ ρ ∈ pinKeep, ρ.WellFormed := by decide

def pinKeepProg : Program := ⟨[], pinKeep⟩

theorem pinKeep_models_iff (M : Interp) :
    pinKeep.Model M ↔ ∀ a, gc "pin" [a] ∈ M ↔ a = gz ∧ gc "pin" [gz] ∈ M := by
  constructor
  · intro hM a
    have := rule hM (ρ := ⟨[pa "pin" [pv 0]], .conj [(pv 0, ps "z")] [pa "pin" [ps "z"]]⟩)
      (by simp [pinKeep]) (by decide) (fun _ => a)
    simpa [Body.HoldsAt, pa, pv, ps, gc, gz, bind_mk] using this
  · intro h ρ hρ
    rw [TRule.holdsIn_iff (pinKeep_wellFormed ρ hρ)]
    intro σ
    simp only [pinKeep, List.mem_singleton] at hρ
    subst hρ
    simpa [Body.HoldsAt, pa, pv, ps, gc, gz, bind_mk] using h (σ 0)

theorem pinKeep_model_empty : pinKeep.Model ∅ :=
  (pinKeep_models_iff ∅).2 fun _ => by simp

theorem pin_not_model_empty : ¬ pinTheory.Model ∅ := fun h =>
  ((pin_models_iff ∅).1 h gz).2 rfl

/-- The span means the same under `pin_keep` as under `pin`. -/
theorem c4_pinKeep :
    pinKeepProg.obs (.rw (pa "pair" [pv 0, pv 1]) (pv 1) [pa "pin" [pv 0]]) =
      {p | ∃ b, p = (gpair gz b, b)} := by
  ext ⟨a, b⟩
  constructor
  · rintro ⟨M, hM, σ, rfl, rfl, hc⟩
    have hz := (((pinKeep_models_iff M).1 hM (σ 0)).1
      (by simpa [pa, pv, gc, bind_mk] using hc)).1
    exact ⟨σ 1, by simp [gpair, pa, pv, bind_mk, hz]⟩
  · rintro ⟨b, hb⟩
    simp only [Prod.mk.injEq] at hb
    obtain ⟨rfl, rfl⟩ := hb
    refine ⟨{gc "pin" [gz]}, (pinKeep_models_iff _).2 fun a => by simp [gc, mk_eq_mk],
      fun n => if n = 0 then gz else b, ?_, ?_, ?_⟩ <;>
      simp [gpair, gc, pa, pv, bind_mk]

/-- In a model of `pin_keep`, the span relates `(pair z b)` to `b` when
`(pin z)` holds in that model, and nothing otherwise. -/
theorem c4_pinKeep_at (M : Interp) (hM : pinKeep.Model M) :
    pinKeepProg.semAt M (.rw (pa "pair" [pv 0, pv 1]) (pv 1) [pa "pin" [pv 0]]) =
      {p | gc "pin" [gz] ∈ M ∧ ∃ b, p = (gpair gz b, b)} := by
  ext ⟨a, b⟩
  constructor
  · rintro ⟨σ, rfl, rfl, hc⟩
    obtain ⟨hz, hp⟩ := ((pinKeep_models_iff M).1 hM (σ 0)).1
      (by simpa [pa, pv, gc, bind_mk] using hc)
    exact ⟨hp, σ 1, by simp [gpair, pa, pv, bind_mk, hz]⟩
  · rintro ⟨hp, b, hb⟩
    simp only [Prod.mk.injEq] at hb
    obtain ⟨rfl, rfl⟩ := hb
    simp only [gc] at hp
    refine ⟨fun n => if n = 0 then gz else b, ?_, ?_, ?_⟩ <;>
      simp [gpair, pa, pv, bind_mk, hp]

end RwLog.Conformance
