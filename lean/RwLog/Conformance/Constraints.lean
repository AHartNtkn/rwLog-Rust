/-
# Constraint conformance cases, stated against the specification

The conformance cases from the Rust interpreter review
(`conformance/rust-interpreter-findings.md`, cases 2 and 4) that involve
constraints, stated as theorems about the observable relation `Program.obs`
and proved. They check that the specification itself gives the intended
answers, independently of any engine:

* a constraint refuted by the theory removes the pair (`c2_nonzero_z`,
  `c2_different_pair_zz`, `c4_neq_self`, `c4_eq_and_neq`);
* a constraint the theory cannot refute keeps the pair, so the semantics does
  not refute too much (`c2_nonzero_sz`, `different_alone`);
* stores carried by different spans combine under `;`, so a multi-head rule
  can refute the combination although each span alone is satisfiable
  (`stores_combine_across_seq`).

The theory is the case file's `eq_neq` in the agreed rule language (heads
only, no guards): the two guarded `nonzero` rules become
`(nonzero z) <=> fail.`, which refutes exactly the stores the guarded pair
was meant to refute. Case 4's `pin` theory, `(pin $x) <=> $x = z.`, uses an
equation in a rule body; `c4_pin` shows the span then means exactly its
instance with `$x` set to `z`.
-/
import RwLog.Trusted.Semantics

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

/-- Fire a `fail` rule whose single head instantiates to a member of the
store. -/
theorem refutes_of_single {T : Theory} {S : GStore} {ρ : TRule} (hρ : ρ ∈ T)
    (hb : ρ.body = .fail) (h : Pat) (hh : ρ.heads = [h]) (σ : Nat → GTerm)
    (hm : h.bind σ ∈ S) : Refutes T S :=
  .fail hρ σ hb ⟨by simp [TRule.headsAt, hh], by simp [TRule.headsAt, hh, hm]⟩

/-! ## Unpacking span denotations -/

theorem mem_span {s : Span} {a b : GTerm} {S : GStore} :
    (a, b, S) ∈ s.den ↔ ∃ σ : Nat → GTerm, a = s.l.bind σ ∧ b = s.r.bind σ ∧ S = s.c.at σ := by
  simp [Span.den]

/-! ## Case 2: a constraint is checked against the store, not guessed -/

/-- `[$q -> $q] ; nonzero_ok ; @z` is empty. -/
theorem c2_nonzero_z : prog.obs (.seq idQ (.seq nonzeroOk (.at_ (ps "z")))) = ∅ := by
  apply Set.eq_empty_of_forall_notMem
  rintro ⟨a, b⟩ ⟨S, ⟨m, S₁, S₂, -, ⟨m', S₃, S₄, h₃, h₄, h₅⟩, h₆⟩, hn⟩
  apply hn
  obtain ⟨σ₃, -, rfl, rfl⟩ := mem_span.1 h₃
  obtain ⟨σ₄, h₄, -, -⟩ := mem_span.1 h₄
  simp only [ps, Term.bind_sym] at h₄
  refine refutes_of_single (ρ := ⟨[pa "nonzero" [ps "z"]], .fail⟩) (by simp [prog, eqNeq])
    rfl _ rfl (fun _ => gz) ?_
  simp only [pv, Term.bind_var] at h₄
  simp only at h₅ h₆
  rw [h₆, h₅]
  simp [Store.at, pa, pv, ps, bind_mk, h₄]

/-- `[$q -> $q] ; different ; @(pair z z)` is empty. -/
theorem c2_different_pair_zz :
    prog.obs (.seq idQ (.seq different (.at_ (pa "pair" [ps "z", ps "z"])))) = ∅ := by
  apply Set.eq_empty_of_forall_notMem
  rintro ⟨a, b⟩ ⟨S, ⟨m, S₁, S₂, -, ⟨m', S₃, S₄, h₃, h₄, h₅⟩, h₆⟩, hn⟩
  apply hn
  obtain ⟨σ₃, -, h₃, hS₃⟩ := mem_span.1 h₃
  obtain ⟨σ₄, h₄, -, -⟩ := mem_span.1 h₄
  simp only [pa, pv, bind_mk, List.map, Term.bind_var] at h₃
  simp only [pa, ps, bind_mk, List.map, Term.bind_sym] at h₄
  rw [h₄, mk_eq_mk] at h₃
  simp only [List.cons.injEq, true_and] at h₃
  refine refutes_of_single (ρ := ⟨[pa "neq" [pv 0, pv 0]], .fail⟩) (by simp [prog, eqNeq])
    rfl _ rfl (fun _ => gz) ?_
  simp only at h₅ h₆
  rw [h₆, h₅, hS₃]
  simp [Store.at, pa, pv, bind_mk, ← h₃.1, ← h₃.2.1, gz]

/-- `[$q -> $q] ; nonzero_ok ; @(s z)` relates `(s z)` to itself: the store
`{(nonzero (s z))}` cannot be refuted. -/
theorem not_refutes_nonzero_sz : ¬ Refutes eqNeq {gc "nonzero" [gs gz]} := by
  intro h
  generalize hS : ({gc "nonzero" [gs gz]} : GStore) = S at h
  induction h with
  | fail hρ σ hb hf =>
    subst hS
    simp only [eqNeq, List.mem_cons, List.not_mem_nil, or_false] at hρ
    rcases hρ with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [reduceCtorEq] at hb <;>
      have := hf.2 _ List.mem_cons_self <;>
      simp [pa, ps, pv, gc, gs, gz, bind_mk, mk_eq_mk, sym_ne_mk] at this
  | eq hρ σ hb hf he hne =>
    simp only [eqNeq, List.mem_cons, List.not_mem_nil, or_false] at hρ
    rcases hρ with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [reduceCtorEq, Body.conj.injEq] at hb <;>
      (obtain ⟨rfl, -⟩ := hb; simp at he)
  | conj hρ σ hb hf _ _ _ =>
    subst hS
    simp only [eqNeq, List.mem_cons, List.not_mem_nil, or_false] at hρ
    rcases hρ with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [reduceCtorEq] at hb <;>
      have := hf.2 _ List.mem_cons_self <;>
      simp [pa, ps, pv, gc, gs, gz, bind_mk, mk_eq_mk] at this

theorem c2_nonzero_sz :
    (gs gz, gs gz) ∈ prog.obs (.seq idQ (.seq nonzeroOk (.at_ (pa "s" [ps "z"])))) := by
  refine ⟨{gc "nonzero" [gs gz]}, ⟨gs gz, ∅, {gc "nonzero" [gs gz]},
    ⟨fun _ => gs gz, ?_⟩, ⟨gs gz, {gc "nonzero" [gs gz]}, ∅,
      ⟨fun _ => gs gz, ?_⟩, ⟨fun _ => gz, ?_⟩, ?_⟩, ?_⟩, not_refutes_nonzero_sz⟩ <;>
    simp [Store.at, pa, pv, ps, gs, gc, gz, bind_mk]

/-! ## Case 4: a rule's own unsatisfiable store denotes nothing -/

/-- `$x { (neq $x $x) } -> $x` is empty. -/
theorem c4_neq_self : prog.obs (.rw (pv 0) (pv 0) [pa "neq" [pv 0, pv 0]]) = ∅ := by
  apply Set.eq_empty_of_forall_notMem
  rintro ⟨a, b⟩ ⟨S, h, hn⟩
  apply hn
  obtain ⟨σ, -, -, rfl⟩ := mem_span.1 h
  exact refutes_of_single (ρ := ⟨[pa "neq" [pv 0, pv 0]], .fail⟩) (by simp [prog, eqNeq])
    rfl _ rfl σ (by simp [Store.at])

/-- `(pair $x $y) { (eq $x $y), (neq $x $y) } -> $x` is empty: the two-head
rule fires on two distinct members of the store. -/
theorem c4_eq_and_neq :
    prog.obs (.rw (pa "pair" [pv 0, pv 1]) (pv 0) [pa "eq" [pv 0, pv 1], pa "neq" [pv 0, pv 1]]) =
      ∅ := by
  apply Set.eq_empty_of_forall_notMem
  rintro ⟨a, b⟩ ⟨S, h, hn⟩
  apply hn
  obtain ⟨σ, -, -, rfl⟩ := mem_span.1 h
  refine .fail (ρ := ⟨[pa "eq" [pv 0, pv 1], pa "neq" [pv 0, pv 1]], .fail⟩)
    (by simp [prog, eqNeq]) σ rfl ⟨?_, ?_⟩
  · simp [TRule.headsAt, pa, bind_mk, mk_eq_mk]
  · simp [TRule.headsAt, Store.at]

/-! ## Case 4: an equation in a rule body unifies the span

Equality is not a constraint: `(pin $x) <=> $x = z.` instantiates `$x` to
`z` in the span the rule fires in. On ground instances that means the
instances with `$x ≠ z` are refuted and the others keep no residual store. -/

/-- `theory pin { (pin $x) <=> $x = z. }` -/
def pinTheory : Theory := [⟨[pa "pin" [pv 0]], .conj [(pv 0, ps "z")] []⟩]

theorem pinTheory_wellFormed : ∀ ρ ∈ pinTheory, ρ.WellFormed := by decide

def pinProg : Program := ⟨[], pinTheory⟩

/-- The store `{(pin z)}` is not refuted: the equation holds and the head is
removed. -/
theorem not_refutes_pin_z : ¬ Refutes pinTheory {gc "pin" [gz]} := by
  intro h
  suffices ∀ S, Refutes pinTheory S → ¬ S ⊆ {gc "pin" [gz]} from this _ h le_rfl
  intro S h
  induction h with
  | fail hρ σ hb hf =>
    simp only [pinTheory, List.mem_singleton] at hρ
    subst hρ
    cases hb
  | eq hρ σ hb hf he hne =>
    intro hS
    simp only [pinTheory, List.mem_singleton] at hρ
    subst hρ
    simp only [Body.conj.injEq] at hb
    obtain ⟨rfl, rfl⟩ := hb
    have hm := hS (hf.2 _ List.mem_cons_self)
    simp [pa, pv, gc, bind_mk, mk_eq_mk] at hm
    simp only [List.mem_singleton] at he
    subst he
    exact hne (by simp [pv, ps, hm, gz])
  | conj hρ σ hb hf he _ ih =>
    intro hS
    apply ih
    intro x hx
    simp only [pinTheory, List.mem_singleton] at hρ
    subst hρ
    simp only [Body.conj.injEq] at hb
    obtain ⟨rfl, rfl⟩ := hb
    simp only [List.map_nil, List.toFinset_nil, Finset.mem_union, Finset.mem_sdiff,
      Finset.notMem_empty, or_false] at hx
    exact hS hx.1

/-- `(pair $x $y) { (pin $x) } -> $y` means exactly `(pair z $y) -> $y`. -/
theorem c4_pin :
    pinProg.obs (.rw (pa "pair" [pv 0, pv 1]) (pv 1) [pa "pin" [pv 0]]) =
      {p | ∃ b, p = (gpair gz b, b)} := by
  ext ⟨a, b⟩
  constructor
  · rintro ⟨S, h, hn⟩
    obtain ⟨σ, rfl, rfl, rfl⟩ := mem_span.1 h
    by_cases hz : σ 0 = gz
    · exact ⟨σ 1, by simp [gpair, pa, pv, bind_mk, hz]⟩
    · exact absurd (.eq (ρ := ⟨[pa "pin" [pv 0]], .conj [(pv 0, ps "z")] []⟩)
        (by simp [pinProg, pinTheory]) σ rfl ⟨by simp [TRule.headsAt],
          by simp [TRule.headsAt, Store.at]⟩ List.mem_cons_self (by simpa [pv, ps, gz] using hz)) hn
  · rintro ⟨b, hb⟩
    simp only [Prod.mk.injEq] at hb
    obtain ⟨rfl, rfl⟩ := hb
    refine ⟨{gc "pin" [gz]}, mem_span.2 ⟨fun n => if n = 0 then gz else b, ?_, ?_, ?_⟩,
      not_refutes_pin_z⟩ <;>
      simp [Store.at, gpair, gc, pa, pv, bind_mk]

/-! ## Firing replaces the head; keeping it means writing it back

`<=>` always replaces its heads by its body. A rule that should keep its
constraint writes it back: `(pin $x) <=> $x = z, (pin z).` The kept
constraint can then still meet another rule, here `(pin z), bad <=> fail.` -/

/-- `(pin $x) <=> $x = z, (pin z).` and `(pin z), bad <=> fail.` -/
def pinKeep : Theory := [
  ⟨[pa "pin" [pv 0]], .conj [(pv 0, ps "z")] [pa "pin" [ps "z"]]⟩,
  ⟨[pa "pin" [ps "z"], ps "bad"], .fail⟩]

theorem pinKeep_wellFormed : ∀ ρ ∈ pinKeep, ρ.WellFormed := by decide

/-- `{(pin z)}` is not refuted: firing the first rule rewrites it to itself. -/
theorem not_refutes_pinKeep_z : ¬ Refutes pinKeep {gc "pin" [gz]} := by
  intro h
  suffices ∀ S, Refutes pinKeep S → ¬ S ⊆ {gc "pin" [gz]} from this _ h le_rfl
  intro S h
  induction h with
  | fail hρ σ hb hf =>
    intro hS
    simp only [pinKeep, List.mem_cons, List.not_mem_nil, or_false] at hρ
    rcases hρ with rfl | rfl
    · cases hb
    · have hm := hS (hf.2 _ (List.mem_cons_of_mem _ List.mem_cons_self))
      simp [ps, gc, gz, sym_ne_mk] at hm
  | eq hρ σ hb hf he hne =>
    intro hS
    simp only [pinKeep, List.mem_cons, List.not_mem_nil, or_false] at hρ
    rcases hρ with rfl | rfl
    · simp only [Body.conj.injEq] at hb
      obtain ⟨rfl, rfl⟩ := hb
      have hm := hS (hf.2 _ List.mem_cons_self)
      simp [pa, pv, gc, bind_mk, mk_eq_mk] at hm
      simp only [List.mem_singleton] at he
      subst he
      exact hne (by simp [pv, ps, hm, gz])
    · cases hb
  | conj hρ σ hb hf _ _ ih =>
    intro hS
    simp only [pinKeep, List.mem_cons, List.not_mem_nil, or_false] at hρ
    rcases hρ with rfl | rfl
    · simp only [Body.conj.injEq] at hb
      obtain ⟨rfl, rfl⟩ := hb
      apply ih
      intro x hx
      simp only [Finset.mem_union, Finset.mem_sdiff, List.map_cons, List.map_nil,
        List.toFinset_cons, List.toFinset_nil, Finset.mem_insert, Finset.notMem_empty,
        or_false] at hx
      rcases hx with hx | rfl
      · exact hS hx.1
      · simp [pa, ps, gc, gz, bind_mk]
    · cases hb

/-- With the head written back, `(pair $x $y) { (pin $x) } -> $y` still means
exactly `(pair z $y) -> $y`. -/
theorem pinKeep_span :
    (⟨[], pinKeep⟩ : Program).obs (.rw (pa "pair" [pv 0, pv 1]) (pv 1) [pa "pin" [pv 0]]) =
      {p | ∃ b, p = (gpair gz b, b)} := by
  ext ⟨a, b⟩
  constructor
  · rintro ⟨S, h, hn⟩
    obtain ⟨σ, rfl, rfl, rfl⟩ := mem_span.1 h
    by_cases hz : σ 0 = gz
    · exact ⟨σ 1, by simp [gpair, pa, pv, bind_mk, hz]⟩
    · exact absurd (.eq (ρ := ⟨[pa "pin" [pv 0]], .conj [(pv 0, ps "z")] [pa "pin" [ps "z"]]⟩)
        (by simp [pinKeep]) σ rfl ⟨by simp [TRule.headsAt],
          by simp [TRule.headsAt, Store.at]⟩ List.mem_cons_self (by simpa [pv, ps, gz] using hz)) hn
  · rintro ⟨b, hb⟩
    simp only [Prod.mk.injEq] at hb
    obtain ⟨rfl, rfl⟩ := hb
    refine ⟨{gc "pin" [gz]}, mem_span.2 ⟨fun n => if n = 0 then gz else b, ?_, ?_, ?_⟩,
      not_refutes_pinKeep_z⟩ <;>
      simp [Store.at, gpair, gc, pa, pv, bind_mk]

/-- The kept `(pin z)` still meets `bad`: composing with a span that carries
`bad` refutes every instance. -/
theorem pinKeep_meets_bad :
    (⟨[], pinKeep⟩ : Program).obs
      (.seq (.rw (pa "pair" [pv 0, pv 1]) (pv 1) [pa "pin" [pv 0]]) (.rw (pv 0) (pv 0) [ps "bad"])) =
      ∅ := by
  apply Set.eq_empty_of_forall_notMem
  rintro ⟨a, b⟩ ⟨S, ⟨m, S₁, S₂, h₁, h₂, h₃⟩, hn⟩
  apply hn
  obtain ⟨σ₁, -, -, rfl⟩ := mem_span.1 h₁
  obtain ⟨σ₂, -, -, rfl⟩ := mem_span.1 h₂
  simp only at h₃
  subst h₃
  by_cases hz : σ₁ 0 = gz
  · -- the pin rule rewrites `(pin z)` to itself; `(pin z), bad <=> fail` fires
    refine .fail (ρ := ⟨[pa "pin" [ps "z"], ps "bad"], .fail⟩) (by simp [pinKeep])
      (fun _ => gz) rfl ⟨?_, ?_⟩
    · simp [TRule.headsAt, pa, ps, bind_mk, mk_ne_sym]
    · simp [TRule.headsAt, Store.at, pa, pv, ps, bind_mk, hz, gz]
  · exact .eq (ρ := ⟨[pa "pin" [pv 0]], .conj [(pv 0, ps "z")] [pa "pin" [ps "z"]]⟩)
      (by simp [pinKeep]) σ₁ rfl ⟨by simp [TRule.headsAt],
        by simp [TRule.headsAt, Store.at]⟩ List.mem_cons_self (by simpa [pv, ps, gz] using hz)

/-! ## Stores combine across composition -/

/-- `(pair $x $y) { (neq $x $y) } -> $x` alone relates `(pair z (s z))` to `z`. -/
theorem not_refutes_neq_z_sz : ¬ Refutes eqNeq {gc "neq" [gz, gs gz]} := by
  intro h
  -- Invariant: every store reached stays inside `{(neq z (s z))}`.
  suffices ∀ S, Refutes eqNeq S → ¬ S ⊆ {gc "neq" [gz, gs gz]} from this _ h le_rfl
  intro S h
  induction h with
  | fail hρ σ hb hf =>
    intro hS
    simp only [eqNeq, List.mem_cons, List.not_mem_nil, or_false] at hρ
    rcases hρ with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [reduceCtorEq] at hb <;>
      have := hS (hf.2 _ List.mem_cons_self) <;>
      simp [pa, ps, pv, gc, gs, gz, bind_mk, mk_eq_mk, mk_ne_sym] at this
    exact sym_ne_mk (this.1.symm.trans this.2)
  | eq hρ σ hb hf he hne =>
    intro _
    simp only [eqNeq, List.mem_cons, List.not_mem_nil, or_false] at hρ
    rcases hρ with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [reduceCtorEq, Body.conj.injEq] at hb <;>
      (obtain ⟨rfl, -⟩ := hb; simp at he)
  | conj hρ σ hb hf _ _ ih =>
    intro hS
    simp only [eqNeq, List.mem_cons, List.not_mem_nil, or_false] at hρ
    rcases hρ with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [reduceCtorEq, Body.conj.injEq] at hb <;>
      have hm := hS (hf.2 _ List.mem_cons_self)
    all_goals
      first
      | (simp [pa, ps, pv, gc, gs, gz, bind_mk, mk_eq_mk, mk_ne_sym] at hm; done)
      | (obtain ⟨rfl, rfl⟩ := hb
         apply ih
         intro x hx
         simp only [List.map_nil, List.toFinset_nil, Finset.mem_union, Finset.mem_sdiff, Finset.notMem_empty, or_false] at hx
         exact hS hx.1)

theorem different_alone :
    (gpair gz (gs gz), gz) ∈
      prog.obs (.rw (pa "pair" [pv 0, pv 1]) (pv 0) [pa "neq" [pv 0, pv 1]]) :=
  ⟨{gc "neq" [gz, gs gz]}, ⟨fun n => if n = 0 then gz else gs gz, by
    simp [Store.at, pa, pv, gpair, gc, bind_mk]⟩, not_refutes_neq_z_sz⟩

/-- `[(pair $x $y) { (eq $x $y) } -> (pair $x $y)] ; [(pair $x $y) { (neq $x $y) } -> $x]`
is empty: each span's store is satisfiable alone, but `;` combines them and
the rule `(eq $x $y), (neq $x $y) <=> fail` refutes the combination. -/
theorem stores_combine_across_seq :
    prog.obs (.seq (.rw (pa "pair" [pv 0, pv 1]) (pa "pair" [pv 0, pv 1]) [pa "eq" [pv 0, pv 1]])
      (.rw (pa "pair" [pv 0, pv 1]) (pv 0) [pa "neq" [pv 0, pv 1]])) = ∅ := by
  apply Set.eq_empty_of_forall_notMem
  rintro ⟨a, b⟩ ⟨S, ⟨m, S₁, S₂, h₁, h₂, h₃⟩, hn⟩
  apply hn
  obtain ⟨σ₁, -, hm₁, rfl⟩ := mem_span.1 h₁
  obtain ⟨σ₂, hm₂, -, rfl⟩ := mem_span.1 h₂
  simp only [pa, pv, bind_mk, List.map, Term.bind_var] at hm₁ hm₂
  rw [hm₁, mk_eq_mk] at hm₂
  simp only [List.cons.injEq, true_and, and_true] at hm₂
  refine .fail (ρ := ⟨[pa "eq" [pv 0, pv 1], pa "neq" [pv 0, pv 1]], .fail⟩)
    (by simp [prog, eqNeq]) σ₁ rfl ⟨?_, ?_⟩
  · simp [TRule.headsAt, pa, bind_mk, mk_eq_mk]
  · simp only at h₃
    rw [h₃]
    simp [TRule.headsAt, Store.at, pa, pv, bind_mk, hm₂.1, hm₂.2]

end RwLog.Conformance
