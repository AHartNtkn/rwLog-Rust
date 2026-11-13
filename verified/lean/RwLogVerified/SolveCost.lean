/-
# What solving a list of equations costs

The Rust `solve_into` keeps its equations as a list in the store. `encEqs` is
that list as a term, so the facts about terms apply to it.

`solveCost E o` bounds the ticks `solve_into` spends on the equations `E`
with the output term `o`. With `L` the length of `E`, `D = dcount E o` the
number of distinct subterms of the equations and of `o`, and `V` the number
of distinct variables of `E`, it is

    10 + 8 D + 3 L + 12 lead + V (35 + 62 D + 28 L),    lead ≤ D.

The loop does three things. It drops an equation between a term and itself
(3 ticks). It splits an equation between two applications (9 ticks). It
eliminates a variable, which rebuilds every equation left and the output
(at most `35 + 22 D + 28 n` ticks when `n` equations are left).

* A variable is eliminated at most `V` times, because the eliminated variable
  is gone from every equation.
* Between two eliminations the loop splits at most `lead` times, and `lead`
  is at most `D` after an elimination.
* The list never has more than `L + D` equations (`Good.len`). The equations
  that splitting has added are the pending right halves along one path down
  a term, so there are no more of them than that term is high. `Good` is the
  invariant that says this; it survives an elimination because a term under
  another stays under it when a variable is replaced in both.

The bound is `O(V (D + L))`, and the loop does spend that much: an
elimination rebuilds every distinct subterm and every cell of the list, and
`x₁ = x₂, x₂ = x₃, …` eliminates a variable at every equation.
-/
import RwLog.Kernel.SolveFacts
import RwLog.Kernel.Subterms

namespace RwLogVerified

open RwLog RwLog.Term

variable {nm : Option Nat → Sym}

/-- A list of equations as a term. -/
def encEqs (nm : Option Nat → Sym) : Eqns Nat → Pat
  | [] => .sym (nm none)
  | p :: E => .app (.app p.1 p.2) (encEqs nm E)

theorem enc_subst (x : Nat) (u : Pat) (E : Eqns Nat) :
    (encEqs nm E).bind (single x u) = encEqs nm (Eqns.subst x u E) := by
  induction E with
  | nil => rfl
  | cons p E ih =>
    show _ = encEqs nm ((p.1.bind (single x u), p.2.bind (single x u)) :: Eqns.subst x u E)
    simp only [encEqs, Term.bind_app, ih]

/-- The nodes of the list itself: each suffix and each pair. -/
def spine (nm : Option Nat → Sym) : Eqns Nat → Finset Pat
  | [] => {.sym (nm none)}
  | p :: E => insert (encEqs nm (p :: E)) (insert (.app p.1 p.2) (spine nm E))

theorem card_spine_le (E : Eqns Nat) : (spine nm E).card ≤ 2 * E.length + 1 := by
  induction E with
  | nil => simp [spine]
  | cons p E ih =>
    simp only [spine, List.length_cons]
    have h1 := Finset.card_insert_le (encEqs nm (p :: E)) (insert (Term.app p.1 p.2) (spine nm E))
    have h2 := Finset.card_insert_le (Term.app p.1 p.2) (spine nm E)
    omega

theorem subs_enc_subset (E : Eqns Nat) : (encEqs nm E).subs ⊆ Eqns.subs E ∪ spine nm E := by
  induction E with
  | nil => simp [encEqs, spine, Term.subs]
  | cons p E ih =>
    intro w hw
    simp only [encEqs, Term.subs, Finset.mem_insert, Finset.mem_union] at hw
    simp only [Eqns.subs, spine, encEqs, Finset.mem_union, Finset.mem_insert]
    rcases hw with h | (h | h | h) | h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inl (Or.inl (Or.inl h))
    · exact Or.inl (Or.inl (Or.inr h))
    · rcases Finset.mem_union.1 (ih h) with h' | h'
      · exact Or.inl (Or.inr h')
      · exact Or.inr (Or.inr (Or.inr h'))

/-- The number of distinct subterms of the equations and of the output. -/
def dcount (E : Eqns Nat) (o : Pat) : Nat := (Eqns.subs E ∪ o.subs).card

theorem card_subs_enc_le (E : Eqns Nat) (o : Pat) :
    ((encEqs nm E).subs ∪ o.subs).card ≤ dcount E o + 2 * E.length + 1 := by
  have hsub : (encEqs nm E).subs ∪ o.subs ⊆ (Eqns.subs E ∪ o.subs) ∪ spine nm E := by
    intro w hw
    rcases Finset.mem_union.1 hw with h | h
    · rcases Finset.mem_union.1 (subs_enc_subset E h) with h' | h'
      · exact Finset.mem_union_left _ (Finset.mem_union_left _ h')
      · exact Finset.mem_union_right _ h'
    · exact Finset.mem_union_left _ (Finset.mem_union_right _ h)
  have h1 := Finset.card_le_card hsub
  have h2 := Finset.card_union_le (Eqns.subs E ∪ o.subs) (spine nm E)
  have h3 := card_spine_le (nm := nm) E
  unfold dcount
  omega

/-! ## Terms under terms -/

theorem height_le_of_mem_subs {t u : Pat} (h : u ∈ t.subs) : u.height ≤ t.height := by
  induction t with
  | var v => simp only [Term.subs, Finset.mem_singleton] at h; subst h; exact Nat.le_refl _
  | sym f => simp only [Term.subs, Finset.mem_singleton] at h; subst h; exact Nat.le_refl _
  | app a b iha ihb =>
    simp only [Term.subs, Finset.mem_insert, Finset.mem_union] at h
    rcases h with rfl | h | h
    · exact Nat.le_refl _
    · have := iha h; simp only [Term.height]; omega
    · have := ihb h; simp only [Term.height]; omega

theorem mem_subs_bind (σ : Nat → Pat) {t u : Pat} (h : u ∈ t.subs) :
    u.bind σ ∈ (t.bind σ).subs := by
  induction t with
  | var v => simp only [Term.subs, Finset.mem_singleton] at h; subst h; exact Term.self_mem_subs _
  | sym f => simp only [Term.subs, Finset.mem_singleton] at h; subst h; exact Term.self_mem_subs _
  | app a b iha ihb =>
    simp only [Term.subs, Finset.mem_insert, Finset.mem_union] at h
    rcases h with rfl | h | h
    · exact Term.self_mem_subs _
    · simp only [Term.bind_app, Term.subs, Finset.mem_insert, Finset.mem_union]
      exact Or.inr (Or.inl (iha h))
    · simp only [Term.bind_app, Term.subs, Finset.mem_insert, Finset.mem_union]
      exact Or.inr (Or.inr (ihb h))

/-- `g` is a subterm of `g'` and is not `g'`. -/
def Under (g g' : Pat) : Prop := ∃ a b, g' = .app a b ∧ (g ∈ a.subs ∨ g ∈ b.subs)

theorem Under.height_lt {g g' : Pat} (h : Under g g') : g.height < g'.height := by
  obtain ⟨a, b, rfl, h | h⟩ := h
  · have := height_le_of_mem_subs h; simp only [Term.height]; omega
  · have := height_le_of_mem_subs h; simp only [Term.height]; omega

theorem Under.mem {g g' : Pat} (h : Under g g') : g ∈ g'.subs := by
  obtain ⟨a, b, rfl, h | h⟩ := h <;> simp [Term.subs, h]

theorem Under.bind (σ : Nat → Pat) {g g' : Pat} (h : Under g g') :
    Under (g.bind σ) (g'.bind σ) := by
  obtain ⟨a, b, rfl, h | h⟩ := h
  · exact ⟨_, _, Term.bind_app _ _ _, Or.inl (mem_subs_bind σ h)⟩
  · exact ⟨_, _, Term.bind_app _ _ _, Or.inr (mem_subs_bind σ h)⟩

theorem Under.of_app {a b g : Pat} (h : Term.app a b ∈ g.subs) : Under a g := by
  cases g with
  | var v => simp [Term.subs] at h
  | sym f => simp [Term.subs] at h
  | app c d =>
    simp only [Term.subs, Finset.mem_insert, Finset.mem_union, Term.app.injEq] at h
    rcases h with ⟨rfl, rfl⟩ | h | h
    · exact ⟨_, _, rfl, Or.inl (Term.self_mem_subs _)⟩
    · exact ⟨_, _, rfl, Or.inl (Term.subs_app_left h)⟩
    · exact ⟨_, _, rfl, Or.inr (Term.subs_app_left h)⟩

/-! ## The equations that splitting has added -/

/-- `run` is a list of equations and `caps` a term for each. The left side of
each equation is a subterm of its term, and each term is under the next. -/
inductive Chain : Eqns Nat → List Pat → Prop
  | nil : Chain [] []
  | one {p : Pat × Pat} {g : Pat} : p.1 ∈ g.subs → Chain [p] [g]
  | cons {p q : Pat × Pat} {run : Eqns Nat} {g g' : Pat} {caps : List Pat} :
      p.1 ∈ g.subs → Under g g' → Chain (q :: run) (g' :: caps) →
      Chain (p :: q :: run) (g :: g' :: caps)

theorem Chain.caps_nil {caps : List Pat} (h : Chain [] caps) : caps = [] := by
  cases h; rfl

theorem Chain.uncons {p : Pat × Pat} {run : Eqns Nat} {caps : List Pat}
    (h : Chain (p :: run) caps) :
    ∃ g caps', caps = g :: caps' ∧ p.1 ∈ g.subs ∧ Chain run caps' := by
  cases h with
  | one h => exact ⟨_, _, rfl, h, .nil⟩
  | cons h _ hc => exact ⟨_, _, rfl, h, hc⟩

theorem Chain.rehead {p p' : Pat × Pat} {run : Eqns Nat} {g : Pat} {caps : List Pat}
    (h : Chain (p :: run) (g :: caps)) (hp : p'.1 ∈ g.subs) : Chain (p' :: run) (g :: caps) := by
  cases h with
  | one _ => exact .one hp
  | cons _ hu hc => exact .cons hp hu hc

theorem Chain.subst (x : Nat) (u : Pat) {run : Eqns Nat} {caps : List Pat} (h : Chain run caps) :
    Chain (Eqns.subst x u run) (caps.map (Term.bind (single x u))) := by
  induction h with
  | nil => exact .nil
  | one h => exact .one (mem_subs_bind _ h)
  | cons h hu _ ih => exact .cons (mem_subs_bind _ h) (hu.bind _) ih

theorem Chain.len_aux {run : Eqns Nat} {caps : List Pat} (h : Chain run caps) (n : Nat)
    (hn : ∀ g ∈ caps, g.height ≤ n) :
    ∀ g caps', caps = g :: caps' → run.length + g.height ≤ n + 1 := by
  induction h with
  | nil => intro g caps' e; cases e
  | @one p g0 _ =>
    intro g caps' e
    cases e
    have := hn g0 (by simp)
    simp only [List.length_cons, List.length_nil]
    omega
  | cons _ hu _ ih =>
    intro g caps' e
    cases e
    have h1 := ih (fun g hg => hn g (List.mem_cons_of_mem _ hg)) _ _ rfl
    have h2 := hu.height_lt
    simp only [List.length_cons] at h1 ⊢
    omega

/-- A chain is no longer than its terms are high. -/
theorem Chain.len {run : Eqns Nat} {caps : List Pat} (h : Chain run caps) (n : Nat)
    (hn : ∀ g ∈ caps, g.height ≤ n) : run.length ≤ n + 1 := by
  cases caps with
  | nil => cases h; simp
  | cons g caps' => have := h.len_aux n hn g caps' rfl; omega

/-! ## The invariant of the loop -/

theorem mem_eqns_subs {E : Eqns Nat} {w : Pat} :
    w ∈ Eqns.subs E ↔ ∃ p ∈ E, w ∈ p.1.subs ∨ w ∈ p.2.subs := by
  induction E with
  | nil => simp
  | cons p E ih =>
    obtain ⟨t, u⟩ := p
    simp only [Eqns.subs_cons, Finset.mem_union, ih, List.mem_cons, exists_eq_or_imp]

/-- The equations, the output and the terms of a chain, as one list of
equations: its subterms are what the loop counts. -/
def full (caps : List Pat) (o : Pat) (E : Eqns Nat) : Eqns Nat :=
  caps.map (fun g => (g, g)) ++ (o, o) :: E

theorem mem_full {caps : List Pat} {o : Pat} {E : Eqns Nat} {w : Pat} :
    w ∈ Eqns.subs (full caps o E) ↔
      (∃ g ∈ caps, w ∈ g.subs) ∨ w ∈ o.subs ∨ w ∈ Eqns.subs E := by
  simp only [mem_eqns_subs, full, List.mem_append, List.mem_map, List.mem_cons]
  constructor
  · rintro ⟨p, (⟨g, hg, rfl⟩ | rfl | hp), hw⟩
    · exact Or.inl ⟨g, hg, by tauto⟩
    · exact Or.inr (Or.inl (by tauto))
    · exact Or.inr (Or.inr ⟨p, hp, hw⟩)
  · rintro (⟨g, hg, hw⟩ | hw | ⟨p, hp, hw⟩)
    · exact ⟨(g, g), Or.inl ⟨g, hg, rfl⟩, Or.inl hw⟩
    · exact ⟨(o, o), Or.inr (Or.inl rfl), Or.inl hw⟩
    · exact ⟨p, Or.inr (Or.inr hp), hw⟩

theorem full_subst (x : Nat) (u : Pat) (caps : List Pat) (o : Pat) (E : Eqns Nat) :
    Eqns.subst x u (full caps o E) =
      full (caps.map (Term.bind (single x u))) (o.bind (single x u)) (Eqns.subst x u E) := by
  simp [full, Eqns.subst]

/-- The invariant: the equations are a chain followed by at most `L`
equations, and they, the output and the chain's terms have at most `D`
distinct subterms. -/
def Good (D L : Nat) (E : Eqns Nat) (o : Pat) : Prop :=
  ∃ run caps rest, E = run ++ rest ∧ Chain run caps ∧
    rest.length + (if run = [] then 0 else 1) ≤ L ∧ (Eqns.subs (full caps o E)).card ≤ D

theorem Good.init (E : Eqns Nat) (o : Pat) : Good (dcount E o) E.length E o := by
  refine ⟨[], [], E, rfl, .nil, by simp, Finset.card_le_card ?_⟩
  intro w hw
  rw [mem_full] at hw
  simp only [List.not_mem_nil, false_and, exists_false, false_or] at hw
  simp only [Finset.mem_union]
  tauto

theorem Good.dcount_le {D L : Nat} {E : Eqns Nat} {o : Pat} (h : Good D L E o) :
    dcount E o ≤ D := by
  obtain ⟨run, caps, rest, -, -, -, hD⟩ := h
  refine (Finset.card_le_card ?_).trans hD
  intro w hw
  rw [mem_full]
  simp only [Finset.mem_union] at hw
  tauto

theorem Good.lead_le {D L : Nat} {E : Eqns Nat} {o : Pat} (h : Good D L E o) :
    Eqns.lead E ≤ D :=
  ((Eqns.lead_le E).trans (Finset.card_le_card Finset.subset_union_left)).trans h.dcount_le

/-- The list is never longer than `L + D`. -/
theorem Good.len {D L : Nat} {E : Eqns Nat} {o : Pat} (h : Good D L E o) :
    E.length ≤ L + D := by
  obtain ⟨run, caps, rest, rfl, hC, hL, hD⟩ := h
  have hrun : run.length ≤ D := by
    cases D with
    | zero =>
      have h0 := Finset.card_eq_zero.1 (Nat.le_zero.1 hD)
      have : o ∈ Eqns.subs (full caps o (run ++ rest)) :=
        mem_full.2 (Or.inr (Or.inl (Term.self_mem_subs o)))
      rw [h0] at this
      cases this
    | succ n =>
      apply hC.len n
      intro g hg
      have h1 := Term.height_lt_card g
      have h2 : g.subs.card ≤ (Eqns.subs (full caps o (run ++ rest))).card :=
        Finset.card_le_card fun w hw => mem_full.2 (Or.inl ⟨g, hg, hw⟩)
      omega
  simp only [List.length_append]
  by_cases hr : run = []
  · subst hr; simp only [List.length_nil, ↓reduceIte] at hL ⊢; omega
  · simp only [hr, ↓reduceIte] at hL; omega

/-- Without its first equation the list is still a chain and a rest, and
counts no new subterm. -/
theorem Good.tail_core {L : Nat} {p : Pat × Pat} {E : Eqns Nat} {o : Pat} {run rest : Eqns Nat}
    {caps : List Pat} (he : p :: E = run ++ rest) (hC : Chain run caps)
    (hL : rest.length + (if run = [] then 0 else 1) ≤ L) :
    ∃ run' caps' rest', E = run' ++ rest' ∧ Chain run' caps' ∧
      rest'.length + (if run' = [] then 0 else 1) ≤ L ∧
      Eqns.subs (full caps' o E) ⊆ Eqns.subs (full caps o (p :: E)) := by
  cases run with
  | nil =>
    simp only [List.nil_append] at he
    subst he
    simp only [↓reduceIte, List.length_cons] at hL
    refine ⟨[], [], E, rfl, .nil, by simp only [↓reduceIte]; omega, ?_⟩
    intro w hw
    rw [mem_full] at hw ⊢
    simp only [List.not_mem_nil, false_and, exists_false, false_or] at hw
    rcases hw with hw | hw
    · exact Or.inr (Or.inl hw)
    · exact Or.inr (Or.inr (Eqns.subs_tail_subset p.1 p.2 E hw))
  | cons q run' =>
    simp only [List.cons_append, List.cons.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    obtain ⟨g, caps', rfl, -, hC'⟩ := hC.uncons
    simp only [reduceCtorEq, ↓reduceIte] at hL
    refine ⟨run', caps', rest, rfl, hC', by split <;> omega, ?_⟩
    intro w hw
    rw [mem_full] at hw ⊢
    rcases hw with ⟨g', hg', hw⟩ | hw | hw
    · exact Or.inl ⟨g', List.mem_cons_of_mem _ hg', hw⟩
    · exact Or.inr (Or.inl hw)
    · exact Or.inr (Or.inr (Eqns.subs_tail_subset p.1 p.2 _ hw))

theorem Good.skip {D L : Nat} {p : Pat × Pat} {E : Eqns Nat} {o : Pat} (h : Good D L (p :: E) o) :
    Good D L E o := by
  obtain ⟨run, caps, rest, he, hC, hL, hD⟩ := h
  obtain ⟨run', caps', rest', he', hC', hL', hS⟩ := Good.tail_core (o := o) he hC hL
  exact ⟨run', caps', rest', he', hC', hL', (Finset.card_le_card hS).trans hD⟩

theorem Good.split {D L : Nat} {a b c d : Pat} {E : Eqns Nat} {o : Pat}
    (h : Good D L ((Term.app a b, Term.app c d) :: E) o) :
    Good D L ((a, c) :: (b, d) :: E) o := by
  obtain ⟨run, caps, rest, he, hC, hL, hD⟩ := h
  have hsp := Eqns.subs_split_subset a b c d E
  cases run with
  | nil =>
    simp only [List.nil_append] at he
    subst he
    obtain rfl := hC.caps_nil
    simp only [↓reduceIte, List.length_cons] at hL
    refine ⟨[(a, c), (b, d)], [a, Term.app a b], E, rfl,
      .cons (Term.self_mem_subs a) ⟨a, b, rfl, Or.inl (Term.self_mem_subs a)⟩
        (.one (by simp [Term.subs, Term.self_mem_subs])),
      by simp only [reduceCtorEq, ↓reduceIte]; omega, (Finset.card_le_card ?_).trans hD⟩
    intro w hw
    rw [mem_full] at hw ⊢
    simp only [List.not_mem_nil, false_and, exists_false, false_or]
    rcases hw with ⟨g, hg, hw⟩ | hw | hw
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
      refine Or.inr ?_
      simp only [Eqns.subs_cons, Finset.mem_union]
      rcases hg with rfl | rfl
      · exact Or.inl (Or.inl (Term.subs_trans (by simp [Term.subs, Term.self_mem_subs]) hw))
      · exact Or.inl (Or.inl hw)
    · exact Or.inl hw
    · exact Or.inr (hsp hw)
  | cons q run' =>
    simp only [List.cons_append, List.cons.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    obtain ⟨g, caps', rfl, hg, -⟩ := hC.uncons
    have hg : Term.app a b ∈ g.subs := hg
    simp only [reduceCtorEq, ↓reduceIte] at hL
    refine ⟨(a, c) :: (b, d) :: run', a :: g :: caps', rest, rfl,
      .cons (Term.self_mem_subs a) (Under.of_app hg) (hC.rehead (Term.subs_app_right hg)),
      by simp only [reduceCtorEq, ↓reduceIte]; omega, (Finset.card_le_card ?_).trans hD⟩
    intro w hw
    rw [mem_full] at hw ⊢
    rcases hw with ⟨g', hg', hw⟩ | hw | hw
    · simp only [List.mem_cons] at hg'
      rcases hg' with rfl | hg'
      · exact Or.inl ⟨g, by simp, Term.subs_trans (Term.subs_app_left hg) hw⟩
      · exact Or.inl ⟨g', by simpa using hg', hw⟩
    · exact Or.inr (Or.inl hw)
    · exact Or.inr (Or.inr (hsp hw))

theorem Good.elim {D L : Nat} {x : Nat} {u t u' : Pat} {E : Eqns Nat} {o : Pat}
    (h : Good D L ((t, u') :: E) o) (hx : x ∉ u.vars)
    (hor : (t = Term.var x ∧ u' = u) ∨ (u' = Term.var x ∧ t = u)) :
    Good D L (Eqns.subst x u E) (o.bind (single x u)) := by
  obtain ⟨run, caps, rest, he, hC, hL, hD⟩ := h
  obtain ⟨run', caps', rest', rfl, hC', hL', hS⟩ := Good.tail_core (o := o) he hC hL
  have hhead : ∀ w, w ∈ t.subs ∨ w ∈ u'.subs →
      w ∈ Eqns.subs (full caps o ((t, u') :: (run' ++ rest'))) := fun w hw =>
    mem_full.2 (Or.inr (Or.inr (by simp only [Eqns.subs_cons, Finset.mem_union]; tauto)))
  have hlt := Eqns.card_subs_subst_lt (E := full caps' o (run' ++ rest')) hx hS
    (by rcases hor with ⟨rfl, _⟩ | ⟨rfl, _⟩
        · exact hhead _ (Or.inl (by simp [Term.subs]))
        · exact hhead _ (Or.inr (by simp [Term.subs])))
    (by intro w hw
        rcases hor with ⟨_, rfl⟩ | ⟨_, rfl⟩
        · exact hhead _ (Or.inr hw)
        · exact hhead _ (Or.inl hw))
  rw [full_subst] at hlt
  refine ⟨Eqns.subst x u run', caps'.map (Term.bind (single x u)), Eqns.subst x u rest',
    by simp [Eqns.subst], hC'.subst x u, ?_, by omega⟩
  have e1 : (Eqns.subst x u rest').length = rest'.length := by simp [Eqns.subst]
  have e2 : Eqns.subst x u run' = [] ↔ run' = [] := by simp [Eqns.subst]
  rw [e1]
  by_cases hr : run' = []
  · simpa [hr, Eqns.subst] using hL'
  · simpa [hr, e2] using hL'

/-! ## The bound -/

/-- What one elimination is charged in the bound, when the list never has
more than `M` equations. -/
def elimCharge (D M : Nat) : Nat := 35 + 34 * D + 28 * M

/-- The ticks the loop may still spend on the equations `E`, when there are
never more than `D` distinct subterms and never more than `M` equations. -/
def pot (D M : Nat) (E : Eqns Nat) : Nat :=
  10 + 8 * D + 3 * E.length + 12 * Eqns.lead E + (Eqns.varset E).card * elimCharge D M

theorem pot_ge (D M : Nat) (E : Eqns Nat) : 10 + 8 * D ≤ pot D M E := by
  unfold pot; omega

theorem pot_skip (D M : Nat) (t : Pat) (E : Eqns Nat) :
    pot D M E + 3 ≤ pot D M ((t, t) :: E) := by
  unfold pot
  rw [Eqns.lead_skip]
  have := Nat.mul_le_mul_right (elimCharge D M) (varset_tail_subset t t E)
  simp only [List.length_cons]
  omega

theorem pot_split (D M : Nat) {a b c d : Pat} (E : Eqns Nat) (h : Term.app a b ≠ Term.app c d) :
    pot D M ((a, c) :: (b, d) :: E) + 9 ≤ pot D M ((Term.app a b, Term.app c d) :: E) := by
  unfold pot
  have hl := Eqns.lead_split E h
  have := Nat.mul_le_mul_right (elimCharge D M) (varset_app_eq a b c d E)
  simp only [List.length_cons]
  omega

theorem pot_elim (D M : Nat) {x : Nat} {u t u' : Pat} (E : Eqns Nat) (hx : x ∉ u.vars)
    (hor : (t = Term.var x ∧ u' = u) ∨ (u' = Term.var x ∧ t = u))
    (hl : Eqns.lead (Eqns.subst x u E) ≤ D) :
    pot D M (Eqns.subst x u E) + (35 + 22 * D + 28 * M) ≤ pot D M ((t, u') :: E) := by
  have hv : (Eqns.varset (Eqns.subst x u E)).card + 1 ≤ (Eqns.varset ((t, u') :: E)).card := by
    apply Finset.card_lt_card
    rcases hor with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Eqns.varset_subst_ssubset hx (by simp [Term.vars])
    · exact Eqns.varset_subst_ssubset' hx (by simp [Term.vars])
  have hm := Nat.mul_le_mul_right (elimCharge D M) hv
  rw [Nat.add_mul, Nat.one_mul] at hm
  have el : (Eqns.subst x u E).length = E.length := by simp [Eqns.subst]
  unfold pot
  rw [el]
  simp only [List.length_cons]
  unfold elimCharge at hm ⊢
  omega

/-- A bound on the ticks `solve_into` spends. -/
def solveCost (E : Eqns Nat) (o : Pat) : Nat :=
  pot (dcount E o) (E.length + dcount E o) E

end RwLogVerified
