/-
# Pushing a sort down a pattern (`sorts::push_sort`)

`push_sort` returns the sorts the variables of a first-order pattern must be
in for an instance of the pattern to be in a sort, as `Sorts.push` of the
specification does (`Sorts.push_some`, `Sorts.push_none`): an instance is in
the sort exactly when it satisfies the atoms returned, and when nothing is
returned no instance is in the sort (`push_sort_spec`). Each atom is listed
once.

The proof is the proof of `member` with patterns for ground terms: the pairs
flagged in table `B` are closed under the step of their sort, a pair of a
variable has its atom on the list, and every pair asked about is in its sort
in every instance that is in the sort asked about.
-/
import RwLogVerified.Sorts
import RwLog.Sorts.Push

open Aeneas Aeneas.Std Result

namespace RwLogVerified

open rwlog_core RwLog

variable {nm : Option Nat → RwLog.Sym}

/-! ## The spine of a pattern -/

theorem unspine_foldl : ∀ (p : Pat) (acc : List Pat),
    acc.foldl .app p = (unspine p acc).2.foldl .app (unspine p acc).1
  | .var _, _ => rfl
  | .sym _, _ => rfl
  | .app g u, acc => by simpa [unspine] using unspine_foldl g (u :: acc)

theorem unspine_length : ∀ (p : Pat) (acc : List Pat),
    (unspine p acc).2.length = nargs p + acc.length
  | .var _, _ => by simp [unspine, nargs]
  | .sym _, _ => by simp [unspine, nargs]
  | .app g u, acc => by
    have := unspine_length g (u :: acc)
    simp only [unspine, nargs, List.length_cons] at this ⊢
    omega

theorem firstOrder_app {g u : Pat} (h : (Term.app g u).firstOrder = true) :
    g.firstOrder = true ∧ u.firstOrder = true ∧ ∀ v, g ≠ .var v := by
  cases g with
  | var x => simp [Term.firstOrder] at h
  | sym f => simp only [Term.firstOrder, Bool.true_and] at h; exact ⟨rfl, h, by simp⟩
  | app a b =>
    simp only [Term.firstOrder, Bool.and_eq_true] at h ⊢
    exact ⟨h.1, h.2, by simp⟩

/-- The head of a first-order pattern that is not a variable is a symbol. -/
theorem unspine_head : ∀ (p : Pat) (acc : List Pat), p.firstOrder = true → (∀ v, p ≠ .var v) →
    ∃ f, (unspine p acc).1 = .sym f
  | .var v, _, _, h => absurd rfl (h v)
  | .sym f, _, _, _ => ⟨f, rfl⟩
  | .app g u, acc, hfo, _ => by
    obtain ⟨h1, -, h3⟩ := firstOrder_app hfo
    simpa [unspine] using unspine_head g (u :: acc) h1 h3

/-- An argument of a pattern is a smaller subterm, and first-order when the
pattern is. -/
theorem unspine_mem : ∀ (p : Pat) (acc : List Pat) (a : Pat), a ∈ (unspine p acc).2 →
    a ∈ acc ∨ (a ∈ p.subs ∧ a.size < p.size ∧ (p.firstOrder = true → a.firstOrder = true))
  | .var _, _, _, h => Or.inl h
  | .sym _, _, _, h => Or.inl h
  | .app g u, acc, a, h => by
    rcases unspine_mem g (u :: acc) a h with h | ⟨h1, h2, h3⟩
    · rcases List.mem_cons.1 h with rfl | h
      · refine Or.inr ⟨?_, ?_, fun hfo => (firstOrder_app hfo).2.1⟩
        · simp only [Term.subs, Finset.mem_insert, Finset.mem_union]
          exact Or.inr (Or.inr (Term.self_mem_subs _))
        · simp only [Term.size]; omega
      · exact Or.inl h
    · refine Or.inr ⟨?_, ?_, fun hfo => h3 (firstOrder_app hfo).1⟩
      · simp only [Term.subs, Finset.mem_insert, Finset.mem_union]
        exact Or.inr (Or.inl h1)
      · simp only [Term.size]; omega

theorem bind_foldl (σ : Nat → GTerm) : ∀ (acc : List Pat) (t : Pat),
    (acc.foldl .app t).bind σ = (acc.map (Term.bind σ)).foldl .app (t.bind σ)
  | [], _ => rfl
  | a :: acc, t => by simpa using bind_foldl σ acc (.app t a)

/-- Membership of an instance of a pattern with a symbol at its head: the
sort has a step, and every argument with a sort has its instance in it. -/
theorem mem_unspine {S : Sorts} {n : Name} {p : Pat} {f : Sym} {args : List Pat}
    (h : unspine p [] = (.sym f, args)) (σ : Nat → GTerm) :
    Sorts.mem S n (p.bind σ) = true ↔
      ∃ ks, Sorts.step S n f args.length = some ks ∧
        ∀ m a, (some m, a) ∈ ks.zip args → Sorts.mem S m (a.bind σ) = true := by
  have hp : p = args.foldl .app (.sym f) := by
    have := unspine_foldl p []
    rw [h] at this
    simpa using this
  have hb : p.bind σ = Term.mk f (args.map (Term.bind σ)) := by
    rw [hp, bind_foldl]; rfl
  rw [hb, Sorts.mem_mk]
  simp only [List.length_map]
  constructor
  · rintro ⟨ks, hs, hall⟩
    refine ⟨ks, hs, ?_⟩
    intro m a hz
    obtain ⟨i, hi, e⟩ := List.mem_iff_getElem.1 hz
    rw [List.getElem_zip] at e
    simp only [List.length_zip, Nat.lt_min] at hi
    simp only [Prod.mk.injEq] at e
    have := hall i (by simpa using hi.2)
    rw [List.getElem?_eq_getElem hi.1, e.1] at this
    simpa [Sorts.memO, e.2] using this
  · rintro ⟨ks, hs, hz⟩
    refine ⟨ks, hs, ?_⟩
    intro i hi
    have hi' : i < args.length := by simpa using hi
    have hl := Sorts.step_length hs
    have hik : i < ks.length := by omega
    rw [List.getElem?_eq_getElem hik]
    cases hk : ks[i] with
    | none => simp [Sorts.memO]
    | some m =>
      simp only [Option.getD_some, Sorts.memO, List.getElem_map]
      apply hz m args[i]
      refine List.mem_iff_getElem.2 ⟨i, by simp only [List.length_zip, Nat.lt_min]; exact ⟨hik, hi'⟩, ?_⟩
      rw [List.getElem_zip, hk]

/-- Every pair of a set is in its sort in an instance that satisfies the
atoms, when each pair of the set is a variable with its atom, or has a step
and the pairs of its arguments are in the set. -/
theorem closed_holds {S : Sorts} (F : Name × Pat → Prop) (A : Sorts.Atoms)
    (h : ∀ x, F x → (∃ v, x.2 = .var v ∧ (v, x.1) ∈ A) ∨
      ∃ f args ks, unspine x.2 [] = (.sym f, args) ∧ Sorts.step S x.1 f args.length = some ks ∧
        ∀ m a, (some m, a) ∈ ks.zip args → F (m, a))
    (σ : Nat → GTerm) (hσ : Sorts.Atoms.Holds S A σ) :
    ∀ (k : Nat) (x : Name × Pat), x.2.size ≤ k → F x → Sorts.mem S x.1 (x.2.bind σ) = true := by
  intro k
  induction k with
  | zero =>
    intro x hk hx
    obtain ⟨m, p⟩ := x
    cases p <;> simp [Term.size] at hk
  | succ k ih =>
    intro x hk hx
    rcases h x hx with ⟨v, e, hv⟩ | ⟨f, args, ks, hu, hs, hall⟩
    · rw [e]; exact hσ (v, x.1) hv
    · refine (mem_unspine hu σ).2 ⟨ks, hs, fun m a hz => ?_⟩
      have ha := (List.of_mem_zip hz).2
      have hm := unspine_mem x.2 [] a (by rw [hu]; exact ha)
      rcases hm with h' | h'
      · cases h'
      · exact ih (m, a) (by simp only; omega) (hall m a hz)

/-! ## What the pairs not yet flagged may still cost -/

open Classical in
/-- What the members of `U` that `fl` does not hold of may still cost. -/
noncomputable def owedG {α : Type} (U : Finset α) (fl : α → Prop) (cost : α → Nat) : Nat :=
  (U.filter fun x => ¬ fl x).sum cost

theorem owedG_le_sum {α : Type} (U : Finset α) (fl : α → Prop) (cost : α → Nat) :
    owedG U fl cost ≤ U.sum cost := by
  classical
  exact Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)

theorem owedG_mono {α : Type} (U : Finset α) {fl fl' : α → Prop} (cost : α → Nat)
    (h : ∀ x, fl x → fl' x) : owedG U fl' cost ≤ owedG U fl cost := by
  classical
  apply Finset.sum_le_sum_of_subset
  intro x hx
  rw [Finset.mem_filter] at hx ⊢
  exact ⟨hx.1, fun hf => hx.2 (h x hf)⟩

theorem owedG_set {α : Type} {U : Finset α} {fl fl' : α → Prop} (cost : α → Nat) {x : α}
    (hx : x ∈ U) (hn : ¬ fl x) (hf : fl' x) (h : ∀ y, fl y → fl' y) :
    owedG U fl' cost + cost x ≤ owedG U fl cost := by
  classical
  have hxm : x ∈ U.filter fun y => ¬ fl y := Finset.mem_filter.2 ⟨hx, hn⟩
  have hsub : (U.filter fun y => ¬ fl' y) ⊆ (U.filter fun y => ¬ fl y).erase x := by
    intro y hy
    rw [Finset.mem_filter] at hy
    refine Finset.mem_erase.2 ⟨?_, Finset.mem_filter.2 ⟨hy.1, fun hfy => hy.2 (h y hfy)⟩⟩
    rintro rfl
    exact hy.2 hf
  have h1 : owedG U fl' cost ≤ ((U.filter fun y => ¬ fl y).erase x).sum cost :=
    Finset.sum_le_sum_of_subset hsub
  have h2 : ((U.filter fun y => ¬ fl y).erase x).sum cost + cost x =
      (U.filter fun y => ¬ fl y).sum cost := Finset.sum_erase_add _ _ hxm
  unfold owedG at h1 ⊢
  omega

theorem owedG_ge {α : Type} {U : Finset α} {fl : α → Prop} (cost : α → Nat) {x : α}
    (hx : x ∈ U) (hn : ¬ fl x) : cost x ≤ owedG U fl cost := by
  classical
  exact Finset.single_le_sum (f := cost) (fun _ _ => Nat.zero_le _)
    (Finset.mem_filter.2 ⟨hx, hn⟩)

/-! ## Is the node a variable? -/

theorem is_var_w (s : store.Store) (p : store.TermId) {q : Pat} (hI : Wf s)
    (hp : Repr nm s.nodes.val p.val q) (hroom : Room s 1) :
    sorts.is_var s p ⦃ b s' => (b = true ↔ ∃ v, q = .var v) ∧ KeptW s s' 1 ⦄ := by
  unfold sorts.is_var
  step with read_w s p hI hp.lt hroom as ⟨n, s1, hn, hK⟩
  cases hp with
  | var hv =>
    obtain ⟨m, hm, hvn⟩ := hv.node
    rw [hm] at hn
    cases hn
    cases n <;> simp_all [IsVarNode]
  | sym h => rw [h] at hn; cases hn; simp_all
  | nil h => rw [h] at hn; cases hn; simp_all
  | app h _ _ => rw [h] at hn; cases hn; simp_all

/-! ## The pairs of the loop -/

/-- The pair of a sort and a pattern, as the store has it. -/
def ppair (x : Name × Pat) : Pat := .app (.sym x.1) x.2

theorem ppair_inj {x y : Name × Pat} (h : ppair x = ppair y) : x = y := by
  obtain ⟨a, b⟩ := x
  obtain ⟨c, d⟩ := y
  simp only [ppair, Term.app.injEq, Term.sym.injEq] at h
  rw [h.1, h.2]

/-- An atom, as the store has it. -/
def atomPat (a : Nat × Name) : Pat := .app (.var a.1) (.sym a.2)

/-- A frame names the pair. -/
def PAt (nm : Option Nat → Sym) (nodes : List store.Node) (f : store.Frame)
    (x : Name × Pat) : Prop :=
  Repr nm nodes (fkey f) (.sym x.1) ∧ Repr nm nodes (faux f) x.2

theorem PAt.unique {nodes : List store.Node} {f : store.Frame} {x y : Name × Pat}
    (h : PAt nm nodes f x) (h' : PAt nm nodes f y) : x = y := by
  obtain ⟨a, b⟩ := x
  obtain ⟨c, d⟩ := y
  have e1 := Repr.unique h.1 h'.1
  have e2 := Repr.unique h.2 h'.2
  simp only [Term.sym.injEq] at e1
  simp only at e2
  rw [e1, e2]

theorem PAt.append {nodes : List store.Node} {f : store.Frame} {x : Name × Pat}
    (h : PAt nm nodes f x) (more : List store.Node) : PAt nm (nodes ++ more) f x :=
  ⟨h.1.append more, h.2.append more⟩

/-- The pair has a flagged node. -/
def PFl (nm : Option Nat → Sym) (nodes : List store.Node) (B : Nat → Option Nat)
    (x : Name × Pat) : Prop :=
  ∃ k, Repr nm nodes k (ppair x) ∧ B k ≠ none

/-- The pair waits on the stack. -/
def POn (nm : Option Nat → Sym) (nodes : List store.Node) (st : List store.Frame)
    (x : Name × Pat) : Prop :=
  ∃ f ∈ st, PAt nm nodes f x

/-- The pair is done: it is a variable with its atom on the list, or its
sort has a step on its pattern and the pair of each argument is flagged or
waits. -/
def PDone (nm : Option Nat → Sym) (S : Sorts) (nodes : List store.Node) (B : Nat → Option Nat)
    (st : List store.Frame) (A : Sorts.Atoms) (x : Name × Pat) : Prop :=
  (∃ v, x.2 = .var v ∧ (v, x.1) ∈ A) ∨
    ∃ f args ks, unspine x.2 [] = (.sym f, args) ∧ Sorts.step S x.1 f args.length = some ks ∧
      ∀ m a, (some m, a) ∈ ks.zip args → PFl nm nodes B (m, a) ∨ POn nm nodes st (m, a)

theorem PFl.mono {nodes more : List store.Node} {B B' : Nat → Option Nat} {x : Name × Pat}
    (h : PFl nm nodes B x) (hB : ∀ k, B k ≠ none → B' k ≠ none) : PFl nm (nodes ++ more) B' x := by
  obtain ⟨k, hk, hb⟩ := h
  exact ⟨k, hk.append more, hB k hb⟩

theorem PDone.mono {S : Sorts} {nodes more : List store.Node} {B B' : Nat → Option Nat}
    {st st' : List store.Frame} {A A' : Sorts.Atoms} {x : Name × Pat}
    (h : PDone nm S nodes B st A x) (hA : ∀ a ∈ A, a ∈ A')
    (hB : ∀ k, B k ≠ none → B' k ≠ none)
    (hst : ∀ y, POn nm nodes st y → PFl nm (nodes ++ more) B' y ∨ POn nm (nodes ++ more) st' y) :
    PDone nm S (nodes ++ more) B' st' A' x := by
  rcases h with ⟨v, e, hv⟩ | ⟨f, args, ks, hu, hs, hall⟩
  · exact Or.inl ⟨v, e, hA _ hv⟩
  · refine Or.inr ⟨f, args, ks, hu, hs, ?_⟩
    intro m a hz
    rcases hall m a hz with h | h
    · exact Or.inl (h.mono hB)
    · exact hst _ h

/-- Every instance in the sort asked about has the pair's pattern in the
pair's sort. -/
def Reach (S : Sorts) (n0 : Name) (p0 : Pat) (x : Name × Pat) : Prop :=
  ∀ σ : Nat → GTerm, Sorts.mem S n0 (p0.bind σ) = true → Sorts.mem S x.1 (x.2.bind σ) = true

/-- The ticks a pair may cost: its step, reading its arguments and putting
them on the stack, and taking each of them off again; or its atom. -/
def ppCost (S : Sorts) (p : Pat) : Nat := sortsCost S + 11 * nargs p + 8

/-- What the pairs with no flagged node may still cost. -/
noncomputable def owedP (nm : Option Nat → Sym) (S : Sorts) (nodes : List store.Node)
    (B : Nat → Option Nat) (U : Finset (Name × Pat)) : Nat :=
  owedG U (PFl nm nodes B) fun x => ppCost S x.2

/-! ## The loop -/

/-- The invariant of the loop of `push_sort`. Every frame names a pair of
the universe `U` with a first-order pattern. The list holds each atom once,
and the pair of each is flagged. While no step has failed, every flagged pair
is done and the pair asked about is flagged or waits; `B` covers the ticks
spent and the ticks the pairs still owe. After a step has failed the stack is
empty and no instance is in the sort. -/
def PushInv (nm : Option Nat → Sym) (S : Sorts) (U : Finset (Name × Pat)) (n0 : Name) (p0 : Pat)
    (s0 : store.Store) (B : Nat) : store.Store × store.TermId × Bool → Prop
  | (s, atoms, ok) => Wf s ∧ Extends s0 s ∧ tbl s .A = tbl s0 .A ∧
    (∀ f ∈ stk s, ∃ x ∈ U, PAt nm s.nodes.val f x ∧ x.2.firstOrder = true ∧ Reach S n0 p0 x) ∧
    ∃ A : Sorts.Atoms, Repr nm s.nodes.val atoms.val (encList (nm none) (A.map atomPat)) ∧
      A.Nodup ∧
      (∀ a ∈ A, (a.2, Term.var a.1) ∈ U ∧ Reach S n0 p0 (a.2, .var a.1) ∧
        PFl nm s.nodes.val (tbl s .B) (a.2, .var a.1)) ∧
      (∀ k, tbl s .B k ≠ none → ∃ x, Repr nm s.nodes.val k (ppair x) ∧
        (ok = true → PDone nm S s.nodes.val (tbl s .B) (stk s) A x) ∧ Reach S n0 p0 x) ∧
      if ok then
        (PFl nm s.nodes.val (tbl s .B) (n0, p0) ∨ POn nm s.nodes.val (stk s) (n0, p0)) ∧
        s.ticks.val + 1 + 3 * (stk s).length + owedP nm S s.nodes.val (tbl s .B) U ≤ B
      else stk s = [] ∧ (∀ σ : Nat → GTerm, Sorts.mem S n0 (p0.bind σ) = false) ∧
        s.ticks.val + 1 ≤ B

/-- What the loop returns: the atoms an instance is in the sort exactly when
it satisfies, or that no instance is in the sort. -/
def PushPost (nm : Option Nat → Sym) (S : Sorts) (U : Finset (Name × Pat)) (n0 : Name) (p0 : Pat)
    (s0 : store.Store) (B : Nat) : store.Store × store.TermId × Bool → Prop
  | (s', atoms, ok) => Wf s' ∧ stk s' = [] ∧ Extends s0 s' ∧ tbl s' .A = tbl s0 .A ∧
      s'.ticks.val ≤ B ∧
      if ok then
        ∃ A : Sorts.Atoms, Repr nm s'.nodes.val atoms.val (encList (nm none) (A.map atomPat)) ∧
          A.Nodup ∧ (∀ a ∈ A, (a.2, Term.var a.1) ∈ U) ∧
          ∀ σ : Nat → GTerm, Sorts.mem S n0 (p0.bind σ) = true ↔ Sorts.Atoms.Holds S A σ
      else ∀ σ : Nat → GTerm, Sorts.mem S n0 (p0.bind σ) = false

def PushBodyPost (nm : Option Nat → Sym) (S : Sorts) (U : Finset (Name × Pat)) (n0 : Name)
    (p0 : Pat) (s0 : store.Store) (B : Nat) (t0 : Nat) :
    ControlFlow (store.Store × store.TermId × Bool) (store.Store × store.TermId × Bool) → Prop
  | .done r => PushPost nm S U n0 p0 s0 B r ∧ t0 ≤ r.1.ticks.val
  | .cont x => PushInv nm S U n0 p0 s0 B x ∧ t0 < x.1.ticks.val

theorem push_sort_body_spec (hnm : Function.Injective nm) (S : Sorts) {sp : Pat}
    (hS : SortsAt (nm none) S sp) (Ns : Finset Name) (n0 : Name) (p0 : Pat)
    (hNs : ∀ m ∈ Ns, ∀ f k ks, Sorts.step S m f k = some ks →
      ∀ m', some m' ∈ ks → m' ∈ Ns ∧ m' ≠ nm none)
    (s0 : store.Store) (decls : store.TermId) (hd : Repr nm s0.nodes.val decls.val sp) (B : Nat)
    (hB : 40 * B + 100 ≤ Usize.max) (s : store.Store) (atoms : store.TermId) (ok : Bool)
    (h : PushInv nm S (Ns ×ˢ p0.subs) n0 p0 s0 B (s, atoms, ok)) :
    sorts.push_sort_loop.body decls s atoms ok ⦃ r =>
      PushBodyPost nm S (Ns ×ˢ p0.subs) n0 p0 s0 B s.ticks.val r ⦄ := by
  unfold sorts.push_sort_loop.body
  obtain ⟨hW, hx0, hA, hSt, A, hAr, hAn, hAU, hF, h⟩ := h
  have hc : s.ticks.val + 1 ≤ B := by
    cases ok
    · simp only [Bool.false_eq_true, ↓reduceIte] at h; exact h.2.2
    · simp only [↓reduceIte] at h; omega
  step with pop_w s hW (by unfold Room; omega) as ⟨o, s1, e1, e2, e3, hW1, eo, est⟩
  cases hstk : stk s with
  | nil =>
    rw [hstk] at eo est
    simp only [List.head?_nil] at eo
    subst eo
    simp only [WP.spec_ok]
    refine ⟨⟨hW1, by simpa using est, hx0.trans (Extends.of_eq e1 (by omega)), by rw [e2, hA],
      by omega, ?_⟩, by simp only; omega⟩
    cases ok with
    | false => simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢; exact h.2.1
    | true =>
      simp only [↓reduceIte] at h ⊢
      refine ⟨A, by rw [e1]; exact hAr, hAn, fun a ha => (hAU a ha).1, fun σ => ⟨?_, ?_⟩⟩
      · intro hm a ha
        exact (hAU a ha).2.1 σ hm
      · intro hσ
        have hcl := closed_holds (S := S) (fun x => PFl nm s.nodes.val (tbl s .B) x) A (by
          rintro x ⟨k, hk, hb⟩
          obtain ⟨x', hx', hdn, -⟩ := hF k hb
          obtain rfl := ppair_inj (Repr.unique hk hx')
          rcases hdn rfl with hv | ⟨f, args, ks, hu, hs, hall⟩
          · exact Or.inl hv
          · refine Or.inr ⟨f, args, ks, hu, hs, fun m a hz => ?_⟩
            rcases hall m a hz with h' | ⟨f', hf', -⟩
            · exact h'
            · rw [hstk] at hf'; cases hf') σ hσ
        rcases h.1 with hr | ⟨f, hf, -⟩
        · exact hcl p0.size (n0, p0) (Nat.le_refl _) hr
        · rw [hstk] at hf; cases hf
  | cons f rest =>
    rw [hstk] at eo est
    simp only [List.head?_cons, List.tail_cons] at eo est
    subst eo
    cases ok with
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte] at h
      rw [hstk] at h
      exact absurd h.1 (by simp)
    | true =>
    simp only [↓reduceIte] at h
    obtain ⟨hroot, hpot⟩ := h
    rw [hstk] at hpot
    simp only [List.length_cons] at hpot
    unfold owedP at hpot
    obtain ⟨x, hxU, hfx, hxfo, hmx⟩ := hSt f (by rw [hstk]; simp)
    obtain ⟨m, q⟩ := x
    obtain ⟨hmN, hqs⟩ := Finset.mem_product.1 hxU
    simp only at hmN hqs hmx hxfo
    have hx1 : Extends s s1 := Extends.of_eq e1 (by omega)
    have hpop : ∀ y, POn nm s.nodes.val (stk s) y → y = (m, q) ∨ POn nm s.nodes.val rest y := by
      rintro y ⟨f', hf', hy⟩
      rw [hstk] at hf'
      rcases List.mem_cons.1 hf' with rfl | hf'
      · exact Or.inl (hy.unique hfx)
      · exact Or.inr ⟨f', hf', hy⟩
    cases f
    all_goals
      rename_i n u
      simp only [PAt, fkey, faux] at hfx
      obtain ⟨hfn, hfu⟩ := hfx
      step with alloc_w s1 (.App n u) hW1 (by rw [e1]; exact ⟨hfn.lt, hfu.lt⟩)
        (by unfold Room; omega) as ⟨pair, s2, hW2, t2, tb2, x2, hid, st2⟩
      have x12 : Extends s s2 := hx1.trans x2
      have hp : Repr nm s2.nodes.val pair.val (ppair (m, q)) :=
        .app hid (x12.repr hfn) (x12.repr hfu)
      step with get_flag_w s2 .B pair hW2 hp.lt (by unfold Room; omega) as ⟨o1, s3, ho1, hK3⟩
      have htb3 : tbl s3 = tbl s := by rw [hK3.tbl, tb2, e2]
      have hst3 : stk s3 = rest := by rw [hK3.stk, st2, est]
      have ht3 := hK3.ticks
      have x3 : Extends s s3 := x12.trans (Extends.of_eq hK3.nodes (by omega))
      have ⟨more3, hm3, _⟩ := x3
      have hp3 : Repr nm s3.nodes.val pair.val (ppair (m, q)) := by rw [hK3.nodes]; exact hp
      rw [tb2, e2] at ho1
      cases hfl : tbl s .B pair.val with
      | some v =>
        rw [hfl] at ho1
        simp only [Option.map_some] at ho1
        subst ho1
        simp only [WP.spec_ok]
        have hflx : PFl nm s3.nodes.val (tbl s3 .B) (m, q) :=
          ⟨pair.val, hp3, by rw [htb3, hfl]; simp⟩
        have hon : ∀ y, POn nm s.nodes.val (stk s) y →
            PFl nm s3.nodes.val (tbl s3 .B) y ∨ POn nm s3.nodes.val (stk s3) y := by
          intro y hy
          rcases hpop y hy with rfl | ⟨f', hf', hy'⟩
          · exact Or.inl hflx
          · exact Or.inr ⟨f', by rw [hst3]; exact hf', by rw [hm3]; exact hy'.append _⟩
        have hBm : ∀ k, tbl s .B k ≠ none → tbl s3 .B k ≠ none := by
          intro k hk; rw [htb3]; exact hk
        have hflm : ∀ y, PFl nm s.nodes.val (tbl s .B) y → PFl nm s3.nodes.val (tbl s3 .B) y := by
          intro y hy
          have := hy.mono (more := more3) hBm
          rw [← hm3] at this
          exact this
        refine ⟨⟨hK3.wf, hx0.trans x3, by rw [htb3, hA], ?_, A, x3.repr hAr, hAn, ?_, ?_, ?_⟩,
          by simp only; omega⟩
        · intro f' hf'
          rw [hst3] at hf'
          obtain ⟨y, hyU, hfy, hyfo, hmy⟩ :=
            hSt f' (by rw [hstk]; exact List.mem_cons_of_mem _ hf')
          exact ⟨y, hyU, by rw [hm3]; exact hfy.append _, hyfo, hmy⟩
        · intro a ha
          obtain ⟨h1, h2, h3⟩ := hAU a ha
          exact ⟨h1, h2, hflm _ h3⟩
        · intro k hk
          rw [htb3] at hk
          obtain ⟨y, hy, hdn, hmy⟩ := hF k hk
          refine ⟨y, x3.repr hy, fun _ => ?_, hmy⟩
          have := (hdn rfl).mono (more := more3) (A' := A) (fun _ ha => ha) hBm
            (by rw [← hm3]; exact hon)
          rw [← hm3] at this
          exact this
        · simp only [↓reduceIte]
          refine ⟨?_, ?_⟩
          · rcases hroot with hr | hr
            · exact Or.inl (hflm _ hr)
            · exact hon _ hr
          · have := owedG_mono (Ns ×ˢ p0.subs) (fun x : Name × Pat => ppCost S x.2) hflm
            rw [hst3]
            unfold owedP
            omega
      | none =>
        rw [hfl] at ho1
        simp only [Option.map_none] at ho1
        subst ho1
        have hnfl : ¬ PFl nm s.nodes.val (tbl s .B) (m, q) := by
          rintro ⟨k, hk, hb⟩
          have := Repr.inj hnm hW2.nodesOK (x12.repr hk) hp
          rw [this] at hb
          exact hb hfl
        have hge := owedG_ge (U := Ns ×ˢ p0.subs) (fl := PFl nm s.nodes.val (tbl s .B))
          (fun x : Name × Pat => ppCost S x.2) hxU hnfl
        simp only at hge
        have ec : ppCost S q = sortsCost S + 11 * nargs q + 8 := rfl
        step with set_flag_w s3 .B pair true hK3.wf (by rw [hK3.nodes]; exact hp.lt)
          (by unfold Room; omega) as ⟨s4, n4, t4, hW4, tb4, tbo4, st4⟩
        have x4 : Extends s s4 := x3.trans (Extends.of_eq n4 (by omega))
        have hp4 : Repr nm s4.nodes.val pair.val (ppair (m, q)) := by rw [n4]; exact hp3
        step with is_var_w s4 u hW4 (x4.repr hfu) (by unfold Room; omega) as ⟨b, s5, hb, hK5⟩
        have x5 : Extends s s5 := x4.trans (Extends.of_eq hK5.nodes (by have := hK5.ticks; omega))
        have t5 := hK5.ticks
        have hp5 : Repr nm s5.nodes.val pair.val (ppair (m, q)) := by rw [hK5.nodes]; exact hp4
        have hB5 : tbl s5 .B = Function.update (tbl s .B) pair.val (some 1) := by
          rw [hK5.tbl, tb4, htb3]; simp
        have hA5 : tbl s5 .A = tbl s0 .A := by
          rw [hK5.tbl, tbo4 .A (by simp), htb3, hA]
        have hst5 : stk s5 = rest := by rw [hK5.stk, st4, hst3]
        have hBm : ∀ k, tbl s .B k ≠ none →
            Function.update (tbl s .B) pair.val (some 1) k ≠ none := by
          intro k hk
          by_cases e : k = pair.val
          · simp [e]
          · rw [Function.update_of_ne e]; exact hk
        cases b with
        | true =>
          obtain ⟨v, rfl⟩ := hb.1 rfl
          simp only [↓reduceIte]
          step with alloc_w s5 (.App u n) hK5.wf ⟨(x5.repr hfu).lt, (x5.repr hfn).lt⟩
            (by unfold Room; omega) as ⟨atom, s6, hW6, t6, tb6, x6, hid6, st6⟩
          have x56 : Extends s s6 := x5.trans x6
          have hat : Repr nm s6.nodes.val atom.val (atomPat (v, m)) :=
            .app hid6 (x56.repr hfu) (x56.repr hfn)
          step with alloc_w s6 (.App atom atoms) hW6 ⟨hat.lt, (x56.repr hAr).lt⟩
            (by unfold Room; omega) as ⟨atoms1, s7, hW7, t7, tb7, x7, hid7, st7⟩
          have x67 : Extends s s7 := x56.trans x7
          have ⟨more7, hm7, _⟩ := x67
          have hp7 : Repr nm s7.nodes.val pair.val (ppair (m, .var v)) :=
            (x6.trans x7).repr hp5
          have hB7 : tbl s7 .B = Function.update (tbl s .B) pair.val (some 1) := by
            rw [tb7, tb6, hB5]
          have hst7 : stk s7 = rest := by rw [st7, st6, hst5]
          have hflx : PFl nm s7.nodes.val (tbl s7 .B) (m, .var v) :=
            ⟨pair.val, hp7, by rw [hB7]; simp⟩
          have hBm' : ∀ k, tbl s .B k ≠ none → tbl s7 .B k ≠ none := by rw [hB7]; exact hBm
          have hflm : ∀ y, PFl nm s.nodes.val (tbl s .B) y →
              PFl nm s7.nodes.val (tbl s7 .B) y := by
            intro y hy
            have := hy.mono (more := more7) hBm'
            rw [← hm7] at this
            exact this
          have hon : ∀ y, POn nm s.nodes.val (stk s) y →
              PFl nm s7.nodes.val (tbl s7 .B) y ∨ POn nm s7.nodes.val (stk s7) y := by
            intro y hy
            rcases hpop y hy with rfl | ⟨f', hf', hy'⟩
            · exact Or.inl hflx
            · exact Or.inr ⟨f', by rw [hst7]; exact hf', by rw [hm7]; exact hy'.append _⟩
          have hnew : (v, m) ∉ A := fun hin => hnfl (hAU _ hin).2.2
          refine ⟨⟨hW7, hx0.trans x67, by rw [tb7, tb6, hA5], ?_, (v, m) :: A,
            .app hid7 (x7.repr hat) ((x56.trans x7).repr hAr), List.nodup_cons.2 ⟨hnew, hAn⟩,
            ?_, ?_, ?_⟩, by simp only; omega⟩
          · intro f' hf'
            rw [hst7] at hf'
            obtain ⟨y, hyU, hfy, hyfo, hmy⟩ :=
              hSt f' (by rw [hstk]; exact List.mem_cons_of_mem _ hf')
            exact ⟨y, hyU, by rw [hm7]; exact hfy.append _, hyfo, hmy⟩
          · intro a ha
            rcases List.mem_cons.1 ha with rfl | ha
            · exact ⟨hxU, hmx, hflx⟩
            · obtain ⟨h1, h2, h3⟩ := hAU a ha
              exact ⟨h1, h2, hflm _ h3⟩
          · intro k hk
            by_cases e : k = pair.val
            · subst e
              exact ⟨(m, .var v), hp7, fun _ => Or.inl ⟨v, rfl, List.mem_cons_self⟩, hmx⟩
            · rw [hB7, Function.update_of_ne e] at hk
              obtain ⟨y, hy, hdn, hmy⟩ := hF k hk
              refine ⟨y, x67.repr hy, fun _ => ?_, hmy⟩
              have := (hdn rfl).mono (more := more7) (A' := (v, m) :: A)
                (fun _ ha => List.mem_cons_of_mem _ ha) hBm' (by rw [← hm7]; exact hon)
              rw [← hm7] at this
              exact this
          · simp only [↓reduceIte]
            refine ⟨?_, ?_⟩
            · rcases hroot with hr | hr
              · exact Or.inl (hflm _ hr)
              · exact hon _ hr
            · have := owedG_set (U := Ns ×ˢ p0.subs) (fl := PFl nm s.nodes.val (tbl s .B))
                (fl' := PFl nm s7.nodes.val (tbl s7 .B)) (fun x : Name × Pat => ppCost S x.2)
                hxU hnfl hflx hflm
              simp only at this
              have ev : ppCost S (Term.var v) = sortsCost S + 8 := rfl
              rw [hst7]
              unfold owedP
              omega
        | false =>
          have hnv : ∀ v, q ≠ .var v := fun v e => by
            have := hb.2 ⟨v, e⟩
            cases this
          simp only [Bool.false_eq_true, ↓reduceIte]
          obtain ⟨f, hf⟩ := unspine_head q [] hxfo hnv
          have hun : unspine q [] = (.sym f, (unspine q []).2) := Prod.ext hf rfl
          generalize hargs : (unspine q []).2 = args at hun
          have hlen : args.length = nargs q := by
            rw [← hargs]; simpa using unspine_length q []
          step with spine_spec s5 u hK5.wf (x5.repr hfu) (by unfold Room; omega)
            as ⟨head, argsI, s6, hR6, r1, r2⟩
          rw [hf] at r1
          rw [hargs] at r2
          have t6 := hR6.ticks
          have x6 := x5.trans hR6.ext
          step with step_spec hnm S hS s6 decls n head argsI (n := m) (f := f)
            (ag := args) hR6.wf ((hx0.trans x6).repr hd) (x6.repr hfn)
            r1 r2 (by unfold Room stepCost; omega)
            as ⟨o2, s7, hR7, hst⟩
          have t7 := hR7.ticks
          unfold stepCost at t7
          have x7 := x6.trans hR7.ext
          have hp7 : Repr nm s7.nodes.val pair.val (ppair (m, q)) :=
            (hR6.ext.trans hR7.ext).repr hp5
          have hlow : s5.ticks.val ≤ s7.ticks.val := by
            have ⟨_, _, hl⟩ := hR6.ext.trans hR7.ext
            omega
          have hB7 : tbl s7 .B = Function.update (tbl s .B) pair.val (some 1) := by
            rw [hR7.tbl, hR6.tbl, hB5]
          have hA7 : tbl s7 .A = tbl s0 .A := by rw [hR7.tbl, hR6.tbl, hA5]
          have hst7 : stk s7 = rest := by rw [hR7.stk, hR6.stk, hst5]
          cases hsm : Sorts.step S m f args.length with
          | none =>
            rw [hsm] at hst
            simp only at hst
            subst hst
            step with drop_stack_w s7 hR7.wf (by unfold Room; omega)
              as ⟨s8, n8, tb8, t8, hW8, st8⟩
            have x8 : Extends s s8 := x7.trans (Extends.of_eq n8 (by omega))
            have hmem : ∀ σ : Nat → GTerm, Sorts.mem S m (q.bind σ) = false := by
              intro σ
              cases hmg : Sorts.mem S m (q.bind σ) with
              | false => rfl
              | true =>
                obtain ⟨ks, hs, -⟩ := (mem_unspine hun σ).1 hmg
                rw [hsm] at hs
                cases hs
            refine ⟨⟨hW8, hx0.trans x8, by rw [tb8, hA7], ?_, A, x8.repr hAr, hAn, ?_, ?_, ?_⟩,
              by simp only; omega⟩
            · intro f' hf'
              rw [st8] at hf'
              cases hf'
            · intro a ha
              obtain ⟨h1, h2, k, hk, hkb⟩ := hAU a ha
              exact ⟨h1, h2, k, x8.repr hk, by rw [tb8, hB7]; exact hBm k hkb⟩
            · intro k hk
              rw [tb8, hB7] at hk
              by_cases e : k = pair.val
              · subst e
                exact ⟨(m, q), by rw [n8]; exact hp7, fun h => Bool.noConfusion h, hmx⟩
              · rw [Function.update_of_ne e] at hk
                obtain ⟨y, hy, -, hmy⟩ := hF k hk
                exact ⟨y, x8.repr hy, fun h => Bool.noConfusion h, hmy⟩
            · simp only [Bool.false_eq_true, ↓reduceIte]
              refine ⟨st8, fun σ => ?_, by omega⟩
              cases hm0 : Sorts.mem S n0 (p0.bind σ) with
              | false => rfl
              | true => have := hmx σ hm0; rw [hmem σ] at this; cases this
          | some ks =>
            rw [hsm] at hst
            obtain ⟨kid, rfl, rkid⟩ := hst
            have hlk := Sorts.step_length hsm
            have hz : ∀ m', some m' ∈ ks → m' ∈ Ns ∧ m' ≠ nm none := hNs m hmN _ _ _ hsm
            step with push_args_loop_spec hnm ks args s7 kid argsI
              hR7.wf (by simp [hlk]) rkid (hR7.ext.repr r2) (fun m' hm' => (hz m' hm').2)
              (by unfold Room; omega) as ⟨s8, hW8, n8, tb8, t8, t8', fs, st8, fl8, pf1, pf2⟩
            have x8 : Extends s s8 := x7.trans (Extends.of_eq n8 t8')
            have ⟨more8, hm8, _⟩ := x8
            rw [← n8] at pf1 pf2
            have hp8 : Repr nm s8.nodes.val pair.val (ppair (m, q)) := by rw [n8]; exact hp7
            have hB8 : tbl s8 .B = Function.update (tbl s .B) pair.val (some 1) := by
              rw [tb8, hB7]
            have hst8 : stk s8 = fs ++ rest := by rw [st8, hst7]
            have hflx : PFl nm s8.nodes.val (tbl s8 .B) (m, q) :=
              ⟨pair.val, hp8, by rw [hB8]; simp⟩
            have hBm' : ∀ k, tbl s .B k ≠ none → tbl s8 .B k ≠ none := by rw [hB8]; exact hBm
            have hflm : ∀ y, PFl nm s.nodes.val (tbl s .B) y →
                PFl nm s8.nodes.val (tbl s8 .B) y := by
              intro y hy
              have := hy.mono (more := more8) hBm'
              rw [← hm8] at this
              exact this
            have hon : ∀ y, POn nm s.nodes.val (stk s) y →
                PFl nm s8.nodes.val (tbl s8 .B) y ∨ POn nm s8.nodes.val (stk s8) y := by
              intro y hy
              rcases hpop y hy with rfl | ⟨f', hf', hy'⟩
              · exact Or.inl hflx
              · exact Or.inr ⟨f', by rw [hst8]; exact List.mem_append_right _ hf',
                  by rw [hm8]; exact hy'.append _⟩
            have hkids : ∀ m' a', (some m', a') ∈ ks.zip args →
                (m', a') ∈ Ns ×ˢ p0.subs ∧ a'.firstOrder = true := by
              intro m' a' hz'
              have hin := List.of_mem_zip hz'
              rcases unspine_mem q [] a' (by rw [hargs]; exact hin.2) with h' | h'
              · cases h'
              · exact ⟨Finset.mem_product.2 ⟨(hz m' hin.1).1, Term.subs_trans hqs h'.1⟩,
                  h'.2.2 hxfo⟩
            refine ⟨⟨hW8, hx0.trans x8, by rw [tb8, hA7], ?_, A, x8.repr hAr, hAn, ?_, ?_, ?_⟩,
              by simp only; omega⟩
            · intro f' hf'
              rw [hst8] at hf'
              rcases List.mem_append.1 hf' with hf' | hf'
              · obtain ⟨m', a, hza, h1, h2⟩ := pf1 f' hf'
                obtain ⟨hU', hfo'⟩ := hkids m' a hza
                refine ⟨(m', a), hU', ⟨h1, h2⟩, hfo', fun σ h0 => ?_⟩
                obtain ⟨ks', hs', hall⟩ := (mem_unspine hun σ).1 (hmx σ h0)
                rw [hsm] at hs'
                cases hs'
                exact hall m' a hza
              · obtain ⟨y, hyU, hfy, hyfo, hmy⟩ :=
                  hSt f' (by rw [hstk]; exact List.mem_cons_of_mem _ hf')
                exact ⟨y, hyU, by rw [hm8]; exact hfy.append _, hyfo, hmy⟩
            · intro a ha
              obtain ⟨h1, h2, h3⟩ := hAU a ha
              exact ⟨h1, h2, hflm _ h3⟩
            · intro k hk
              by_cases e : k = pair.val
              · subst e
                refine ⟨(m, q), hp8, fun _ => Or.inr ⟨f, args, ks, hun, hsm,
                  fun m' a' hz' => Or.inr ?_⟩, hmx⟩
                obtain ⟨f', hf', h1, h2⟩ := pf2 m' a' hz'
                exact ⟨f', by rw [hst8]; exact List.mem_append_left _ hf', h1, h2⟩
              · rw [hB8, Function.update_of_ne e] at hk
                obtain ⟨y, hy, hdn, hmy⟩ := hF k hk
                refine ⟨y, x8.repr hy, fun _ => ?_, hmy⟩
                have := (hdn rfl).mono (more := more8) (A' := A) (fun _ ha => ha) hBm'
                  (by rw [← hm8]; exact hon)
                rw [← hm8] at this
                exact this
            · simp only [↓reduceIte]
              refine ⟨?_, ?_⟩
              · rcases hroot with hr | hr
                · exact Or.inl (hflm _ hr)
                · exact hon _ hr
              · have := owedG_set (U := Ns ×ˢ p0.subs) (fl := PFl nm s.nodes.val (tbl s .B))
                  (fl' := PFl nm s8.nodes.val (tbl s8 .B)) (fun x : Name × Pat => ppCost S x.2)
                  hxU hnfl hflx hflm
                simp only at this
                rw [hst8]
                simp only [List.length_append]
                unfold owedP
                omega

/-- The ticks `push_sort` may spend: eight, and for each sort of `Ns` and
each distinct subterm of the pattern, the cost of that pair. -/
noncomputable def pushCost (S : Sorts) (Ns : Finset Name) (p : Pat) : Nat :=
  8 + (Ns ×ˢ p.subs).sum fun x => ppCost S x.2

theorem push_sort_loop_spec (hnm : Function.Injective nm) (S : Sorts) {sp : Pat}
    (hS : SortsAt (nm none) S sp) (Ns : Finset Name) (n0 : Name) (p0 : Pat)
    (hNs : ∀ m ∈ Ns, ∀ f k ks, Sorts.step S m f k = some ks →
      ∀ m', some m' ∈ ks → m' ∈ Ns ∧ m' ≠ nm none)
    (s0 : store.Store) (decls : store.TermId) (hd : Repr nm s0.nodes.val decls.val sp) (B : Nat)
    (hB : 40 * B + 100 ≤ Usize.max) (s : store.Store) (atoms : store.TermId) (ok : Bool)
    (h : PushInv nm S (Ns ×ˢ p0.subs) n0 p0 s0 B (s, atoms, ok)) :
    sorts.push_sort_loop s decls atoms ok ⦃ r => PushPost nm S (Ns ×ˢ p0.subs) n0 p0 s0 B r ⦄ := by
  unfold sorts.push_sort_loop
  have hloop := loop.spec_decr_nat
    (fun y : store.Store × store.TermId × Bool => B + 1 - y.1.ticks.val)
    (fun y => PushInv nm S (Ns ×ˢ p0.subs) n0 p0 s0 B y)
    (fun y : store.Store × store.TermId × Bool => PushPost nm S (Ns ×ˢ p0.subs) n0 p0 s0 B y)
    (fun y : store.Store × store.TermId × Bool =>
      sorts.push_sort_loop.body decls y.1 y.2.1 y.2.2) (s, atoms, ok)
    (by
      rintro ⟨y, at', ok'⟩ hinv
      refine WP.spec_mono (push_sort_body_spec hnm S hS Ns n0 p0 hNs s0 decls hd B hB y at' ok'
        hinv) ?_
      intro r hr
      cases r with
      | done z => exact hr.1
      | cont y' =>
        obtain ⟨h1, h2⟩ := hr
        obtain ⟨z, at'', ok''⟩ := y'
        have hz : z.ticks.val + 1 ≤ B := by
          obtain ⟨-, -, -, -, A, -, -, -, -, h⟩ := h1
          cases ok'' with
          | true => simp only [↓reduceIte] at h; omega
          | false => simp only [Bool.false_eq_true, ↓reduceIte] at h; exact h.2.2
        simp only at h2
        exact ⟨h1, by simp only; omega⟩)
    h
  exact hloop

/-- `push_sort` returns the sorts the variables of a first-order pattern must
be in for an instance of it to be in a sort: an instance is in the sort
exactly when it satisfies the atoms of the list, each listed once and each a
variable of the pattern with a sort of `Ns`; and when nothing is returned no
instance is in the sort. `Ns` is a set of names that has the sort asked
about and every sort a step from one of its members names; no name is the
end of a list. Table `A` is left as it was. -/
theorem push_sort_spec (hnm : Function.Injective nm) (S : Sorts) {sp : Pat}
    (hS : SortsAt (nm none) S sp) (Ns : Finset Name) {n0 : Name} (p0 : Pat)
    (hfo : p0.firstOrder = true) (hn0 : n0 ∈ Ns)
    (hNs : ∀ m ∈ Ns, ∀ f k ks, Sorts.step S m f k = some ks →
      ∀ m', some m' ∈ ks → m' ∈ Ns ∧ m' ≠ nm none)
    (s : store.Store) (decls nme t : store.TermId) (hI : Inv s)
    (hd : Repr nm s.nodes.val decls.val sp) (hn : Repr nm s.nodes.val nme.val (.sym n0))
    (ht : Repr nm s.nodes.val t.val p0) (hroom : Room s (pushCost S Ns p0)) :
    sorts.push_sort s decls nme t ⦃ o s' =>
      Inv s' ∧ Extends s s' ∧ tbl s' .A = tbl s .A ∧
        s'.ticks.val ≤ s.ticks.val + pushCost S Ns p0 ∧
        match o with
        | none => ∀ σ : Nat → GTerm, Sorts.mem S n0 (p0.bind σ) = false
        | some l => ∃ A : Sorts.Atoms,
            Repr nm s'.nodes.val l.val (encList (nm none) (A.map atomPat)) ∧ A.Nodup ∧
            (∀ a ∈ A, a.2 ∈ Ns ∧ Term.var a.1 ∈ p0.subs) ∧
            ∀ σ : Nat → GTerm, Sorts.mem S n0 (p0.bind σ) = true ↔ Sorts.Atoms.Holds S A σ ⦄ := by
  unfold sorts.push_sort
  have hroom' := hroom
  unfold Room at hroom'
  have h8 : 8 ≤ pushCost S Ns p0 := by unfold pushCost; omega
  step with alloc_w s .Nil hI.toWf trivial (by unfold Room; omega)
    as ⟨atoms, s1, hW1, t1, tb1, x1, hid1, st1⟩
  step with clear_w s1 .B hW1 (by unfold Room; omega) as ⟨s2, n2, t2, hW2, hBe, tbo2, st2⟩
  step with push_w s2 (.Visit nme t) hW2 (by unfold Room; omega) as ⟨s3, n3, tb3, t3, hW3, st3⟩
  have x3 : Extends s s3 := x1.trans (Extends.of_eq (n3.trans n2) (by omega))
  have hstk3 : stk s3 = [.Visit nme t] := by rw [st3, st2, st1, hI.empty]
  have hB3 : ∀ k, tbl s3 .B k = none := by intro k; rw [tb3]; exact hBe k
  have hroot : PAt nm s3.nodes.val (.Visit nme t) (n0, p0) := ⟨x3.repr hn, x3.repr ht⟩
  have hP : owedP nm S s3.nodes.val (tbl s3 .B) (Ns ×ˢ p0.subs) ≤
      (Ns ×ˢ p0.subs).sum fun x => ppCost S x.2 := owedG_le_sum _ _ _
  have hinv : PushInv nm S (Ns ×ˢ p0.subs) n0 p0 s (s.ticks.val + pushCost S Ns p0)
      (s3, atoms, true) := by
    refine ⟨hW3, x3, by rw [tb3, tbo2 .A (by simp), tb1], ?_, [], ?_, List.nodup_nil, ?_, ?_, ?_⟩
    · intro f hf
      rw [hstk3] at hf
      simp only [List.mem_singleton] at hf
      subst hf
      exact ⟨(n0, p0), Finset.mem_product.2 ⟨hn0, Term.self_mem_subs p0⟩, hroot, hfo,
        fun _ h => h⟩
    · have : s3.nodes.val = s1.nodes.val := n3.trans n2
      rw [this]
      exact .nil hid1
    · intro a ha; cases ha
    · intro k hk
      exact absurd (hB3 k) hk
    · simp only [↓reduceIte]
      refine ⟨Or.inr ⟨.Visit nme t, by rw [hstk3]; simp, hroot⟩, ?_⟩
      rw [hstk3]
      simp only [List.length_singleton]
      unfold pushCost
      omega
  step with push_sort_loop_spec hnm S hS Ns n0 p0 hNs s decls hd
    (s.ticks.val + pushCost S Ns p0) (by omega) s3 atoms true
    hinv as ⟨s4, atoms1, ok1, hr⟩
  obtain ⟨hW4, hst4, x4, hA4, ht4, hres⟩ := hr
  cases ok1 with
  | true =>
    simp only [↓reduceIte] at hres ⊢
    obtain ⟨A, hAr, hAn, hAU, hsem⟩ := hres
    simp only [WP.spec_ok]
    refine ⟨⟨hW4, hst4⟩, x4, hA4, ht4, A, hAr, hAn, fun a ha => ?_, hsem⟩
    have := Finset.mem_product.1 (hAU a ha)
    exact ⟨this.1, this.2⟩
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at hres ⊢
    simp only [WP.spec_ok]
    exact ⟨⟨hW4, hst4⟩, x4, hA4, ht4, hres⟩

end RwLogVerified
