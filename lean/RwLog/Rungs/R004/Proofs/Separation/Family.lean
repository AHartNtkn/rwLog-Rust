/-
# The separating family: spans, expressions, products

Facts about `sepFam k` that mention no machine.

* The spans: `a -> a`, `q -> q` and the two wrappers. A chain of wrappers
  always composes (`chain_wraps`), and a wrapper followed by `q -> q` never
  does (`chain_wrap_qq`).
* The normal form of `gen j` is `2 ^ (j + 1)` single spans, all different
  (`norm_gen`): the one for a string of wrappers relates every term to its
  wrapping by that string.
* The table key of the query is the query (`norm_root`), and the input has
  size `12 k + 21` (`size_sepRel`).
-/
import RwLog.Rungs.R004.Spec
import RwLog.Rungs.R003.Proofs.Separation.Family
import RwLog.Kernel.Chain
import RwLog.Rungs.Tabled.Machine

namespace RwLog

namespace R004

namespace Sep

open R000 R001

/-! ## The spans -/

/-- `a -> a`, the one answer. -/
abbrev aa : Span := ⟨.sym "a", .sym "a", []⟩

/-- `q -> q`, the test no wrapped term passes. -/
abbrev qq : Span := ⟨.sym "q", .sym "q", []⟩

abbrev w0 : Span := wrap "0"
abbrev w1 : Span := wrap "1"

/-- One of the two wrappers. -/
def Wrap (s : Span) : Prop := s = w0 ∨ s = w1

theorem size_wrap {s : Span} (h : Wrap s) : s.size = 4 := by
  rcases h with rfl | rfl <;> simp [wrap, Span.size, Store.size, Term.size]

theorem size_aa : aa.size = 2 := by simp [Span.size, Store.size, Term.size]
theorem size_qq : qq.size = 2 := by simp [Span.size, Store.size, Term.size]

/-- What a wrapper denotes. -/
theorem den_wrap (f : Sym) : (wrap f).den = {x | ∃ t : GTerm, x = (t, .app (.sym f) t, ∅)} := by
  ext x
  constructor
  · rintro ⟨σ, rfl⟩
    exact ⟨σ 0, by simp [wrap, Term.bind, Store.at]⟩
  · rintro ⟨t, rfl⟩
    exact ⟨fun _ => t, by simp [wrap, Term.bind, Store.at]⟩

theorem den_qq : qq.den = {x | x = (.sym "q", .sym "q", ∅)} := by
  ext x
  constructor
  · rintro ⟨σ, rfl⟩
    simp [Term.bind, Store.at]
  · rintro rfl
    exact ⟨fun _ => .sym "q", by simp [Term.bind, Store.at]⟩

/-- A term wrapped by a string of symbols, the first one outermost. -/
def wrapBy : List Sym → GTerm → GTerm
  | [], t => t
  | f :: bs, t => .app (.sym f) (wrapBy bs t)

theorem wrapBy_snoc : ∀ (bs : List Sym) (f : Sym) (t : GTerm),
    wrapBy (bs ++ [f]) t = wrapBy bs (.app (.sym f) t)
  | [], _, _ => rfl
  | g :: bs, f, t => by rw [List.cons_append, wrapBy, wrapBy, wrapBy_snoc bs f t]

theorem wrapBy_inj : ∀ {bs bs' : List Sym} {t : GTerm}, bs.length = bs'.length →
    wrapBy bs t = wrapBy bs' t → bs = bs'
  | [], [], _, _, _ => rfl
  | [], _ :: _, _, h, _ => by cases h
  | _ :: _, [], _, h, _ => by cases h
  | f :: bs, g :: bs', t, h, e => by
    simp only [wrapBy, Term.app.injEq, Term.sym.injEq] at e
    rw [e.1, wrapBy_inj (by simpa using h) e.2]

/-- The relation of a term to its wrapping by a string. -/
def wrapDen (bs : List Sym) : GRel := {x | ∃ t : GTerm, x = (t, wrapBy bs t, ∅)}

theorem wrapDen_inj {bs bs' : List Sym} (hl : bs.length = bs'.length)
    (h : wrapDen bs = wrapDen bs') : bs = bs' := by
  have hm : ((.sym "" : GTerm), wrapBy bs (.sym ""), (∅ : GStore)) ∈ wrapDen bs := ⟨_, rfl⟩
  rw [h] at hm
  obtain ⟨t, ht⟩ := hm
  simp only [Prod.mk.injEq] at ht
  obtain ⟨rfl, e, -⟩ := ht
  exact wrapBy_inj hl e

theorem den_wrap_eq (f : Sym) : (wrap f).den = wrapDen [f] := den_wrap f

/-- A wrapper before a wrapping is a wrapping, the new symbol innermost. -/
theorem comp_wrapDen (f : Sym) (bs : List Sym) :
    (wrap f).den.comp (wrapDen bs) = wrapDen (bs ++ [f]) := by
  rw [den_wrap]
  ext ⟨a, b, S⟩
  constructor
  · rintro ⟨m, S₁, S₂, ⟨t, ht⟩, ⟨u, hu⟩, hS⟩
    simp only [Prod.mk.injEq] at ht hu hS
    obtain ⟨rfl, rfl, rfl⟩ := ht
    obtain ⟨rfl, rfl, rfl⟩ := hu
    exact ⟨a, by simp [wrapBy_snoc, hS]⟩
  · rintro ⟨t, ht⟩
    simp only [Prod.mk.injEq] at ht
    obtain ⟨rfl, rfl, rfl⟩ := ht
    exact ⟨.app (.sym f) a, ∅, ∅, ⟨a, rfl⟩, ⟨_, by rw [wrapBy_snoc]⟩, by simp⟩

/-- Every chain of wrappers relates every term to something. -/
theorem chain_wraps_total : ∀ L : List Span, (∀ s ∈ L, Wrap s) → ∀ t : GTerm,
    ∃ u, (t, u, (∅ : GStore)) ∈ GRel.chain (L.map Span.den)
  | [], _, t => ⟨t, rfl, rfl⟩
  | s :: L, h, t => by
    have hs : ∃ f, s = wrap f := by
      rcases h s (by simp) with rfl | rfl
      · exact ⟨_, rfl⟩
      · exact ⟨_, rfl⟩
    obtain ⟨f, rfl⟩ := hs
    obtain ⟨u, hu⟩ := chain_wraps_total L (fun x hx => h x (by simp [hx])) (.app (.sym f) t)
    refine ⟨u, .app (.sym f) t, ∅, ∅, ?_, hu, by simp⟩
    rw [den_wrap]
    exact ⟨t, rfl⟩

/-- Every chain of wrappers composes. -/
theorem chain_wraps {L : List Span} (h : ∀ s ∈ L, Wrap s) : (Span.chain L).isSome = true := by
  rw [Span.chain_isSome_iff]
  obtain ⟨u, hu⟩ := chain_wraps_total L h (.sym "")
  exact ⟨_, hu⟩

/-- A wrapper followed by `q -> q` does not compose. -/
theorem chain_wrap_qq {s : Span} (h : Wrap s) : (Span.chain [s, qq]).isSome = false := by
  rw [Bool.eq_false_iff, Ne, Span.chain_isSome_iff]
  have hs : ∃ f, s = wrap f := by
    rcases h with rfl | rfl
    · exact ⟨_, rfl⟩
    · exact ⟨_, rfl⟩
  obtain ⟨f, rfl⟩ := hs
  rintro ⟨⟨a, b, S⟩, m, S₁, S₂, h1, ⟨m', S₃, S₄, h2, -, -⟩, -⟩
  rw [den_wrap] at h1
  rw [den_qq] at h2
  obtain ⟨t, ht⟩ := h1
  simp only [Set.mem_ofPred_eq, Prod.mk.injEq] at ht h2
  obtain ⟨-, rfl, -⟩ := ht
  cases h2.1

/-! ## The products of `gen j` -/

/-- The strings of wrappers of `gen j`, in the normalizer's order. -/
def strs : Nat → List (List Sym)
  | 0 => [["0"], ["1"]]
  | j + 1 => (strs j).map (· ++ ["0"]) ++ (strs j).map (· ++ ["1"])

theorem length_strs : ∀ j, (strs j).length = 2 ^ (j + 1)
  | 0 => rfl
  | j + 1 => by simp [strs, length_strs j, pow_succ]; omega

theorem length_of_mem_strs : ∀ j, ∀ bs ∈ strs j, bs.length = j + 1
  | 0, bs, h => by
    simp only [strs, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl <;> rfl
  | j + 1, bs, h => by
    simp only [strs, List.mem_append, List.mem_map] at h
    rcases h with ⟨b, hb, rfl⟩ | ⟨b, hb, rfl⟩ <;> simp [length_of_mem_strs j b hb]

theorem nodup_strs : ∀ j, (strs j).Nodup
  | 0 => by decide
  | j + 1 => by
    have inj : ∀ f : Sym, Function.Injective fun bs : List Sym => bs ++ [f] :=
      fun f a b h => List.append_cancel_right h
    rw [strs, List.nodup_append]
    refine ⟨(nodup_strs j).map (inj _), (nodup_strs j).map (inj _), ?_⟩
    intro a ha b hb e
    obtain ⟨x, -, rfl⟩ := List.mem_map.mp ha
    obtain ⟨y, -, rfl⟩ := List.mem_map.mp hb
    have := congrArg List.getLast? e
    simp at this

/-- The span denotes the wrapping by the string. -/
def Den (bs : List Sym) (s : Span) : Prop := s.den = wrapDen bs

theorem wrapDen_nonempty (bs : List Sym) : (wrapDen bs).Nonempty := ⟨_, .sym "", rfl⟩

/-- A wrapper fused before each span of a list of wrappings. -/
theorem join_wrap (f : Sym) : ∀ {l : List (List Sym)} {S : List Span}, List.Forall₂ Den l S →
    ∃ S', (S.map fun s => [Rel.span s]).filterMap (joinSeq [.span (wrap f)]) =
        S'.map (fun s => [Rel.span s]) ∧ List.Forall₂ Den (l.map (· ++ [f])) S'
  | _, _, .nil => ⟨[], rfl, .nil⟩
  | _, _, .cons (a := bs) (b := s) h t => by
    obtain ⟨S', e, h'⟩ := join_wrap f t
    have hd : (wrap f).den.comp s.den = wrapDen (bs ++ [f]) := by rw [h, comp_wrapDen]
    cases hc : (wrap f).compose s with
    | none =>
      have := compose_none hc
      rw [hd] at this
      exact absurd this (wrapDen_nonempty _).ne_empty
    | some c =>
      refine ⟨c :: S', ?_, .cons ((compose_some hc).trans hd) h'⟩
      simp only [List.map_cons, List.filterMap_cons, e]
      simp [joinSeq, hc]

/-- The normal form of `gen j`: one span for each string of wrappers. -/
theorem norm_gen_den : ∀ j, ∃ S, norm false (gen j) = S.map (fun s => [Rel.span s]) ∧
    List.Forall₂ Den (strs j) S
  | 0 => ⟨[w0, w1], rfl, .cons (den_wrap_eq _) (.cons (den_wrap_eq _) .nil)⟩
  | j + 1 => by
    obtain ⟨S, e, h⟩ := norm_gen_den j
    obtain ⟨S0, e0, h0⟩ := join_wrap "0" h
    obtain ⟨S1, e1, h1⟩ := join_wrap "1" h
    refine ⟨S0 ++ S1, ?_, ?_⟩
    · rw [gen, norm, e]
      simp only [bit, norm, List.cons_append, List.nil_append, List.flatMap_cons,
        List.flatMap_nil, List.append_nil, List.map_append]
      exact congrArg₂ _ e0 e1
    · rw [strs]
      exact List.rel_append h0 h1

theorem exists_of_forall₂ {α β : Type} {R : α → β → Prop} : ∀ {l : List α} {S : List β},
    List.Forall₂ R l S → ∀ {b : β}, b ∈ S → ∃ a ∈ l, R a b
  | _, _, .nil, _, hb => by cases hb
  | _, _, .cons h t, b, hb => by
    rcases List.mem_cons.mp hb with rfl | hb
    · exact ⟨_, List.mem_cons_self, h⟩
    · obtain ⟨a, ha, hab⟩ := exists_of_forall₂ t hb
      exact ⟨a, List.mem_cons_of_mem _ ha, hab⟩

theorem nodup_of_forall₂ {α β : Type} {R : α → β → Prop}
    (hR : ∀ a a' b, R a b → R a' b → a = a') : ∀ {l : List α} {S : List β},
    List.Forall₂ R l S → l.Nodup → S.Nodup
  | _, _, .nil, _ => List.nodup_nil
  | _, _, .cons (a := a) (b := b) h t, hn => by
    rw [List.nodup_cons] at hn ⊢
    refine ⟨fun hb => ?_, nodup_of_forall₂ hR t hn.2⟩
    obtain ⟨a', ha', hab⟩ := exists_of_forall₂ t hb
    exact hn.1 (hR a a' b h hab ▸ ha')

/-- The normal form of `gen j` is `2 ^ (j + 1)` single spans, all
different. -/
theorem norm_gen (j : Nat) : ∃ S : List Span, norm false (gen j) = S.map (fun s => [Rel.span s]) ∧
    S.Nodup ∧ S.length = 2 ^ (j + 1) := by
  obtain ⟨S, e, h⟩ := norm_gen_den j
  refine ⟨S, e, ?_, by rw [← h.length_eq, length_strs]⟩
  have hmem : ∀ {l : List (List Sym)} {S : List Span}, List.Forall₂ Den l S →
      List.Forall₂ (fun bs s => bs ∈ l ∧ Den bs s) l S := by
    intro l S h
    induction h with
    | nil => exact .nil
    | cons h' _ ih =>
      exact .cons ⟨List.mem_cons_self, h'⟩ (ih.imp fun _ _ h => ⟨List.mem_cons_of_mem _ h.1, h.2⟩)
  refine nodup_of_forall₂ ?_ (hmem h) (nodup_strs j)
  rintro a a' b ⟨ha, h1⟩ ⟨ha', h2⟩
  exact wrapDen_inj (by rw [length_of_mem_strs j a ha, length_of_mem_strs j a' ha'])
    (h1.symm.trans h2)

/-! ## The expressions -/

/-- The family's program: no definitions and no theory. -/
abbrev P0 : Program := ⟨[], []⟩

/-- `gen k ; @q`, the branch with no answers. -/
abbrev dead (k : Nat) : Rel := .seq (gen k) (.span qq)

theorem sepRel_eq (k : Nat) : sepRel k = .or (.span aa) (dead k) := rfl

/-- No wrapped term passes the test: `gen k ; @q` has no product. -/
theorem norm_dead (k : Nat) : norm false (dead k) = [] := by
  obtain ⟨S, e, h⟩ := norm_gen_den k
  have hnone : ∀ s ∈ S, s.compose qq = none := by
    intro s hs
    obtain ⟨bs, hbs, hd⟩ := exists_of_forall₂ h hs
    have hlen := length_of_mem_strs k bs hbs
    cases hc : s.compose qq with
    | none => rfl
    | some c =>
      obtain ⟨⟨a, b, X⟩, hx⟩ := c.den_nonempty
      rw [compose_some hc, hd, den_qq] at hx
      obtain ⟨m, S₁, S₂, ⟨t, ht⟩, hq, -⟩ := hx
      simp only [Set.mem_ofPred_eq, Prod.mk.injEq] at ht hq
      obtain ⟨-, rfl, -⟩ := ht
      cases bs with
      | nil => cases hlen
      | cons f bs => cases hq.1
  rw [norm, e, List.flatMap_eq_nil_iff]
  intro p hp
  obtain ⟨s, hs, rfl⟩ := List.mem_map.1 hp
  simp [norm, joinSeq, hnone s hs]

theorem canon_bit : canon bit = bit := by
  have h : compare ("0" : Sym) "1" ≠ .gt := by decide
  simp [bit, wrap, canon, orBranches, sortedBranches, relCmp, spanCmp, patCmp, listCmp, h,
    List.eraseDups_cons, mkOr]

theorem canon_gen : ∀ k, canon (gen k) = gen k
  | 0 => canon_bit
  | k + 1 => by rw [gen, canon, canon_bit, canon_gen k]

theorem canon_dead (k : Nat) : canon (dead k) = dead k := by
  rw [dead, canon, canon_gen k, canon]

theorem canon_sepRel (k : Nat) : canon (sepRel k) = sepRel k := by
  rw [sepRel_eq, canon, canon_dead, canon]
  simp [orBranches, sortedBranches, relCmp, List.eraseDups_cons, mkOr]

theorem size_gen : ∀ k, (gen k).size = 12 * k + 11
  | 0 => by simp [gen, bit, wrap, Rel.size, Span.size, Term.size, Store.size]
  | k + 1 => by
    have h0 := size_gen 0
    have ih := size_gen k
    simp only [gen, Rel.size] at h0 ih ⊢
    omega

theorem size_dead (k : Nat) : (dead k).size = 12 * k + 15 := by
  simp only [Rel.size, size_gen, size_qq]; omega

theorem size_sepRel (k : Nat) : (sepRel k).size = 12 * k + 19 := by
  rw [sepRel_eq, Rel.size, size_dead]; simp only [Rel.size, size_aa]; omega

theorem size_le (k : Nat) : (sepFam k).1.size + (sepFam k).2.size ≤ 12 * (k + 2) := by
  have e : (sepFam k).1.size = 0 := by simp [sepFam, Program.size, Theory.size]
  have := size_sepRel k
  simp only [sepFam] at e ⊢
  omega

theorem calls_gen : ∀ k, (gen k).calls = []
  | 0 => by simp [gen, bit, Rel.calls]
  | k + 1 => by rw [gen, Rel.calls, calls_gen k]; simp [bit, Rel.calls]

theorem calls_sepRel (k : Nat) : (sepRel k).calls = [] := by
  simp [sepRel_eq, Rel.calls, calls_gen]

theorem wellFormed (k : Nat) : (sepFam k).1.WellFormed (sepFam k).2 := by
  refine ⟨by simp [sepFam], ?_, by simp [sepFam]⟩
  intro n hn
  simp [sepFam, calls_sepRel] at hn

theorem model_nil (k : Nat) : (sepFam k).1.theory.Model ∅ := by
  intro ρ h
  exact absurd h List.not_mem_nil

/-- The goal of the query, with no boundaries. -/
abbrev g0 (k : Nat) : Goal := ⟨none, sepRel k, none⟩

theorem norm_g0 (k : Nat) : (g0 k).norm = (false, g0 k) := by
  rw [Goal.norm, canon_sepRel, sepRel_eq, Goal.stripConv]
  · rfl
  · intro lb a rb h
    cases h

theorem unfoldN_zero (e : Rel) : unfoldN P0 0 e = e := rfl

/-- R001's unfolding race on the query: final, and the one answer. -/
theorem unfold_g0 (k : Nat) :
    unfoldFinal P0 0 (g0 k) = true ∧ unfoldAnswers P0 0 (g0 k) = [aa] := by
  have hp : R000.products P0 (g0 k).rel 0 = [[.span aa]] := by
    show norm false (unfoldN P0 0 (.or (.span aa) (dead k))) = _
    rw [unfoldN_zero, norm, norm_dead]
    rfl
  have hf : unfoldFinal P0 0 (g0 k) = true := by
    simp [unfoldFinal, R000.roundFinal, hp, toRel, Rel.calls]
  refine ⟨hf, ?_⟩
  simp [unfoldAnswers, hf, R000.roundSpans, hp, toRel, derivs, live, Theory.simplify,
    Theory.simplifyWithin, Theory.refutes?, Theory.firings, Store.varCount]

/-- The state the machine starts from: the table of the query. -/
abbrev st0 (k : Nat) : R001.State := ⟨P0, [⟨g0 k, [], false⟩], false, 0⟩

theorem init_eq (k : Nat) (U : Oracle) :
    (Tabled.machine U).init (sepFam k).1 (sepFam k).2 = st0 k := by
  show R001.State.ofGoal P0 (g0 k) = _
  rw [R001.State.ofGoal, norm_g0]

end Sep

end R004

end RwLog
