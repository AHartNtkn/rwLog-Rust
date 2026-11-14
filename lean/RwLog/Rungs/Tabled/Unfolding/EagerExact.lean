/-
# The whole unfolding builds exactly the products of the goal

`Unfolding/Model.lean` says what the unfolding of a goal relates, product by
product (`SE`). Here the list `Unfold.eager` builds is shown to be that set
(`eager_ex`): every product of the list is one of the set, and every product
of the set is in the list, a closed product read by the pairs of its
representative and an open one by the left ends of its first stretch and the
right ends of its last (`semP`).

It follows from the laws of a domain alone: a composition or a meet has a
representative exactly when it relates a pair. So the whole unfolding says a
goal's unfolding is final exactly when the set has no open product
(`eagerRace_final`).
-/
import RwLog.Rungs.Tabled.Unfolding.Model
import RwLog.Rungs.Tabled.Unfolding.Eager

namespace RwLog

namespace Tabled

namespace Unfold

open Answer

variable {R : Type} [Answer R] [DecidableEq R] {D : Domain R} {P : Program}

/-! ## Products, by what they relate -/

/-- The left ends of a first stretch: every term when there is none. -/
def lsetO (M : Interp) : Option R → Set GTerm
  | none => Set.univ
  | some x => (den M x).lends

/-- The right ends of a last stretch: every term when there is none. -/
def rsetO (M : Interp) : Option R → Set GTerm
  | none => Set.univ
  | some x => (den M x).rends

/-- A product, by what it relates. -/
def semP (M : Interp) : Pr D P → SP
  | .closed a => .closed (den M a.span)
  | .opn l r => .opn (lsetO M l) (rsetO M r)

theorem preS_univ (X : PRel) : preS X Set.univ = X.lends := by
  ext x
  exact ⟨fun ⟨m, _, h⟩ => ⟨m, h⟩, fun ⟨m, h⟩ => ⟨m, trivial, h⟩⟩

theorem postS_univ (X : PRel) : postS Set.univ X = X.rends := by
  ext z
  exact ⟨fun ⟨m, _, h⟩ => ⟨m, h⟩, fun ⟨m, h⟩ => ⟨m, trivial, h⟩⟩

theorem lends_comp (X Y : PRel) : (X.comp Y).lends = preS X Y.lends := by
  ext x
  constructor
  · rintro ⟨z, m, h₁, h₂⟩; exact ⟨m, ⟨z, h₂⟩, h₁⟩
  · rintro ⟨m, ⟨z, h₂⟩, h₁⟩; exact ⟨z, m, h₁, h₂⟩

theorem rends_comp (X Y : PRel) : (X.comp Y).rends = postS X.rends Y := by
  ext z
  constructor
  · rintro ⟨x, m, h₁, h₂⟩; exact ⟨m, ⟨x, h₁⟩, h₂⟩
  · rintro ⟨m, ⟨x, h₁⟩, h₂⟩; exact ⟨x, m, h₁, h₂⟩

section laws

variable {M : Interp} (hL : D.Lawful M)
include hL

omit [DecidableEq R] in
theorem lsetO_bound {b : Option R} (hb : IsBound D b) : lsetO M b = bset M b := by
  cases b with
  | none => rfl
  | some r =>
    ext x
    constructor
    · rintro ⟨z, h⟩
      have := (mem_bden hL hb (b := some r)).1 h
      exact this.2
    · intro h; exact ⟨x, h⟩

omit [DecidableEq R] in
theorem rsetO_bound {b : Option R} (hb : IsBound D b) : rsetO M b = bset M b := by
  cases b with
  | none => rfl
  | some r =>
    ext z
    constructor
    · rintro ⟨x, h⟩
      have := (mem_bden hL hb (b := some r)).1 h
      obtain rfl := this.1
      exact this.2
    · intro h; exact ⟨z, h⟩

omit [DecidableEq R] in
theorem lsetO_nonempty (l : Option R) : (lsetO M l).Nonempty := by
  cases l with
  | none => exact ⟨.sym "", trivial⟩
  | some x => obtain ⟨⟨a, b⟩, h⟩ := hL.live x; exact ⟨a, b, h⟩

omit [DecidableEq R] in
theorem rsetO_nonempty (r : Option R) : (rsetO M r).Nonempty := by
  cases r with
  | none => exact ⟨.sym "", trivial⟩
  | some x => obtain ⟨⟨a, b⟩, h⟩ := hL.live x; exact ⟨b, a, h⟩

omit [DecidableEq R] in
/-- The pairs between two boundaries are the pairs between the terms they
let through. -/
theorem wrap_restr {lb rb : Option R} (hl : IsBound D lb) (hr : IsBound D rb) (X : PRel) :
    wrapAt M lb X rb = restr (bset M lb) X (bset M rb) := by
  ext ⟨x, z⟩
  rw [mem_wrap hL hl hr, mem_bden hL hl, mem_bden hL hr]
  exact ⟨fun ⟨h₁, h₂, h₃⟩ => ⟨h₂, h₁.2, h₃.2⟩, fun ⟨h₂, h₁, h₃⟩ => ⟨⟨rfl, h₁⟩, h₂, rfl, h₃⟩⟩

omit [DecidableEq R] in
/-- A composition has a representative exactly when it relates a pair. -/
theorem compose_iff (a b : R) :
    ((den M a).comp (den M b)).Nonempty ↔ ∃ z, D.compose a b = some z := by
  constructor
  · intro h
    cases hc : D.compose a b with
    | none => rw [hL.compose_none a b hc] at h; exact absurd h Set.not_nonempty_empty
    | some z => exact ⟨z, rfl⟩
  · rintro ⟨z, hz⟩
    rw [← hL.compose_some a b z hz]; exact hL.live z

omit [DecidableEq R] in
/-- A meet has a representative exactly when it relates a pair. -/
theorem meet_iff (a b : R) : (den M a ∩ den M b).Nonempty ↔ ∃ z, D.meet a b = some z := by
  constructor
  · intro h
    cases hc : D.meet a b with
    | none => rw [hL.meet_none a b hc] at h; exact absurd h Set.not_nonempty_empty
    | some z => exact ⟨z, rfl⟩
  · rintro ⟨z, hz⟩
    rw [← hL.meet_some a b z hz]; exact hL.live z

end laws

/-- The products are exactly the products of a set, and the closed ones are
answers between the boundaries. -/
structure PEx (lb rb : Option R) (S : Set SP) (ps : List (Pr D P)) : Prop where
  lb : ∀ a, .closed a ∈ ps → a.goal.lb = lb
  rb : ∀ a, .closed a ∈ ps → a.goal.rb = rb
  sound : ∀ p ∈ ps, semP P.sorts.interp p ∈ S
  complete : ∀ s ∈ S, ∃ p ∈ ps, semP P.sorts.interp p = s

omit [DecidableEq R] in
theorem PEx.of_eq {lb rb : Option R} {S S' : Set SP} {ps : List (Pr D P)} (h : PEx lb rb S ps)
    (e : S' = S) : PEx lb rb S' ps := e ▸ h

omit [DecidableEq R] in
theorem PEx.nonempty {lb rb : Option R} {S : Set SP} {ps : List (Pr D P)} (h : PEx lb rb S ps) :
    S.Nonempty ↔ ps ≠ [] := by
  constructor
  · rintro ⟨s, hs⟩ e
    obtain ⟨p, hp, -⟩ := h.complete s hs
    rw [e] at hp; cases hp
  · intro hne
    obtain ⟨p, hp⟩ := List.exists_mem_of_ne_nil _ hne
    exact ⟨_, h.sound p hp⟩

omit [DecidableEq R] in
theorem PEx.hasOpn {lb rb : Option R} {S : Set SP} {ps : List (Pr D P)} (h : PEx lb rb S ps) :
    HasOpn S ↔ ps.any Prod.isOpn = true := by
  rw [List.any_eq_true]
  constructor
  · rintro ⟨A, B, hs⟩
    obtain ⟨p, hp, e⟩ := h.complete _ hs
    cases p with
    | closed a => cases e
    | opn l r => exact ⟨_, hp, rfl⟩
  · rintro ⟨p, hp, ho⟩
    cases p with
    | closed a => cases ho
    | opn l r => exact ⟨_, _, h.sound _ hp⟩

variable (hL : D.Lawful P.sorts.interp) (K : Kernel R Cost) (hK : K.Refines D)

/-! ## A product followed by a product -/

include hL in
theorem seqProd_sound {p q r : Pr D P} (h : seqProdV K hK p q = some r) :
    SeqS (semP P.sorts.interp p) (semP P.sorts.interp q) (semP P.sorts.interp r) := by
  cases p with
  | closed a =>
    cases q with
    | closed b =>
      simp only [seqProdV, Option.map_eq_some_iff] at h
      obtain ⟨c, hc, rfl⟩ := h
      obtain ⟨-, hs, -⟩ := (Ans.join_val K hK).1 hc
      have e := hL.compose_some _ _ _ hs
      simp only [semP]
      rw [e]
      exact .cc (by rw [← e]; exact hL.live _)
    | opn l r₀ =>
      cases l with
      | none =>
        simp only [seqProdV, glueV, Option.map_some, Option.some.injEq] at h
        subst h
        simp only [semP, lsetO]
        rw [← preS_univ]
        exact .co (by rw [preS_univ]; obtain ⟨⟨x, z⟩, hx⟩ := hL.live a.span; exact ⟨x, z, hx⟩)
      | some x =>
        simp only [seqProdV, glueV, Option.map_map, Option.map_eq_some_iff] at h
        obtain ⟨z, hz, rfl⟩ := h
        have e := hL.compose_some _ _ _ hz
        simp only [semP, lsetO, Function.comp]
        rw [e, lends_comp]
        refine .co ?_
        rw [← lends_comp, ← e]
        obtain ⟨⟨u, v⟩, hu⟩ := hL.live z
        exact ⟨u, v, hu⟩
  | opn l r₀ =>
    cases q with
    | closed b =>
      cases r₀ with
      | none =>
        simp only [seqProdV, glueV, Option.map_some, Option.some.injEq] at h
        subst h
        simp only [semP, rsetO]
        rw [← postS_univ]
        exact .oc (by rw [postS_univ]; obtain ⟨⟨x, z⟩, hx⟩ := hL.live b.span; exact ⟨z, x, hx⟩)
      | some x =>
        simp only [seqProdV, glueV, Option.map_map, Option.map_eq_some_iff] at h
        obtain ⟨z, hz, rfl⟩ := h
        have e := hL.compose_some _ _ _ hz
        simp only [semP, rsetO, Function.comp]
        rw [e, rends_comp]
        refine .oc ?_
        rw [← rends_comp, ← e]
        obtain ⟨⟨u, v⟩, hu⟩ := hL.live z
        exact ⟨v, u, hu⟩
    | opn l' r' =>
      simp only [seqProdV, Option.map_eq_some_iff] at h
      obtain ⟨m, hm, rfl⟩ := h
      simp only [semP]
      refine .oo ?_
      cases r₀ with
      | none =>
        rw [show rsetO P.sorts.interp (none : Option R) = Set.univ from rfl, Set.univ_inter]
        exact lsetO_nonempty hL l'
      | some x =>
        cases l' with
        | none =>
          rw [show lsetO P.sorts.interp (none : Option R) = Set.univ from rfl, Set.inter_univ]
          exact rsetO_nonempty hL (some x)
        | some y =>
          simp only [glueV, Option.map_eq_some_iff] at hm
          obtain ⟨z, hz, -⟩ := hm
          obtain ⟨⟨u, v⟩, k, h₁, h₂⟩ := (compose_iff hL x y).2 ⟨z, hz⟩
          exact ⟨k, ⟨u, h₁⟩, ⟨v, h₂⟩⟩

include hL in
theorem seqProd_complete {p q : Pr D P} {s : SP}
    (hp : ∀ a, p = .closed a → a.goal.rb = none) (hq : ∀ b, q = .closed b → b.goal.lb = none)
    (h : SeqS (semP P.sorts.interp p) (semP P.sorts.interp q) s) :
    ∃ r, seqProdV K hK p q = some r ∧ semP P.sorts.interp r = s := by
  cases p with
  | closed a =>
    cases q with
    | closed b =>
      cases h with
      | cc hne =>
        obtain ⟨z, hz⟩ := (compose_iff hL _ _).1 hne
        obtain ⟨c, hc, hcs, -⟩ := Ans.join_ok (P := P) K hK (a := a) (b := b)
          (.inl ⟨hp a rfl, .inl (hq b rfl)⟩) hz
        refine ⟨.closed c, by simp [seqProdV, hc], ?_⟩
        simp only [semP]
        rw [hcs, hL.compose_some _ _ _ hz]
    | opn l r₀ =>
      cases h with
      | co hne =>
        cases l with
        | none =>
          refine ⟨.opn (some a.span) r₀, by simp [seqProdV, glueV], ?_⟩
          simp only [semP, lsetO]
          rw [preS_univ]
        | some x =>
          simp only [lsetO] at hne ⊢
          rw [← lends_comp] at hne ⊢
          obtain ⟨u, v, huv⟩ := hne
          obtain ⟨z, hz⟩ := (compose_iff hL a.span x).1 ⟨_, huv⟩
          refine ⟨.opn (some z) r₀, by simp [seqProdV, glueV, hz], ?_⟩
          simp only [semP, lsetO]
          rw [hL.compose_some _ _ _ hz]
  | opn l r₀ =>
    cases q with
    | closed b =>
      cases h with
      | oc hne =>
        cases r₀ with
        | none =>
          refine ⟨.opn l (some b.span), by simp [seqProdV, glueV], ?_⟩
          simp only [semP, rsetO]
          rw [postS_univ]
        | some x =>
          simp only [rsetO] at hne ⊢
          rw [← rends_comp] at hne ⊢
          obtain ⟨v, u, huv⟩ := hne
          obtain ⟨z, hz⟩ := (compose_iff hL x b.span).1 ⟨_, huv⟩
          refine ⟨.opn l (some z), by simp [seqProdV, glueV, hz], ?_⟩
          simp only [semP, rsetO]
          rw [hL.compose_some _ _ _ hz]
    | opn l' r' =>
      cases h with
      | oo hne =>
        refine ⟨.opn l r', ?_, rfl⟩
        cases r₀ with
        | none => simp [seqProdV, glueV]
        | some x =>
          cases l' with
          | none => simp [seqProdV, glueV]
          | some y =>
            obtain ⟨k, ⟨u, h₁⟩, ⟨v, h₂⟩⟩ := hne
            obtain ⟨z, hz⟩ := (compose_iff hL x y).1 ⟨(u, v), k, h₁, h₂⟩
            simp [seqProdV, glueV, hz]

include hL in
/-- The products of a stretch of a chain followed by the products of the next
member. -/
theorem seq_step_ex {lb rb : Option R} {S T : Set SP} {ps qs : List (Pr D P)}
    (h₁ : PEx lb none S ps) (h₂ : PEx none rb T qs) :
    PEx lb rb (seqSets S T) (ps.flatMap fun p => qs.filterMap (seqProdV K hK p)) := by
  have hmem : ∀ {r}, r ∈ (ps.flatMap fun p => qs.filterMap (seqProdV K hK p)) ↔
      ∃ p ∈ ps, ∃ q ∈ qs, seqProdV K hK p q = some r := by
    intro r
    simp only [List.mem_flatMap, List.mem_filterMap]
  have hgoal : ∀ c, .closed c ∈ (ps.flatMap fun p => qs.filterMap (seqProdV K hK p)) →
      ∃ a b, .closed a ∈ ps ∧ .closed b ∈ qs ∧ c.goal.lb = a.goal.lb ∧ c.goal.rb = b.goal.rb := by
    intro c hc
    obtain ⟨p, hp, q, hq, e⟩ := hmem.1 hc
    cases p with
    | closed a =>
      cases q with
      | closed b =>
        simp only [seqProdV, Option.map_eq_some_iff, Prod.closed.injEq] at e
        obtain ⟨c', hc', rfl⟩ := e
        obtain ⟨-, -, hg⟩ := (Ans.join_val K hK).1 hc'
        exact ⟨a, b, hp, hq, by rw [hg], by rw [hg]⟩
      | opn l r => simp [seqProdV] at e
    | opn l r =>
      cases q <;> simp [seqProdV] at e
  refine ⟨fun c hc => ?_, fun c hc => ?_, fun r hr => ?_, fun s hs => ?_⟩
  · obtain ⟨a, b, ha, -, e, -⟩ := hgoal c hc
    rw [e, h₁.lb a ha]
  · obtain ⟨a, b, -, hb, -, e⟩ := hgoal c hc
    rw [e, h₂.rb b hb]
  · obtain ⟨p, hp, q, hq, e⟩ := hmem.1 hr
    exact ⟨_, h₁.sound p hp, _, h₂.sound q hq, seqProd_sound hL K hK e⟩
  · obtain ⟨sp, hsp, sq, hsq, h⟩ := hs
    obtain ⟨p, hp, rfl⟩ := h₁.complete sp hsp
    obtain ⟨q, hq, rfl⟩ := h₂.complete sq hsq
    obtain ⟨r, hr, e⟩ := seqProd_complete hL K hK
      (fun a ea => h₁.rb a (ea ▸ hp)) (fun b eb => h₂.lb b (eb ▸ hq)) h
    exact ⟨r, hmem.2 ⟨p, hp, q, hq, hr⟩, e⟩

/-- The members of a chain after its first, with their products: each between
no boundaries, but for the right boundary of the last. -/
inductive TailEx (rb : Option R) : List (List (Pr D P)) → List (Set SP) → Prop
  | last {q : List (Pr D P)} {T : Set SP} : PEx none rb T q → TailEx rb [q] [T]
  | cons {q : List (Pr D P)} {T : Set SP} {qs : List (List (Pr D P))} {Ts : List (Set SP)} :
      PEx none (none : Option R) T q → TailEx rb qs Ts → TailEx rb (q :: qs) (T :: Ts)

include hL in
theorem seq_fold_ex {lb rb : Option R} {qs : List (List (Pr D P))} {Ts : List (Set SP)}
    (ht : TailEx rb qs Ts) : ∀ {S : Set SP} {acc : List (Pr D P)}, PEx lb none S acc →
      PEx lb rb (Ts.foldl seqSets S)
        (qs.foldl (fun acc qs => acc.flatMap fun p => qs.filterMap (seqProdV K hK p)) acc) := by
  induction ht with
  | last hq => intro S acc h₀; exact seq_step_ex hL K hK h₀ hq
  | cons hq _ ih => intro S acc h₀; exact ih (seq_step_ex hL K hK h₀ hq)

omit [DecidableEq R] in
/-- The products of the members of a chain after its first are a tail. -/
theorem tailEx_of {rb : Option R} {N : Nat} (F : Rel × Nat → List (Pr D P))
    (G : Rel × Nat → Set SP) :
    ∀ (tl : List Rel) (k : Nat), tl ≠ [] → k + tl.length = N →
      (∀ x ∈ tl, ∀ i, i + 1 < N → k ≤ i → PEx none (none : Option R) (G (x, i)) (F (x, i))) →
      (∀ x ∈ tl, PEx none rb (G (x, N - 1)) (F (x, N - 1))) →
      TailEx rb ((tl.zipIdx k).map F) ((tl.zipIdx k).map G)
  | [], _, h, _, _, _ => absurd rfl h
  | [x], k, _, hk, _, hl => by
    have hk' : k = N - 1 := by simp at hk; omega
    subst hk'
    exact .last (hl x (by simp))
  | x :: y :: tl, k, _, hk, hm, hl => by
    refine .cons (hm x (by simp) k (by simp at hk; omega) le_rfl) ?_
    exact tailEx_of F G (y :: tl) (k + 1) (by simp) (by simp at hk ⊢; omega)
      (fun z hz i hi hki => hm z (List.mem_cons_of_mem _ hz) i hi (by omega))
      (fun z hz => hl z (List.mem_cons_of_mem _ hz))

/-! ## A rule applied to the answers, and a union -/

omit [DecidableEq R] in
theorem lift_ex {lb rb : Option R} {S : Set SP} {ps : List (Pr D P)}
    {f : Ans D P → Option (Ans D P)} (h : PEx lb rb S ps)
    (hf₁ : ∀ a c, f a = some c → c.span = a.span ∧ c.goal.lb = a.goal.lb ∧ c.goal.rb = a.goal.rb)
    (hf₂ : ∀ a, .closed a ∈ ps → ∃ c, f a = some c) :
    PEx lb rb S (liftV f ps) := by
  have hcl : ∀ c, .closed c ∈ liftV f ps ↔ ∃ a, .closed a ∈ ps ∧ f a = some c := by
    intro c
    unfold liftV
    rw [List.mem_filterMap]
    constructor
    · rintro ⟨p, hp, e⟩
      cases p with
      | closed a =>
        simp only [Option.map_eq_some_iff, Prod.closed.injEq] at e
        obtain ⟨c', hc', rfl⟩ := e
        exact ⟨a, hp, hc'⟩
      | opn l r => simp at e
    · rintro ⟨a, ha, e⟩
      exact ⟨_, ha, by simp [e]⟩
  refine ⟨fun c hc => ?_, fun c hc => ?_, fun r hr => ?_, fun s hs => ?_⟩
  · obtain ⟨a, ha, e⟩ := (hcl c).1 hc
    rw [(hf₁ a c e).2.1, h.lb a ha]
  · obtain ⟨a, ha, e⟩ := (hcl c).1 hc
    rw [(hf₁ a c e).2.2, h.rb a ha]
  · cases r with
    | closed c =>
      obtain ⟨a, ha, e⟩ := (hcl c).1 hr
      have := h.sound _ ha
      simp only [semP] at this ⊢
      rwa [(hf₁ a c e).1]
    | opn l r =>
      obtain ⟨p, hp, e⟩ := List.mem_filterMap.1 hr
      cases p with
      | closed a => simp at e
      | opn l' r' => cases e; exact h.sound _ hp
  · obtain ⟨p, hp, rfl⟩ := h.complete s hs
    cases p with
    | closed a =>
      obtain ⟨c, hc⟩ := hf₂ a hp
      refine ⟨.closed c, (hcl c).2 ⟨a, hp, hc⟩, ?_⟩
      simp only [semP]
      rw [(hf₁ a c hc).1]
    | opn l r => exact ⟨.opn l r, List.mem_filterMap.2 ⟨_, hp, rfl⟩, rfl⟩

omit [DecidableEq R] in
theorem union_ex {ι : Type} {lb rb : Option R} (L : List ι) (S : ι → Set SP)
    (ps : ι → List (Pr D P)) (h : ∀ i ∈ L, PEx lb rb (S i) (ps i)) :
    PEx lb rb {r | ∃ i ∈ L, r ∈ S i} (L.flatMap ps) := by
  refine ⟨fun c hc => ?_, fun c hc => ?_, fun r hr => ?_, ?_⟩
  · obtain ⟨i, hi, hc⟩ := List.mem_flatMap.1 hc
    exact (h i hi).lb c hc
  · obtain ⟨i, hi, hc⟩ := List.mem_flatMap.1 hc
    exact (h i hi).rb c hc
  · obtain ⟨i, hi, hr⟩ := List.mem_flatMap.1 hr
    exact ⟨i, hi, (h i hi).sound r hr⟩
  · rintro s ⟨i, hi, hs⟩
    obtain ⟨p, hp, e⟩ := (h i hi).complete s hs
    exact ⟨p, List.mem_flatMap.2 ⟨i, hi, hp⟩, e⟩

/-! ## A meet -/

/-- The answers relate exactly the relations of a set, between the
boundaries. -/
structure AEx (lb rb : Option R) (S : Set PRel) (as : List (Ans D P)) : Prop where
  lb : ∀ a ∈ as, a.goal.lb = lb
  rb : ∀ a ∈ as, a.goal.rb = rb
  sound : ∀ a ∈ as, den P.sorts.interp a.span ∈ S
  complete : ∀ X ∈ S, ∃ a ∈ as, den P.sorts.interp a.span = X

omit [DecidableEq R] in
theorem PEx.aex {lb rb : Option R} {S : Set SP} {ps : List (Pr D P)} (h : PEx lb rb S ps) :
    AEx lb rb (closedPart S) (closedOf ps) := by
  refine ⟨fun a ha => h.lb a (mem_closedOf.1 ha), fun a ha => h.rb a (mem_closedOf.1 ha),
    fun a ha => h.sound _ (mem_closedOf.1 ha), fun X hX => ?_⟩
  obtain ⟨p, hp, e⟩ := h.complete _ hX
  cases p with
  | closed a =>
    simp only [semP, SP.closed.injEq] at e
    exact ⟨a, mem_closedOf.2 hp, e⟩
  | opn l r => cases e

include hL in
theorem meet_step_ex {lb rb : Option R} {S T : Set PRel} {as bs : List (Ans D P)}
    (h₁ : AEx lb rb S as) (h₂ : AEx lb rb T bs) :
    AEx lb rb (meetSets S T)
      (as.flatMap fun a => bs.filterMap fun b => (Ans.meetA D P K hK a b).val) := by
  have hmem : ∀ {c}, c ∈ (as.flatMap fun a => bs.filterMap fun b =>
      (Ans.meetA D P K hK a b).val) ↔ ∃ a ∈ as, ∃ b ∈ bs, (Ans.meetA D P K hK a b).val = some c := by
    intro c
    simp only [List.mem_flatMap, List.mem_filterMap]
  refine ⟨fun c hc => ?_, fun c hc => ?_, fun c hc => ?_, fun Z hZ => ?_⟩
  · obtain ⟨a, ha, b, -, e⟩ := hmem.1 hc
    obtain ⟨-, -, hg⟩ := (Ans.meetA_val K hK).1 e
    rw [hg]; exact h₁.lb a ha
  · obtain ⟨a, ha, b, -, e⟩ := hmem.1 hc
    obtain ⟨-, -, hg⟩ := (Ans.meetA_val K hK).1 e
    rw [hg]; exact h₁.rb a ha
  · obtain ⟨a, ha, b, hb, e⟩ := hmem.1 hc
    obtain ⟨-, hs, -⟩ := (Ans.meetA_val K hK).1 e
    have e' := hL.meet_some _ _ _ hs
    exact ⟨_, h₁.sound a ha, _, h₂.sound b hb, e', by rw [e']; exact (meet_iff hL _ _).2 ⟨_, hs⟩⟩
  · obtain ⟨X, hX, Y, hY, rfl, hne⟩ := hZ
    obtain ⟨a, ha, rfl⟩ := h₁.complete X hX
    obtain ⟨b, hb, rfl⟩ := h₂.complete Y hY
    obtain ⟨z, hz⟩ := (meet_iff hL _ _).1 hne
    obtain ⟨c, hc, hcs, -⟩ := Ans.meetA_ok (P := P) K hK (a := a) (b := b)
      (.inl ⟨by rw [h₁.lb a ha, h₂.lb b hb], by rw [h₁.rb a ha, h₂.rb b hb]⟩) hz
    exact ⟨c, hmem.2 ⟨a, ha, b, hb, hc⟩, by rw [hcs, hL.meet_some _ _ _ hz]⟩

include hL in
theorem meet_fold_ex {lb rb : Option R} : ∀ {Ts : List (Set PRel)} {As : List (List (Ans D P))},
    List.Forall₂ (AEx lb rb) Ts As → ∀ {S : Set PRel} {acc : List (Ans D P)}, AEx lb rb S acc →
      AEx lb rb (Ts.foldl meetSets S)
        (As.foldl (fun acc bs => acc.flatMap fun a => bs.filterMap fun b =>
          (Ans.meetA D P K hK a b).val) acc)
  | _, _, .nil, _, _, h₀ => h₀
  | _, _, .cons hx ht, _, _, h₀ => meet_fold_ex ht (meet_step_ex hL K hK h₀ hx)

include hL in
/-- The closed products of a meet from the closed products of its members. -/
theorem meetAll_ex {lb rb : Option R} {Ts : List (Set PRel)} {As : List (List (Ans D P))}
    (h : List.Forall₂ (AEx lb rb) Ts As) (hne : Ts ≠ []) :
    AEx lb rb (meetAllS Ts) (meetAllV K hK As) := by
  cases h with
  | nil => exact absurd rfl hne
  | cons h₀ ht => exact meet_fold_ex hL K hK ht h₀

include hL in
/-- The products of a meet from the products of its members. -/
theorem meet_ex {lb rb : Option R} (hl : IsBound D lb) (hr : IsBound D rb) {xs : List Rel}
    (hne : xs ≠ []) (S : Rel → Set SP) (ps : Rel → List (Pr D P))
    (h : ∀ x ∈ xs, PEx lb rb (S x) (ps x)) :
    PEx lb rb (meetS (bset P.sorts.interp lb) (bset P.sorts.interp rb) (xs.map S))
      ((meetAllV K hK ((xs.map ps).map closedOf)).map .closed ++
        if ((xs.map ps).all fun ps => !ps.isEmpty) && ((xs.map ps).any fun ps => ps.any Prod.isOpn)
        then [.opn lb rb] else []) := by
  have hA : AEx lb rb (meetAllS ((xs.map S).map closedPart))
      (meetAllV K hK ((xs.map ps).map closedOf)) := by
    refine meetAll_ex hL K hK ?_ (by simpa using hne)
    rw [List.map_map, List.map_map, List.forall₂_map_left_iff, List.forall₂_map_right_iff]
    exact List.forall₂_same.2 fun x hx => (h x hx).aex
  have hflag : (((xs.map ps).all fun ps => !ps.isEmpty) &&
      ((xs.map ps).any fun ps => ps.any Prod.isOpn)) = true ↔
      (∀ T ∈ xs.map S, T.Nonempty) ∧ ∃ T ∈ xs.map S, HasOpn T := by
    simp only [Bool.and_eq_true, List.all_eq_true, List.any_eq_true, List.mem_map,
      forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, exists_exists_and_eq_and,
      Bool.not_eq_eq_eq_not, Bool.not_true, List.isEmpty_eq_false_iff]
    constructor
    · rintro ⟨h₁, x, hx, h₂⟩
      exact ⟨fun x hx => (h x hx).nonempty.2 (h₁ x hx), x, hx, (h x hx).hasOpn.2
        (List.any_eq_true.2 h₂)⟩
    · rintro ⟨h₁, x, hx, h₂⟩
      exact ⟨fun x hx => (h x hx).nonempty.1 (h₁ x hx), x, hx,
        List.any_eq_true.1 ((h x hx).hasOpn.1 h₂)⟩
  have hcl : ∀ c : Ans D P, (Prod.closed c : Pr D P) ∈
      ((meetAllV K hK ((xs.map ps).map closedOf)).map .closed ++
        if ((xs.map ps).all fun ps => !ps.isEmpty) && ((xs.map ps).any fun ps => ps.any Prod.isOpn)
        then [.opn lb rb] else []) → c ∈ meetAllV K hK ((xs.map ps).map closedOf) := by
    intro c hc
    rcases List.mem_append.1 hc with hc | hc
    · obtain ⟨c', hc', e⟩ := List.mem_map.1 hc
      cases e; exact hc'
    · split at hc
      · simp at hc
      · cases hc
  refine ⟨fun c hc => hA.lb c (hcl c hc), fun c hc => hA.rb c (hcl c hc), fun r hr' => ?_,
    fun s hs => ?_⟩
  · rcases List.mem_append.1 hr' with hm | hm
    · obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hm
      exact .inl ⟨_, hA.sound c hc, rfl⟩
    · split at hm
      · next hf =>
        obtain rfl : r = .opn lb rb := by simpa using hm
        refine .inr ⟨?_, hflag.1 hf⟩
        simp only [semP]
        rw [lsetO_bound hL hl, rsetO_bound hL hr]
      · cases hm
  · rcases hs with ⟨X, hX, rfl⟩ | ⟨rfl, hf⟩
    · obtain ⟨c, hc, e⟩ := hA.complete X hX
      exact ⟨.closed c, List.mem_append_left _ (List.mem_map_of_mem hc), by simp only [semP]; rw [e]⟩
    · refine ⟨.opn lb rb, List.mem_append_right _ ?_, ?_⟩
      · have hfl := hflag.2 hf
        simp only [hfl, ite_true, List.mem_singleton]
      · simp only [semP]
        rw [lsetO_bound hL hl, rsetO_bound hL hr]

/-! ## The whole unfolding -/

include hL in
/-- The products `Unfold.eager` builds are exactly the products of the goal. -/
theorem eager_ex (hP : ProgFO P) : ∀ (d : Nat) (lb : Option R) (n : Rel) (rb : Option R),
    IsBound D lb → IsBound D rb → Normal n → n.FO →
    PEx lb rb (SE P P.sorts.interp d (bset P.sorts.interp lb) n (bset P.sorts.interp rb))
      (eager (K := DerivationKernel.over D K hK P) d lb n rb).val
  | 0, lb, n, rb, hl, hr, _, _ => by
    rw [eager_zero, se_zero]
    refine ⟨fun a ha => by simp at ha, fun a ha => by simp at ha, fun p hp => ?_, fun s hs => ?_⟩
    · obtain rfl : p = .opn lb rb := by simpa using hp
      show SP.opn _ _ = SP.opn _ _
      rw [lsetO_bound hL hl, rsetO_bound hL hr]
    · obtain rfl : s = .opn _ _ := hs
      refine ⟨.opn lb rb, by simp, ?_⟩
      show SP.opn _ _ = SP.opn _ _
      rw [lsetO_bound hL hl, rsetO_bound hL hr]
  | d + 1, lb, n, rb, hl, hr, hn, hfo => by
    have hok := eager_ok hL K hK hP
    cases hv : n.view.forget with
    | span u =>
      obtain ⟨s, rfl⟩ := forget_span hv
      rw [eager_span K hK d lb _ rb hv, se_span]
      have hfo' : s.firstOrder = true := hfo s (by simp [RelOf.spans])
      have hmem : ∀ {c : Ans D P}, (Prod.closed c : Pr D P) ∈
          (Ans.leaf D P K hK lb (.span s) rb).val.toList.map .closed ↔
          (Ans.leaf D P K hK lb (.span s) rb).val = some c := by
        intro c
        simp only [List.mem_map, Option.mem_toList, Prod.closed.injEq, exists_eq_right]
      refine ⟨fun c hc => ?_, fun c hc => ?_, fun p hp => ?_, fun r hr => ?_⟩
      · obtain ⟨s', -, -, -, -, hcg⟩ := (Ans.leaf_val K hK).1 (hmem.1 hc)
        rw [hcg]
      · obtain ⟨s', -, -, -, -, hcg⟩ := (Ans.leaf_val K hK).1 (hmem.1 hc)
        rw [hcg]
      · obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hp
        obtain ⟨s', hs, -, -, hsb, -⟩ := (Ans.leaf_val K hK).1 (Option.mem_toList.1 hc)
        cases hs
        have e := spanBoth_den hL hsb
        rw [wrap_restr hL hl hr] at e
        exact ⟨by simp only [semP]; rw [e], by rw [← e]; exact hL.live _⟩
      · obtain ⟨rfl, hne⟩ := hr
        have hden := denO_spanBoth hL hfo' lb rb
        rw [wrap_restr hL hl hr] at hden
        cases hsb : spanBoth D lb s rb with
        | none =>
          rw [hsb, Domain.denO_none] at hden
          exact absurd hden.symm hne.ne_empty
        | some z =>
          rw [hsb, Domain.denO_some] at hden
          obtain ⟨c, hc, hcs, -⟩ := Ans.leaf_ok (P := P) K hK hl hr hsb
          exact ⟨.closed c, hmem.2 hc, by simp only [semP]; rw [hcs, hden]⟩
    | call m f =>
      obtain ⟨b, hb⟩ := forget_call (P := P) hv
      rw [eager_call K hK d lb n rb hv hb, se_call hv hb]
      have hbn := bodyOf_normal hb
      have hbf := bodyOf_fo hP hb
      refine lift_ex (eager_ex hP d lb b rb hl hr hbn hbf)
        (fun a c e => ?_) (fun a ha => ?_)
      · obtain ⟨-, hs, hg⟩ := Ans.unfold_val.1 e
        exact ⟨hs, by rw [hg], by rw [hg]⟩
      · obtain ⟨c, hc, -⟩ := Ans.unfold_ok (a := a) (n := n) (by
          rw [hb, (hok d lb b rb hl hr hbn hbf).goal a (mem_closedOf.2 ha)])
        exact ⟨c, hc⟩
    | union xs =>
      have hvu := forget_union hv
      have hparts := hn.view_union_eq hvu
      rw [eager_union K hK d lb n rb hv, se_union hv]
      have hzip : ∀ (r : SP), (∃ p ∈ xs.zipIdx, r ∈ SE P P.sorts.interp d (bset P.sorts.interp lb)
          p.1 (bset P.sorts.interp rb)) ↔ ∃ x ∈ xs, r ∈ SE P P.sorts.interp d
            (bset P.sorts.interp lb) x (bset P.sorts.interp rb) := by
        intro r
        constructor
        · rintro ⟨⟨x, i⟩, hp, hG⟩
          exact ⟨x, List.mem_of_getElem? (List.mem_zipIdx_iff_getElem?.1 hp), hG⟩
        · rintro ⟨x, hx, hG⟩
          obtain ⟨i, hi⟩ := List.getElem?_of_mem hx
          exact ⟨(x, i), List.mem_zipIdx_iff_getElem?.2 hi, hG⟩
      refine (union_ex (lb := lb) (rb := rb) xs.zipIdx
        (fun p => SE P P.sorts.interp d (bset P.sorts.interp lb) p.1 (bset P.sorts.interp rb))
        (fun p => liftV (fun a => (Ans.inj D P a n p.2).val)
          (eager (K := DerivationKernel.over D K hK P) d lb p.1 rb).val) (fun p hp => ?_)).of_eq
        (by ext r; exact (hzip r).symm)
      have hx : xs[p.2]? = some p.1 := List.mem_zipIdx_iff_getElem?.1 hp
      have hm : p.1 ∈ n.view.members := by rw [hvu]; exact List.mem_of_getElem? hx
      have hxn := hn.view_members hm
      have hxf := hfo.view_members hm
      refine lift_ex (eager_ex hP d lb p.1 rb hl hr hxn hxf) (fun a c e => ?_) (fun a ha => ?_)
      · obtain ⟨-, hs, hg⟩ := Ans.inj_val.1 e
        exact ⟨hs, by rw [hg], by rw [hg]⟩
      · obtain ⟨c, hc, -⟩ := Ans.inj_ok (a := a) (u := n) (i := p.2) (by
          rw [← hparts, (hok d lb p.1 rb hl hr hxn hxf).goal a (mem_closedOf.2 ha)]; exact hx)
        exact ⟨c, hc⟩
    | chain xs =>
      have hvc := forget_chain hv
      obtain ⟨h2, hmem, -⟩ := hn.view_chain hvc
      rw [eager_chain K hK d lb n rb hv, se_chain hv]
      obtain ⟨x₀, tl, rfl⟩ : ∃ x₀ tl, xs = x₀ :: tl := by
        cases xs with
        | nil => simp at h2
        | cons a b => exact ⟨a, b, rfl⟩
      have htl : 0 < tl.length := by simp at h2; omega
      have hin : ∀ x ∈ x₀ :: tl, Normal x ∧ x.FO := fun x hx =>
        ⟨(hmem x hx).1, hfo.view_members (by rw [hvc]; exact hx)⟩
      have ht := tailEx_of (D := D) (P := P) (rb := rb) (N := tl.length + 1)
        (fun p => (eager (K := DerivationKernel.over D K hK P) d (if p.2 = 0 then lb else none) p.1
          (if p.2 + 1 = tl.length + 1 then rb else none)).val)
        (fun p => SE P P.sorts.interp d (if p.2 = 0 then bset P.sorts.interp lb else Set.univ) p.1
          (if p.2 + 1 = tl.length + 1 then bset P.sorts.interp rb else Set.univ)) tl 1
        (List.ne_nil_of_length_pos htl) (by omega)
        (fun x hx i hi hki => by
          have e₁ : i ≠ 0 := by omega
          have e₂ : i + 1 ≠ tl.length + 1 := by omega
          simp only [e₁, e₂, ite_false]
          exact eager_ex hP d none x none (isBound_none D) (isBound_none D)
            (hin x (List.mem_cons_of_mem _ hx)).1 (hin x (List.mem_cons_of_mem _ hx)).2)
        (fun x hx => by
          have e₁ : tl.length + 1 - 1 ≠ 0 := by omega
          have e₂ : tl.length + 1 - 1 + 1 = tl.length + 1 := by omega
          simp only [e₁, e₂, ite_false, ite_true]
          exact eager_ex hP d none x rb (isBound_none D) hr
            (hin x (List.mem_cons_of_mem _ hx)).1 (hin x (List.mem_cons_of_mem _ hx)).2)
      have h₀ := eager_ex hP d lb x₀ none hl (isBound_none D) (hin x₀ (by simp)).1
        (hin x₀ (by simp)).2
      have := seq_fold_ex hL K hK ht h₀
      have e₂ : (0 + 1 = tl.length + 1) = False := by
        simp only [eq_iff_iff, iff_false]; omega
      simp only [List.zipIdx_cons, List.map_cons, seqAllV, chainS, ite_true, List.length_cons, e₂,
        ite_false]
      exact this
    | meet xs =>
      have hvm := forget_meet hv
      obtain ⟨h2, hmem, -, -⟩ := hn.view_meet hvm
      rw [eager_meet K hK d lb n rb hv, se_meet hv]
      exact meet_ex hL K hK hl hr (by rintro rfl; simp at h2)
        (fun x => SE P P.sorts.interp d (bset P.sorts.interp lb) x (bset P.sorts.interp rb))
        (fun x => (eager (K := DerivationKernel.over D K hK P) d lb x rb).val)
        (fun x hx => eager_ex hP d lb x rb hl hr (hmem x hx).1
          (hfo.view_members (by rw [hvm]; exact hx)))

include hL in
/-- The unfolding race says the unfolding is final exactly when it has no open
product. -/
theorem eagerRace_final (hP : ProgFO P) (d : Nat) (g : GoalOf R Rel) (hg : GoalOk D g) :
    (eagerRace (K := DerivationKernel.over D K hK P) d g).val.1 = true ↔
      Final P P.sorts.interp d (bset P.sorts.interp g.lb) g.node (bset P.sorts.interp g.rb) := by
  have h := (eager_ex hL K hK hP d g.lb g.node g.rb hg.lb hg.rb hg.normal hg.fo).hasOpn
  rw [eagerRace_val, Final, h]
  split <;> simp [*]

end Unfold

end Tabled

end RwLog
