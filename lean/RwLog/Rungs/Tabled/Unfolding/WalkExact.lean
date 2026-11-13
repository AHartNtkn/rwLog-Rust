/-
# A walk hands on exactly the products of the unfolding

`Unfolding/Model.lean` says what the unfolding of a node to a depth relates,
product by product (`SE`). Here: when interfaces are exact
(`Domain.ExactIface`), what a walk holds of the items it hands on (`semI`:
the pairs of an answer, the far ends of an open product) is what a walk
holds of exactly those products (`walk_ex`), in either direction and under
whatever was pushed on the near side.

So the race answered by a walk says the unfolding is final exactly when the
model has no open product (`walkRace_final`): the same verdict as the whole
unfolding (`eagerRace_final`).

Exact interfaces are what makes the restriction a walk pushes into the next
member of a chain lose nothing and keep nothing dead: the interface of an
answer lets through exactly its far ends (`bset_farBound`).
-/
import RwLog.Rungs.Tabled.Unfolding.Walk
import RwLog.Rungs.Tabled.Unfolding.EagerExact

namespace RwLog

namespace Tabled

namespace Unfold

open Answer

variable {R : Type} [Answer R] [DecidableEq R] {D : Domain R} {P : Program}

/-! ## What a walk holds of an item -/

/-- What a walk holds of an item, by what it relates. -/
def semI (M : Interp) (rev : Bool) : It D P → SI
  | .closed a => .closed (den M a.span)
  | .opn none => .opn Set.univ
  | .opn (some t) => .opn (farEnds rev (den M t))

/-- What a walk holds of the items of a list. -/
def Sem (M : Interp) (rev : Bool) (is : List (It D P)) : Set SI :=
  {s | ∃ it ∈ is, semI M rev it = s}

section sem

variable {M : Interp} {rev : Bool}

omit [DecidableEq R] in
theorem sem_nil : Sem M rev ([] : List (It D P)) = ∅ := by
  ext s; simp [Sem]

omit [DecidableEq R] in
theorem sem_append (xs ys : List (It D P)) : Sem M rev (xs ++ ys) = Sem M rev xs ∪ Sem M rev ys := by
  ext s
  simp only [Sem, List.mem_append, Set.mem_ofPred_eq, Set.mem_union]
  constructor
  · rintro ⟨it, h | h, e⟩
    · exact .inl ⟨it, h, e⟩
    · exact .inr ⟨it, h, e⟩
  · rintro (⟨it, h, e⟩ | ⟨it, h, e⟩)
    · exact ⟨it, .inl h, e⟩
    · exact ⟨it, .inr h, e⟩

omit [DecidableEq R] in
theorem sem_flatMap {α : Type} (l : List α) (f : α → List (It D P)) :
    Sem M rev (l.flatMap f) = {s | ∃ x ∈ l, s ∈ Sem M rev (f x)} := by
  ext s
  constructor
  · rintro ⟨it, h, e⟩
    obtain ⟨x, hx, hit⟩ := List.mem_flatMap.1 h
    exact ⟨x, hx, it, hit, e⟩
  · rintro ⟨x, hx, it, hit, e⟩
    exact ⟨it, List.mem_flatMap.2 ⟨x, hx, hit⟩, e⟩

omit [DecidableEq R] in
/-- A rule that keeps the representative of every answer keeps what the walk
holds. -/
theorem sem_lift {is : List (It D P)} {f : Ans D P → Option (Ans D P)}
    (h₁ : ∀ a c, f a = some c → c.span = a.span)
    (h₂ : ∀ a, Item.closed a ∈ is → ∃ c, f a = some c) :
    Sem M rev (is.flatMap fun it => (liftItemV f it).toList) = Sem M rev is := by
  ext s
  constructor
  · rintro ⟨it', h, rfl⟩
    obtain ⟨it, hit, e⟩ := mem_lift.1 h
    refine ⟨it, hit, ?_⟩
    cases it with
    | closed a =>
      simp only [liftItemV, Option.map_eq_some_iff] at e
      obtain ⟨c, hc, rfl⟩ := e
      simp only [semI]
      rw [h₁ a c hc]
    | opn t =>
      obtain rfl : Item.opn t = it' := by simpa [liftItemV] using e
      rfl
  · rintro ⟨it, hit, rfl⟩
    cases it with
    | closed a =>
      obtain ⟨c, hc⟩ := h₂ a hit
      refine ⟨.closed c, mem_lift.2 ⟨_, hit, by simp [liftItemV, hc]⟩, ?_⟩
      simp only [semI]
      rw [h₁ a c hc]
    | opn t => exact ⟨.opn t, mem_lift.2 ⟨_, hit, rfl⟩, rfl⟩

end sem

/-! ## The products in the direction of a walk -/

/-- The products of the unfolding of a node between the terms let through on
the near side and those let through on the far side. -/
def SED (P : Program) (M : Interp) (rev : Bool) (d : Nat) (N : Set GTerm) (n : Rel)
    (F : Set GTerm) : Set SP :=
  if rev then SE P M d F n N else SE P M d N n F

/-- The pairs of `X` between the terms of the near side and those of the far
side. -/
def restrO (rev : Bool) (N : Set GTerm) (X : PRel) (F : Set GTerm) : PRel :=
  if rev then restr F X N else restr N X F

theorem restrD_restrO (rev : Bool) (π : Set GTerm) (X : PRel) (F : Set GTerm) :
    restrD rev π (restrO rev Set.univ X F) = restrO rev π X F := by
  cases rev
  · ext ⟨x, z⟩
    simp only [restrD_false, restrO, restr, Set.mem_ofPred_eq, Set.mem_univ, true_and, and_true]
    constructor
    · rintro ⟨⟨h, hz⟩, hx⟩; exact ⟨h, hx, hz⟩
    · rintro ⟨h, hx, hz⟩; exact ⟨⟨h, hz⟩, hx⟩
  · ext ⟨x, z⟩
    simp only [restrD_true, restrO, restr, Set.mem_ofPred_eq, Set.mem_univ, true_and, and_true,
      ite_true]
    constructor
    · rintro ⟨⟨h, hx⟩, hz⟩; exact ⟨h, hx, hz⟩
    · rintro ⟨h, hx, hz⟩; exact ⟨⟨h, hx⟩, hz⟩

theorem restrO_mono (rev : Bool) {π : Set GTerm} (X : PRel) (F : Set GTerm) :
    restrO rev π X F ⊆ restrO rev Set.univ X F := by
  rw [← restrD_restrO]
  cases rev
  · rintro p ⟨h, -, -⟩; exact h
  · rintro p ⟨h, -, -⟩; exact h

section sed

variable {M : Interp} {rev : Bool}

theorem sed_zero (N F : Set GTerm) (n : Rel) :
    SED P M rev 0 N n F = {if rev then SP.opn F N else SP.opn N F} := by
  cases rev <;> rfl

theorem sed_span {d : Nat} {N F : Set GTerm} {s : Span} :
    SED P M rev (d + 1) N (.span s) F =
      {r | r = .closed (restrO rev N (s.den.at M) F) ∧ (restrO rev N (s.den.at M) F).Nonempty} := by
  cases rev
  · exact (se_span : SE P M (d + 1) N (.span s) F = _)
  · exact (se_span : SE P M (d + 1) F (.span s) N = _)

theorem sed_call {d : Nat} {N F : Set GTerm} {e b : Rel} {m : Name} {f : Bool}
    (h : e.view.forget = .call m f) (hb : Charged.bodyOf P e = some b) :
    SED P M rev (d + 1) N e F = SED P M rev d N b F := by
  cases rev
  · exact se_call h hb
  · exact se_call h hb

theorem sed_union {d : Nat} {N F : Set GTerm} {e : Rel} {xs : List Rel}
    (h : e.view.forget = .union xs) :
    SED P M rev (d + 1) N e F = {r | ∃ x ∈ xs, r ∈ SED P M rev d N x F} := by
  cases rev
  · exact se_union h
  · exact se_union h

theorem sed_live (d : Nat) {N F : Set GTerm} (n : Rel) (hN : N.Nonempty) (hF : F.Nonempty) :
    ∀ p ∈ SED P M rev d N n F, p.Live := by
  cases rev
  · exact se_live d N n F hN hF
  · exact se_live d F n N hF hN

end sed

/-! ## What is pushed on the near side -/

/-- The products a walk goes through under its near context: those between
the near boundary and the far one, or, when the near boundary was pushed
there by the walk, those from anywhere restricted to it. -/
def WS (P : Program) (M : Interp) (rev : Bool) (d : Nat) (c : Near R) (n : Rel)
    (far : Option R) : Set SP :=
  if c.pushed then pushSet rev (bset M c.bound) (SED P M rev d Set.univ n (bset M far))
  else SED P M rev d (bset M c.bound) n (bset M far)

/-- What a walk holds of them. -/
def WT (P : Program) (M : Interp) (rev : Bool) (d : Nat) (c : Near R) (n : Rel)
    (far : Option R) : Set SI :=
  farD rev '' WS P M rev d c n far

theorem univ_nonempty' : (Set.univ : Set GTerm).Nonempty := ⟨.sym "", trivial⟩

section ctx

variable {M : Interp} {rev : Bool} (hL : D.Lawful M)

theorem pushSet_union {ι : Type} (π : Set GTerm) (L : List ι) (S : ι → Set SP) :
    pushSet rev π {r | ∃ i ∈ L, r ∈ S i} = {r | ∃ i ∈ L, r ∈ pushSet rev π (S i)} := by
  ext r
  constructor
  · rintro ⟨p, ⟨i, hi, hp⟩, h⟩; exact ⟨i, hi, p, hp, h⟩
  · rintro ⟨i, hi, p, hp, h⟩; exact ⟨p, ⟨i, hi, hp⟩, h⟩

include hL in
omit [DecidableEq R] in
/-- With no boundary on the near side nothing is restricted. -/
theorem ws_none {d : Nat} {c : Near R} {n : Rel} {far : Option R} (hc : c.bound = none)
    (hf : IsBound D far) :
    WS P M rev d c n far = SED P M rev d Set.univ n (bset M far) := by
  unfold WS
  rw [hc]
  split
  · exact pushSet_univ rev (sed_live d n univ_nonempty' (bset_nonempty hL hf))
  · rfl

include hL in
omit [DecidableEq R] in
/-- Where the walk pushed nothing the goal does not have, a node stands
between its boundaries. -/
theorem ws_plain {d : Nat} {c : Near R} {n : Rel} {far : Option R} (hp : c.isPushed = false)
    (hf : IsBound D far) :
    WS P M rev d c n far = SED P M rev d (bset M c.bound) n (bset M far) := by
  cases hb : c.bound with
  | none => rw [ws_none hL hb hf]; rfl
  | some b =>
    have : c.pushed = false := by
      simpa [Near.isPushed, hb] using hp
    simp only [WS, this, Bool.false_eq_true, ite_false, hb]

include hL in
omit [DecidableEq R] in
theorem wt_zero {c : Near R} {n : Rel} {far : Option R} (hc : IsBound D c.bound) :
    WT P M rev 0 c n far = {.opn (bset M far)} := by
  unfold WT WS
  have hne := bset_nonempty hL hc
  split
  · rw [sed_zero]
    ext s
    constructor
    · rintro ⟨r, ⟨p, hp, h⟩, rfl⟩
      obtain rfl := hp
      cases rev <;> cases h <;> rfl
    · rintro rfl
      cases rev
      · exact ⟨_, ⟨_, rfl, .opn (by simpa [nearE] using hne)⟩, rfl⟩
      · exact ⟨_, ⟨_, rfl, .opn (by simpa [nearE] using hne)⟩, rfl⟩
  · rw [sed_zero]
    cases rev <;> simp [farD, farE]

omit [DecidableEq R] in
theorem ws_span {d : Nat} {c : Near R} {s : Span} {far : Option R} :
    WS P M rev (d + 1) c (.span s) far =
      SED P M rev (d + 1) (bset M c.bound) (.span s) (bset M far) := by
  unfold WS
  split
  · rw [sed_span, sed_span]
    ext r
    constructor
    · rintro ⟨p, ⟨rfl, -⟩, h⟩
      cases h with
      | closed hne =>
        rw [restrD_restrO] at hne ⊢
        exact ⟨rfl, hne⟩
    · rintro ⟨rfl, hne⟩
      refine ⟨_, ⟨rfl, hne.mono (restrO_mono rev _ _)⟩, ?_⟩
      have := PushD.closed (rev := rev) (π := bset M c.bound)
        (X := restrO rev Set.univ (s.den.at M) (bset M far)) (by rwa [restrD_restrO])
      rwa [restrD_restrO] at this
  · rfl

omit [DecidableEq R] in
theorem ws_call {d : Nat} {c : Near R} {e b : Rel} {far : Option R} {m : Name} {f : Bool}
    (h : e.view.forget = .call m f) (hb : Charged.bodyOf P e = some b) :
    WS P M rev (d + 1) c e far = WS P M rev d c b far := by
  unfold WS
  rw [sed_call h hb, sed_call h hb]

omit [DecidableEq R] in
theorem ws_union {d : Nat} {c : Near R} {e : Rel} {xs : List Rel} {far : Option R}
    (h : e.view.forget = .union xs) :
    WS P M rev (d + 1) c e far = {r | ∃ x ∈ xs, r ∈ WS P M rev d c x far} := by
  unfold WS
  rw [sed_union h, sed_union h]
  split
  · exact pushSet_union _ xs _
  · rfl

end ctx

/-! ## The members of a chain, in the order they are walked -/

/-- The products of the members of a chain: only the first is next to what
is let through on the one side, only the last to what is let through on the
other. -/
def membS (S : Set GTerm → Rel → Set GTerm → Set SP) :
    Set GTerm → Set GTerm → List Rel → List (Set SP)
  | _, _, [] => []
  | A, B, [x] => [S A x B]
  | A, B, x :: y :: zs => S A x Set.univ :: membS S Set.univ B (y :: zs)

theorem zip_membS (S : Set GTerm → Rel → Set GTerm → Set SP) (B : Set GTerm) :
    ∀ (xs : List Rel) (k : Nat) (A : Set GTerm),
      (xs.zipIdx k).map (fun p => S (if p.2 = k then A else Set.univ) p.1
        (if p.2 + 1 = k + xs.length then B else Set.univ)) = membS S A B xs
  | [], _, _ => rfl
  | [x], k, A => by simp [membS]
  | x :: y :: zs, k, A => by
    have ih := zip_membS S B (y :: zs) (k + 1) Set.univ
    rw [List.zipIdx_cons, List.map_cons, membS, ← ih]
    congr 1
    · have : ¬ (k + 1 = k + (x :: y :: zs).length) := by simp
      simp only [this, ite_true, ite_false]
    · refine List.map_congr_left fun p hp => ?_
      have hk : k + 1 ≤ p.2 := by
        obtain ⟨x', i⟩ := p
        exact (List.mem_zipIdx hp).1
      have e₁ : ¬ p.2 = k := by omega
      have e₂ : (p.2 + 1 = k + (x :: y :: zs).length) = (p.2 + 1 = k + 1 + (y :: zs).length) := by
        simp only [List.length_cons, eq_iff_iff]; omega
      simp only [e₁, e₂, ite_false, ite_self]

theorem membS_snoc (S : Set GTerm → Rel → Set GTerm → Set SP) (B : Set GTerm) (z : Rel) :
    ∀ (xs : List Rel) (A : Set GTerm), xs ≠ [] →
      membS S A B (xs ++ [z]) = membS S A Set.univ xs ++ [S Set.univ z B]
  | [], _, h => absurd rfl h
  | [x], _, _ => rfl
  | x :: y :: zs, A, _ => by
    have ih := membS_snoc S B z (y :: zs) Set.univ (by simp)
    show S A x Set.univ :: membS S Set.univ B (y :: (zs ++ [z])) = _
    rw [show y :: (zs ++ [z]) = (y :: zs) ++ [z] from rfl, ih]
    rfl

theorem membS_reverse (S : Set GTerm → Rel → Set GTerm → Set SP) :
    ∀ (xs : List Rel) (A B : Set GTerm),
      (membS S A B xs).reverse = membS (fun N x F => S F x N) B A xs.reverse
  | [], _, _ => rfl
  | [x], _, _ => rfl
  | x :: y :: zs, A, B => by
    have ih := membS_reverse S (y :: zs) Set.univ B
    rw [membS, List.reverse_cons, ih, List.reverse_cons (a := x),
      membS_snoc _ _ _ _ _ (by simp)]

theorem sed_chain {M : Interp} {rev : Bool} {d : Nat} {N F : Set GTerm} {e : Rel} {xs : List Rel}
    (h : e.view.forget = .chain xs) :
    SED P M rev (d + 1) N e F =
      chainD rev (membS (SED P M rev d) N F (if rev then xs.reverse else xs)) := by
  have hz := fun A B => zip_membS (SE P M d) B xs 0 A
  simp only [Nat.zero_add] at hz
  cases rev
  · show SE P M (d + 1) N e F = _
    rw [se_chain h, hz, chainD_false]
    rfl
  · show SE P M (d + 1) F e N = _
    rw [se_chain h, hz, ← chainD_true, membS_reverse]
    rfl

theorem pushSet_foldl (rev : Bool) (π : Set GTerm) : ∀ (rest : List (Set SP)) (S : Set SP),
    pushSet rev π (rest.foldl (seqSetsD rev) S) = rest.foldl (seqSetsD rev) (pushSet rev π S)
  | [], _ => rfl
  | T :: rest, S => by
    rw [List.foldl_cons, List.foldl_cons, pushSet_foldl rev π rest, pushSet_seq]

omit [DecidableEq R] in
/-- The products of a chain under a near context: those of its first member
under it, followed by the rest. -/
theorem ws_chain {M : Interp} {rev : Bool} {d : Nat} {c : Near R} {e : Rel} {xs : List Rel}
    {far : Option R} {y₀ y₁ : Rel} {zs : List Rel} (h : e.view.forget = .chain xs)
    (hys : (if rev then xs.reverse else xs) = y₀ :: y₁ :: zs) :
    WS P M rev (d + 1) c e far =
      (membS (SED P M rev d) Set.univ (bset M far) (y₁ :: zs)).foldl (seqSetsD rev)
        (WS P M rev d c y₀ none) := by
  unfold WS
  rw [sed_chain h, sed_chain h, hys]
  split
  · exact pushSet_foldl rev _ _ _
  · rfl

/-! ## What a walk holds, followed by the rest of a chain -/

/-- What a walk holds after the members of the rest of a chain. -/
def chainI (rev : Bool) : SI → List (Set SP) → Set SI
  | i, [] => {i}
  | i, S :: rest => {j | ∃ q ∈ S, ∃ i₁, SeqI rev i q i₁ ∧ j ∈ chainI rev i₁ rest}

theorem farD_foldl (rev : Bool) : ∀ (rest : List (Set SP)) (S : Set SP),
    farD rev '' rest.foldl (seqSetsD rev) S = {j | ∃ p ∈ S, j ∈ chainI rev (farD rev p) rest}
  | [], S => by
    ext j
    constructor
    · rintro ⟨p, hp, rfl⟩; exact ⟨p, hp, rfl⟩
    · rintro ⟨p, hp, rfl⟩; exact ⟨p, hp, rfl⟩
  | T :: rest, S => by
    rw [List.foldl_cons, farD_foldl rev rest]
    ext j
    constructor
    · rintro ⟨r, hr, hj⟩
      obtain ⟨p, hp, q, hq, hs⟩ := mem_seqSetsD.1 hr
      exact ⟨p, hp, q, hq, _, seqD_far hs, hj⟩
    · rintro ⟨p, hp, q, hq, i₁, hs, hj⟩
      obtain ⟨r, hr, rfl⟩ := seqI_lift hs
      exact ⟨r, mem_seqSetsD.2 ⟨p, hp, q, hq, hr⟩, hj⟩

/-! ## The rules, by what their answers relate -/

section laws

variable (hL : D.Lawful P.sorts.interp) (hE : D.ExactIface P.sorts.interp)
  (K : Kernel R Cost) (hK : K.Refines D)

local notation "𝕄" => P.sorts.interp

include hL in
/-- The answer of `leaf`, when there is one, relates the pairs of the span
between the boundaries, and there is one when there is such a pair. -/
theorem leaf_sem {lb rb : Option R} (hl : IsBound D lb) (hr : IsBound D rb) {s : Span}
    (hfo : s.firstOrder = true) (d : Nat) :
    {r : SP | ∃ c, (Ans.leaf D P K hK lb (.span s) rb).val = some c ∧
        r = .closed (den 𝕄 c.span)} =
      SE P 𝕄 (d + 1) (bset 𝕄 lb) (.span s) (bset 𝕄 rb) := by
  rw [se_span]
  ext r
  constructor
  · rintro ⟨c, hc, rfl⟩
    obtain ⟨s', hs, -, -, hsb, -⟩ := (Ans.leaf_val K hK).1 hc
    cases hs
    have e := spanBoth_den hL hsb
    rw [wrap_restr hL hl hr] at e
    exact ⟨by rw [e], by rw [← e]; exact hL.live _⟩
  · rintro ⟨rfl, hne⟩
    have hden := denO_spanBoth hL hfo lb rb
    rw [wrap_restr hL hl hr] at hden
    cases hsb : spanBoth D lb s rb with
    | none =>
      rw [hsb, Domain.denO_none] at hden
      exact absurd hden.symm hne.ne_empty
    | some z =>
      rw [hsb, Domain.denO_some] at hden
      obtain ⟨c, hc, hcs, -⟩ := Ans.leaf_ok (P := P) K hK hl hr hsb
      exact ⟨c, hc, by rw [hcs, hden]⟩

include hL in
/-- A span: its pairs between the near and the far boundary. -/
theorem leaf_ex (rev : Bool) {c : Near R} {far : Option R} (hc : IsBound D c.bound)
    (hf : IsBound D far) {s : Span} (hfo : s.firstOrder = true) (d : Nat) :
    Sem 𝕄 rev ((leafAtV (P := P) K hK rev c.bound (.span s) far).toList.map .closed) =
      WT P 𝕄 rev (d + 1) c (.span s) far := by
  unfold WT
  rw [ws_span]
  have key : ∀ lb rb : Option R, IsBound D lb → IsBound D rb →
      Sem 𝕄 rev ((Ans.leaf D P K hK lb (.span s) rb).val.toList.map .closed) =
        farD rev '' SE P 𝕄 (d + 1) (bset 𝕄 lb) (.span s) (bset 𝕄 rb) := by
    intro lb rb hl hr
    rw [← leaf_sem hL K hK hl hr hfo d]
    ext i
    constructor
    · rintro ⟨it, hit, rfl⟩
      obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hit
      exact ⟨_, ⟨a, Option.mem_toList.1 ha, rfl⟩, rfl⟩
    · rintro ⟨r, ⟨a, ha, rfl⟩, rfl⟩
      exact ⟨.closed a, List.mem_map.2 ⟨a, Option.mem_toList.2 ha, rfl⟩, rfl⟩
  cases rev
  · exact key _ _ hc hf
  · exact key _ _ hf hc

include hL hE in
omit [DecidableEq R] in
/-- The interface of a representative on the far side lets through exactly
its far ends. -/
theorem bset_farBound (rev : Bool) (s : R) :
    bset 𝕄 (farBoundV D rev s) = farEnds rev (den 𝕄 s) := by
  cases rev
  · exact bset_rightBound hL hE s
  · exact bset_leftBound hL hE s

include hL in
omit [DecidableEq R] in
/-- An open product that ends at the far boundary. -/
theorem semI_far (rev : Bool) {far : Option R} (hf : IsBound D far) :
    semI 𝕄 rev (.opn far : It D P) = .opn (bset 𝕄 far) := by
  cases far with
  | none => rfl
  | some b =>
    show SI.opn _ = SI.opn _
    congr 1
    cases rev
    · exact rsetO_bound hL hf
    · exact lsetO_bound hL hf

include hL in
omit [DecidableEq R] in
theorem nearAfterV_isBound (rev : Bool) (it : It D P) :
    IsBound D (nearAfterV D rev it).bound := by
  cases it with
  | closed a => exact nearB_isBound hL rev (some a.span)
  | opn t => rw [nearAfterV_bound]; exact nearB_isBound hL rev t

include hL hE in
omit [DecidableEq R] in
/-- The products of the next member under what an item pushes: its products
from anywhere, restricted to the ends the walk holds. -/
theorem ws_after (rev : Bool) (d : Nat) (it : It D P) (x : Rel) {fr : Option R}
    (hf : IsBound D fr) :
    WS P 𝕄 rev d (nearAfterV D rev it) x fr =
      pushSet rev (ifaceI rev (semI 𝕄 rev it)) (SED P 𝕄 rev d Set.univ x (bset 𝕄 fr)) := by
  cases it with
  | closed a =>
    show pushSet rev (bset 𝕄 (farBoundV D rev a.span)) _ = _
    rw [bset_farBound hL hE]
    rfl
  | opn t =>
    cases t with
    | none =>
      rw [ws_none hL rfl hf]
      exact (pushSet_univ rev (sed_live d x univ_nonempty' (bset_nonempty hL hf))).symm
    | some t =>
      show pushSet rev (bset 𝕄 (farBoundV D rev t)) _ = _
      rw [bset_farBound hL hE]
      rfl

include hL in
theorem joinAt_den (rev : Bool) {a b c : Ans D P} (h : joinAtV K hK rev a b = some c) :
    den 𝕄 c.span = compP rev (den 𝕄 a.span) (den 𝕄 b.span) := by
  cases rev
  · exact hL.compose_some _ _ _ ((Ans.join_val K hK).1 h).2.1
  · exact hL.compose_some _ _ _ ((Ans.join_val K hK).1 h).2.1

/-- An answer of what was walked so far has no boundary on its far side. -/
def ItNone (rev : Bool) : It D P → Prop
  | .closed a => ∃ l n₁, a.goal = goalD rev l n₁ none
  | .opn _ => True

include hL in
/-- An item followed by an item of the next member, by what the walk holds
of them. -/
theorem extend_ex (rev : Bool) {it it₁ : It D P} {x : Rel} {fr : Option R}
    (hit : ItNone rev it)
    (hg : ∀ b, it₁ = .closed b → b.goal = goalD rev (nearAfterV D rev it).bound x fr) (i : SI) :
    (∃ it', extendV K hK rev (some it) it₁ = some it' ∧ semI 𝕄 rev it' = i) ↔
      ExtI rev (semI 𝕄 rev it) (semI 𝕄 rev it₁) i := by
  cases it with
  | closed a =>
    cases it₁ with
    | closed b =>
      obtain ⟨l, n₁, ha⟩ := hit
      have hb := hg b rfl
      constructor
      · rintro ⟨it', he, rfl⟩
        simp only [extendV, Option.map_eq_some_iff] at he
        obtain ⟨c, hc, rfl⟩ := he
        have e := joinAt_den hL K hK rev hc
        show ExtI rev (.closed _) (.closed _) (.closed _)
        rw [e]
        exact .cc (by rw [← e]; exact hL.live _)
      · intro h
        have h' : ExtI rev (.closed (den 𝕄 a.span)) (.closed (den 𝕄 b.span)) i := h
        cases h' with
        | cc hne =>
          obtain ⟨c, hc, -, -⟩ := joinD hL K hK rev ha hb subset_rfl subset_rfl hne
          refine ⟨.closed c, by simp [extendV, hc], ?_⟩
          show SI.closed _ = SI.closed _
          rw [joinAt_den hL K hK rev hc]
    | opn t =>
      have e₁ : ∃ F, semI 𝕄 rev (.opn t : It D P) = .opn F := by cases t <;> exact ⟨_, rfl⟩
      obtain ⟨F, e₁⟩ := e₁
      constructor
      · rintro ⟨it', he, rfl⟩
        obtain rfl : Item.opn t = it' := by simpa [extendV] using he
        rw [e₁]
        exact .co
      · intro h
        rw [e₁] at h
        have h' : ExtI rev (.closed (den 𝕄 a.span)) (.opn F) i := h
        cases h'
        exact ⟨.opn t, rfl, e₁⟩
  | opn t₀ =>
    have e₀ : ∃ F₀, semI 𝕄 rev (.opn t₀ : It D P) = .opn F₀ := by cases t₀ <;> exact ⟨_, rfl⟩
    obtain ⟨F₀, e₀⟩ := e₀
    rw [e₀]
    cases it₁ with
    | closed b =>
      constructor
      · rintro ⟨it', he, rfl⟩
        obtain rfl : Item.opn (some b.span) = it' := by simpa [extendV] using he
        exact .oc
      · intro h
        have h' : ExtI rev (.opn F₀) (.closed (den 𝕄 b.span)) i := h
        cases h'
        exact ⟨.opn (some b.span), rfl, rfl⟩
    | opn t =>
      have e₁ : ∃ F, semI 𝕄 rev (.opn t : It D P) = .opn F := by cases t <;> exact ⟨_, rfl⟩
      obtain ⟨F, e₁⟩ := e₁
      constructor
      · rintro ⟨it', he, rfl⟩
        obtain rfl : Item.opn t = it' := by simpa [extendV] using he
        rw [e₁]
        exact .oo
      · intro h
        rw [e₁] at h
        cases h
        exact ⟨.opn t, rfl, e₁⟩

theorem extend_none (rev : Bool) {it it₁ it' : It D P} {x : Rel} {β : Option R}
    (hit : ItNone rev it) (hg : ∀ b, it₁ = .closed b → b.goal = goalD rev β x none)
    (he : extendV K hK rev (some it) it₁ = some it') : ItNone rev it' := by
  cases it with
  | closed a =>
    cases it₁ with
    | closed b =>
      obtain ⟨l, n₁, ha⟩ := hit
      simp only [extendV, Option.map_eq_some_iff] at he
      obtain ⟨c, hc, rfl⟩ := he
      exact ⟨l, _, joinD_goal K hK rev hc ha (hg b rfl)⟩
    | opn t =>
      obtain rfl : Item.opn t = it' := by simpa [extendV] using he
      trivial
  | opn t₀ =>
    cases it₁ with
    | closed b =>
      obtain rfl : Item.opn (some b.span) = it' := by simpa [extendV] using he
      trivial
    | opn t =>
      obtain rfl : Item.opn t = it' := by simpa [extendV] using he
      trivial

/-! ## A chain -/

/-- What the proof of a chain asks of the walks of its members. -/
def MemEx (rev : Bool) (d : Nat) (wv : Near R → Rel → Option R → List (It D P))
    (ys : List Rel) : Prop :=
  ∀ x ∈ ys, ∀ (c : Near R) (fr : Option R), IsBound D c.bound → IsBound D fr →
    Sem 𝕄 rev (wv c x fr) = WT P 𝕄 rev d c x fr ∧
      ∀ b, Item.closed b ∈ wv c x fr → b.goal = goalD rev c.bound x fr

include hL hE in
/-- One member more: the items of the next member under what an item pushes,
each after that item, are what the walk holds of the item followed by the
products of that member. -/
theorem step_ex (rev : Bool) (d : Nat) {wv : Near R → Rel → Option R → List (It D P)} {x : Rel}
    (hx : MemEx (P := P) rev d wv [x]) {it : It D P} (hit : ItNone rev it) {fr : Option R}
    (hf : IsBound D fr) (s : SI) :
    (∃ it₁ ∈ wv (nearAfterV D rev it) x fr, ∃ it',
        extendV K hK rev (some it) it₁ = some it' ∧ semI 𝕄 rev it' = s) ↔
      ∃ q ∈ SED P 𝕄 rev d Set.univ x (bset 𝕄 fr), SeqI rev (semI 𝕄 rev it) q s := by
  obtain ⟨hsem, hgoal⟩ := hx x (by simp) (nearAfterV D rev it) fr (nearAfterV_isBound hL rev it) hf
  have hT : Sem 𝕄 rev (wv (nearAfterV D rev it) x fr) =
      farD rev '' pushSet rev (ifaceI rev (semI 𝕄 rev it))
        (SED P 𝕄 rev d Set.univ x (bset 𝕄 fr)) := by
    rw [hsem, WT, ws_after hL hE rev d it x hf]
  constructor
  · rintro ⟨it₁, h₁, hex⟩
    have hext := (extend_ex hL K hK rev hit (fun b hb => hgoal b (hb ▸ h₁)) s).1 hex
    have hm : semI 𝕄 rev it₁ ∈ Sem 𝕄 rev (wv (nearAfterV D rev it) x fr) := ⟨it₁, h₁, rfl⟩
    rw [hT] at hm
    obtain ⟨q', ⟨q, hq, hpush⟩, e⟩ := hm
    exact ⟨q, hq, seqI_iff_push_ext.2 ⟨q', hpush, by rw [e]; exact hext⟩⟩
  · rintro ⟨q, hq, hseq⟩
    obtain ⟨q', hpush, hext⟩ := seqI_iff_push_ext.1 hseq
    have hm : farD rev q' ∈ Sem 𝕄 rev (wv (nearAfterV D rev it) x fr) := by
      rw [hT]
      exact ⟨q', ⟨q, hq, hpush⟩, rfl⟩
    obtain ⟨it₁, h₁, e⟩ := hm
    exact ⟨it₁, h₁, (extend_ex hL K hK rev hit (fun b hb => hgoal b (hb ▸ h₁)) s).2
      (by rw [e]; exact hext)⟩

include hL hE in
/-- After an item, the rest of a chain. -/
theorem seq_tail (rev : Bool) (d : Nat) (wv : Near R → Rel → Option R → List (It D P))
    (far : Option R) (hfar : IsBound D far) :
    ∀ (ys : List Rel), ys ≠ [] → MemEx (P := P) rev d wv ys → ∀ it : It D P, ItNone rev it →
      Sem 𝕄 rev (seqV K hK rev wv far (some it) (nearAfterV D rev it) ys) =
        chainI rev (semI 𝕄 rev it) (membS (SED P 𝕄 rev d) Set.univ (bset 𝕄 far) ys)
  | [], h, _, _, _ => absurd rfl h
  | [x], _, HW, it, hit => by
    ext s
    have hstep := step_ex hL hE K hK rev d HW hit hfar s
    constructor
    · rintro ⟨it'', h, rfl⟩
      obtain ⟨it₁, h₁, he⟩ := (mem_seqV_one K hK rev wv far).1 h
      obtain ⟨q, hq, hs⟩ := hstep.1 ⟨it₁, h₁, it'', he, rfl⟩
      exact ⟨q, hq, _, hs, rfl⟩
    · rintro ⟨q, hq, i₁, hs, hj⟩
      obtain rfl : s = i₁ := hj
      obtain ⟨it₁, h₁, it', he, e⟩ := hstep.2 ⟨q, hq, hs⟩
      exact ⟨it', (mem_seqV_one K hK rev wv far).2 ⟨it₁, h₁, he⟩, e⟩
  | x :: y :: zs, _, HW, it, hit => by
    have HWx : MemEx (P := P) rev d wv [x] := fun z hz => HW z (by
      obtain rfl : z = x := by simpa using hz
      simp)
    have HW' : MemEx (P := P) rev d wv (y :: zs) := fun z hz => HW z (List.mem_cons_of_mem _ hz)
    have ih := seq_tail rev d wv far hfar (y :: zs) (by simp) HW'
    obtain ⟨-, hgoal⟩ := HW x (by simp) (nearAfterV D rev it) none
      (nearAfterV_isBound hL rev it) (isBound_none D)
    have hstep := step_ex hL hE K hK rev d HWx hit (isBound_none D)
    ext s
    constructor
    · rintro ⟨it'', h, rfl⟩
      obtain ⟨it₁, h₁, it', he, h'⟩ := (mem_seqV_two K hK rev wv far).1 h
      have hn := extend_none K hK rev hit (fun b hb => hgoal b (hb ▸ h₁)) he
      obtain ⟨q, hq, hs⟩ := (hstep _).1 ⟨it₁, h₁, it', he, rfl⟩
      refine ⟨q, hq, _, hs, ?_⟩
      rw [← ih it' hn]
      exact ⟨it'', h', rfl⟩
    · rintro ⟨q, hq, i₁, hs, hj⟩
      obtain ⟨it₁, h₁, it', he, rfl⟩ := (hstep i₁).2 ⟨q, hq, hs⟩
      have hn := extend_none K hK rev hit (fun b hb => hgoal b (hb ▸ h₁)) he
      rw [← ih it' hn] at hj
      obtain ⟨it'', h', e⟩ := hj
      exact ⟨it'', (mem_seqV_two K hK rev wv far).2 ⟨it₁, h₁, it', he, h'⟩, e⟩

include hL hE in
/-- The items of a chain are what the walk holds of its products. -/
theorem chain_ex (rev : Bool) (d : Nat) (wv : Near R → Rel → Option R → List (It D P))
    {far : Option R} (hfar : IsBound D far) {e : Rel} {xs : List Rel}
    (h : e.view.forget = .chain xs) {y₀ y₁ : Rel} {zs : List Rel}
    (hys : (if rev then xs.reverse else xs) = y₀ :: y₁ :: zs)
    (HW : MemEx (P := P) rev d wv (y₀ :: y₁ :: zs)) (c : Near R) (hc : IsBound D c.bound) :
    Sem 𝕄 rev (seqV K hK rev wv far none c (y₀ :: y₁ :: zs)) = WT P 𝕄 rev (d + 1) c e far := by
  unfold WT
  rw [ws_chain h hys, farD_foldl]
  obtain ⟨hsem, hgoal⟩ := HW y₀ (by simp) c none hc (isBound_none D)
  have HW' : MemEx (P := P) rev d wv (y₁ :: zs) := fun z hz => HW z (List.mem_cons_of_mem _ hz)
  have tail := seq_tail hL hE K hK rev d wv far hfar (y₁ :: zs) (by simp) HW'
  have hn : ∀ it₁ ∈ wv c y₀ none, ItNone rev it₁ := by
    intro it₁ h₁
    cases it₁ with
    | closed b => exact ⟨_, _, hgoal b h₁⟩
    | opn t => trivial
  ext s
  constructor
  · rintro ⟨it'', h', rfl⟩
    obtain ⟨it₁, h₁, it', he, h''⟩ := (mem_seqV_two K hK rev wv far).1 h'
    obtain rfl : it₁ = it' := by simpa [extendV] using he
    have hm : semI 𝕄 rev it₁ ∈ WT P 𝕄 rev d c y₀ none := by
      rw [← hsem]
      exact ⟨it₁, h₁, rfl⟩
    obtain ⟨p, hp, e⟩ := hm
    refine ⟨p, hp, ?_⟩
    rw [e, ← tail it₁ (hn it₁ h₁)]
    exact ⟨it'', h'', rfl⟩
  · rintro ⟨p, hp, hj⟩
    have hm : farD rev p ∈ Sem 𝕄 rev (wv c y₀ none) := by
      rw [hsem]
      exact ⟨p, hp, rfl⟩
    obtain ⟨it₁, h₁, e⟩ := hm
    rw [← e, ← tail it₁ (hn it₁ h₁)] at hj
    obtain ⟨it'', h'', e'⟩ := hj
    exact ⟨it'', (mem_seqV_two K hK rev wv far).2 ⟨it₁, h₁, it₁, rfl, h''⟩, e'⟩

/-! ## A meet -/

/-- The pairs of the answers among the items. -/
def clI (M : Interp) (is : List (It D P)) : Set PRel :=
  {X | ∃ a, Item.closed a ∈ is ∧ den M a.span = X}

theorem si_ext {T₁ T₂ : Set SI} (hc : ∀ X, SI.closed X ∈ T₁ ↔ SI.closed X ∈ T₂)
    (ho : ∀ F, SI.opn F ∈ T₁ ↔ SI.opn F ∈ T₂) : T₁ = T₂ := by
  ext s
  cases s
  · exact hc _
  · exact ho _

section parts

variable {M : Interp} {rev : Bool}

omit [DecidableEq R] in
theorem semI_opn (t : Option R) : ∃ F, semI M rev (.opn t : It D P) = .opn F := by
  cases t <;> exact ⟨_, rfl⟩

omit [DecidableEq R] in
theorem sem_closed_iff {is : List (It D P)} {X : PRel} :
    SI.closed X ∈ Sem M rev is ↔ X ∈ clI M is := by
  constructor
  · rintro ⟨it, hit, e⟩
    cases it with
    | closed a =>
      simp only [semI, SI.closed.injEq] at e
      exact ⟨a, hit, e⟩
    | opn t =>
      obtain ⟨F, hF⟩ := semI_opn (M := M) (rev := rev) (D := D) (P := P) t
      rw [hF] at e
      cases e
  · rintro ⟨a, ha, rfl⟩
    exact ⟨_, ha, rfl⟩

theorem farD_closed_iff {S : Set SP} {X : PRel} : SI.closed X ∈ farD rev '' S ↔ SP.closed X ∈ S := by
  constructor
  · rintro ⟨p, hp, e⟩
    cases p with
    | closed Y =>
      simp only [farD, SI.closed.injEq] at e
      subst e
      exact hp
    | opn A B => simp [farD] at e
  · intro h
    exact ⟨_, h, rfl⟩

theorem farD_opn_iff {S : Set SP} {F : Set GTerm} :
    SI.opn F ∈ farD rev '' S ↔ ∃ A B, SP.opn A B ∈ S ∧ farE rev A B = F := by
  constructor
  · rintro ⟨p, hp, e⟩
    cases p with
    | closed Y => simp [farD] at e
    | opn A B =>
      simp only [farD, SI.opn.injEq] at e
      exact ⟨A, B, hp, e⟩
  · rintro ⟨A, B, h, rfl⟩
    exact ⟨_, h, rfl⟩

variable {is : List (It D P)} {S : Set SP}

omit [DecidableEq R] in
theorem clI_eq (h : Sem M rev is = farD rev '' S) : clI M is = closedPart S := by
  ext X
  rw [← sem_closed_iff (rev := rev), h, farD_closed_iff]
  rfl

omit [DecidableEq R] in
theorem ne_nil_iff (h : Sem M rev is = farD rev '' S) : is ≠ [] ↔ S.Nonempty := by
  constructor
  · intro hne
    obtain ⟨it, hit⟩ := List.exists_mem_of_ne_nil _ hne
    have hm : semI M rev it ∈ Sem M rev is := ⟨it, hit, rfl⟩
    rw [h] at hm
    obtain ⟨p, hp, -⟩ := hm
    exact ⟨p, hp⟩
  · rintro ⟨p, hp⟩
    have hm : farD rev p ∈ Sem M rev is := by
      rw [h]
      exact ⟨p, hp, rfl⟩
    obtain ⟨it, hit, -⟩ := hm
    exact List.ne_nil_of_mem hit

omit [DecidableEq R] in
theorem opn_iff (h : Sem M rev is = farD rev '' S) : (∃ t, Item.opn t ∈ is) ↔ HasOpn S := by
  constructor
  · rintro ⟨t, ht⟩
    obtain ⟨F, hF⟩ := semI_opn (M := M) (rev := rev) (D := D) (P := P) t
    have hm : SI.opn F ∈ Sem M rev is := ⟨_, ht, hF⟩
    rw [h] at hm
    obtain ⟨A, B, hAB, -⟩ := farD_opn_iff.1 hm
    exact ⟨A, B, hAB⟩
  · rintro ⟨A, B, hAB⟩
    have hm : SI.opn (farE rev A B) ∈ Sem M rev is := by
      rw [h]
      exact ⟨_, hAB, rfl⟩
    obtain ⟨it, hit, e⟩ := hm
    cases it with
    | closed a => simp [semI] at e
    | opn t => exact ⟨t, hit⟩

end parts

theorem foldl_meetSets_union : ∀ (rest : List (Set PRel)) (S : Set PRel),
    rest.foldl meetSets S = {Z | ∃ Y ∈ S, Z ∈ rest.foldl meetSets {Y}}
  | [], S => by
    ext Z
    constructor
    · intro h; exact ⟨Z, h, rfl⟩
    · rintro ⟨Y, hY, h⟩
      obtain rfl : Z = Y := h
      exact hY
  | T :: rest, S => by
    rw [List.foldl_cons, foldl_meetSets_union rest]
    ext Z
    constructor
    · rintro ⟨W, ⟨X, hX, Y, hY, rfl, hne⟩, hZ⟩
      refine ⟨X, hX, ?_⟩
      rw [List.foldl_cons, foldl_meetSets_union rest]
      exact ⟨_, ⟨X, rfl, Y, hY, rfl, hne⟩, hZ⟩
    · rintro ⟨X, hX, hZ⟩
      rw [List.foldl_cons, foldl_meetSets_union rest] at hZ
      obtain ⟨W, ⟨X', hX', Y, hY, rfl, hne⟩, hZ⟩ := hZ
      obtain rfl : X' = X := hX'
      exact ⟨_, ⟨X', hX, Y, hY, rfl, hne⟩, hZ⟩

/-- The relations of a set restricted on the near side that still relate a
pair. -/
def pushC (rev : Bool) (π : Set GTerm) (C : Set PRel) : Set PRel :=
  {Y | ∃ X ∈ C, Y = restrD rev π X ∧ Y.Nonempty}

theorem restrD_inter (rev : Bool) (π : Set GTerm) (X Y : PRel) :
    restrD rev π (X ∩ Y) = restrD rev π X ∩ restrD rev π Y := by
  cases rev
  · ext p
    constructor
    · rintro ⟨⟨h₁, h₂⟩, h⟩; exact ⟨⟨h₁, h⟩, h₂, h⟩
    · rintro ⟨⟨h₁, h⟩, h₂, -⟩; exact ⟨⟨h₁, h₂⟩, h⟩
  · ext p
    constructor
    · rintro ⟨⟨h₁, h₂⟩, h⟩; exact ⟨⟨h₁, h⟩, h₂, h⟩
    · rintro ⟨⟨h₁, h⟩, h₂, -⟩; exact ⟨⟨h₁, h₂⟩, h⟩

theorem restrD_sub (rev : Bool) (π : Set GTerm) (X : PRel) : restrD rev π X ⊆ X := by
  cases rev <;> exact fun p h => h.1

theorem pushC_meetSets (rev : Bool) (π : Set GTerm) (S T : Set PRel) :
    pushC rev π (meetSets S T) = meetSets (pushC rev π S) (pushC rev π T) := by
  ext Z
  constructor
  · rintro ⟨W, ⟨X, hX, Y, hY, rfl, -⟩, rfl, hne⟩
    rw [restrD_inter] at hne ⊢
    exact ⟨_, ⟨X, hX, rfl, hne.mono Set.inter_subset_left⟩, _,
      ⟨Y, hY, rfl, hne.mono Set.inter_subset_right⟩, rfl, hne⟩
  · rintro ⟨_, ⟨X, hX, rfl, -⟩, _, ⟨Y, hY, rfl, -⟩, rfl, hne⟩
    rw [← restrD_inter] at hne ⊢
    exact ⟨X ∩ Y, ⟨X, hX, Y, hY, rfl, hne.mono (restrD_sub rev π _)⟩, rfl, hne⟩

theorem pushC_foldl (rev : Bool) (π : Set GTerm) : ∀ (rest : List (Set PRel)) (S : Set PRel),
    pushC rev π (rest.foldl meetSets S) = (rest.map (pushC rev π)).foldl meetSets (pushC rev π S)
  | [], _ => rfl
  | T :: rest, S => by
    rw [List.foldl_cons, pushC_foldl rev π rest, pushC_meetSets]
    rfl

theorem pushC_meetAllS (rev : Bool) (π : Set GTerm) (Cs : List (Set PRel)) :
    pushC rev π (meetAllS Cs) = meetAllS (Cs.map (pushC rev π)) := by
  cases Cs with
  | nil =>
    ext Z
    constructor
    · rintro ⟨X, hX, -⟩; cases hX
    · intro h; cases h
  | cons S rest => exact pushC_foldl rev π rest S

theorem closedPart_pushSet (rev : Bool) (π : Set GTerm) (T : Set SP) :
    closedPart (pushSet rev π T) = pushC rev π (closedPart T) := by
  ext Y
  constructor
  · rintro ⟨p, hp, h⟩
    generalize hr : SP.closed Y = r at h
    cases h with
    | closed hne =>
      cases hr
      exact ⟨_, hp, rfl, hne⟩
    | opn hne => cases rev <;> simp [pushO] at hr
  · rintro ⟨X, hX, rfl, hne⟩
    exact ⟨_, hX, .closed hne⟩

theorem closedPart_meetS (A B : Set GTerm) (Ss : List (Set SP)) :
    closedPart (meetS A B Ss) = meetAllS (Ss.map closedPart) := by
  ext X
  constructor
  · rintro (⟨X', hX', e⟩ | ⟨e, -⟩)
    · cases e; exact hX'
    · cases e
  · intro h
    exact .inl ⟨X, h, rfl⟩

theorem sed_meet {M : Interp} {rev : Bool} {d : Nat} {N F : Set GTerm} {e : Rel} {xs : List Rel}
    (h : e.view.forget = .meet xs) :
    SED P M rev (d + 1) N e F =
      meetS (if rev then F else N) (if rev then N else F)
        (xs.map fun x => SED P M rev d N x F) := by
  cases rev
  · exact se_meet h
  · exact se_meet h

include hL in
theorem meetA_den {a b c : Ans D P} (h : (Ans.meetA D P K hK a b).val = some c) :
    den 𝕄 c.span = den 𝕄 a.span ∩ den 𝕄 b.span :=
  hL.meet_some _ _ _ ((Ans.meetA_val K hK).1 h).2.1

section meet

variable (rev : Bool) (opq : Bool) (wv : Rel → List (It D P)) (near far : Option R)

include hL in
/-- After an answer, the answers of the meet relate the meets of what it
relates with what one answer of every member still to walk relates. -/
theorem and_closed_ex : ∀ (xs : List Rel) (a : Ans D P) (n₀ : Rel),
    a.goal = goalD rev near n₀ far →
    (∀ x ∈ xs, ∀ b, Item.closed b ∈ wv x → b.goal = goalD rev near x far) →
    clI 𝕄 (andV K hK true opq wv far (.closed a) xs) =
      (xs.map fun x => clI 𝕄 (wv x)).foldl meetSets {den 𝕄 a.span}
  | [], a, _, _, _ => by
    ext X
    constructor
    · rintro ⟨c, hc, rfl⟩
      obtain ⟨-, e⟩ := (mem_andV_closed_nil K hK true opq wv far).1 hc
      obtain rfl : a = c := by simpa using e
      rfl
    · intro h
      obtain rfl : X = den 𝕄 a.span := h
      exact ⟨a, (mem_andV_closed_nil K hK true opq wv far).2 ⟨rfl, rfl⟩, rfl⟩
  | x :: xs, a, n₀, ha, H => by
    have ih := fun (c' : Ans D P) (n' : Rel) (hc' : c'.goal = goalD rev near n' far) =>
      and_closed_ex xs c' n' hc' (fun y hy => H y (List.mem_cons_of_mem _ hy))
    rw [List.map_cons, List.foldl_cons, foldl_meetSets_union]
    ext X
    constructor
    · rintro ⟨c, hc, rfl⟩
      obtain ⟨b, c', hb, hm, hc'⟩ := (mem_andV_closed K hK true opq wv far).1 hc
      have hcg := meetD_goal K hK rev hm ha (H x (by simp) b hb)
      have e := meetA_den hL K hK hm
      refine ⟨den 𝕄 c'.span, ⟨_, rfl, _, ⟨b, hb, rfl⟩, e, hL.live _⟩, ?_⟩
      rw [← ih c' _ hcg]
      exact ⟨c, hc', rfl⟩
    · rintro ⟨Y, ⟨X₁, hX₁, X₂, ⟨b, hb, rfl⟩, rfl, hne⟩, hX⟩
      obtain rfl : X₁ = den 𝕄 a.span := hX₁
      obtain ⟨c', hm, -, hcg⟩ := meetD hL K hK rev ha (H x (by simp) b hb)
        Set.inter_subset_left Set.inter_subset_right hne
      rw [← meetA_den hL K hK hm, ← ih c' _ hcg] at hX
      obtain ⟨c, hc, rfl⟩ := hX
      exact ⟨c, (mem_andV_closed K hK true opq wv far).2 ⟨b, c', hb, hm, hc⟩, rfl⟩

include hL in
/-- The answers of a meet relate the meets of what one answer of every
member relates. -/
theorem and_start_ex (xs : List Rel)
    (H : ∀ x ∈ xs, ∀ b, Item.closed b ∈ wv x → b.goal = goalD rev near x far) :
    clI 𝕄 (andV K hK true opq wv far .start xs) = meetAllS (xs.map fun x => clI 𝕄 (wv x)) := by
  cases xs with
  | nil =>
    ext X
    constructor
    · rintro ⟨c, hc, -⟩
      simp [andV] at hc
    · intro h; cases h
  | cons x₀ tl =>
    have ih := fun (b : Ans D P) (hb : Item.closed b ∈ wv x₀) =>
      and_closed_ex hL K hK rev opq wv near far tl b _ (H x₀ (by simp) b hb)
        (fun y hy => H y (List.mem_cons_of_mem _ hy))
    show _ = (tl.map fun x => clI 𝕄 (wv x)).foldl meetSets (clI 𝕄 (wv x₀))
    rw [foldl_meetSets_union]
    ext X
    constructor
    · rintro ⟨c, hc, rfl⟩
      obtain ⟨it, hit, h'⟩ := (mem_andV_closed_cons K hK true opq wv far).1 hc
      cases it with
      | closed b =>
        refine ⟨_, ⟨b, hit, rfl⟩, ?_⟩
        rw [← ih b hit]
        exact ⟨c, by simpa [metNext] using h', rfl⟩
      | opn t => exact absurd h' (and_noclosed K hK true opq wv far _ _ c (.inl rfl))
    · rintro ⟨Y, ⟨b, hb, rfl⟩, hX⟩
      rw [← ih b hb] at hX
      obtain ⟨c, hc, rfl⟩ := hX
      exact ⟨c, (mem_andV_closed_cons K hK true opq wv far).2
        ⟨_, hb, by simpa [metNext] using hc⟩, rfl⟩

end meet

include hL in
/-- The items of a meet where nothing was pushed. -/
theorem meet_plain_ex (rev : Bool) (wv : Rel → List (It D P)) (S : Rel → Set SP)
    (xs : List Rel) {near far : Option R} (hf : IsBound D far) {A B : Set GTerm}
    (hAB : farE rev A B = bset 𝕄 far)
    (hw : ∀ x ∈ xs, Sem 𝕄 rev (wv x) = farD rev '' S x)
    (hg : ∀ x ∈ xs, ∀ b, Item.closed b ∈ wv x → b.goal = goalD rev near x far) :
    Sem 𝕄 rev (andV K hK true true wv far .start xs) = farD rev '' meetS A B (xs.map S) := by
  have hcl : (xs.map fun x => clI 𝕄 (wv x)) = (xs.map S).map closedPart := by
    rw [List.map_map]
    exact List.map_congr_left fun x hx => clI_eq (hw x hx)
  apply si_ext
  · intro X
    rw [sem_closed_iff, farD_closed_iff, and_start_ex hL K hK rev true wv near far xs hg, hcl,
      ← closedPart_meetS A B]
    rfl
  · intro F
    constructor
    · rintro ⟨it, hit, e⟩
      cases it with
      | closed a => simp [semI] at e
      | opn t =>
        obtain ⟨rfl, -, hall, hex⟩ := (mem_andV_opn K hK true true wv far xs .start t).1 hit
        rw [semI_far hL rev hf] at e
        refine farD_opn_iff.2 ⟨A, B, .inr ⟨rfl, fun T hT => ?_, ?_⟩, by
          rw [hAB]; exact SI.opn.inj e⟩
        · obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hT
          exact (ne_nil_iff (hw x hx)).1 (hall x hx)
        · rcases hex with h | ⟨x, hx, ht⟩
          · cases h
          · exact ⟨S x, List.mem_map_of_mem hx, (opn_iff (hw x hx)).1 ht⟩
    · intro h
      obtain ⟨A', B', hm, e⟩ := farD_opn_iff.1 h
      rcases hm with ⟨X, -, e'⟩ | ⟨e', hall, T, hT, hop⟩
      · cases e'
      · cases e'
        refine ⟨.opn far, (mem_andV_opn K hK true true wv far xs .start far).2
          ⟨rfl, rfl, fun x hx => ?_, .inr ?_⟩, ?_⟩
        · exact (ne_nil_iff (hw x hx)).2 (hall _ (List.mem_map_of_mem hx))
        · obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hT
          exact ⟨x, hx, (opn_iff (hw x hx)).2 hop⟩
        · rw [semI_far hL rev hf, ← hAB, e]

include hL in
/-- The items of a meet under a pushed boundary: its answers under it, and
whether it is opaque without it. -/
theorem meet_pushed_ex (rev : Bool) (wv wvo : Rel → List (It D P)) (S : Rel → Set SP)
    (xs : List Rel) {near far : Option R} (hf : IsBound D far) {π : Set GTerm} (hπ : π.Nonempty)
    {A B : Set GTerm} (hN : nearE rev A B = Set.univ) (hAB : farE rev A B = bset 𝕄 far)
    (hw : ∀ x ∈ xs, Sem 𝕄 rev (wv x) = farD rev '' pushSet rev π (S x))
    (hg : ∀ x ∈ xs, ∀ b, Item.closed b ∈ wv x → b.goal = goalD rev near x far)
    (hwo : ∀ x ∈ xs, Sem 𝕄 rev (wvo x) = farD rev '' S x) :
    Sem 𝕄 rev (andV K hK true false wv far .start xs ++ andV K hK false true wvo far .start xs) =
      farD rev '' pushSet rev π (meetS A B (xs.map S)) := by
  apply si_ext
  · intro X
    rw [sem_closed_iff, farD_closed_iff]
    have hl : X ∈ clI 𝕄 (andV K hK true false wv far .start xs ++
        andV K hK false true wvo far .start xs) ↔
        X ∈ clI 𝕄 (andV K hK true false wv far .start xs) :=
      ⟨fun ⟨a, ha, e⟩ => (List.mem_append.1 ha).elim (fun h => ⟨a, h, e⟩)
          (fun h => absurd h (and_noclosed_flag K hK true wvo far _ _ a)),
        fun ⟨a, ha, e⟩ => ⟨a, List.mem_append_left _ ha, e⟩⟩
    have hcl : (xs.map fun x => clI 𝕄 (wv x)) =
        ((xs.map S).map closedPart).map (pushC rev π) := by
      rw [List.map_map, List.map_map]
      exact List.map_congr_left fun x hx => by
        rw [clI_eq (hw x hx), closedPart_pushSet]
        rfl
    rw [hl, and_start_ex hL K hK rev false wv near far xs hg, hcl, ← pushC_meetAllS,
      ← closedPart_meetS A B, ← closedPart_pushSet]
    rfl
  · intro F
    constructor
    · rintro ⟨it, hit, e⟩
      cases it with
      | closed a => simp [semI] at e
      | opn t =>
        rcases List.mem_append.1 hit with h | h
        · have := ((mem_andV_opn K hK true false wv far xs .start t).1 h).2.1
          cases this
        · obtain ⟨rfl, -, hall, hex⟩ := (mem_andV_opn K hK false true wvo far xs .start t).1 h
          rw [semI_far hL rev hf] at e
          have hmem : SP.opn A B ∈ meetS A B (xs.map S) := by
            refine .inr ⟨rfl, fun T hT => ?_, ?_⟩
            · obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hT
              exact (ne_nil_iff (hwo x hx)).1 (hall x hx)
            · rcases hex with h | ⟨x, hx, ht⟩
              · cases h
              · exact ⟨S x, List.mem_map_of_mem hx, (opn_iff (hwo x hx)).1 ht⟩
          have hpush : PushD rev π (.opn A B) (pushO rev π A B) :=
            .opn (by rw [hN, Set.univ_inter]; exact hπ)
          exact ⟨pushO rev π A B, ⟨_, hmem, hpush⟩, by rw [farD_pushO, hAB]; exact e⟩
    · rintro ⟨r, ⟨p, hp, hpush⟩, e⟩
      rcases hp with ⟨X, -, rfl⟩ | ⟨rfl, hall, T, hT, hop⟩
      · cases hpush with
        | closed hne => simp [farD] at e
      · cases hpush with
        | opn hne =>
          rw [farD_pushO, hAB] at e
          refine ⟨.opn far, List.mem_append_right _
            ((mem_andV_opn K hK false true wvo far xs .start far).2
              ⟨rfl, rfl, fun x hx => ?_, .inr ?_⟩), ?_⟩
          · exact (ne_nil_iff (hwo x hx)).2 (hall _ (List.mem_map_of_mem hx))
          · obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hT
            exact ⟨x, hx, (opn_iff (hwo x hx)).2 hop⟩
          · rw [semI_far hL rev hf]
            exact e

/-! ## The walk -/

include hL hE in
/-- What a walk holds of the items it hands on is what a walk holds of the
products of the unfolding, under its near context. -/
theorem walk_ex (hP : ProgFO P) (rev : Bool) : ∀ (d : Nat) (c : Near R) (n : Rel)
    (far : Option R), IsBound D c.bound → IsBound D far → Normal n → n.FO →
    Sem 𝕄 rev (walkV (P := P) K hK rev d c n far) = WT P 𝕄 rev d c n far
  | 0, c, n, far, hc, hf, _, _ => by
    rw [wt_zero hL hc]
    ext s
    constructor
    · rintro ⟨it, hit, rfl⟩
      obtain rfl : it = .opn far := by simpa [walkV] using hit
      exact semI_far hL rev hf
    · intro h
      obtain rfl : s = .opn (bset 𝕄 far) := h
      exact ⟨.opn far, by simp [walkV], semI_far hL rev hf⟩
  | d + 1, c, n, far, hc, hf, hn, hfo => by
    have hok := walk_ok hL K hK hP rev
    cases hv : n.view.forget with
    | span u =>
      obtain ⟨s, rfl⟩ := forget_span hv
      have e : walkV (P := P) K hK rev (d + 1) c (.span s) far =
          (leafAtV (P := P) K hK rev c.bound (.span s) far).toList.map .closed := by
        simp only [walkV, hv]
      rw [e]
      exact leaf_ex hL K hK rev hc hf (hfo s (by simp [RelOf.spans])) d
    | call m f =>
      obtain ⟨b, hb⟩ := forget_call (P := P) hv
      have e : walkV (P := P) K hK rev (d + 1) c n far =
          (walkV K hK rev d c b far).flatMap fun it =>
            (liftItemV (fun a => (Ans.unfold D P a n).val) it).toList := by
        simp only [walkV, hv, hb]
      have hbn := bodyOf_normal hb
      have hbf := bodyOf_fo hP hb
      have hl := sem_lift (M := 𝕄) (rev := rev) (is := walkV (P := P) K hK rev d c b far)
        (f := fun a => (Ans.unfold D P a n).val) (fun a c e => (Ans.unfold_val.1 e).2.1)
        (fun a ha => by
          obtain ⟨c', hc', -⟩ := Ans.unfold_ok (a := a) (n := n) (by
            rw [hb, (hok d c b far hc hf hbn hbf).goal a ha]; cases rev <;> rfl)
          exact ⟨c', hc'⟩)
      rw [e, hl, walk_ex hP rev d c b far hc hf hbn hbf, WT, WT, ws_call hv hb]
    | union xs =>
      have hvu := forget_union hv
      have hparts := hn.view_union_eq hvu
      have e : walkV (P := P) K hK rev (d + 1) c n far =
          xs.zipIdx.flatMap fun p => (walkV K hK rev d c p.1 far).flatMap fun it =>
            (liftItemV (fun a => (Ans.inj D P a n p.2).val) it).toList := by
        simp only [walkV, hv]
      have hmemb : ∀ p ∈ xs.zipIdx,
          Sem 𝕄 rev ((walkV (P := P) K hK rev d c p.1 far).flatMap fun it =>
            (liftItemV (fun a => (Ans.inj D P a n p.2).val) it).toList) =
            WT P 𝕄 rev d c p.1 far := by
        intro p hp
        have hx : xs[p.2]? = some p.1 := List.mem_zipIdx_iff_getElem?.1 hp
        have hm : p.1 ∈ n.view.members := by rw [hvu]; exact List.mem_of_getElem? hx
        have hl := sem_lift (M := 𝕄) (rev := rev) (is := walkV (P := P) K hK rev d c p.1 far)
          (f := fun a => (Ans.inj D P a n p.2).val) (fun a c e => (Ans.inj_val.1 e).2.1)
          (fun a ha => by
            obtain ⟨c', hc', -⟩ := Ans.inj_ok (a := a) (u := n) (i := p.2) (by
              rw [← hparts, (hok d c p.1 far hc hf (hn.view_members hm)
                (hfo.view_members hm)).goal a ha]
              cases rev <;> exact hx)
            exact ⟨c', hc'⟩)
        rw [hl]
        exact walk_ex hP rev d c p.1 far hc hf (hn.view_members hm) (hfo.view_members hm)
      rw [e, sem_flatMap, WT, ws_union hv]
      ext s
      constructor
      · rintro ⟨p, hp, hs⟩
        rw [hmemb p hp] at hs
        obtain ⟨r, hr, rfl⟩ := hs
        exact ⟨r, ⟨p.1, List.mem_of_getElem? (List.mem_zipIdx_iff_getElem?.1 hp), hr⟩, rfl⟩
      · rintro ⟨r, ⟨x, hx, hr⟩, rfl⟩
        obtain ⟨i, hi⟩ := List.getElem?_of_mem hx
        refine ⟨(x, i), List.mem_zipIdx_iff_getElem?.2 hi, ?_⟩
        rw [hmemb (x, i) (List.mem_zipIdx_iff_getElem?.2 hi)]
        exact ⟨r, hr, rfl⟩
    | chain xs =>
      have hvc := forget_chain hv
      obtain ⟨h2, hmem, -⟩ := hn.view_chain hvc
      have e : walkV (P := P) K hK rev (d + 1) c n far =
          seqV K hK rev (walkV K hK rev d) far none c (if rev then xs.reverse else xs) := by
        simp only [walkV, hv]
      have hin : ∀ x, x ∈ (if rev then xs.reverse else xs) → x ∈ xs := fun x hx => by
        cases rev
        · exact hx
        · exact List.mem_reverse.1 hx
      have h2' : 2 ≤ (if rev then xs.reverse else xs).length := by cases rev <;> simpa using h2
      rw [e]
      cases hys : (if rev then xs.reverse else xs) with
      | nil => rw [hys] at h2'; simp at h2'
      | cons y₀ t =>
        cases t with
        | nil => rw [hys] at h2'; simp at h2'
        | cons y₁ zs =>
          refine chain_ex hL hE K hK rev d (walkV K hK rev d) hf hv hys
            (fun x hx c' fr hc' hfr => ?_) c hc
          have hxm : x ∈ xs := hin x (by rw [hys]; exact hx)
          have hxn := (hmem x hxm).1
          have hxf := hfo.view_members (by rw [hvc]; exact hxm)
          exact ⟨walk_ex hP rev d c' x fr hc' hfr hxn hxf, (hok d c' x fr hc' hfr hxn hxf).goal⟩
    | meet xs =>
      have hvm := forget_meet hv
      obtain ⟨-, hmem, -, -⟩ := hn.view_meet hvm
      have ih : ∀ c' : Near R, IsBound D c'.bound → ∀ x ∈ xs,
          Sem 𝕄 rev (walkV (P := P) K hK rev d c' x far) = WT P 𝕄 rev d c' x far ∧
            ∀ b, Item.closed b ∈ walkV (P := P) K hK rev d c' x far →
              b.goal = goalD rev c'.bound x far :=
        fun c' hc' x hx =>
          ⟨walk_ex hP rev d c' x far hc' hf (hmem x hx).1
              (hfo.view_members (by rw [hvm]; exact hx)),
            (hok d c' x far hc' hf (hmem x hx).1 (hfo.view_members (by rw [hvm]; exact hx))).goal⟩
      cases hp : c.isPushed with
      | false =>
        have e : walkV (P := P) K hK rev (d + 1) c n far =
            andV K hK true true (fun x => walkV K hK rev d c x far) far .start xs := by
          simp only [walkV, hv, hp, Bool.false_eq_true, ite_false]
        rw [e, WT, ws_plain hL hp hf, sed_meet hv]
        refine meet_plain_ex hL K hK rev _
          (fun x => SED P 𝕄 rev d (bset 𝕄 c.bound) x (bset 𝕄 far)) xs hf
          (by cases rev <;> rfl) (fun x hx => ?_) (fun x hx => (ih c hc x hx).2)
        rw [(ih c hc x hx).1, WT, ws_plain hL hp hf]
      | true =>
        have hpp : c.pushed = true := by
          have h := hp
          simp only [Near.isPushed, Bool.and_eq_true] at h
          exact h.1
        have ho : c.own = ⟨none, false⟩ := by simp [Near.own, hpp]
        have e : walkV (P := P) K hK rev (d + 1) c n far =
            andV K hK true false (fun x => walkV K hK rev d c x far) far .start xs ++
              andV K hK false true (fun x => walkV K hK rev d c.own x far) far .start xs := by
          simp only [walkV, hv, hp, ite_true]
        have hws : ∀ (d' : Nat) (n' : Rel), WS P 𝕄 rev d' c n' far =
            pushSet rev (bset 𝕄 c.bound) (SED P 𝕄 rev d' Set.univ n' (bset 𝕄 far)) := by
          intro d' n'
          simp only [WS, hpp, ite_true]
        rw [e, WT, hws, sed_meet hv]
        refine meet_pushed_ex hL K hK rev _ _
          (fun x => SED P 𝕄 rev d Set.univ x (bset 𝕄 far)) xs hf (bset_nonempty hL hc)
          (by cases rev <;> rfl) (by cases rev <;> rfl) (fun x hx => ?_)
          (fun x hx => (ih c hc x hx).2) (fun x hx => ?_)
        · rw [(ih c hc x hx).1, WT, hws]
        · have hco : IsBound D c.own.bound := by rw [ho]; exact isBound_none D
          rw [(ih c.own hco x hx).1, WT, ws_none hL (by rw [ho]) hf]

/-! ## The race -/

include hL hE in
/-- The race answered by a walk says the unfolding is final exactly when it
has no open product. -/
theorem walkRace_final (hP : ProgFO P) (rev : Bool) (d : Nat) (g : GoalOf R Rel)
    (hg : GoalOk D g) :
    (walkRace (K := DerivationKernel.over D K hK P) rev d g).val.1 = true ↔
      Final P 𝕄 d (bset 𝕄 g.lb) g.node (bset 𝕄 g.rb) := by
  have hn : IsBound D (if rev then g.rb else g.lb) := by
    cases rev <;> first | exact hg.lb | exact hg.rb
  have hf : IsBound D (if rev then g.lb else g.rb) := by
    cases rev <;> first | exact hg.lb | exact hg.rb
  have hex := walk_ex hL hE K hK hP rev d ⟨if rev then g.rb else g.lb, false⟩ g.node
    (if rev then g.lb else g.rb) hn hf hg.normal hg.fo
  have hS : WS P 𝕄 rev d ⟨if rev then g.rb else g.lb, false⟩ g.node (if rev then g.lb else g.rb) =
      SE P 𝕄 d (bset 𝕄 g.lb) g.node (bset 𝕄 g.rb) := by
    cases rev <;> rfl
  rw [WT, hS] at hex
  have hop := opn_iff hex
  rw [walkRace_val, Final, ← hop, ← any_itOpn]
  generalize (walkV (P := P) K hK rev d ⟨if rev then g.rb else g.lb, false⟩ g.node
    (if rev then g.lb else g.rb)).any itOpn = o
  cases o <;> simp

end laws

end Unfold

end Tabled

end RwLog
