/-
# What an unfolding relates, product by product

The unfolding of a goal to a depth is a list of products
(`Rungs/Tabled/Unfold.lean`). This file says what the list stands for, with
no representative in it: a closed product is the relation it relates, and an
open product is the set of left ends of its first stretch and the set of
right ends of its last one (`SP`). `SE P M d A e B` is the set of products of
the node `e` at depth `d` between the sets of terms `A` and `B` its
boundaries let through.

* A product followed by a product of the next member of a chain is `SeqS`.
  It is associative (`SeqS.assoc_right`, `SeqS.assoc_left`), so the products
  of a chain are the same folded from the left (`chainS`) and from the right
  (`chainR`, `chainS_eq_chainR`), and in the order a walk takes them in
  either direction (`chainD`).
* A walk and the shared evaluation keep of an open product only the end on
  the far side (`SI`, `farD`). What they hold followed by a product is
  `SeqI`, and it is what `SeqS` gives (`seqD_far`, `seqI_lift`).
* They do not compose what they hold with what follows: they restrict what
  follows to the far ends of what they hold (`PushD`) and then extend
  (`ExtI`). That is `SeqI` (`seqI_iff_push_ext`), and restricting a chain is
  restricting its first member (`pushSet_seq`).

Nothing here mentions a domain. `Unfolding/EagerExact.lean` and the files
after it show that each evaluation of the unfolding builds this set.
-/
import RwLog.Kernel.ExactIface
import RwLog.Rungs.Tabled.Unfolding.Dir

namespace RwLog

namespace Tabled

namespace Unfold

/-- A product of an unfolding, by what it relates: the pairs of a closed
product, or the left ends of the first stretch and the right ends of the
last stretch of an open one. -/
inductive SP where
  | closed (X : PRel)
  | opn (A B : Set GTerm)

/-- What a walk holds of a product: the pairs of a closed one, the ends on
the far side of an open one. -/
inductive SI where
  | closed (X : PRel)
  | opn (F : Set GTerm)

/-- The pairs of `X` from `A` to `B`. -/
def restr (A : Set GTerm) (X : PRel) (B : Set GTerm) : PRel := {p | p ∈ X ∧ p.1 ∈ A ∧ p.2 ∈ B}

/-- The terms `X` relates to a term of `A`. -/
def preS (X : PRel) (A : Set GTerm) : Set GTerm := {x | ∃ m ∈ A, (x, m) ∈ X}

/-- The terms a term of `B` is related to by `X`. -/
def postS (B : Set GTerm) (X : PRel) : Set GTerm := {z | ∃ m ∈ B, (m, z) ∈ X}

theorem preS_comp (X Y : PRel) (A : Set GTerm) : preS (X.comp Y) A = preS X (preS Y A) := by
  ext x
  constructor
  · rintro ⟨m, hm, k, h₁, h₂⟩; exact ⟨k, ⟨m, hm, h₂⟩, h₁⟩
  · rintro ⟨k, ⟨m, hm, h₂⟩, h₁⟩; exact ⟨m, hm, k, h₁, h₂⟩

theorem postS_comp (B : Set GTerm) (Y Z : PRel) : postS (postS B Y) Z = postS B (Y.comp Z) := by
  ext z
  constructor
  · rintro ⟨k, ⟨m, hm, h₁⟩, h₂⟩; exact ⟨m, hm, k, h₁, h₂⟩
  · rintro ⟨m, hm, k, h₁, h₂⟩; exact ⟨k, ⟨m, hm, h₁⟩, h₂⟩

/-! ## A product followed by a product -/

/-- A product followed by a product of the next member of a chain: there is
one when the stretches that meet relate a pair. -/
inductive SeqS : SP → SP → SP → Prop
  | cc {X Y : PRel} : (X.comp Y).Nonempty → SeqS (.closed X) (.closed Y) (.closed (X.comp Y))
  | co {X : PRel} {A B : Set GTerm} : (preS X A).Nonempty →
      SeqS (.closed X) (.opn A B) (.opn (preS X A) B)
  | oc {A B : Set GTerm} {Y : PRel} : (postS B Y).Nonempty →
      SeqS (.opn A B) (.closed Y) (.opn A (postS B Y))
  | oo {A B A' B' : Set GTerm} : (B ∩ A').Nonempty → SeqS (.opn A B) (.opn A' B') (.opn A B')

theorem SeqS.cast {p q r r' : SP} (h : SeqS p q r) (e : r = r') : SeqS p q r' := e ▸ h

theorem SeqS.assoc_right {p q r u v : SP} (h₁ : SeqS p q u) (h₂ : SeqS u r v) :
    ∃ w, SeqS q r w ∧ SeqS p w v := by
  cases h₁ with
  | @cc X Y h =>
    cases h₂ with
    | @cc _ Z h' =>
      have hn : (X.comp (Y.comp Z)).Nonempty := by rwa [← PRel.comp_assoc]
      obtain ⟨⟨x, z⟩, m, -, hm⟩ := id hn
      exact ⟨_, .cc ⟨_, hm⟩, (SeqS.cc hn).cast (by rw [PRel.comp_assoc])⟩
    | @co _ A B h' =>
      rw [preS_comp] at h' ⊢
      obtain ⟨x, k, hk, hx⟩ := h'
      exact ⟨_, .co ⟨k, hk⟩, .co ⟨x, k, hk, hx⟩⟩
  | @co X A B h =>
    cases h₂ with
    | oc h' => exact ⟨_, .oc h', .co h⟩
    | oo h' => exact ⟨_, .oo h', .co h⟩
  | @oc A B Y h =>
    cases h₂ with
    | @oc _ _ Z h' =>
      rw [postS_comp] at h' ⊢
      obtain ⟨z, m, hm, k, h₁, h₂⟩ := h'
      exact ⟨_, .cc ⟨(m, z), k, h₁, h₂⟩, .oc ⟨z, m, hm, k, h₁, h₂⟩⟩
    | @oo _ _ A' B' h' =>
      obtain ⟨k, ⟨m, hm, hmk⟩, hk⟩ := h'
      exact ⟨_, .co ⟨m, k, hk, hmk⟩, .oo ⟨m, hm, k, hk, hmk⟩⟩
  | @oo A B A' B' h =>
    cases h₂ with
    | oc h' => exact ⟨_, .oc h', .oo h⟩
    | oo h' => exact ⟨_, .oo h', .oo h⟩

theorem SeqS.assoc_left {p q r w v : SP} (h₁ : SeqS q r w) (h₂ : SeqS p w v) :
    ∃ u, SeqS p q u ∧ SeqS u r v := by
  cases h₁ with
  | @cc Y Z h =>
    cases h₂ with
    | @cc X _ h' =>
      have hn : ((X.comp Y).comp Z).Nonempty := by rwa [PRel.comp_assoc]
      obtain ⟨⟨x, z⟩, m, hm, -⟩ := id hn
      exact ⟨_, .cc ⟨_, hm⟩, (SeqS.cc hn).cast (by rw [PRel.comp_assoc])⟩
    | @oc A B _ h' =>
      rw [← postS_comp] at h' ⊢
      obtain ⟨z, k, hk, hz⟩ := id h'
      exact ⟨_, .oc ⟨k, hk⟩, .oc h'⟩
  | @co Y A' B' h =>
    cases h₂ with
    | @co X _ _ h' =>
      rw [← preS_comp] at h' ⊢
      obtain ⟨x, m, hm, k, h₁, h₂⟩ := id h'
      exact ⟨_, .cc ⟨(x, m), k, h₁, h₂⟩, .co h'⟩
    | @oo A B _ _ h' =>
      obtain ⟨k, hkB, m, hm, hkm⟩ := h'
      exact ⟨_, .oc ⟨m, k, hkB, hkm⟩, .oo ⟨m, ⟨k, hkB, hkm⟩, hm⟩⟩
  | @oc A' B' Z h =>
    cases h₂ with
    | co h' => exact ⟨_, .co h', .oc h⟩
    | oo h' => exact ⟨_, .oo h', .oc h⟩
  | @oo A' B' A'' B'' h =>
    cases h₂ with
    | co h' => exact ⟨_, .co h', .oo h⟩
    | oo h' => exact ⟨_, .oo h', .oo h⟩

/-- The products of two sets, one of each, in order. -/
def seqSets (S T : Set SP) : Set SP := {r | ∃ p ∈ S, ∃ q ∈ T, SeqS p q r}

theorem seqSets_assoc (S T U : Set SP) :
    seqSets (seqSets S T) U = seqSets S (seqSets T U) := by
  ext v
  constructor
  · rintro ⟨u, ⟨p, hp, q, hq, h₁⟩, r, hr, h₂⟩
    obtain ⟨w, h₃, h₄⟩ := h₁.assoc_right h₂
    exact ⟨p, hp, w, ⟨q, hq, r, hr, h₃⟩, h₄⟩
  · rintro ⟨p, hp, w, ⟨q, hq, r, hr, h₁⟩, h₂⟩
    obtain ⟨u, h₃, h₄⟩ := h₁.assoc_left h₂
    exact ⟨u, ⟨p, hp, q, hq, h₃⟩, r, hr, h₄⟩

/-- The products of a chain from the products of its members, folded from
the left as `Unfold.seqAll` folds them. -/
def chainS : List (Set SP) → Set SP
  | [] => ∅
  | S :: rest => rest.foldl seqSets S

/-- The products of a chain, folded from the right. -/
def chainR : List (Set SP) → Set SP
  | [] => ∅
  | [S] => S
  | S :: T :: rest => seqSets S (chainR (T :: rest))

theorem chainR_cons (S : Set SP) {l : List (Set SP)} (h : l ≠ []) :
    chainR (S :: l) = seqSets S (chainR l) := by
  cases l with
  | nil => exact absurd rfl h
  | cons T rest => rfl

theorem foldl_seqSets (S T : Set SP) : ∀ rest : List (Set SP),
    rest.foldl seqSets (seqSets S T) = seqSets S (rest.foldl seqSets T)
  | [] => rfl
  | U :: rest => by
    simp only [List.foldl_cons]
    rw [seqSets_assoc, foldl_seqSets S (seqSets T U) rest]

theorem chainS_eq_chainR : ∀ l : List (Set SP), chainS l = chainR l
  | [] => rfl
  | [S] => rfl
  | S :: T :: rest => by
    have ih := chainS_eq_chainR (T :: rest)
    show (T :: rest).foldl seqSets S = seqSets S (chainR (T :: rest))
    rw [← ih]
    exact foldl_seqSets S T rest

/-! ## The order a walk takes the members in -/

/-- The products of what was walked first followed by what was walked after
it. -/
def seqSetsD (rev : Bool) (S T : Set SP) : Set SP := if rev then seqSets T S else seqSets S T

/-- The products of a chain from the products of its members in the order a
walk takes them, folded as the walk goes. -/
def chainD (rev : Bool) : List (Set SP) → Set SP
  | [] => ∅
  | S :: rest => rest.foldl (seqSetsD rev) S

theorem chainD_false (l : List (Set SP)) : chainD false l = chainS l := by
  cases l <;> rfl

theorem chainR_snoc (y acc : Set SP) : ∀ l : List (Set SP),
    chainR (l ++ [seqSets y acc]) = chainR (l ++ [y, acc])
  | [] => rfl
  | [a] => rfl
  | a :: b :: l => by
    have ih := chainR_snoc y acc (b :: l)
    show chainR (a :: (b :: l ++ [seqSets y acc])) = chainR (a :: (b :: l ++ [y, acc]))
    rw [chainR_cons a (by simp), chainR_cons a (by simp), ih]

theorem foldl_rev (acc : Set SP) : ∀ ys : List (Set SP),
    ys.foldl (seqSetsD true) acc = chainR (ys.reverse ++ [acc])
  | [] => rfl
  | y :: ys => by
    rw [List.foldl_cons, foldl_rev _ ys]
    show chainR (ys.reverse ++ [seqSets y acc]) = _
    rw [chainR_snoc, List.reverse_cons, List.append_assoc]
    rfl

theorem chainD_true (l : List (Set SP)) : chainD true l.reverse = chainS l := by
  rw [chainS_eq_chainR]
  cases h : l.reverse with
  | nil => rw [List.reverse_eq_nil_iff.1 h]; rfl
  | cons S rest =>
    show rest.foldl (seqSetsD true) S = _
    rw [foldl_rev, ← List.reverse_cons, ← h, List.reverse_reverse]

/-! ## What a walk holds, followed by a product -/

/-- The ends of a relation on the far side. -/
def farEnds (rev : Bool) (X : PRel) : Set GTerm := if rev then X.lends else X.rends

/-- Of the two ends of an open product, the one on the near side. -/
def nearE (rev : Bool) (A B : Set GTerm) : Set GTerm := if rev then B else A

/-- Of the two ends of an open product, the one on the far side. -/
def farE (rev : Bool) (A B : Set GTerm) : Set GTerm := if rev then A else B

/-- The terms a relation takes a set to, away from the near side. -/
def thru (rev : Bool) (F : Set GTerm) (Y : PRel) : Set GTerm := if rev then preS Y F else postS F Y

/-- What a walk holds of a product. -/
def farD (rev : Bool) : SP → SI
  | .closed X => .closed X
  | .opn A B => .opn (farE rev A B)

/-- What a walk holds, followed by a product of the next member it walks. -/
inductive SeqI (rev : Bool) : SI → SP → SI → Prop
  | cc {X Y : PRel} : (compP rev X Y).Nonempty →
      SeqI rev (.closed X) (.closed Y) (.closed (compP rev X Y))
  | co {X : PRel} {A B : Set GTerm} : (farEnds rev X ∩ nearE rev A B).Nonempty →
      SeqI rev (.closed X) (.opn A B) (.opn (farE rev A B))
  | oc {F : Set GTerm} {Y : PRel} : (thru rev F Y).Nonempty →
      SeqI rev (.opn F) (.closed Y) (.opn (thru rev F Y))
  | oo {F A B : Set GTerm} : (F ∩ nearE rev A B).Nonempty →
      SeqI rev (.opn F) (.opn A B) (.opn (farE rev A B))

/-- A product walked first followed by a product walked after it. -/
def SeqD (rev : Bool) (p q r : SP) : Prop := if rev then SeqS q p r else SeqS p q r

theorem mem_seqSetsD {rev : Bool} {S T : Set SP} {r : SP} :
    r ∈ seqSetsD rev S T ↔ ∃ p ∈ S, ∃ q ∈ T, SeqD rev p q r := by
  cases rev
  · exact Iff.rfl
  · constructor
    · rintro ⟨q, hq, p, hp, h⟩; exact ⟨p, hp, q, hq, h⟩
    · rintro ⟨p, hp, q, hq, h⟩; exact ⟨q, hq, p, hp, h⟩

theorem seqD_far {rev : Bool} {p q r : SP} (h : SeqD rev p q r) :
    SeqI rev (farD rev p) q (farD rev r) := by
  cases rev
  · cases (h : SeqS p q r) with
    | cc h => exact .cc h
    | co h =>
      obtain ⟨x, m, hm, hx⟩ := h
      exact .co ⟨m, ⟨x, hx⟩, hm⟩
    | oc h => exact .oc h
    | oo h => exact .oo h
  · cases (h : SeqS q p r) with
    | cc h => exact .cc h
    | co h => exact .oc h
    | oc h =>
      obtain ⟨z, m, hm, hz⟩ := h
      exact .co ⟨m, ⟨z, hz⟩, hm⟩
    | oo h => exact .oo (by rwa [Set.inter_comm] at h)

theorem seqI_lift {rev : Bool} {p q : SP} {i : SI} (h : SeqI rev (farD rev p) q i) :
    ∃ r, SeqD rev p q r ∧ farD rev r = i := by
  cases rev
  · cases p with
    | closed X =>
      cases h with
      | cc h => exact ⟨_, SeqS.cc h, rfl⟩
      | co h =>
        obtain ⟨m, ⟨x, hx⟩, hm⟩ := h
        exact ⟨_, SeqS.co ⟨x, m, hm, hx⟩, rfl⟩
    | opn A B =>
      cases h with
      | oc h => exact ⟨_, SeqS.oc h, rfl⟩
      | oo h => exact ⟨_, SeqS.oo h, rfl⟩
  · cases p with
    | closed X =>
      cases h with
      | cc h => exact ⟨_, SeqS.cc h, rfl⟩
      | co h =>
        obtain ⟨m, ⟨z, hz⟩, hm⟩ := h
        exact ⟨_, SeqS.oc ⟨z, m, hm, hz⟩, rfl⟩
    | opn A B =>
      cases h with
      | oc h => exact ⟨_, SeqS.co h, rfl⟩
      | oo h => exact ⟨_, SeqS.oo (by rwa [Set.inter_comm]), rfl⟩

/-! ## Restricting what follows, then extending -/

/-- A relation restricted on the near side. -/
def restrD (rev : Bool) (π : Set GTerm) (X : PRel) : PRel :=
  if rev then restr Set.univ X π else restr π X Set.univ

@[simp] theorem restrD_false (π : Set GTerm) (X : PRel) :
    restrD false π X = restr π X Set.univ := rfl

@[simp] theorem restrD_true (π : Set GTerm) (X : PRel) :
    restrD true π X = restr Set.univ X π := rfl

/-- An open product restricted on the near side. -/
def pushO (rev : Bool) (π A B : Set GTerm) : SP := if rev then .opn A (B ∩ π) else .opn (A ∩ π) B

/-- A product restricted on the near side to the terms of `π`: there is one
when something is left. -/
inductive PushD (rev : Bool) (π : Set GTerm) : SP → SP → Prop
  | closed {X : PRel} : (restrD rev π X).Nonempty →
      PushD rev π (.closed X) (.closed (restrD rev π X))
  | opn {A B : Set GTerm} : (nearE rev A B ∩ π).Nonempty →
      PushD rev π (.opn A B) (pushO rev π A B)

/-- The ends a walk pushes into what follows. -/
def ifaceI (rev : Bool) : SI → Set GTerm
  | .closed X => farEnds rev X
  | .opn F => F

/-- What a walk holds, extended by what it holds of a product of the next
member, walked under what the first pushes. -/
inductive ExtI (rev : Bool) : SI → SI → SI → Prop
  | cc {X Y : PRel} : (compP rev X Y).Nonempty →
      ExtI rev (.closed X) (.closed Y) (.closed (compP rev X Y))
  | co {X : PRel} {F : Set GTerm} : ExtI rev (.closed X) (.opn F) (.opn F)
  | oc {F₀ : Set GTerm} {Y : PRel} : ExtI rev (.opn F₀) (.closed Y) (.opn (farEnds rev Y))
  | oo {F₀ F : Set GTerm} : ExtI rev (.opn F₀) (.opn F) (.opn F)

theorem compP_restrD (rev : Bool) (X Y : PRel) :
    compP rev X (restrD rev (farEnds rev X) Y) = compP rev X Y := by
  cases rev
  · ext ⟨x, z⟩
    constructor
    · rintro ⟨m, h₁, h₂, -, -⟩; exact ⟨m, h₁, h₂⟩
    · rintro ⟨m, h₁, h₂⟩; exact ⟨m, h₁, h₂, ⟨x, h₁⟩, trivial⟩
  · ext ⟨x, z⟩
    constructor
    · rintro ⟨m, ⟨h₁, -, -⟩, h₂⟩; exact ⟨m, h₁, h₂⟩
    · rintro ⟨m, h₁, h₂⟩; exact ⟨m, ⟨h₁, trivial, ⟨z, h₂⟩⟩, h₂⟩

theorem farEnds_restrD (rev : Bool) (F : Set GTerm) (Y : PRel) :
    farEnds rev (restrD rev F Y) = thru rev F Y := by
  cases rev
  · ext z
    constructor
    · rintro ⟨m, h, hm, -⟩; exact ⟨m, hm, h⟩
    · rintro ⟨m, hm, h⟩; exact ⟨m, h, hm, trivial⟩
  · ext x
    constructor
    · rintro ⟨m, h, -, hm⟩; exact ⟨m, hm, h⟩
    · rintro ⟨m, hm, h⟩; exact ⟨m, h, trivial, hm⟩

theorem farD_pushO (rev : Bool) (π A B : Set GTerm) :
    farD rev (pushO rev π A B) = .opn (farE rev A B) := by
  cases rev <;> rfl

theorem restrD_nonempty_of_comp {rev : Bool} {X Y : PRel} (h : (compP rev X Y).Nonempty) :
    (restrD rev (farEnds rev X) Y).Nonempty := by
  rw [← compP_restrD] at h
  exact compP_ne_right rev h

/-- Following what a walk holds by a product is restricting the product to
the ends the walk pushes and then extending. -/
theorem seqI_iff_push_ext {rev : Bool} {i₀ i : SI} {q : SP} :
    SeqI rev i₀ q i ↔ ∃ q', PushD rev (ifaceI rev i₀) q q' ∧ ExtI rev i₀ (farD rev q') i := by
  constructor
  · intro h
    cases h with
    | @cc X Y h =>
      refine ⟨_, .closed (restrD_nonempty_of_comp h), ?_⟩
      have := ExtI.cc (rev := rev) (X := X) (Y := restrD rev (farEnds rev X) Y)
        (by rwa [compP_restrD])
      rwa [compP_restrD] at this
    | @co X A B h =>
      refine ⟨_, .opn (by rwa [Set.inter_comm]), ?_⟩
      rw [farD_pushO]
      exact .co
    | @oc F Y h =>
      refine ⟨_, .closed (π := F) (X := Y) ?_, ?_⟩
      · rw [← farEnds_restrD] at h
        cases rev
        · obtain ⟨z, x, hx⟩ := h; exact ⟨_, hx⟩
        · obtain ⟨x, z, hx⟩ := h; exact ⟨_, hx⟩
      · have := ExtI.oc (rev := rev) (F₀ := F) (Y := restrD rev F Y)
        rwa [farEnds_restrD] at this
    | @oo F A B h =>
      refine ⟨_, .opn (by rwa [Set.inter_comm]), ?_⟩
      rw [farD_pushO]
      exact .oo
  · rintro ⟨q', hp, he⟩
    cases i₀ with
    | closed X =>
      cases hp with
      | @closed Y hY =>
        cases he with
        | cc h =>
          simp only [ifaceI] at h ⊢
          rw [compP_restrD] at h ⊢
          exact .cc h
      | @opn A B hA =>
        rw [farD_pushO] at he
        cases he with
        | co => exact .co (by rwa [Set.inter_comm])
    | opn F =>
      cases hp with
      | @closed Y hY =>
        cases he with
        | oc =>
          simp only [ifaceI] at hY ⊢
          rw [farEnds_restrD]
          refine .oc ?_
          rw [← farEnds_restrD]
          cases rev
          · obtain ⟨⟨x, z⟩, hx⟩ := hY; exact ⟨z, x, hx⟩
          · obtain ⟨⟨x, z⟩, hx⟩ := hY; exact ⟨x, z, hx⟩
      | @opn A B hA =>
        rw [farD_pushO] at he
        cases he with
        | oo => exact .oo (by rwa [Set.inter_comm])

/-! ## Restricting a chain is restricting its first member -/

/-- The products of a set restricted on the near side. -/
def pushSet (rev : Bool) (π : Set GTerm) (S : Set SP) : Set SP := {r | ∃ p ∈ S, PushD rev π p r}

theorem restr_comp_left (π : Set GTerm) (X Y : PRel) :
    (restr π X Set.univ).comp Y = restr π (X.comp Y) Set.univ := by
  ext ⟨x, z⟩
  constructor
  · rintro ⟨m, ⟨h₁, hx, -⟩, h₂⟩; exact ⟨⟨m, h₁, h₂⟩, hx, trivial⟩
  · rintro ⟨⟨m, h₁, h₂⟩, hx, -⟩; exact ⟨m, ⟨h₁, hx, trivial⟩, h₂⟩

theorem restr_comp_right (π : Set GTerm) (Y X : PRel) :
    Y.comp (restr Set.univ X π) = restr Set.univ (Y.comp X) π := by
  ext ⟨x, z⟩
  constructor
  · rintro ⟨m, h₁, h₂, -, hz⟩; exact ⟨⟨m, h₁, h₂⟩, trivial, hz⟩
  · rintro ⟨⟨m, h₁, h₂⟩, -, hz⟩; exact ⟨m, h₁, h₂, trivial, hz⟩

theorem preS_restr (π : Set GTerm) (X : PRel) (A : Set GTerm) :
    preS (restr π X Set.univ) A = preS X A ∩ π := by
  ext x
  constructor
  · rintro ⟨m, hm, h, hx, -⟩; exact ⟨⟨m, hm, h⟩, hx⟩
  · rintro ⟨⟨m, hm, h⟩, hx⟩; exact ⟨m, hm, h, hx, trivial⟩

theorem postS_restr (π : Set GTerm) (B : Set GTerm) (X : PRel) :
    postS B (restr Set.univ X π) = postS B X ∩ π := by
  ext z
  constructor
  · rintro ⟨m, hm, h, -, hz⟩; exact ⟨⟨m, hm, h⟩, hz⟩
  · rintro ⟨⟨m, hm, h⟩, hz⟩; exact ⟨m, hm, h, trivial, hz⟩

theorem restr_nonempty_left {π : Set GTerm} {X Y : PRel}
    (h : (restr π (X.comp Y) Set.univ).Nonempty) : (restr π X Set.univ).Nonempty := by
  obtain ⟨⟨x, z⟩, ⟨m, h₁, -⟩, hx, -⟩ := h
  exact ⟨(x, m), h₁, hx, trivial⟩

theorem restr_nonempty_right {π : Set GTerm} {Y X : PRel}
    (h : (restr Set.univ (Y.comp X) π).Nonempty) : (restr Set.univ X π).Nonempty := by
  obtain ⟨⟨x, z⟩, ⟨m, -, h₂⟩, -, hz⟩ := h
  exact ⟨(m, z), h₂, trivial, hz⟩

theorem pushD_seq {rev : Bool} {π : Set GTerm} {p q r r' : SP} (h : SeqD rev p q r)
    (hp : PushD rev π r r') : ∃ p', PushD rev π p p' ∧ SeqD rev p' q r' := by
  cases rev
  · cases (h : SeqS p q r) with
    | @cc X Y h =>
      cases hp with
      | closed hn =>
        have hn' : (restr π (X.comp Y) Set.univ).Nonempty := hn
        refine ⟨_, .closed (restr_nonempty_left hn'), ?_⟩
        simp only [restrD_false]
        exact (SeqS.cc (by rw [restr_comp_left]; exact hn')).cast
          (congrArg SP.closed (restr_comp_left π X Y))
    | @co X A B h =>
      cases hp with
      | opn hn =>
        have hn' : (preS X A ∩ π).Nonempty := hn
        obtain ⟨x, ⟨m, hm, hx⟩, hπ⟩ := id hn'
        refine ⟨_, .closed (X := X) ⟨(x, m), hx, hπ, trivial⟩, ?_⟩
        exact (SeqS.co (X := restr π X Set.univ) (A := A) (B := B)
          (by rw [preS_restr]; exact hn')).cast (by rw [preS_restr]; rfl)
    | oc h =>
      cases hp with
      | opn hn => exact ⟨_, .opn hn, SeqS.oc h⟩
    | oo h =>
      cases hp with
      | opn hn => exact ⟨_, .opn hn, SeqS.oo h⟩
  · cases (h : SeqS q p r) with
    | @cc Y X h =>
      cases hp with
      | closed hn =>
        have hn' : (restr Set.univ (Y.comp X) π).Nonempty := hn
        refine ⟨_, .closed (restr_nonempty_right hn'), ?_⟩
        simp only [restrD_true]
        exact (SeqS.cc (by rw [restr_comp_right]; exact hn')).cast
          (congrArg SP.closed (restr_comp_right π Y X))
    | co h =>
      cases hp with
      | opn hn => exact ⟨_, .opn hn, SeqS.co h⟩
    | @oc A B X h =>
      cases hp with
      | opn hn =>
        have hn' : (postS B X ∩ π).Nonempty := hn
        obtain ⟨z, ⟨m, hm, hz⟩, hπ⟩ := id hn'
        refine ⟨_, .closed (X := X) ⟨(m, z), hz, trivial, hπ⟩, ?_⟩
        exact (SeqS.oc (A := A) (B := B) (Y := restr Set.univ X π)
          (by rw [postS_restr]; exact hn')).cast (by rw [postS_restr]; rfl)
    | oo h =>
      cases hp with
      | opn hn => exact ⟨_, .opn hn, SeqS.oo h⟩

theorem seq_pushD {rev : Bool} {π : Set GTerm} {p p' q r' : SP} (hp : PushD rev π p p')
    (h : SeqD rev p' q r') : ∃ r, SeqD rev p q r ∧ PushD rev π r r' := by
  cases rev
  · cases hp with
    | @closed X hn =>
      cases (h : SeqS (.closed (restr π X Set.univ)) q r') with
      | @cc _ Y h =>
        simp only [restrD_false] at h ⊢
        rw [restr_comp_left] at h ⊢
        obtain ⟨⟨x, z⟩, hc, -⟩ := id h
        exact ⟨_, SeqS.cc ⟨_, hc⟩, .closed h⟩
      | @co _ A B h =>
        simp only [restrD_false] at h ⊢
        rw [preS_restr] at h ⊢
        obtain ⟨x, hx, -⟩ := id h
        exact ⟨_, SeqS.co ⟨x, hx⟩, .opn h⟩
    | @opn A B hn =>
      cases (h : SeqS (.opn (A ∩ π) B) q r') with
      | oc h => exact ⟨_, SeqS.oc h, .opn hn⟩
      | oo h => exact ⟨_, SeqS.oo h, .opn hn⟩
  · cases hp with
    | @closed X hn =>
      cases (h : SeqS q (.closed (restr Set.univ X π)) r') with
      | @cc Y _ h =>
        simp only [restrD_true] at h ⊢
        rw [restr_comp_right] at h ⊢
        obtain ⟨⟨x, z⟩, hc, -⟩ := id h
        exact ⟨_, SeqS.cc ⟨_, hc⟩, .closed h⟩
      | @oc A B _ h =>
        simp only [restrD_true] at h ⊢
        rw [postS_restr] at h ⊢
        obtain ⟨z, hz, -⟩ := id h
        exact ⟨_, SeqS.oc ⟨z, hz⟩, .opn h⟩
    | @opn A B hn =>
      cases (h : SeqS q (.opn A (B ∩ π)) r') with
      | co h => exact ⟨_, SeqS.co h, .opn hn⟩
      | oo h => exact ⟨_, SeqS.oo h, .opn hn⟩

theorem pushSet_seq (rev : Bool) (π : Set GTerm) (S T : Set SP) :
    pushSet rev π (seqSetsD rev S T) = seqSetsD rev (pushSet rev π S) T := by
  ext r'
  constructor
  · rintro ⟨r, hr, hpush⟩
    obtain ⟨p, hp, q, hq, h⟩ := mem_seqSetsD.1 hr
    obtain ⟨p', h₁, h₂⟩ := pushD_seq h hpush
    exact mem_seqSetsD.2 ⟨p', ⟨p, hp, h₁⟩, q, hq, h₂⟩
  · intro hr
    obtain ⟨p', ⟨p, hp, h₁⟩, q, hq, h₂⟩ := mem_seqSetsD.1 hr
    obtain ⟨r, h₃, h₄⟩ := seq_pushD h₁ h₂
    exact ⟨r, mem_seqSetsD.2 ⟨p, hp, q, hq, h₃⟩, h₄⟩

/-! ## The products of a meet -/

/-- The relations of the closed products of a set. -/
def closedPart (S : Set SP) : Set PRel := {X | SP.closed X ∈ S}

/-- The set has an open product. -/
def HasOpn (S : Set SP) : Prop := ∃ A B, SP.opn A B ∈ S

/-- The meets of one relation of each set that relate a pair. -/
def meetSets (S T : Set PRel) : Set PRel := {Z | ∃ X ∈ S, ∃ Y ∈ T, Z = X ∩ Y ∧ Z.Nonempty}

/-- The closed products of a meet from those of its members, folded as
`Unfold.meetAll` folds them. -/
def meetAllS : List (Set PRel) → Set PRel
  | [] => ∅
  | S :: rest => rest.foldl meetSets S

/-- The products of a meet between `A` and `B` from the products of its
members between them: the meets of one closed product of each, and the meet
itself as an open product when every member has a product and one of them an
open one. -/
def meetS (A B : Set GTerm) (Ss : List (Set SP)) : Set SP :=
  {r | (∃ X ∈ meetAllS (Ss.map closedPart), r = .closed X) ∨
    (r = .opn A B ∧ (∀ S ∈ Ss, S.Nonempty) ∧ ∃ S ∈ Ss, HasOpn S)}

/-! ## The products of a node -/

/-- The products of the unfolding of the node `e` to depth `d`, between the
terms `A` its left boundary lets through and the terms `B` its right
boundary lets through. -/
def SE (P : Program) (M : Interp) : Nat → Set GTerm → Rel → Set GTerm → Set SP
  | 0, A, _, B => {.opn A B}
  | d + 1, A, e, B =>
    match e.view.forget with
    | .span _ => {r | ∃ s, e = .span s ∧ r = .closed (restr A (s.den.at M) B) ∧
        (restr A (s.den.at M) B).Nonempty}
    | .call _ _ =>
      match Charged.bodyOf P e with
      | some b => SE P M d A b B
      | none => ∅
    | .union xs => {r | ∃ x ∈ xs, r ∈ SE P M d A x B}
    | .chain xs => chainS (xs.zipIdx.map fun p =>
        SE P M d (if p.2 = 0 then A else Set.univ) p.1
          (if p.2 + 1 = xs.length then B else Set.univ))
    | .meet xs => meetS A B (xs.map fun x => SE P M d A x B)

variable {P : Program} {M : Interp}

theorem se_zero (A B : Set GTerm) (e : Rel) : SE P M 0 A e B = {.opn A B} := rfl

theorem se_span {d : Nat} {A B : Set GTerm} {s : Span} :
    SE P M (d + 1) A (.span s) B =
      {r | r = .closed (restr A (s.den.at M) B) ∧ (restr A (s.den.at M) B).Nonempty} := by
  simp only [SE, RelOf.view, NodeView.forget]
  ext r
  constructor
  · rintro ⟨s', e, h⟩; cases e; exact h
  · intro h; exact ⟨s, rfl, h⟩

theorem se_call {d : Nat} {A B : Set GTerm} {e b : Rel} {n : Name} {f : Bool}
    (h : e.view.forget = .call n f) (hb : Charged.bodyOf P e = some b) :
    SE P M (d + 1) A e B = SE P M d A b B := by
  simp only [SE, h, hb]

theorem se_union {d : Nat} {A B : Set GTerm} {e : Rel} {xs : List Rel}
    (h : e.view.forget = .union xs) :
    SE P M (d + 1) A e B = {r | ∃ x ∈ xs, r ∈ SE P M d A x B} := by
  simp only [SE, h]

theorem se_chain {d : Nat} {A B : Set GTerm} {e : Rel} {xs : List Rel}
    (h : e.view.forget = .chain xs) :
    SE P M (d + 1) A e B = chainS (xs.zipIdx.map fun p =>
      SE P M d (if p.2 = 0 then A else Set.univ) p.1
        (if p.2 + 1 = xs.length then B else Set.univ)) := by
  simp only [SE, h]

theorem se_meet {d : Nat} {A B : Set GTerm} {e : Rel} {xs : List Rel}
    (h : e.view.forget = .meet xs) :
    SE P M (d + 1) A e B = meetS A B (xs.map fun x => SE P M d A x B) := by
  simp only [SE, h]

/-- The unfolding has no open product. -/
def Final (P : Program) (M : Interp) (d : Nat) (A : Set GTerm) (e : Rel) (B : Set GTerm) : Prop :=
  ¬ HasOpn (SE P M d A e B)

/-! ## Every product relates something -/

/-- A closed product relates a pair, and both ends of an open one have a
term. -/
def SP.Live : SP → Prop
  | .closed X => X.Nonempty
  | .opn A B => A.Nonempty ∧ B.Nonempty

theorem SeqS.live {p q r : SP} (h : SeqS p q r) (hp : p.Live) (hq : q.Live) : r.Live := by
  cases h with
  | cc h => exact h
  | co h => exact ⟨h, hq.2⟩
  | oc h => exact ⟨hp.1, h⟩
  | oo h => exact ⟨hp.1, hq.2⟩

theorem foldl_seqSets_live : ∀ (rest : List (Set SP)) (S : Set SP), (∀ p ∈ S, p.Live) →
    (∀ T ∈ rest, ∀ p ∈ T, p.Live) → ∀ p ∈ rest.foldl seqSets S, p.Live
  | [], _, hS, _ => hS
  | T :: rest, S, hS, hr => by
    refine foldl_seqSets_live rest (seqSets S T) ?_ fun U hU => hr U (List.mem_cons_of_mem _ hU)
    rintro r ⟨p, hp, q, hq, h⟩
    exact h.live (hS p hp) (hr T (by simp) q hq)

theorem chainS_live {l : List (Set SP)} (h : ∀ T ∈ l, ∀ p ∈ T, p.Live) : ∀ p ∈ chainS l, p.Live := by
  cases l with
  | nil => intro p hp; cases hp
  | cons S rest =>
    exact foldl_seqSets_live rest S (h S (by simp)) fun T hT => h T (List.mem_cons_of_mem _ hT)

theorem foldl_meetSets_live : ∀ (rest : List (Set PRel)) (S : Set PRel), (∀ X ∈ S, X.Nonempty) →
    ∀ X ∈ rest.foldl meetSets S, X.Nonempty
  | [], _, hS => hS
  | T :: rest, S, _ => by
    refine foldl_meetSets_live rest (meetSets S T) ?_
    rintro Z ⟨X, -, Y, -, -, hZ⟩
    exact hZ

theorem meetAllS_live {l : List (Set PRel)} (h : ∀ S ∈ l, ∀ X ∈ S, X.Nonempty) :
    ∀ X ∈ meetAllS l, X.Nonempty := by
  cases l with
  | nil => intro X hX; cases hX
  | cons S rest => exact foldl_meetSets_live rest S (h S (by simp))

theorem se_live : ∀ (d : Nat) (A : Set GTerm) (e : Rel) (B : Set GTerm), A.Nonempty →
    B.Nonempty → ∀ p ∈ SE P M d A e B, p.Live
  | 0, A, e, B, hA, hB => by
    intro p hp
    obtain rfl : p = .opn A B := hp
    exact ⟨hA, hB⟩
  | d + 1, A, e, B, hA, hB => by
    have hU : (Set.univ : Set GTerm).Nonempty := ⟨.sym "", trivial⟩
    cases hv : e.view.forget with
    | span u =>
      obtain ⟨s, rfl⟩ := forget_span hv
      rw [se_span]
      rintro p ⟨rfl, hne⟩
      exact hne
    | call n f =>
      cases hb : Charged.bodyOf P e with
      | none =>
        obtain ⟨b, hb'⟩ := forget_call (P := P) hv
        rw [hb] at hb'; cases hb'
      | some b =>
        rw [se_call hv hb]
        exact se_live d A b B hA hB
    | union xs =>
      rw [se_union hv]
      rintro p ⟨x, -, hp⟩
      exact se_live d A x B hA hB p hp
    | chain xs =>
      rw [se_chain hv]
      refine chainS_live fun T hT => ?_
      obtain ⟨q, -, rfl⟩ := List.mem_map.1 hT
      exact se_live d _ q.1 _ (by split <;> assumption) (by split <;> assumption)
    | meet xs =>
      rw [se_meet hv]
      rintro p (⟨X, hX, rfl⟩ | ⟨rfl, -, -⟩)
      · refine meetAllS_live (fun S hS X hX => ?_) X hX
        obtain ⟨T, hT, rfl⟩ := List.mem_map.1 hS
        obtain ⟨x, -, rfl⟩ := List.mem_map.1 hT
        exact se_live d A x B hA hB _ hX
      · exact ⟨hA, hB⟩

/-- Restricting to every term changes nothing. -/
theorem pushSet_univ (rev : Bool) {S : Set SP} (hS : ∀ p ∈ S, p.Live) :
    pushSet rev Set.univ S = S := by
  have hr : ∀ X : PRel, restrD rev Set.univ X = X := by
    intro X
    cases rev
    · ext ⟨x, z⟩; exact ⟨fun h => h.1, fun h => ⟨h, trivial, trivial⟩⟩
    · ext ⟨x, z⟩; exact ⟨fun h => h.1, fun h => ⟨h, trivial, trivial⟩⟩
  have ho : ∀ A B : Set GTerm, pushO rev Set.univ A B = .opn A B := by
    intro A B
    cases rev <;> simp [pushO]
  ext r
  constructor
  · rintro ⟨p, hp, h⟩
    cases h with
    | closed h => rw [hr]; exact hp
    | opn h => rw [ho]; exact hp
  · intro hr'
    refine ⟨r, hr', ?_⟩
    cases r with
    | closed X =>
      have := PushD.closed (rev := rev) (π := Set.univ) (X := X) (by rw [hr]; exact hS _ hr')
      rwa [hr] at this
    | opn A B =>
      have := PushD.opn (rev := rev) (π := Set.univ) (A := A) (B := B) (by
        rw [Set.inter_univ]
        have := hS _ hr'
        cases rev
        · exact this.1
        · exact this.2)
      rwa [ho] at this

end Unfold

end Tabled

end RwLog
