/-
# The normal form denotes what the expression denotes

`DerivesG P e G` is `Derives P e s` on ground relations: `G` is the relation
of a derivation of `e`, where a composition or a meet that matches nothing is
kept as the empty relation. The derivable spans of `e` are exactly the
nonempty relations it derives (`derives_iff_derivesG`).

On ground relations the rules of derivation are plain operations on sets
(`gd_seq`, `gd_and`, ...), composition is associative with a unit and meet is
associative and commutative with a unit. From that:

* `gd_normB`: the normal form of an expression derives the relations the
  expression derives, and the normal form of its converse derives their
  converses;
* `derives_norm_iff`: so the normal form has the derivable spans of the
  expression, up to the ground relation a span denotes;
* `sem_norm`, `semAt_norm`: so it has the meaning of the expression;
* the normal form forgets the grouping of `;`, the order and grouping of `&`
  and of `|`, and a double converse (`norm_seq_assoc`, `norm_and_comm`, ...).

The same facts are given for the node operations of the kernel: joining two
chains (`gd_mkSeq_append`), meeting two meets (`gd_mkAnd_sorted_append`),
membership in a union (`gd_unionParts`).
-/
import RwLog.Kernel.NormalForm
import RwLog.Kernel.Order
import RwLog.SpanLayer.Derives
import RwLog.SpanLayer.Algebra

namespace RwLog

/-! ## Algebra of ground relations -/

namespace GRel

/-- The unit of `meet`: every pair, with the empty store. -/
def top : GRel := {x | x.2.2 = ∅}

theorem meet_top (R : GRel) : R.meet top = R := by
  ext ⟨a, b, X⟩
  constructor
  · rintro ⟨S₁, S₂, h₁, h₂, h₃⟩
    have h₂' : S₂ = ∅ := h₂
    subst h₂'
    have : X = S₁ := by simpa using h₃
    subst this; exact h₁
  · intro h; exact ⟨X, ∅, h, rfl, by simp⟩

theorem meet_comm (R S : GRel) : R.meet S = S.meet R := by
  ext ⟨a, b, X⟩
  simp only [meet, Set.mem_ofPred_eq]
  constructor <;> rintro ⟨S₁, S₂, h₁, h₂, rfl⟩ <;> exact ⟨S₂, S₁, h₂, h₁, Finset.union_comm _ _⟩

theorem meet_assoc (R S U : GRel) : (R.meet S).meet U = R.meet (S.meet U) := by
  ext ⟨a, b, X⟩
  simp only [meet, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨_, S₃, ⟨S₁, S₂, h₁, h₂, rfl⟩, h₃, rfl⟩
    exact ⟨S₁, S₂ ∪ S₃, h₁, ⟨S₂, S₃, h₂, h₃, rfl⟩, Finset.union_assoc _ _ _⟩
  · rintro ⟨S₁, _, h₁, ⟨S₂, S₃, h₂, h₃, rfl⟩, rfl⟩
    exact ⟨S₁ ∪ S₂, S₃, ⟨S₁, S₂, h₁, h₂, rfl⟩, h₃, (Finset.union_assoc _ _ _).symm⟩

theorem meet_nonempty_left {R S : GRel} (h : (R.meet S).Nonempty) : R.Nonempty := by
  obtain ⟨x, S₁, _, h₁, _⟩ := h; exact ⟨_, h₁⟩

theorem meet_nonempty_right {R S : GRel} (h : (R.meet S).Nonempty) : S.Nonempty := by
  obtain ⟨x, _, S₂, _, h₂, _⟩ := h; exact ⟨_, h₂⟩

theorem inv_nonempty {R : GRel} : R.inv.Nonempty ↔ R.Nonempty := by
  constructor
  · rintro ⟨x, hx⟩; exact ⟨_, hx⟩
  · rintro ⟨⟨a, b, X⟩, hx⟩; exact ⟨(b, a, X), hx⟩

theorem inv_injective : Function.Injective GRel.inv := fun R S h => by
  rw [← inv_inv R, ← inv_inv S, h]

end GRel

/-! ## Derivations on ground relations -/

variable (P : Program)

/-- `Derives` on ground relations, with the compositions and meets that match
nothing kept as the empty relation. -/
inductive DerivesG : Rel → GRel → Prop
  | span (s : Span) : DerivesG (.span s) s.den
  | orl {a b G} : DerivesG a G → DerivesG (.or a b) G
  | orr {a b G} : DerivesG b G → DerivesG (.or a b) G
  | seq {a b A B} : DerivesG a A → DerivesG b B → DerivesG (.seq a b) (A.comp B)
  | and {a b A B} : DerivesG a A → DerivesG b B → DerivesG (.and a b) (A.meet B)
  | conv {a A} : DerivesG a A → DerivesG (.conv a) A.inv
  | call {n G} : DerivesG (P.body n) G → DerivesG (.call n) G

/-- The ground relations an expression derives. -/
def GD (e : Rel) : Set GRel := {G | DerivesG P e G}

variable {P}

theorem Derives.derivesG {e : Rel} {s : Span} (h : Derives P e s) : DerivesG P e s.den := by
  induction h with
  | span s => exact .span s
  | orl _ ih => exact .orl ih
  | orr _ ih => exact .orr ih
  | seq _ _ hc ih₁ ih₂ => rw [compose_some hc]; exact .seq ih₁ ih₂
  | and _ _ hc ih₁ ih₂ => rw [meet_some hc]; exact .and ih₁ ih₂
  | conv _ ih => rw [swap_den]; exact .conv ih
  | call _ ih => exact .call ih

theorem DerivesG.derives {e : Rel} {G : GRel} (h : DerivesG P e G) :
    G.Nonempty → ∃ s, Derives P e s ∧ s.den = G := by
  induction h with
  | span s => intro _; exact ⟨s, .span s, rfl⟩
  | orl _ ih => intro hn; obtain ⟨s, hs, rfl⟩ := ih hn; exact ⟨s, .orl hs, rfl⟩
  | orr _ ih => intro hn; obtain ⟨s, hs, rfl⟩ := ih hn; exact ⟨s, .orr hs, rfl⟩
  | seq _ _ ih₁ ih₂ =>
    intro hn
    obtain ⟨s₁, h₁, rfl⟩ := ih₁ (GRel.comp_nonempty_left hn)
    obtain ⟨s₂, h₂, rfl⟩ := ih₂ (GRel.comp_nonempty_right hn)
    obtain ⟨s, hc, hd⟩ := compose_isSome hn
    exact ⟨s, .seq h₁ h₂ hc, hd⟩
  | and _ _ ih₁ ih₂ =>
    intro hn
    obtain ⟨s₁, h₁, rfl⟩ := ih₁ (GRel.meet_nonempty_left hn)
    obtain ⟨s₂, h₂, rfl⟩ := ih₂ (GRel.meet_nonempty_right hn)
    obtain ⟨s, hc, hd⟩ := meet_isSome hn
    exact ⟨s, .and h₁ h₂ hc, hd⟩
  | conv _ ih =>
    intro hn
    obtain ⟨s, hs, rfl⟩ := ih (GRel.inv_nonempty.1 hn)
    exact ⟨s.swap, .conv hs, swap_den s⟩
  | call _ ih => intro hn; obtain ⟨s, hs, rfl⟩ := ih hn; exact ⟨s, .call hs, rfl⟩

/-- The derivable spans of an expression are the nonempty ground relations it
derives. -/
theorem derives_iff_derivesG {e : Rel} {G : GRel} :
    (∃ s, Derives P e s ∧ s.den = G) ↔ G ∈ GD P e ∧ G.Nonempty := by
  constructor
  · rintro ⟨s, hs, rfl⟩; exact ⟨hs.derivesG, s.den_nonempty⟩
  · rintro ⟨h, hn⟩; exact h.derives hn

/-! ### One equation per constructor -/

variable (P)

theorem gd_zero : GD P .zero = ∅ := by
  ext G; simp only [GD, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]; intro h; cases h

theorem gd_span (s : Span) : GD P (.span s) = {s.den} := by
  ext G; simp only [GD, Set.mem_ofPred_eq, Set.mem_singleton_iff]
  constructor
  · intro h; cases h; rfl
  · rintro rfl; exact .span s

theorem gd_or (a b : Rel) : GD P (.or a b) = GD P a ∪ GD P b := by
  ext G; simp only [GD, Set.mem_ofPred_eq, Set.mem_union]
  constructor
  · intro h; cases h with
    | orl h => exact .inl h
    | orr h => exact .inr h
  · rintro (h | h)
    · exact .orl h
    · exact .orr h

theorem gd_seq (a b : Rel) : GD P (.seq a b) = Set.image2 GRel.comp (GD P a) (GD P b) := by
  ext G; simp only [GD, Set.mem_ofPred_eq, Set.mem_image2]
  constructor
  · intro h; cases h with
    | seq h₁ h₂ => exact ⟨_, h₁, _, h₂, rfl⟩
  · rintro ⟨A, h₁, B, h₂, rfl⟩; exact .seq h₁ h₂

theorem gd_and (a b : Rel) : GD P (.and a b) = Set.image2 GRel.meet (GD P a) (GD P b) := by
  ext G; simp only [GD, Set.mem_ofPred_eq, Set.mem_image2]
  constructor
  · intro h; cases h with
    | and h₁ h₂ => exact ⟨_, h₁, _, h₂, rfl⟩
  · rintro ⟨A, h₁, B, h₂, rfl⟩; exact .and h₁ h₂

theorem gd_conv (a : Rel) : GD P (.conv a) = GRel.inv '' GD P a := by
  ext G; simp only [GD, Set.mem_ofPred_eq, Set.mem_image]
  constructor
  · intro h; cases h with
    | conv h => exact ⟨_, h, rfl⟩
  · rintro ⟨A, h, rfl⟩; exact .conv h

theorem gd_call (n : Name) : GD P (.call n) = GD P (P.body n) := by
  ext G; simp only [GD, Set.mem_ofPred_eq]
  constructor
  · intro h; cases h with
    | call h => exact h
  · exact .call

/-! ### Converse on sets of ground relations -/

theorem inv_image_inv_image (X : Set GRel) : GRel.inv '' (GRel.inv '' X) = X := by
  rw [Set.image_image]; simp [GRel.inv_inv]

theorem inv_image_comp (X Y : Set GRel) :
    GRel.inv '' Set.image2 GRel.comp X Y = Set.image2 GRel.comp (GRel.inv '' Y) (GRel.inv '' X) := by
  rw [Set.image_image2, Set.image2_image_left, Set.image2_image_right, Set.image2_swap]
  simp only [GRel.inv_comp]

theorem inv_image_meet (X Y : Set GRel) :
    GRel.inv '' Set.image2 GRel.meet X Y = Set.image2 GRel.meet (GRel.inv '' X) (GRel.inv '' Y) := by
  rw [Set.image_image2, Set.image2_image_left, Set.image2_image_right]
  simp only [GRel.inv_meet]

/-! ## Chains, meets and unions as lists -/

/-- The relations a chain of sets of relations derives. -/
def seqAll (L : List (Set GRel)) : Set GRel := L.foldr (Set.image2 GRel.comp) {GRel.id}

/-- The relations a meet of sets of relations derives. -/
def andAll (L : List (Set GRel)) : Set GRel := L.foldr (Set.image2 GRel.meet) {GRel.top}

theorem image2_comp_id (X : Set GRel) : Set.image2 GRel.comp X {GRel.id} = X := by
  rw [Set.image2_singleton_right]; simp only [GRel.comp_id, Set.image_id']

theorem image2_id_comp (X : Set GRel) : Set.image2 GRel.comp {GRel.id} X = X := by
  rw [Set.image2_singleton_left, show GRel.id.comp = id from funext GRel.id_comp, Set.image_id]

theorem image2_meet_top (X : Set GRel) : Set.image2 GRel.meet X {GRel.top} = X := by
  rw [Set.image2_singleton_right]; simp only [GRel.meet_top, Set.image_id']

theorem image2_top_meet (X : Set GRel) : Set.image2 GRel.meet {GRel.top} X = X := by
  have : GRel.top.meet = id := by
    funext b; rw [GRel.meet_comm, GRel.meet_top]; rfl
  rw [Set.image2_singleton_left, this, Set.image_id]

theorem image2_comp_assoc (X Y Z : Set GRel) :
    Set.image2 GRel.comp (Set.image2 GRel.comp X Y) Z =
      Set.image2 GRel.comp X (Set.image2 GRel.comp Y Z) :=
  Set.image2_assoc GRel.comp_assoc

theorem image2_meet_assoc (X Y Z : Set GRel) :
    Set.image2 GRel.meet (Set.image2 GRel.meet X Y) Z =
      Set.image2 GRel.meet X (Set.image2 GRel.meet Y Z) :=
  Set.image2_assoc GRel.meet_assoc

theorem image2_meet_comm (X Y : Set GRel) :
    Set.image2 GRel.meet X Y = Set.image2 GRel.meet Y X :=
  Set.image2_comm GRel.meet_comm

theorem seqAll_append (L₁ L₂ : List (Set GRel)) :
    seqAll (L₁ ++ L₂) = Set.image2 GRel.comp (seqAll L₁) (seqAll L₂) := by
  induction L₁ with
  | nil => exact (image2_id_comp _).symm
  | cons X L ih =>
    simp only [seqAll, List.cons_append, List.foldr_cons] at ih ⊢
    rw [ih, image2_comp_assoc]

theorem andAll_append (L₁ L₂ : List (Set GRel)) :
    andAll (L₁ ++ L₂) = Set.image2 GRel.meet (andAll L₁) (andAll L₂) := by
  induction L₁ with
  | nil => exact (image2_top_meet _).symm
  | cons X L ih =>
    simp only [andAll, List.cons_append, List.foldr_cons] at ih ⊢
    rw [ih, image2_meet_assoc]

theorem andAll_perm {L₁ L₂ : List (Set GRel)} (h : L₁.Perm L₂) : andAll L₁ = andAll L₂ := by
  induction h with
  | nil => rfl
  | cons X _ ih => simp only [andAll, List.foldr_cons] at ih ⊢; rw [ih]
  | swap X Y L =>
    simp only [andAll, List.foldr_cons]
    rw [← image2_meet_assoc, ← image2_meet_assoc, image2_meet_comm Y X]
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-! ### What follows from the equations alone

The equations above, for every constructor but a call, are all that the facts
about the normal form use. They are stated for any assignment `G` of ground
relations to expressions that satisfies them (`GLaws`), so that they hold of
the derivations of a bounded depth too (`Kernel/NormalFormDepth.lean`). -/

/-- The equations of `GD` for every constructor but a call. -/
structure GLaws (G : Rel → Set GRel) : Prop where
  zero : G .zero = ∅
  span : ∀ s : Span, G (.span s) = {s.den}
  or : ∀ a b : Rel, G (.or a b) = G a ∪ G b
  seq : ∀ a b : Rel, G (.seq a b) = Set.image2 GRel.comp (G a) (G b)
  and : ∀ a b : Rel, G (.and a b) = Set.image2 GRel.meet (G a) (G b)
  conv : ∀ a : Rel, G (.conv a) = GRel.inv '' G a

theorem gd_laws : GLaws (GD P) := ⟨gd_zero P, gd_span P, gd_or P, gd_seq P, gd_and P, gd_conv P⟩

theorem seqParts_ne_nil : ∀ e : Rel, seqParts e ≠ []
  | .seq a b => by simp [seqParts, seqParts_ne_nil a]
  | .zero | .span _ | .or _ _ | .and _ _ | .conv _ | .call _ => by simp [seqParts]

theorem andParts_ne_nil : ∀ e : Rel, andParts e ≠ []
  | .and a b => by simp [andParts, andParts_ne_nil a]
  | .zero | .span _ | .or _ _ | .seq _ _ | .conv _ | .call _ => by simp [andParts]

theorem sortedParts_perm (L : List Rel) : (sortedParts L).Perm L := List.mergeSort_perm _ _

section

variable {G : Rel → Set GRel} (hG : GLaws G)
include hG

theorem GLaws.gd_mkSeq : ∀ {L : List Rel}, L ≠ [] → G (mkSeq L) = seqAll (L.map (G))
  | [], h => absurd rfl h
  | [e], _ => (image2_comp_id _).symm
  | e :: e' :: es, _ => by
    rw [show mkSeq (e :: e' :: es) = .seq e (mkSeq (e' :: es)) from rfl, hG.seq,
      GLaws.gd_mkSeq (L := e' :: es) (by simp)]
    rfl

theorem GLaws.gd_mkAnd : ∀ {L : List Rel}, L ≠ [] → G (mkAnd L) = andAll (L.map (G))
  | [], h => absurd rfl h
  | [e], _ => (image2_meet_top _).symm
  | e :: e' :: es, _ => by
    rw [show mkAnd (e :: e' :: es) = .and e (mkAnd (e' :: es)) from rfl, hG.and,
      GLaws.gd_mkAnd (L := e' :: es) (by simp)]
    rfl

theorem GLaws.gd_mkOr : ∀ L : List Rel, G (mkOr L) = ⋃ e ∈ L, G e
  | [] => by simp [mkOr, hG.zero]
  | [e] => by simp [mkOr]
  | e :: e' :: es => by
    rw [show mkOr (e :: e' :: es) = .or e (mkOr (e' :: es)) from rfl, hG.or, GLaws.gd_mkOr (e' :: es)]
    simp only [List.mem_cons, Set.iUnion_iUnion_eq_or_left]

/-- An expression derives what the chain of its members derives. -/
theorem GLaws.gd_seqParts : ∀ e : Rel, seqAll ((seqParts e).map (G)) = G e
  | .seq a b => by
    rw [seqParts, List.map_append, seqAll_append, GLaws.gd_seqParts a, GLaws.gd_seqParts b, hG.seq]
  | .zero | .span _ | .or _ _ | .and _ _ | .conv _ | .call _ => image2_comp_id _

/-- An expression derives what the meet of its members derives. -/
theorem GLaws.gd_andParts : ∀ e : Rel, andAll ((andParts e).map (G)) = G e
  | .and a b => by
    rw [andParts, List.map_append, andAll_append, GLaws.gd_andParts a, GLaws.gd_andParts b, hG.and]
  | .zero | .span _ | .or _ _ | .seq _ _ | .conv _ | .call _ => image2_meet_top _

/-- An expression derives what its branches derive. -/
theorem GLaws.gd_orBranches : ∀ e : Rel, (⋃ x ∈ orBranches e, G x) = G e
  | .or a b => by
    rw [orBranches, hG.or, ← GLaws.gd_orBranches a, ← GLaws.gd_orBranches b]
    ext G; simp only [List.mem_append, Set.mem_iUnion, Set.mem_union, exists_prop]
    constructor
    · rintro ⟨x, hx | hx, hX⟩
      · exact .inl ⟨x, hx, hX⟩
      · exact .inr ⟨x, hx, hX⟩
    · rintro (⟨x, hx, hX⟩ | ⟨x, hx, hX⟩)
      · exact ⟨x, .inl hx, hX⟩
      · exact ⟨x, .inr hx, hX⟩
  | .zero | .span _ | .and _ _ | .seq _ _ | .conv _ | .call _ => by simp [orBranches]

/-- Sorting the branches and dropping `0` and repeats changes nothing. -/
theorem GLaws.gd_sortedBranches (L : List Rel) :
    (⋃ x ∈ sortedBranches L, G x) = ⋃ x ∈ L, G x := by
  ext G
  simp only [Set.mem_iUnion, exists_prop, mem_sortedBranches]
  constructor
  · rintro ⟨x, ⟨hx, _⟩, hX⟩; exact ⟨x, hx, hX⟩
  · rintro ⟨x, hx, hX⟩
    refine ⟨x, ⟨hx, ?_⟩, hX⟩
    rintro rfl
    rw [hG.zero] at hX; exact hX

/-! ### The node operations of the kernel -/

/-- Joining two chains: the chain of the members of both derives the
compositions. -/
theorem GLaws.gd_mkSeq_append (a b : Rel) :
    G (mkSeq (seqParts a ++ seqParts b)) = Set.image2 GRel.comp (G a) (G b) := by
  rw [hG.gd_mkSeq (by simp [seqParts_ne_nil]), List.map_append, seqAll_append, hG.gd_seqParts,
    hG.gd_seqParts]

/-- Meeting two meets: the sorted meet of the members of both derives the
meets. -/
theorem GLaws.gd_mkAnd_sorted_append (a b : Rel) :
    G (mkAnd (sortedParts (andParts a ++ andParts b))) =
      Set.image2 GRel.meet (G a) (G b) := by
  have hne : sortedParts (andParts a ++ andParts b) ≠ [] := by
    intro h
    have := (sortedParts_perm (andParts a ++ andParts b)).length_eq
    rw [h, List.length_append] at this
    exact andParts_ne_nil a (List.length_eq_zero_iff.1 (by simp at this; omega))
  rw [hG.gd_mkAnd hne, andAll_perm ((sortedParts_perm _).map _), List.map_append, andAll_append,
    hG.gd_andParts, hG.gd_andParts]

/-- A union derives what its members derive. -/
theorem GLaws.gd_unionParts (e : Rel) : (⋃ x ∈ e.unionParts, G x) = G e := by
  cases e with
  | zero => simp [RelOf.unionParts, hG.zero]
  | _ => exact hG.gd_orBranches _

/-! ## The normal form -/

/-- **The normal form derives what the expression derives**, and the normal
form of the converse derives the converses. -/
theorem GLaws.gd_normB : ∀ (b : Bool) (e : Rel),
    G (normB b e) = if b then GRel.inv '' G e else G e
  | b, .zero => by cases b <;> simp [normB, hG.zero]
  | false, .span s => by simp [normB]
  | true, .span s => by simp [normB, hG.span, swap_den]
  | b, .or x y => by
    rw [normB, hG.gd_mkOr, hG.gd_sortedBranches]
    have : (⋃ z ∈ orBranches (normB b x) ++ orBranches (normB b y), G z) =
        (⋃ z ∈ orBranches (normB b x), G z) ∪ ⋃ z ∈ orBranches (normB b y), G z := by
      ext G; simp only [List.mem_append, Set.mem_iUnion, Set.mem_union, exists_prop]
      constructor
      · rintro ⟨z, hz | hz, hX⟩
        · exact .inl ⟨z, hz, hX⟩
        · exact .inr ⟨z, hz, hX⟩
      · rintro (⟨z, hz, hX⟩ | ⟨z, hz, hX⟩)
        · exact ⟨z, .inl hz, hX⟩
        · exact ⟨z, .inr hz, hX⟩
    rw [this, hG.gd_orBranches, hG.gd_orBranches, GLaws.gd_normB b x, GLaws.gd_normB b y, hG.or]
    cases b
    · rfl
    · simp only [ite_true, Set.image_union]
  | b, .and x y => by
    rw [normB, hG.gd_mkAnd_sorted_append, GLaws.gd_normB b x, GLaws.gd_normB b y, hG.and]
    cases b
    · rfl
    · simp only [ite_true, inv_image_meet]
  | false, .seq x y => by
    rw [normB, hG.gd_mkSeq_append, GLaws.gd_normB false x, GLaws.gd_normB false y, hG.seq]; rfl
  | true, .seq x y => by
    rw [normB, hG.gd_mkSeq_append, GLaws.gd_normB true x, GLaws.gd_normB true y, hG.seq]
    simp only [ite_true, inv_image_comp]
  | false, .conv x => by
    rw [normB, show (!false) = true from rfl, GLaws.gd_normB true x, hG.conv]
    simp only [ite_true, Bool.false_eq_true, ite_false]
  | true, .conv x => by
    rw [normB, show (!true) = false from rfl, GLaws.gd_normB false x, hG.conv]
    simp only [Bool.false_eq_true, ite_false, ite_true, inv_image_inv_image]
  | false, .call n => by simp [normB]
  | true, .call n => by simp [normB, hG.conv]

theorem GLaws.gd_norm (e : Rel) : G e.norm = G e := by
  simpa [RelOf.norm] using hG.gd_normB false e

theorem GLaws.gd_normConv (e : Rel) : G e.normConv = GRel.inv '' G e := by
  simpa [RelOf.normConv] using hG.gd_normB true e

end

/-! ### The same for `GD` -/

theorem gd_mkSeq {L : List Rel} (h : L ≠ []) : GD P (mkSeq L) = seqAll (L.map (GD P)) :=
  (gd_laws P).gd_mkSeq h

theorem gd_mkAnd {L : List Rel} (h : L ≠ []) : GD P (mkAnd L) = andAll (L.map (GD P)) :=
  (gd_laws P).gd_mkAnd h

theorem gd_mkOr (L : List Rel) : GD P (mkOr L) = ⋃ e ∈ L, GD P e := (gd_laws P).gd_mkOr L

theorem gd_seqParts (e : Rel) : seqAll ((seqParts e).map (GD P)) = GD P e := (gd_laws P).gd_seqParts e

theorem gd_andParts (e : Rel) : andAll ((andParts e).map (GD P)) = GD P e := (gd_laws P).gd_andParts e

theorem gd_orBranches (e : Rel) : (⋃ x ∈ orBranches e, GD P x) = GD P e :=
  (gd_laws P).gd_orBranches e

theorem gd_mkSeq_append (a b : Rel) :
    GD P (mkSeq (seqParts a ++ seqParts b)) = Set.image2 GRel.comp (GD P a) (GD P b) :=
  (gd_laws P).gd_mkSeq_append a b

theorem gd_mkAnd_sorted_append (a b : Rel) :
    GD P (mkAnd (sortedParts (andParts a ++ andParts b))) =
      Set.image2 GRel.meet (GD P a) (GD P b) :=
  (gd_laws P).gd_mkAnd_sorted_append a b

theorem gd_unionParts (e : Rel) : (⋃ x ∈ e.unionParts, GD P x) = GD P e :=
  (gd_laws P).gd_unionParts e

theorem gd_normB (b : Bool) (e : Rel) :
    GD P (normB b e) = if b then GRel.inv '' GD P e else GD P e := (gd_laws P).gd_normB b e

theorem gd_norm (e : Rel) : GD P e.norm = GD P e := (gd_laws P).gd_norm e

theorem gd_normConv (e : Rel) : GD P e.normConv = GRel.inv '' GD P e := (gd_laws P).gd_normConv e

variable {P}

/-- The normal form of an expression has the derivable spans of the
expression, up to the ground relation a span denotes. -/
theorem derives_norm_iff {e : Rel} {G : GRel} :
    (∃ s, Derives P e.norm s ∧ s.den = G) ↔ ∃ s, Derives P e s ∧ s.den = G := by
  rw [derives_iff_derivesG, derives_iff_derivesG, gd_norm]

/-- The meaning of an expression is the union of the ground relations it
derives. -/
theorem sem_eq_sUnion_gd (e : Rel) : P.sem e = ⋃₀ GD P e := by
  rw [sem_eq_derivable]
  ext x
  simp only [mem_derivable, Set.mem_sUnion]
  constructor
  · rintro ⟨s, hs, hx⟩; exact ⟨_, hs.derivesG, hx⟩
  · rintro ⟨G, hG, hx⟩
    obtain ⟨s, hs, rfl⟩ := DerivesG.derives hG ⟨x, hx⟩
    exact ⟨s, hs, hx⟩

/-- **The normal form of an expression denotes what the expression
denotes.** -/
theorem sem_norm (e : Rel) : P.sem e.norm = P.sem e := by
  rw [sem_eq_sUnion_gd, sem_eq_sUnion_gd, gd_norm]

/-- The normal form of the converse denotes the converse. -/
theorem sem_normConv (e : Rel) : P.sem e.normConv = (P.sem e).inv := by
  rw [sem_eq_sUnion_gd, sem_eq_sUnion_gd, gd_normConv]
  ext ⟨a, b, X⟩
  simp only [Set.mem_sUnion, Set.mem_image, GRel.inv, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨_, ⟨G, hG, rfl⟩, hx⟩; exact ⟨G, hG, hx⟩
  · rintro ⟨G, hG, hx⟩; exact ⟨_, ⟨G, hG, rfl⟩, hx⟩

/-! ## What the normal form forgets -/

/-! ### Lists that are already flat and sorted -/

def NotOr (e : Rel) : Prop := ∀ a b, e ≠ .or a b

theorem notOr_of_mem_orBranches : ∀ {e x : Rel}, x ∈ orBranches e → NotOr x
  | .or a b, x, h => by
    rw [orBranches, List.mem_append] at h
    exact h.elim notOr_of_mem_orBranches notOr_of_mem_orBranches
  | .zero, x, h | .span _, x, h | .and _ _, x, h | .seq _ _, x, h | .conv _, x, h | .call _, x, h => by
    simp only [orBranches, List.mem_singleton] at h; subst h; intro a b h; cases h

theorem orBranches_notOr {e : Rel} (h : NotOr e) : orBranches e = [e] := by
  cases e with
  | or a b => exact absurd rfl (h a b)
  | _ => rfl

theorem mem_orBranches_mkOr : ∀ {L : List Rel}, (∀ x ∈ L, NotOr x) →
    ∀ z, z ≠ .zero → (z ∈ orBranches (mkOr L) ↔ z ∈ L)
  | [], _, z, hz => by simp [mkOr, orBranches, hz]
  | [e], hL, z, _ => by
    rw [mkOr, orBranches_notOr (hL e (by simp))]
  | e :: e' :: es, hL, z, hz => by
    rw [show mkOr (e :: e' :: es) = .or e (mkOr (e' :: es)) from rfl, orBranches,
      orBranches_notOr (hL e (by simp)), List.mem_append,
      mem_orBranches_mkOr (fun x hx => hL x (List.mem_cons_of_mem _ hx)) z hz]
    simp


/-- Not a `;`. -/
def NotSeq (e : Rel) : Prop := ∀ a b, e ≠ .seq a b

/-- Not a `&`. -/
def NotAnd (e : Rel) : Prop := ∀ a b, e ≠ .and a b

theorem notSeq_of_mem_seqParts : ∀ {e x : Rel}, x ∈ seqParts e → NotSeq x
  | .seq a b, x, h => by
    rw [seqParts, List.mem_append] at h
    exact h.elim notSeq_of_mem_seqParts notSeq_of_mem_seqParts
  | .zero, x, h | .span _, x, h | .and _ _, x, h | .or _ _, x, h | .conv _, x, h | .call _, x, h => by
    simp only [seqParts, List.mem_singleton] at h; subst h; intro a b h; cases h

theorem notAnd_of_mem_andParts : ∀ {e x : Rel}, x ∈ andParts e → NotAnd x
  | .and a b, x, h => by
    rw [andParts, List.mem_append] at h
    exact h.elim notAnd_of_mem_andParts notAnd_of_mem_andParts
  | .zero, x, h | .span _, x, h | .seq _ _, x, h | .or _ _, x, h | .conv _, x, h | .call _, x, h => by
    simp only [andParts, List.mem_singleton] at h; subst h; intro a b h; cases h

theorem seqParts_notSeq {e : Rel} (h : NotSeq e) : seqParts e = [e] := by
  cases e with
  | seq a b => exact absurd rfl (h a b)
  | _ => rfl

theorem andParts_notAnd {e : Rel} (h : NotAnd e) : andParts e = [e] := by
  cases e with
  | and a b => exact absurd rfl (h a b)
  | _ => rfl

/-- The members of a rebuilt chain are the members it was built from. -/
theorem seqParts_mkSeq : ∀ {L : List Rel}, L ≠ [] → (∀ x ∈ L, NotSeq x) → seqParts (mkSeq L) = L
  | [], h, _ => absurd rfl h
  | [e], _, hL => seqParts_notSeq (hL e (by simp))
  | e :: e' :: es, _, hL => by
    rw [show mkSeq (e :: e' :: es) = .seq e (mkSeq (e' :: es)) from rfl, seqParts,
      seqParts_notSeq (hL e (by simp)),
      seqParts_mkSeq (L := e' :: es) (by simp) fun x hx => hL x (List.mem_cons_of_mem _ hx)]
    rfl

/-- The members of a rebuilt meet are the members it was built from. -/
theorem andParts_mkAnd : ∀ {L : List Rel}, L ≠ [] → (∀ x ∈ L, NotAnd x) → andParts (mkAnd L) = L
  | [], h, _ => absurd rfl h
  | [e], _, hL => andParts_notAnd (hL e (by simp))
  | e :: e' :: es, _, hL => by
    rw [show mkAnd (e :: e' :: es) = .and e (mkAnd (e' :: es)) from rfl, andParts,
      andParts_notAnd (hL e (by simp)),
      andParts_mkAnd (L := e' :: es) (by simp) fun x hx => hL x (List.mem_cons_of_mem _ hx)]
    rfl

theorem pairwise_sortedParts (xs : List Rel) :
    (sortedParts xs).Pairwise fun a b => (relCmp a b != .gt) = true := by
  unfold sortedParts
  refine List.pairwise_mergeSort ?_ ?_ _
  · intro a b c h₁ h₂
    rw [relLE_iff] at h₁ h₂ ⊢
    exact relCmp_trans h₁ h₂
  · intro a b
    rw [relLE_iff, relLE_iff, relCmp_swap b a]
    cases relCmp a b <;> rfl

/-- A sorted list is determined by its members, counted with repeats. -/
theorem sortedParts_eq {xs ys : List Rel} (h : xs.Perm ys) : sortedParts xs = sortedParts ys := by
  refine List.Perm.eq_of_pairwise (le := fun a b => (relCmp a b != .gt) = true)
    (fun a b _ _ h₁ h₂ => ?_) (pairwise_sortedParts xs) (pairwise_sortedParts ys)
    ((sortedParts_perm xs).trans (h.trans (sortedParts_perm ys).symm))
  rw [relLE_iff] at h₁ h₂
  rw [relCmp_swap] at h₁
  cases hc : relCmp b a with
  | eq => exact (relCmp_eq hc).symm
  | lt => rw [hc] at h₁; cases h₁
  | gt => rw [hc] at h₂; cases h₂

theorem sortedParts_ne_nil {L : List Rel} (h : L ≠ []) : sortedParts L ≠ [] := fun h' =>
  h (List.length_eq_zero_iff.1 (by rw [← (sortedParts_perm L).length_eq, h']; rfl))

theorem seqParts_normB_seq (b : Bool) (x y : Rel) :
    seqParts (normB b (.seq x y)) =
      if b then seqParts (normB true y) ++ seqParts (normB true x)
      else seqParts (normB false x) ++ seqParts (normB false y) := by
  cases b
  · exact seqParts_mkSeq (by simp [seqParts_ne_nil]) fun z hz =>
      (List.mem_append.1 hz).elim notSeq_of_mem_seqParts notSeq_of_mem_seqParts
  · exact seqParts_mkSeq (by simp [seqParts_ne_nil]) fun z hz =>
      (List.mem_append.1 hz).elim notSeq_of_mem_seqParts notSeq_of_mem_seqParts

theorem andParts_normB_and (b : Bool) (x y : Rel) :
    andParts (normB b (.and x y)) =
      sortedParts (andParts (normB b x) ++ andParts (normB b y)) := by
  rw [normB]
  refine andParts_mkAnd (sortedParts_ne_nil (by simp [andParts_ne_nil])) fun z hz => ?_
  have hz' := (sortedParts_perm _).mem_iff.1 hz
  exact (List.mem_append.1 hz').elim notAnd_of_mem_andParts notAnd_of_mem_andParts

theorem mem_orBranches_normB_or (b : Bool) {x y z : Rel} (hz : z ≠ .zero) :
    z ∈ orBranches (normB b (.or x y)) ↔
      z ∈ orBranches (normB b x) ∨ z ∈ orBranches (normB b y) := by
  rw [normB, mem_orBranches_mkOr (fun w hw => ?_) z hz, mem_sortedBranches, List.mem_append]
  · simp [hz]
  · rw [mem_sortedBranches, List.mem_append] at hw
    exact hw.1.elim notOr_of_mem_orBranches notOr_of_mem_orBranches

/-- The normal form forgets the grouping of `;`. -/
theorem normB_seq_assoc (b : Bool) (x y z : Rel) :
    normB b (.seq (.seq x y) z) = normB b (.seq x (.seq y z)) := by
  have h₁ := seqParts_normB_seq b x y
  have h₂ := seqParts_normB_seq b y z
  cases b
  · conv => lhs; rw [normB]
    conv => rhs; rw [normB]
    rw [h₁, h₂]; simp
  · conv => lhs; rw [normB]
    conv => rhs; rw [normB]
    rw [h₁, h₂]; simp

/-- The normal form forgets the order of `&`. -/
theorem normB_and_comm (b : Bool) (x y : Rel) : normB b (.and x y) = normB b (.and y x) := by
  rw [normB, normB, sortedParts_eq List.perm_append_comm]

/-- The normal form forgets the grouping of `&`. -/
theorem normB_and_assoc (b : Bool) (x y z : Rel) :
    normB b (.and (.and x y) z) = normB b (.and x (.and y z)) := by
  conv => lhs; rw [normB]
  conv => rhs; rw [normB]
  rw [andParts_normB_and, andParts_normB_and]
  congr 1
  refine sortedParts_eq ?_
  refine ((sortedParts_perm _).append_right _).trans ?_
  rw [List.append_assoc]
  exact ((sortedParts_perm _).append_left _).symm

/-- The normal form forgets the order of `|`. -/
theorem normB_or_comm (b : Bool) (x y : Rel) : normB b (.or x y) = normB b (.or y x) := by
  rw [normB, normB]
  congr 1
  exact sortedBranches_eq fun z _ => by simp only [List.mem_append]; exact or_comm

/-- The normal form forgets the grouping of `|`. -/
theorem normB_or_assoc (b : Bool) (x y z : Rel) :
    normB b (.or (.or x y) z) = normB b (.or x (.or y z)) := by
  conv => lhs; rw [normB]
  conv => rhs; rw [normB]
  congr 1
  refine sortedBranches_eq fun w hw => ?_
  simp only [List.mem_append, mem_orBranches_normB_or b hw]
  exact or_assoc

/-- The normal form forgets a repeated branch of `|`. -/
theorem normB_or_self (b : Bool) (x y : Rel) :
    normB b (.or (.or x y) y) = normB b (.or x y) := by
  conv => lhs; rw [normB]
  conv => rhs; rw [normB]
  congr 1
  refine sortedBranches_eq fun w hw => ?_
  simp only [List.mem_append, mem_orBranches_normB_or b hw]
  tauto

theorem norm_conv_conv (e : Rel) : (RelOf.conv (.conv e)).norm = e.norm := by
  simp [RelOf.norm, normB]

theorem norm_conv_seq (a b : Rel) :
    (RelOf.conv (.seq a b)).norm = (RelOf.seq (.conv b) (.conv a)).norm := by
  simp [RelOf.norm, normB]

theorem norm_conv_and (a b : Rel) :
    (RelOf.conv (.and a b)).norm = (RelOf.and (.conv a) (.conv b)).norm := by
  simp [RelOf.norm, normB]

theorem norm_conv_or (a b : Rel) :
    (RelOf.conv (.or a b)).norm = (RelOf.or (.conv a) (.conv b)).norm := by
  simp [RelOf.norm, normB]

end RwLog
