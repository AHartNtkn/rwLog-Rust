/-
# Rung R001: facts about the engine every proof group uses

Table keys, orientation, the shape of a round and the composite a span goal
computes. The proof groups (Tier 0, termination, symmetry) import this
rather than each proving their own copy.
-/
import RwLog.Rungs.R001.Proofs.Kernel
import RwLog.Lib.List

namespace RwLog

namespace R001

/-! ## Table keys form an equivalence -/

theorem boundEq_refl : ∀ a : Option Span, boundEq a a = true
  | none => rfl
  | some a => by simp [boundEq, covers?_refl]

theorem boundEq_symm : ∀ {a b : Option Span}, boundEq a b = true → boundEq b a = true
  | none, none, _ => rfl
  | some a, some b, h => by
    simp only [boundEq, Bool.and_eq_true] at h ⊢; exact ⟨h.2, h.1⟩
  | none, some _, h => by simp [boundEq] at h
  | some _, none, h => by simp [boundEq] at h

theorem boundEq_trans : ∀ {a b c : Option Span}, boundEq a b = true → boundEq b c = true →
    boundEq a c = true
  | none, none, none, _, _ => rfl
  | some a, some b, some c, h₁, h₂ => by
    simp only [boundEq, Bool.and_eq_true] at h₁ h₂ ⊢
    exact ⟨covers?_trans h₁.1 h₂.1, covers?_trans h₂.2 h₁.2⟩
  | none, some _, _, h, _ => by simp [boundEq] at h
  | some _, none, _, h, _ => by simp [boundEq] at h
  | none, none, some _, _, h => by simp [boundEq] at h
  | some _, some _, none, _, h => by simp [boundEq] at h

theorem boundEq_swap : ∀ (a b : Option Span),
    boundEq (a.map Span.swap) (b.map Span.swap) = boundEq a b
  | none, none => rfl
  | some a, some b => by simp [boundEq, covers?_swap]
  | none, some _ => rfl
  | some _, none => rfl

/-- `boundEq` as an equivalence between the boundaries' spans. -/
theorem boundEq_equiv : ∀ {a b : Option Span}, boundEq a b = true → Option.Rel Span.Equiv a b
  | none, none, _ => .none
  | some a, some b, h => by
    simp only [boundEq, Bool.and_eq_true, covers?_iff] at h
    exact .some ⟨h.1, h.2⟩
  | none, some _, h | some _, none, h => by cases h

theorem GoalOf.same_refl (g : Goal) : g.same g = true := by
  simp [GoalOf.same, boundEq_refl]

theorem GoalOf.same_symm {g h : Goal} (hs : g.same h = true) : h.same g = true := by
  simp only [GoalOf.same, Bool.and_eq_true, decide_eq_true_eq] at hs ⊢
  exact ⟨⟨hs.1.1.symm, boundEq_symm hs.1.2⟩, boundEq_symm hs.2⟩

theorem GoalOf.same_trans {g h k : Goal} (h₁ : g.same h = true) (h₂ : h.same k = true) :
    g.same k = true := by
  simp only [GoalOf.same, Bool.and_eq_true, decide_eq_true_eq] at h₁ h₂ ⊢
  exact ⟨⟨h₁.1.1.trans h₂.1.1, boundEq_trans h₁.1.2 h₂.1.2⟩, boundEq_trans h₁.2 h₂.2⟩

theorem GoalOf.same_iff {g h : Goal} :
    g.same h = true ↔ g.e = h.e ∧ boundEq g.lb h.lb = true ∧ boundEq g.rb h.rb = true := by
  simp only [GoalOf.same, Bool.and_eq_true, decide_eq_true_eq, and_assoc]

/-! ## Orientation and rounds -/

theorem orient_not (f : Bool) (xs : List Span) :
    orient (!f) xs = (orient f xs).map Span.swap := by
  cases f <;> simp [orient, Function.comp_def]

theorem round_P (st : State) : (round st).1.P = st.P := rfl
theorem round_depth (st : State) : (round st).1.depth = st.depth + 1 := rfl
theorem round_rootFlip (st : State) : (round st).1.rootFlip = st.rootFlip := rfl

/-- The default table `getD` uses. -/
def dflt : Table := ⟨⟨none, .zero, none⟩, [], false⟩

/-! ## Canonical `|` nests -/

theorem mem_sortedBranches {xs : List Rel} {z : Rel} :
    z ∈ sortedBranches xs ↔ z ∈ xs ∧ z ≠ .zero := by
  simp [sortedBranches, List.mem_eraseDups, List.mem_mergeSort, List.mem_filter]

/-! ## The composite of a span goal -/

/-- The meaning of a boundary: no boundary is the identity. -/
def bden : Option Span → GRel
  | none => GRel.id
  | some s => s.den

/-- The span a goal `⟨lb, s, rb⟩` composes to before simplification, if any. -/
def spanBoth (lb : Option Span) (s : Span) (rb : Option Span) : Option Span :=
  (match lb with
    | none => some s
    | some l => l.compose s).bind fun s' => match rb with
    | none => some s'
    | some r => s'.compose r

theorem spanAnswer_eq (T : Theory) (lb : Option Span) (s : Span) (rb : Option Span) :
    spanAnswer T lb s rb = liveO T (spanBoth lb s rb) := by
  cases lb <;> cases rb <;> rfl

end R001

end RwLog
