/-
# An edge is read in the end

`readEdge` gives up when the program is deeper than the depth it is given,
and the depth doubles each time. Here: there is a depth, `readNeed`, from
which it never gives up (`readEdge_some`).

`runs` follows an edge inwards through each call once. A call it has not
passed is one of the call nodes of the names the program defines
(`callNodes`), or its body is `0`; so the calls still to pass grow fewer
(`rem`), and under a call the node read is no larger than the largest body
(`bodyBound`).
-/
import RwLog.Rungs.Symmetric.Edge

namespace RwLog

namespace Symmetric

open Traverse Answer

variable {R : Type} [Answer R] [DecidableEq R] {D : Domain R} {P : Program}

/-- The call nodes of the names the program defines. -/
def callNodes (P : Program) : List Rel :=
  P.defs.flatMap fun d => [.call d.1, .conv (.call d.1)]

/-- No body of a name the program defines is larger, in either direction. -/
def bodyBound (P : Program) : Nat :=
  (P.defs.map fun d => d.2.norm.size + d.2.normConv.size).sum

/-- The call nodes of defined names that are not among `seen`. -/
def rem (P : Program) (seen : List Rel) : Nat :=
  ((callNodes P).filter fun c => decide (c ∉ seen)).length

/-- The depth that is enough under `m` calls still to pass, less the size of
the node. -/
def underCalls (P : Program) (m : Nat) : Nat := m * (bodyBound P + 2) + 1

/-- The depth from which the edges of a node are read. -/
def readNeed (P : Program) (n : Rel) : Nat := n.size + 1 + underCalls P (rem P [])

omit [Answer R] [DecidableEq R] in
/-- The body of a call node: the node is one of a defined name and the body
is within the bound, or the body is `0`. -/
theorem bodyOf_cases {n bd : Rel} (h : Charged.bodyOf P n = some bd) :
    (n ∈ callNodes P ∧ bd.size ≤ bodyBound P) ∨ bd = .zero := by
  have key : ∀ m : Name, (∃ b, (m, b) ∈ P.defs ∧ P.body m = b) ∨ P.body m = .zero := by
    intro m
    unfold ProgramOf.body
    cases hl : P.defs.lookup m with
    | none => exact .inr rfl
    | some b => exact .inl ⟨b, mem_of_lookup _ _ _ hl, rfl⟩
  have hle : ∀ (m : Name) (b : Rel), (m, b) ∈ P.defs →
      b.norm.size + b.normConv.size ≤ bodyBound P := fun m b hb =>
    le_sum_of_mem (List.mem_map.2 ⟨(m, b), hb, rfl⟩)
  unfold Charged.bodyOf at h
  split at h
  · next m =>
    cases h
    rcases key m with ⟨b, hb, e⟩ | e
    · refine .inl ⟨List.mem_flatMap.2 ⟨(m, b), hb, by simp⟩, ?_⟩
      rw [e]
      have := hle m b hb
      omega
    · rw [e]
      exact .inr rfl
  · next m =>
    cases h
    rcases key m with ⟨b, hb, e⟩ | e
    · refine .inl ⟨List.mem_flatMap.2 ⟨(m, b), hb, by simp⟩, ?_⟩
      rw [e]
      have := hle m b hb
      omega
    · rw [e]
      exact .inr rfl
  · cases h

omit [Answer R] [DecidableEq R] in
/-- Passing a call node of a defined name leaves fewer to pass. -/
theorem rem_cons_lt {n : Rel} {seen : List Rel} (hn : n ∈ callNodes P) (hs : n ∉ seen) :
    rem P (n :: seen) < rem P seen := by
  unfold rem
  have e : (callNodes P).filter (fun c => decide (c ∉ n :: seen)) =
      ((callNodes P).filter fun c => decide (c ∉ seen)).filter fun c => decide (c ∉ n :: seen) := by
    rw [List.filter_filter]
    congr 1
    funext c
    by_cases h : c ∈ n :: seen
    · simp [h]
    · have : c ∉ seen := fun h' => h (List.mem_cons_of_mem _ h')
      simp [h, this]
  rw [e]
  exact List.length_filter_lt_length_iff_exists.2
    ⟨n, List.mem_filter.2 ⟨hn, by simpa using hs⟩, by simp⟩

omit [Answer R] [DecidableEq R] in
theorem underCalls_step {m m' : Nat} (h : m' < m) :
    underCalls P m' + bodyBound P + 2 ≤ underCalls P m := by
  unfold underCalls
  have := Nat.mul_le_mul_right (bodyBound P + 2) (Nat.succ_le_of_lt h)
  rw [Nat.succ_mul] at this
  omega

omit [Answer R] [DecidableEq R] in
theorem RelOf.size_pos' (n : Rel) : 0 < n.size := by
  cases n <;> simp only [RelOf.size] <;> omega

section kernel

variable {K : Kernel R Cost} {hK : K.Refines D}

/-- Whether a node contains a call is known at any depth past its size. -/
theorem hasCall_some : ∀ (d : Nat) (n : Rel), n.size < d →
    (hasCall (K := DerivationKernel.over D K hK P) d n).val ≠ none := by
  at_cost K hK
  intro d
  induction d with
  | zero => intro n h; omega
  | succ d ih =>
    intro n hd
    have step : ∀ xs : List Rel, (∀ x ∈ xs, x ∈ n.view.members) →
        (foldL (fun (acc : Option Bool) x =>
          match acc with
          | some false => hasCall (K := DerivationKernel.over D _ hK P) d x
          | r => pure r) (some false) xs).val ≠ none := by
      intro xs hxs
      refine foldL_inv (fun acc : Option Bool => acc ≠ none) _ _ (fun b x hx hb => ?_) _
        (by simp)
      split
      · exact ih x (by have := size_view_member_lt (hxs x hx); omega)
      · exact hb
    simp only [hasCall, Cost.bind_val]
    split
    · simp
    · simp
    · next xs hv => exact step xs fun x hx => by rw [forget_chain hv]; exact hx
    · next xs hv => exact step xs fun x hx => by rw [forget_meet hv]; exact hx
    · next xs hv => exact step xs fun x hx => by rw [forget_union hv]; exact hx

/-- **The runs at an edge are read** at any depth past the size of the node
and what the calls still to pass can need. -/
theorem runs_some (last : Bool) : ∀ (d : Nat) (seen : List Rel) (n : Rel),
    n.size + 1 + underCalls P (rem P seen) ≤ d →
    (runs (K := DerivationKernel.over D K hK P) last d seen n).val ≠ none := by
  at_cost K hK
  intro d
  induction d with
  | zero => intro seen n h; omega
  | succ d ih =>
    intro seen n hd
    have hmem : ∀ x, x ∈ n.view.members →
        (runs (K := DerivationKernel.over D _ hK P) last d seen x).val ≠ none := fun x hx =>
      ih seen x (by have := size_view_member_lt hx; omega)
    simp only [runs, Cost.bind_val]
    split
    · simp
    · simp
    · next xs hv =>
      have hvu := forget_union hv
      refine foldL_inv (fun acc : Option (List (Run R)) => acc ≠ none) _ _
        (fun b x hx hb => ?_) _ (by simp)
      split
      · exact absurd rfl hb
      · simp only [Cost.bind_val]
        have := hmem x (by rw [hvu]; exact hx)
        split
        · next hr => exact absurd hr this
        · simp
    · next f fl hv =>
      simp only [Cost.bind_val, anyL_std]
      split
      · simp
      · next hseen =>
        simp only [Cost.bind_val, over_body]
        split
        · simp
        · next bd hb =>
          have hb' : Charged.bodyOf P n = some bd := hb
          have hpos := RelOf.size_pos' n
          rcases bodyOf_cases hb' with ⟨hn, hbd⟩ | rfl
          · have hns : n ∉ seen := by
              intro hin
              apply hseen
              simp only [Cost.anyL_val, List.any_eq_true]
              exact ⟨n, hin, by simp [over_eqNode, Charged.eqNode, Charged.op]⟩
            have := underCalls_step (P := P) (rem_cons_lt hn hns)
            exact ih (n :: seen) bd (by omega)
          · cases d with
            | zero => unfold underCalls at hd; omega
            | succ d =>
              simp [runs, Cost.bind_val, over_view, Charged.viewNode, Charged.op, RelOf.view,
                NodeView.forget, foldL_std, Cost.foldL_val]
    · next xs hv =>
      have hvc := forget_chain hv
      split
      · simp
      · next e rest heq =>
        have hsub : ∀ y ∈ e :: rest, y ∈ n.view.members := by
          intro y hy
          rw [← heq] at hy
          rw [hvc]
          cases last <;> simpa [NodeView.members] using hy
        simp only [Cost.bind_val]
        refine foldL_inv (fun acc : Option (List (Run R)) => acc ≠ none) _ _
          (fun b x hx hb => ?_) _ (hmem e (hsub e List.mem_cons_self))
        split
        · exact absurd rfl hb
        · split
          · simp only [Cost.bind_val]
            have := hmem x (hsub x (List.mem_cons_of_mem _ hx))
            split
            · next hr => exact absurd hr this
            · simp
          · exact hb

/-- **An edge is read in the end**: from the depth `readNeed` on, a reading
never gives up. -/
theorem readEdge_some (last : Bool) (d : Nat) (n : Rel) (hd : readNeed P n ≤ d) :
    (readEdge (K := DerivationKernel.over D K hK P) last d n).val ≠ none := by
  have h1 := hasCall_some (K := K) (hK := hK) (P := P) d n (by unfold readNeed at hd; omega)
  have h2 := runs_some (K := K) (hK := hK) (P := P) last d [] n hd
  at_cost K hK
  simp only [readEdge, Cost.bind_val]
  split
  · next hc => exact absurd hc h1
  · simp
  · simp only [Cost.bind_val]
    split
    · next hr => exact absurd hr h2
    · simp

end kernel

end Symmetric

end RwLog
