/-
# The first round of a chain with enough dear sides reads one of them

The groups of a chain goal are made split by split, and the edge of each
side of a split is read to the depth of the state. A reading that fails
doubles the depth, which is one at first. A dear side costs `B` to read when
the reading returns something or is to the depth `T` or more. So of `N`
dear sides, read in turn while none has been read, the last is read to a
depth of `2 ^ (N - 1)`, and that is `T` or more. Making the groups of such a
chain goal costs `B` (`expand_dear`), which is what `Dear` asks of a marked
goal (`Dear.of_chain`).
-/
import RwLog.Rungs.Symmetric.Paid

namespace RwLog

namespace Symmetric

open Traverse Cost

variable {R : Type} [Answer R] [DecidableEq R] {D : Domain R} {P : Program}
variable {rd : EdgeReader} {Exp : Rel → Bool → Prop} {B T N : Nat}

/-- No dear edge has been read, `c` readings of dear edges have failed, and
`c` is less than `N`. -/
def Deep (Exp : Rel → Bool → Prop) (N c : Nat) (st : StateOf R Rel (Ans D P)) : Prop :=
  CheapE Exp st ∧ 2 ^ c ≤ st.depth ∧ c < N

omit [DecidableEq R] in
theorem Deep.same {c : Nat} {st st' : StateOf R Rel (Ans D P)} (h : Deep Exp N c st)
    (he : SameE st st') : Deep Exp N c st' :=
  ⟨h.1.same he, by rw [he.2]; exact h.2.1, h.2.2⟩

section kernel

variable {K : Kernel R Cost} {hK : K.Refines D}

/-- What is asked of the reading: a dear edge read to the depth `T` or
more, or with something returned, costs `B`. -/
abbrev DearRead (rd : EdgeReader) (K : Kernel R Cost) (hK : K.Refines D) (P : Program)
    (Exp : Rel → Bool → Prop) (B T : Nat) : Prop :=
  ∀ (last : Bool) (depth : Nat) (n : Rel), Exp n last →
    (T ≤ depth ∨
      ∃ e, (@rd R Rel (Ans D P) Cost (DerivationKernel.over D K hK P) last depth n).val = some e) →
    B ≤ (@rd R Rel (Ans D P) Cost (DerivationKernel.over D K hK P) last depth n).ticks

/-- An edge is read: `B` is paid, or no dear edge has been read and the depth
is no less. -/
theorem deep_edgeOf (hD : DearRead @rd K hK P Exp B T) {c : Nat} {st : StateOf R Rel (Ans D P)}
    (h : Deep Exp N c st) (last : Bool) (n : Rel) :
    PaidOr B (edgeOf @rd (K := DerivationKernel.over D K hK P) st last n)
      (fun r => Deep Exp N c r.1) := by
  have hread := hD last st.depth n
  clear hD
  at_cost K hK
  unfold edgeOf
  refine PaidOr.bind (Q := fun _ => True) (.of_val trivial) fun _ => ?_
  split
  · exact .of_val h
  · refine PaidOr.bind (Q := fun r => ∀ e, r = some e → ¬ Exp n last) ?_ fun hr => ?_
    · by_cases hE : Exp n last
      · cases hv : (@rd R Rel (Ans D P) Cost (DerivationKernel.over D _ hK P) last st.depth n).val with
        | none => exact .inr fun e he => by rw [hv] at he; cases he
        | some e => exact .inl (hread hE (.inr ⟨e, hv⟩))
      · exact .of_val fun _ _ => hE
    · refine .of_val ?_
      simp only [Cost.pure_val]
      split
      · next e he =>
        refine ⟨⟨fun x hx => ?_, h.1.2⟩, h.2⟩
        rcases List.mem_append.1 hx with hx | hx
        · exact h.1.1 x hx
        · obtain rfl := List.mem_singleton.1 hx
          exact hr e he
      · exact ⟨⟨h.1.1, Nat.le_trans h.1.2 (Nat.le_mul_of_pos_left _ (by decide))⟩,
          Nat.le_trans h.2.1 (Nat.le_mul_of_pos_left _ (by decide)), h.2.2⟩

/-- A dear edge is read while none has been: `B` is paid, or the reading has
failed and the depth has doubled. -/
theorem deep_edgeOf_dear (hD : DearRead @rd K hK P Exp B T) (hTN : T ≤ 2 ^ (N - 1)) {c : Nat}
    {st : StateOf R Rel (Ans D P)} (h : Deep Exp N c st) {last : Bool} {n : Rel}
    (hE : Exp n last) :
    PaidOr B (edgeOf @rd (K := DerivationKernel.over D K hK P) st last n)
      (fun r => Deep Exp N (c + 1) r.1) := by
  have hread := hD last st.depth n hE
  have hlook := lookupEdge_mem (K := K) (hK := hK) (P := P) n last st.edges
  clear hD
  at_cost K hK
  unfold edgeOf
  refine PaidOr.bind (Q := fun r => ∀ e, r = some e → (n, last, e) ∈ st.edges)
    (.of_val hlook) fun hq => ?_
  split
  · next e he => exact absurd hE (h.1.1 _ (hq e he))
  · refine PaidOr.bind (Q := fun r => r = none ∧ ¬ T ≤ st.depth) ?_ fun hr => ?_
    · by_cases hd : T ≤ st.depth
      · exact .inl (hread (.inl hd))
      · cases hv : (@rd R Rel (Ans D P) Cost (DerivationKernel.over D _ hK P) last st.depth n).val with
        | none => exact .inr ⟨hv, hd⟩
        | some e => exact .inl (hread (.inr ⟨e, hv⟩))
    · refine .of_val ?_
      simp only [Cost.pure_val]
      rw [hr.1]
      have hc : c + 1 < N := by
        have h3 : 2 ^ c < 2 ^ (N - 1) :=
          Nat.lt_of_le_of_lt h.2.1 (Nat.lt_of_lt_of_le (Nat.lt_of_not_le hr.2) hTN)
        have := (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).1 h3
        omega
      refine ⟨⟨h.1.1, Nat.le_trans h.1.2 (Nat.le_mul_of_pos_left _ (by decide))⟩, ?_, hc⟩
      show 2 ^ (c + 1) ≤ 2 * st.depth
      rw [Nat.pow_succ, Nat.mul_comm]
      exact Nat.mul_le_mul_left 2 h.2.1

theorem deep_checkOf (hD : DearRead @rd K hK P Exp B T) {c : Nat} {st : StateOf R Rel (Ans D P)}
    (h : Deep Exp N c st) (left : Bool) (side other : Rel) :
    PaidOr B (checkOf @rd (K := DerivationKernel.over D K hK P) st left side other)
      (fun r => Deep Exp N c r.1) := by
  have hE := deep_edgeOf (rd := @rd) (N := N) hD h left side
  clear hD
  at_cost K hK
  unfold checkOf
  exact PaidOr.bind hE fun h' => .of_val h'

theorem deep_checkOf_dear (hD : DearRead @rd K hK P Exp B T) (hTN : T ≤ 2 ^ (N - 1)) {c : Nat}
    {st : StateOf R Rel (Ans D P)} (h : Deep Exp N c st) {left : Bool} {side : Rel}
    (hx : Exp side left) (other : Rel) :
    PaidOr B (checkOf @rd (K := DerivationKernel.over D K hK P) st left side other)
      (fun r => Deep Exp N (c + 1) r.1) := by
  have hE := deep_edgeOf_dear (rd := @rd) hD hTN h hx
  clear hD
  at_cost K hK
  unfold checkOf
  exact PaidOr.bind hE fun h' => .of_val h'

/-- **The groups of a chain with `N` dear sides cost `B`.** The splits at
the positions `Dr` have a dear side each: the left one read at its last end,
or the right one read at its first. -/
theorem chainGroups_dear (hD : DearRead @rd K hK P Exp B T) (hTN : T ≤ 2 ^ (N - 1)) (hN : 0 < N)
    {st : StateOf R Rel (Ans D P)}
    (h : CheapE Exp st) (g : GoalOf R Rel) (k : Nat) (Dr : Nat → Bool)
    (h3 : N ≤ ((List.range k).drop 1).countP Dr)
    (hDr : ∀ i, Dr i = true → ∃ l r, g.node.interval 0 i = some l ∧
      g.node.interval i k = some r ∧ (Exp l true ∨ Exp r false)) :
    B ≤ (chainGroups @rd (K := DerivationKernel.over D K hK P) g k st).ticks := by
  have hck := fun c (st : StateOf R Rel (Ans D P)) h left side other =>
    deep_checkOf (rd := @rd) (N := N) hD (c := c) (st := st) h left side other
  have hckd := fun c (st : StateOf R Rel (Ans D P)) h left side (hx : Exp side left) other =>
    deep_checkOf_dear (rd := @rd) hD hTN (c := c) (st := st) h hx other
  have hsg := fun k L Rg st => sameE_splitGroup (K := K) (hK := hK) (P := P) k L Rg st
  clear hD
  at_cost K hK
  suffices hp : PaidOr B (chainGroups @rd (K := DerivationKernel.over D _ hK P) g k st)
      (fun _ => False) by
    rcases hp with hp | hp
    · exact hp
    · exact hp.elim
  unfold chainGroups
  refine (paidOr_foldL_done (fun (done : List Nat)
    (acc : StateOf R Rel (Ans D P) × List (Group Rel (Ans D P)) × List (Strat Rel (Ans D P))) =>
      Deep Exp N (done.countP Dr) acc.1) _ _ (fun done b i _ hb => ?_) (st, [], [])
    ⟨h, h.2, hN⟩).mono fun hfin => by
      have := hfin.2.2
      omega
  rw [List.countP_append, List.countP_singleton]
  refine PaidOr.bind' (Q := fun v => v = g.node.interval 0 i) (.of_val rfl) ?_
  rintro _ rfl
  refine PaidOr.bind' (Q := fun v => v = g.node.interval i k) (.of_val rfl) ?_
  rintro _ rfl
  cases hdr : Dr i with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
    split
    · refine PaidOr.bind (Q := fun r => Deep Exp N (done.countP Dr) r.1)
        (.of_val (hb.same (hsg _ _ _ _))) fun h1 => ?_
      refine PaidOr.bind (hck _ _ h1 _ _ _) fun h2 => ?_
      exact PaidOr.bind (hck _ _ h2 _ _ _) fun h3 => .of_val h3
    · exact .of_val hb
  | true =>
    simp only [↓reduceIte]
    obtain ⟨l, r, hl, hr, hE⟩ := hDr i hdr
    rw [hl, hr]
    dsimp only
    refine PaidOr.bind (Q := fun r => Deep Exp N (done.countP Dr) r.1)
      (.of_val (hb.same (hsg _ _ _ _))) fun h1 => ?_
    rcases hE with hE | hE
    · refine PaidOr.bind (hckd _ _ h1 _ _ hE _) fun h2 => ?_
      exact PaidOr.bind (hck _ _ h2 _ _ _) fun h3 => .of_val h3
    · refine PaidOr.bind (hck _ _ h1 _ _ _) fun h2 => ?_
      exact PaidOr.bind (hckd _ _ h2 _ _ hE _) fun h3 => .of_val h3

/-- Making the groups of a chain goal with `N` dear sides costs `B`. -/
theorem expand_dear (hD : DearRead @rd K hK P Exp B T) (hTN : T ≤ 2 ^ (N - 1)) (hN : 0 < N)
    {st : StateOf R Rel (Ans D P)}
    (h : CheapE Exp st) (g : GoalOf R Rel) {xs : List Rel} (hv : g.node.view = .chain xs)
    (Dr : Nat → Bool) (h3 : N ≤ ((List.range xs.length).drop 1).countP Dr)
    (hDr : ∀ i, Dr i = true → ∃ l r, g.node.interval 0 i = some l ∧
      g.node.interval i xs.length = some r ∧ (Exp l true ∨ Exp r false)) :
    B ≤ (expand @rd (K := DerivationKernel.over D K hK P) g st).ticks := by
  have hcg := chainGroups_dear (rd := @rd) hD hTN hN h g xs.length Dr h3 hDr
  clear hD
  at_cost K hK
  unfold expand
  simp only [Cost.bind_ticks, over_view, Charged.viewNode, Charged.op_val, hv, NodeView.forget]
  omega

/-- A reading whose dear edges cost `B`, and marked goals that are chains
with `N` dear sides, are what `Dear` asks. -/
theorem Dear.of_chain {Mark : Rel → Prop} (hD : DearRead @rd K hK P Exp B T)
    (hTN : T ≤ 2 ^ (N - 1)) (hN : 0 < N)
    (hM : ∀ n, Mark n → ∃ (xs : List Rel) (Dr : Nat → Bool), n.view = .chain xs ∧
      N ≤ ((List.range xs.length).drop 1).countP Dr ∧
      ∀ i, Dr i = true → ∃ l r, n.interval 0 i = some l ∧
        n.interval i xs.length = some r ∧ (Exp l true ∨ Exp r false)) :
    Dear @rd K hK P Exp Mark B where
  read last depth n hE he := hD last depth n hE (.inr he)
  expand g st hm hst := by
    obtain ⟨xs, Dr, hv, h3, hDr⟩ := hM g.node hm
    exact expand_dear (rd := @rd) hD hTN hN hst g hv Dr h3 hDr

end kernel

end Symmetric

end RwLog
