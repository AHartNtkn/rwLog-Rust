/-
# The hedge is never much slower than its second machine

Whatever `A` does, `Hedge.machine A B` has taken `n` steps of `B` after
spending at most `Hedge.boundB`, a polynomial in what `B` spends on those
steps and on testing which of its answers are plain (`boundB_le`). By then it
has halted, or it has emitted an answer covering each plain answer of `B`
(`follows_second`).

It mirrors `First.lean`. While `B`'s next step costs `w` (`costB`) and `B`
carries the handicap `p`, `A` can only win a race it finishes within
`2 (p + w)`, and each win raises `A`'s handicap by one.
-/
import RwLog.Rungs.Hedge.First

namespace RwLog

open Cost

namespace Hedge

variable (A B : CostedRuntime)

/-- What `B`'s side of a race costs without its handicap: its step, and
testing which of its answers are plain. -/
def costB (b : B.State) : Nat :=
  (B.step b).ticks + match (B.step b).val with
    | .done => 0
    | .emit bs _ => (filterL plain bs).ticks

/-- What `B`'s sides cost over its first `n` steps. -/
def spentB : B.State → Nat → Nat
  | _, 0 => 0
  | b, n + 1 =>
    costB B b + match (B.step b).val with
      | .emit _ b' => spentB b' n
      | .done => 0

variable {A B}

theorem sideB_ticks (st : State A.State B.State) :
    (sideB A B st).ticks = padB A B st + costB B st.b := by
  unfold sideB costB
  simp only [bind_ticks, tick_ticks]
  cases (B.step st.b).val with
  | done => simp
  | emit bs b' => simp

variable (B) in
/-- What the hedge may spend to take `n` steps of `B` from the state `b`,
when `B` carries the handicap `p`, `A` can win at most `c` more races before
`B`'s next step, and the answers emitted so far have sizes adding up to
`S`. -/
def boundB : Nat → B.State → Nat → Nat → Nat → Nat
  | 0, _, _, _, _ => 0
  | n + 1, b, p, c, S =>
    c * (7 * (p + costB B b) + 4 * (p + costB B b) * (S + 2 * c * (p + costB B b))) +
      7 * (p + costB B b) + 2 * (p + costB B b) * (S + 2 * c * (p + costB B b)) +
      6 * (p + costB B b) * (p + costB B b) +
      match (B.step b).val with
      | .emit _ b' => boundB n b' (p + 1) (2 * (p + 1 + costB B b') + 1)
          (S + 2 * c * (p + costB B b) + (p + costB B b))
      | .done => 0

theorem boundB_succ_c (n : Nat) (b : B.State) (p c S : Nat) :
    7 * (p + costB B b) + 4 * (p + costB B b) * S +
        boundB B (n + 1) b p c (S + 2 * (p + costB B b)) ≤
      boundB B (n + 1) b p (c + 1) S := by
  have e : S + 2 * (p + costB B b) + 2 * c * (p + costB B b) =
      S + 2 * (c + 1) * (p + costB B b) := by ring
  have h : 4 * (p + costB B b) * S ≤
      4 * (p + costB B b) * (S + 2 * (c + 1) * (p + costB B b)) :=
    Nat.mul_le_mul_left _ (Nat.le_add_right _ _)
  simp only [boundB, e]
  linarith

/-- The claim, for one state: `n` steps of `B` are taken within the bound,
unless the hedge halts first. -/
def FollowsB (n c : Nat) (st : State A.State B.State) (p S : Nat) : Prop :=
  Inv A B st → st.live = true → padB A B st ≤ p →
  2 * (padB A B st + costB B st.b) + 1 ≤ c + padA A B st →
  sizes st.seen ≤ S →
  ∃ m, (machine A B).spent st m ≤ boundB B n st.b p c S ∧
    ((machine A B).runtime.Halts st m ∨
      ∀ x ∈ B.runtime.emitted st.b n, (plain x).val = true →
        ∃ y ∈ st.seen ++ (machine A B).runtime.emitted st m, y.Covers x)

variable (hB : ∀ (s : B.State) (bs : List Span) (s' : B.State),
  (B.step s).val = .emit bs s' → sizes bs ≤ (B.step s).ticks)

include hB in
theorem resB_sizes_cost {st : State A.State B.State} {ps : List Span} {b' : B.State}
    (h : resB st = some (ps, b')) : sizes ps ≤ costB B st.b := by
  unfold resB at h
  unfold costB
  cases hs : (B.step st.b).val with
  | done => rw [hs] at h; cases h
  | emit bs b'' =>
    rw [hs] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    have h1 := hB st.b bs b'' hs
    have h2 : sizes ps ≤ sizes bs := by
      rw [← h.1]; exact sizes_sublist List.filter_sublist
    omega

include hB in
/-- A step of the hedge that is a step of `B`. -/
theorem followsB_take {n : Nat} (ihn : ∀ c (st : State A.State B.State) p S, FollowsB n c st p S)
    {c : Nat} {st : State A.State B.State} {p S : Nat} (hinv : Inv A B st)
    (hlive : st.live = true)
    (hp : padB A B st ≤ p) (hS : sizes st.seen ≤ S)
    (hv : (step A B st).val = (afterB A B st (resB st)).val)
    (ht : (step A B st).ticks ≤ 7 * (sideB A B st).ticks + (afterB A B st (resB st)).ticks) :
    ∃ m, (machine A B).spent st m ≤ boundB B (n + 1) st.b p c S ∧
      ((machine A B).runtime.Halts st m ∨
        ∀ x ∈ B.runtime.emitted st.b (n + 1), (plain x).val = true →
          ∃ y ∈ st.seen ++ (machine A B).runtime.emitted st m, y.Covers x) := by
  have hsb := sideB_ticks st
  have hβ : (sideB A B st).ticks ≤ p + costB B st.b := by omega
  cases hres : resB st with
  | none =>
    rw [hres] at hv ht
    have he : ((machine A B).step st).val = .emit [] { st with live := false } := hv
    have hdb : (B.step st.b).val = .done := by
      unfold resB at hres
      cases hs : (B.step st.b).val with
      | done => rfl
      | emit bs b' => rw [hs] at hres; cases hres
    have hdb' : B.runtime.step st.b = .done := hdb
    refine ⟨1, ?_, .inr fun x hx _ => ?_⟩
    · rw [(machine A B).spent_succ_emit he]
      have ht' : ((machine A B).step st).ticks ≤ 7 * (sideB A B st).ticks + 0 := ht
      have h0 : (machine A B).spent { st with live := false } 0 = 0 := rfl
      simp only [boundB, hdb]
      omega
    · unfold Runtime.emitted at hx
      rw [B.runtime.run_succ_done hdb'] at hx
      cases hx
  | some r =>
    obtain ⟨ps, b'⟩ := r
    rw [hres] at hv ht
    obtain ⟨hbv, hbt⟩ := afterB_some st ps b'
    rw [hbv] at hv
    rw [hbt] at ht
    have he : ((machine A B).step st).val = .emit (outB st ps) (stB st ps b') := hv
    have he' : (machine A B).runtime.step st = .emit (outB st ps) (stB st ps b') := he
    have hsz := resB_sizes_cost hB hres
    have hpl := resB_plain hres
    have hπ : sizes ps ≤ p + costB B st.b := le_trans hsz (Nat.le_add_left _ _)
    have hf := afterB_ticks_le st hpl hπ hS
    obtain ⟨bs, hbs, hps⟩ : ∃ bs, (B.step st.b).val = .emit bs b' ∧
        ps = bs.filter fun x => (plain x).val := by
      unfold resB at hres
      cases hs : (B.step st.b).val with
      | done => rw [hs] at hres; cases hres
      | emit bs b'' =>
        rw [hs] at hres
        simp only [Option.some.injEq, Prod.mk.injEq] at hres
        exact ⟨bs, by rw [hres.2], hres.1.symm⟩
    have heb : B.runtime.step st.b = .emit bs b' := hbs
    have hS' : sizes (stB st ps b').seen ≤
        S + 2 * c * (p + costB B st.b) + (p + costB B st.b) := by
      have := sizes_stB st ps b'
      omega
    obtain ⟨m, hm, hres'⟩ := ihn (2 * (p + 1 + costB B b') + 1) (stB st ps b') (p + 1)
      (S + 2 * c * (p + costB B st.b) + (p + costB B st.b)) (inv_stB hinv hpl b') hlive
      (by
        have e2 : padB A B (stB st ps b') = padB A B st + 1 := by
          simp only [padB, stB]
          cases st.last <;> simp
        omega)
      (by
        have e1 : padA A B (stB st ps b') = 0 := by simp [padA, stB]
        have e2 : padB A B (stB st ps b') = padB A B st + 1 := by
          simp only [padB, stB]
          cases st.last <;> simp
        have e3 : (stB st ps b').b = b' := rfl
        rw [e1, e2, e3]
        omega) hS'
    refine ⟨m + 1, ?_, ?_⟩
    · rw [(machine A B).spent_succ_emit he]
      have ht' : ((machine A B).step st).ticks ≤
          7 * (sideB A B st).ticks + (Tabled.fresh st.seen ps).ticks := ht
      have hm' : (machine A B).spent (stB st ps b') m ≤
          boundB B n b' (p + 1) (2 * (p + 1 + costB B b') + 1)
            (S + 2 * c * (p + costB B st.b) + (p + costB B st.b)) := hm
      have hmul : 2 * (p + costB B st.b) * S ≤
          2 * (p + costB B st.b) * (S + 2 * c * (p + costB B st.b)) :=
        Nat.mul_le_mul_left _ (Nat.le_add_right _ _)
      simp only [boundB, hbs]
      omega
    · rcases hres' with hh | hcov
      · left
        unfold Runtime.Halts at hh ⊢
        rw [(machine A B).runtime.run_succ_emit he']
        exact hh
      · right
        intro x hx hxp
        unfold Runtime.emitted at hx ⊢
        rw [B.runtime.run_succ_emit heb] at hx
        rw [(machine A B).runtime.run_succ_emit he']
        rcases List.mem_append.1 hx with hx | hx
        · have hxps : x ∈ ps := by rw [hps]; exact List.mem_filter.2 ⟨hx, hxp⟩
          obtain ⟨y, hy, hyx⟩ := fresh_cover (old := st.seen) hxps
          refine ⟨y, ?_, hyx⟩
          rcases List.mem_append.1 hy with hy | hy
          · exact List.mem_append_left _ hy
          · exact List.mem_append_right _ (List.mem_append_left _ hy)
        · obtain ⟨y, hy, hyx⟩ := hcov x hx hxp
          refine ⟨y, ?_, hyx⟩
          have e : (stB st ps b').seen = st.seen ++ outB st ps := rfl
          rw [e] at hy
          simpa [Runtime.emitted, List.append_assoc] using hy

variable (hA : ∀ (s : A.State) (as : List Span) (s' : A.State),
  (A.step s).val = .emit as s' → sizes as ≤ (A.step s).ticks)

include hA in
/-- A step of the hedge that is a step of `A`, which `A` won. -/
theorem followsB_lose {n c : Nat}
    (ihc : ∀ (st : State A.State B.State) p S, FollowsB (n + 1) c st p S)
    {st : State A.State B.State} {p S : Nat} (hinv : Inv A B st) (hlive : st.live = true)
    (hp : padB A B st ≤ p)
    (hc : 2 * (padB A B st + costB B st.b) + 1 ≤ c + 1 + padA A B st)
    (hS : sizes st.seen ≤ S)
    (hv : (step A B st).val = (afterA A B st (A.step st.a).val).val)
    (ht : (step A B st).ticks ≤ 7 * (sideB A B st).ticks +
      (afterA A B st (A.step st.a).val).ticks)
    (hle : padA A B st + (A.step st.a).ticks ≤ 2 * (sideB A B st).ticks) :
    ∃ m, (machine A B).spent st m ≤ boundB B (n + 1) st.b p (c + 1) S ∧
      ((machine A B).runtime.Halts st m ∨
        ∀ x ∈ B.runtime.emitted st.b (n + 1), (plain x).val = true →
          ∃ y ∈ st.seen ++ (machine A B).runtime.emitted st m, y.Covers x) := by
  have hb := boundB_succ_c n st.b p c S
  have hsb := sideB_ticks st
  have hβ : (sideB A B st).ticks ≤ p + costB B st.b := by omega
  cases hr : (A.step st.a).val with
  | done =>
    rw [hr] at hv ht
    have hd : ((machine A B).step st).val = .done := hv
    have hd' : (machine A B).runtime.step st = .done := hd
    refine ⟨1, ?_, .inl ?_⟩
    · rw [(machine A B).spent_succ_done hd]
      have ht' : ((machine A B).step st).ticks ≤ 7 * (sideB A B st).ticks + 0 := ht
      have h0 : 0 ≤ boundB B (n + 1) st.b p c (S + 2 * (p + costB B st.b)) := Nat.zero_le _
      have h1 : 0 ≤ 4 * (p + costB B st.b) * S := Nat.zero_le _
      omega
    · unfold Runtime.Halts
      rw [(machine A B).runtime.run_succ_done hd']
  | emit as a' =>
    rw [hr] at hv ht
    obtain ⟨hav, hat⟩ := afterA_emit st as a'
    rw [hav] at hv
    rw [hat] at ht
    have he : ((machine A B).step st).val = .emit (outA st as) (stA st as a') := hv
    have he' : (machine A B).runtime.step st = .emit (outA st as) (stA st as a') := he
    have hsz : sizes as ≤ 2 * (p + costB B st.b) := by
      have := hA st.a as a' hr
      omega
    have hf := afterA_ticks_le hinv hsz hS
    have hS' : sizes (stA st as a').seen ≤ S + 2 * (p + costB B st.b) := by
      have := sizes_stA st as a'
      omega
    obtain ⟨m, hm, hres'⟩ := ihc (stA st as a') p (S + 2 * (p + costB B st.b))
      (inv_stA hinv as a') hlive
      (by
        have e1 : padB A B (stA st as a') = 0 := by simp [padB, stA]
        omega)
      (by
        have e1 : padB A B (stA st as a') = 0 := by simp [padB, stA]
        have e2 : padA A B (stA st as a') = padA A B st + 1 := by
          simp only [padA, stA]
          cases st.last <;> simp
        have e3 : (stA st as a').b = st.b := rfl
        rw [e1, e2, e3]
        omega) hS'
    refine ⟨m + 1, ?_, ?_⟩
    · rw [(machine A B).spent_succ_emit he]
      have ht' : ((machine A B).step st).ticks ≤
          7 * (sideB A B st).ticks + (dropCovered st.seenB as).ticks := ht
      have hm' : (machine A B).spent (stA st as a') m ≤
          boundB B (n + 1) st.b p c (S + 2 * (p + costB B st.b)) := hm
      have e : 2 * (2 * (p + costB B st.b)) * S = 4 * (p + costB B st.b) * S := by ring
      omega
    · rcases hres' with hh | hcov
      · left
        unfold Runtime.Halts at hh ⊢
        rw [(machine A B).runtime.run_succ_emit he']
        exact hh
      · right
        intro x hx hxp
        obtain ⟨y, hy, hyx⟩ := hcov x hx hxp
        refine ⟨y, ?_, hyx⟩
        unfold Runtime.emitted
        rw [(machine A B).runtime.run_succ_emit he']
        have e : (stA st as a').seen = st.seen ++ outA st as := rfl
        rw [e] at hy
        simpa [Runtime.emitted, List.append_assoc] using hy

include hA hB in
/-- Each number of steps of `B`, with any number of races `A` may still win. -/
theorem followsB : ∀ (n c : Nat) (st : State A.State B.State) (p S : Nat), FollowsB n c st p S := by
  intro n
  induction n with
  | zero =>
    intro c st p S _ _ _ _ _
    exact ⟨0, Nat.le_refl _, .inr fun x hx => nomatch hx⟩
  | succ n ihn =>
    intro c
    induction c with
    | zero =>
      intro st p S hinv hlive hp hc hS
      rcases step_live hlive with ⟨hv, -, ht, hle⟩ | ⟨hv, ht, hlt⟩
      · have := sideB_ticks st
        omega
      · exact followsB_take hB ihn hinv hlive hp hS hv ht
    | succ c ihc =>
      intro st p S hinv hlive hp hc hS
      rcases step_live hlive with ⟨hv, -, ht, hle⟩ | ⟨hv, ht, hlt⟩
      · exact followsB_lose hA ihc hinv hlive hp hc hS hv ht hle
      · exact followsB_take hB ihn hinv hlive hp hS hv ht

end Hedge

end RwLog
