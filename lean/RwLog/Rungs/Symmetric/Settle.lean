/-
# A group that works for ever runs out of work

Of a group that works in infinitely many requests (`Line`), once the tables
a strategy of it reads gain no more answers (`Still`):

* a span has run (`Line.span_ran`);
* a call or a union has read every answer of every table it reads
  (`Line.copy_read`);
* a join has combined every pair, and has nothing left to combine
  (`Line.join_done`);
* a push sees every answer of its side once the side gains no more
  (`Line.push_seen`), then opens the goal of each that is not superseded
  (`Line.push_opened`), and then files every answer of each of those goals
  and takes every unit (`Line.push_done`);
* a check has read its side, and is the same from then on
  (`Line.check_read`).

Each falls in a well-founded measure whenever the group works while the
strategy has work, and never rises.

And while the group works, with no table still: the table a push opened for
an answer that is never superseded needs no round again and again
(`Line.push_fed`), by the measure of its feed cursor.

Nothing here is about a kernel.
-/
import RwLog.Rungs.Symmetric.Lines
import RwLog.Rungs.Symmetric.PushCursor

namespace RwLog

namespace Symmetric

variable {S N A : Type} {need : N → Nat} {Rc : RaceSem S N A} {σ : Nat → StateOf S N A}

/-- From the state `T` on the table at `j` gains no answer. -/
def Still (σ : Nat → StateOf S N A) (T j : Nat) : Prop :=
  ∀ r, T ≤ r → (σ r).len j = (σ T).len j

theorem Still.mono {T T' j : Nat} (h : Still σ T j) (hT : T ≤ T') : Still σ T' j :=
  fun r hr => (h r (hT.trans hr)).trans (h T' hT).symm

variable {k r0 : Nat} {L : Nat → List (Strat N A)}

/-- What holds of the strategy at one place of the group in the state `r1`
and is kept by a strategy moving on holds of it from then on. -/
theorem Line.along_from (hL : Line need σ k r0 L) (Q : Nat → Strat N A → Prop) {m r1 : Nat}
    {s1 : Strat N A} (hr1 : r0 ≤ r1) (h1 : (L r1)[m]? = some s1) (hQ : Q r1 s1)
    (hstep : ∀ r s s', r1 ≤ r → (L r)[m]? = some s → (L (r + 1))[m]? = some s' → Q r s →
      SAdv s s' → Q (r + 1) s') {r : Nat} (hr : r1 ≤ r) :
    ∃ s, (L r)[m]? = some s ∧ Q r s := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hr
  induction d with
  | zero => exact ⟨s1, h1, hQ⟩
  | succ d ih =>
    obtain ⟨s, hs, hq⟩ := ih (by omega)
    obtain ⟨s', hs', hadv⟩ := (hL.adv (r1 + d) (by omega)).get hs
    exact ⟨s', hs', hstep (r1 + d) s s' (by omega) hs hs' hq hadv⟩

/-- A span has run from some state on. -/
theorem Line.span_ran (hL : Line need σ k r0 L) {m : Nat} {ran0 : Bool}
    (h0 : (L r0)[m]? = some (.span ran0)) :
    ∃ T, r0 ≤ T ∧ ∀ r, T ≤ r → (L r)[m]? = some (.span true) := by
  obtain ⟨r, -, hr, hst⟩ := hL.step m r0
  obtain ⟨s, hs, ran, rfl⟩ := hL.along (fun _ s => ∃ ran, s = Strat.span ran) h0 ⟨ran0, rfl⟩
    (fun r s s' _ _ _ hq hadv => by
      obtain ⟨ran, rfl⟩ := hq
      cases hadv
      exact ⟨_, rfl⟩) hr
  obtain ⟨s', hs', hstep⟩ := hst _ hs
  cases hstep
  refine ⟨r + 1, by omega, fun r' hr' => ?_⟩
  obtain ⟨s2, hs2, e⟩ := hL.along_from (fun _ s => s = Strat.span true) (by omega) hs' rfl
    (fun r s s' _ _ _ hq hadv => by
      subst hq
      cases hadv with
      | span h => rw [h rfl]) hr'
  rw [← e]
  exact hs2

/-- A call or a union stays one, reading the same tables no less far. -/
theorem Line.copy_kept (hL : Line need σ k r0 L) {m : Nat} {c : Bool} {ra : Nat}
    {subsa : List (Nat × Nat)} (hra : r0 ≤ ra) (hsa : (L ra)[m]? = some (.copy c subsa))
    {r : Nat} (hr : ra ≤ r) :
    ∃ subs, (L r)[m]? = some (.copy c subs) ∧ Pointwise SubAdv subsa subs := by
  obtain ⟨_, hs, subs, rfl, hp⟩ := hL.along_from
    (fun _ s => ∃ subs, s = Strat.copy c subs ∧ Pointwise SubAdv subsa subs) hra hsa
    ⟨subsa, rfl, Pointwise.refl (fun p => ⟨rfl, Nat.le_refl _⟩) _⟩
    (fun r s s' _ _ _ hq hadv => by
      obtain ⟨subs, rfl, hp⟩ := hq
      cases hadv with
      | copy hp' => exact ⟨_, rfl, Pointwise.comp (r₁ := SubAdv) (r₂ := SubAdv) (r₃ := SubAdv)
          (fun _ _ _ h1 h2 => SubAdv.trans h1 h2) hp hp'⟩) hr
  exact ⟨subs, hs, hp⟩

/-- **A call or a union reads all there is.** Once the tables it reads gain
no more answers, it has read every answer of each from some state on. -/
theorem Line.copy_read (hL : Line need σ k r0 L) {m : Nat} {c : Bool}
    {subs0 : List (Nat × Nat)} (h0 : (L r0)[m]? = some (.copy c subs0)) {T : Nat}
    (hT : r0 ≤ T) (hstill : ∀ p ∈ subs0, Still σ T p.1) :
    ∃ T', T ≤ T' ∧ ∀ r, T' ≤ r → ∃ subs, (L r)[m]? = some (.copy c subs) ∧
      Pointwise SubAdv subs0 subs ∧ ∀ p ∈ subs, (σ r).len p.1 ≤ p.2 := by
  have keep := fun ra subsa (hra : r0 ≤ ra) (hsa : (L ra)[m]? = some (.copy c subsa)) r
    (hr : ra ≤ r) => hL.copy_kept hra hsa hr
  have each : ∀ m', m' < subs0.length → ∃ T', ∀ r, T' ≤ r → ∀ subs p,
      (L r)[m]? = some (.copy c subs) → subs[m']? = some p → (σ r).len p.1 ≤ p.2 := by
    intro m' hm'
    have hp0 : subs0[m']? = some subs0[m'] := List.getElem?_eq_getElem hm'
    generalize subs0[m'] = p0 at hp0
    have hst := hstill p0 (List.mem_of_getElem? hp0)
    by_cases hex : ∃ ra subsa pa, T ≤ ra ∧ (L ra)[m]? = some (.copy c subsa) ∧
        subsa[m']? = some pa ∧ (σ T).len p0.1 ≤ pa.2
    · obtain ⟨ra, subsa, pa, hra, hsa, hma, hna⟩ := hex
      refine ⟨ra, fun r hr subs p hs hp => ?_⟩
      obtain ⟨subs', hs', hadv⟩ := keep ra subsa (by omega) hsa r hr
      rw [hs] at hs'
      cases hs'
      obtain ⟨p', hp', hadv'⟩ := hadv.get hma
      rw [hp] at hp'
      cases hp'
      obtain ⟨subs2, hs2, hadv2⟩ := keep r0 subs0 (Nat.le_refl _) h0 ra (by omega)
      rw [hsa] at hs2
      cases hs2
      obtain ⟨p2, hp2, hadv3⟩ := hadv2.get hp0
      rw [hma] at hp2
      cases hp2
      have h1 := hst r (by omega)
      have h2 := hadv'.2
      rw [hadv'.1, hadv3.1, h1]
      omega
    · exfalso
      let f : Nat → Nat := fun r =>
        match (L r)[m]? with
        | some (.copy _ subs) => behind ((σ T).len p0.1) subs
        | _ => 0
      refine no_descent (· < ·) Nat.lt_wfRel.wf (fun _ _ _ h1 h2 => Nat.lt_trans h1 h2) f
        T (fun r hr => ?_) (fun r' => ?_)
      · obtain ⟨subs, hs, -⟩ := keep r0 subs0 (Nat.le_refl _) h0 r (by omega)
        obtain ⟨s', hs', hadv⟩ := (hL.adv r (by omega)).get hs
        cases hadv with
        | copy hp' =>
          have := behind_le ((σ T).len p0.1) hp'
          simp only [f, hs, hs']
          omega
      · obtain ⟨r, hr', hr, hstp⟩ := hL.step m (max r' T)
        obtain ⟨subs, hs, hadv⟩ := keep r0 subs0 (Nat.le_refl _) h0 r hr
        obtain ⟨p, hp, hadv'⟩ := hadv.get hp0
        obtain ⟨s', hs', hstep⟩ := hstp _ hs
        cases hstep with
        | copy hp' hlt =>
          refine ⟨r, by omega, ?_⟩
          simp only [f, hs, hs']
          refine hlt _ m' p.1 p.2 hp ?_ ?_
          · by_contra hc
            exact hex ⟨r, subs, p, by omega, hs, hp, by omega⟩
          · rw [hadv'.1, hst r (by omega)]
  obtain ⟨T', hT'⟩ := eventually_forall_lt subs0.length _ each
  refine ⟨max T' T, Nat.le_max_right _ _, fun r hr => ?_⟩
  obtain ⟨subs, hs, hp⟩ := keep r0 subs0 (Nat.le_refl _) h0 r (by omega)
  refine ⟨subs, hs, hp, fun p hp' => ?_⟩
  obtain ⟨m', hm'⟩ := List.getElem?_of_mem hp'
  have hlt : m' < subs0.length := by
    rw [hp.1]
    exact (List.getElem?_eq_some_iff.1 hm').1
  exact hT' m' hlt r (by omega) subs p hs hm'

/-- A join stays one of the same tables, with every pair it has combined
combined and no fewer answers filed. -/
theorem Line.join_kept (hL : Line need σ k r0 L) {m : Nat} {kd : Kind} {a b ra : Nat}
    {ca : Cursor} (hra : r0 ≤ ra) (hsa : (L ra)[m]? = some (.join kd a b ca)) {r : Nat}
    (hr : ra ≤ r) :
    ∃ c, (L r)[m]? = some (.join kd a b c) ∧ (∀ p q, ca.Before p q → c.Before p q) ∧
      ca.pa.length ≤ c.pa.length ∧ ca.pb.length ≤ c.pb.length := by
  obtain ⟨_, hs, c, rfl, h1, h2⟩ := hL.along_from
    (fun _ s => ∃ c, s = Strat.join kd a b c ∧ (∀ p q, ca.Before p q → c.Before p q) ∧
      ca.pa.length ≤ c.pa.length ∧ ca.pb.length ≤ c.pb.length) hra hsa
    ⟨ca, rfl, fun _ _ h => h, Nat.le_refl _, Nat.le_refl _⟩
    (fun r s s' _ _ _ hq hadv => by
      obtain ⟨c, rfl, h1, h2, h3⟩ := hq
      cases hadv with
      | join b1 _ b3 =>
        exact ⟨_, rfl, fun p q h => b1 p q (h1 p q h), h2.trans b3.1, h3.trans b3.2⟩) hr
  exact ⟨c, hs, h1, h2⟩

/-- **A join combines all there is.** Once the two tables it reads gain no
more answers, it has no pair left to combine from some state on. -/
theorem Line.join_done (hL : Line need σ k r0 L) {m : Nat} {kd : Kind} {a b : Nat}
    {c0 : Cursor} (h0 : (L r0)[m]? = some (.join kd a b c0)) {T : Nat} (hT : r0 ≤ T)
    (ha : Still σ T a) (hb : Still σ T b)
    (hok : ∀ r c, T ≤ r → (L r)[m]? = some (.join kd a b c) →
      c.Ok ((σ r).len a) ((σ r).len b)) :
    ∃ T', T ≤ T' ∧ ∀ r, T' ≤ r → ∃ c, (L r)[m]? = some (.join kd a b c) ∧
      c.pending ((σ r).len a) ((σ r).len b) = false := by
  have keep := fun ra ca (hra : r0 ≤ ra) (hsa : (L ra)[m]? = some (.join kd a b ca)) r
    (hr : ra ≤ r) => hL.join_kept hra hsa hr
  -- once the join has worked after `T`, it has filed every answer
  obtain ⟨rf, hrf', hrf, hstf⟩ := hL.step m T
  obtain ⟨cf, hsf, -⟩ := keep r0 c0 (Nat.le_refl _) h0 rf hrf
  obtain ⟨sf', hsf', hstepf⟩ := hstf _ hsf
  obtain ⟨cf', rfl, hfa, hfb⟩ : ∃ cf', sf' = .join kd a b cf' ∧
      (σ T).len a ≤ cf'.pa.length ∧ (σ T).len b ≤ cf'.pb.length := by
    cases hstepf with
    | join _ _ _ g5 _ =>
      have h1 := ha rf hrf'
      have h2 := hb rf hrf'
      exact ⟨_, rfl, by omega, by omega⟩
  have filed : ∀ r c, rf + 1 ≤ r → (L r)[m]? = some (.join kd a b c) →
      (σ T).len a ≤ c.pa.length ∧ (σ T).len b ≤ c.pb.length := fun r c hr hs => by
    obtain ⟨c2, hs2, -, hna, hnb⟩ := keep (rf + 1) cf' (by omega) hsf' r hr
    rw [hs] at hs2
    cases hs2
    exact ⟨hfa.trans hna, hfb.trans hnb⟩
  have each : ∀ p, p < (σ T).len a → ∀ q, q < (σ T).len b → ∃ T', ∀ r, T' ≤ r → ∀ c,
      (L r)[m]? = some (.join kd a b c) → c.Before p q := by
    intro p hp q hq
    by_cases hex : ∃ ra ca, T ≤ ra ∧ (L ra)[m]? = some (.join kd a b ca) ∧ ca.Before p q
    · obtain ⟨ra, ca, hra, hsa, hba⟩ := hex
      refine ⟨ra, fun r hr c hs => ?_⟩
      obtain ⟨c', hs', h1, -⟩ := keep ra ca (by omega) hsa r hr
      rw [hs] at hs'
      cases hs'
      exact h1 p q hba
    · exfalso
      have hno : ∀ r c, T ≤ r → (L r)[m]? = some (.join kd a b c) → ¬ c.Before p q :=
        fun r c hr hs hbf => hex ⟨r, c, hr, hs, hbf⟩
      let f : Nat → List Nat := fun r =>
        match (L r)[m]? with
        | some (.join _ _ _ c) => c.rank p q
        | _ => []
      refine no_descent RankLt rankLt_wf (fun _ _ _ h1 h2 => RankLt.trans h1 h2) f
        (rf + 1) (fun r hr => ?_) (fun r' => ?_)
      · obtain ⟨c, hs, -⟩ := keep r0 c0 (Nat.le_refl _) h0 r (by omega)
        obtain ⟨s', hs', hadv⟩ := (hL.adv r (by omega)).get hs
        obtain ⟨fa, fb⟩ := filed r c hr hs
        cases hadv with
        | join h1 h2 _ =>
          simp only [f, hs, hs']
          rcases h2 p q (by omega) (by omega) with hb' | he | hlt
          · exact absurd hb' (hno (r + 1) _ (by omega) hs')
          · exact .inl he
          · exact .inr hlt
      · obtain ⟨r, hr', hr, hst⟩ := hL.step m (max r' (rf + 1))
        obtain ⟨c, hs, -⟩ := keep r0 c0 (Nat.le_refl _) h0 r hr
        obtain ⟨s', hs', hstep⟩ := hst _ hs
        obtain ⟨fa, fb⟩ := filed r c (by omega) hs
        cases hstep with
        | join h1 h2 _ _ _ =>
          refine ⟨r, by omega, ?_⟩
          simp only [f, hs, hs']
          rcases h2 p q (by omega) (by omega) with hb' | hlt
          · exact absurd hb' (hno (r + 1) _ (by omega) hs')
          · exact hlt
  obtain ⟨T1, hT1⟩ := eventually_forall_lt ((σ T).len a)
    (fun p r => ∀ q, q < (σ T).len b → ∀ c, (L r)[m]? = some (.join kd a b c) → c.Before p q)
    (fun p hp => by
      obtain ⟨T', hT'⟩ := eventually_forall_lt ((σ T).len b)
        (fun q r => ∀ c, (L r)[m]? = some (.join kd a b c) → c.Before p q)
        (fun q hq => each p hp q hq)
      exact ⟨T', fun r hr q hq => hT' q hq r hr⟩)
  obtain ⟨r, hr', hr, hst⟩ := hL.step m (max T1 T)
  obtain ⟨c, hs, -⟩ := keep r0 c0 (Nat.le_refl _) h0 r hr
  obtain ⟨s', hs', hstep⟩ := hst _ hs
  cases hstep with
  | join h1 h2 h3 h5 h4 =>
    rename_i c'
    have hpa := ha r (by omega)
    have hqb := hb r (by omega)
    have hpa' := ha (r + 1) (by omega)
    have hqb' := hb (r + 1) (by omega)
    have hdone : c'.Full ((σ T).len a) ((σ T).len b) := by
      rcases h4 with h4 | ⟨p, q, hn, hy⟩
      · rw [hpa, hqb] at h4
        exact h4
      · have hlt := (hok (r + 1) c' (by omega) hs').before_lt hy
        rw [hpa', hqb'] at hlt
        exact absurd (hT1 p hlt.1 r (by omega) q hlt.2 c hs) hn
    refine ⟨r + 1, by omega, fun r2 hr2 => ?_⟩
    obtain ⟨c2, hs2, hbf, -⟩ := keep (r + 1) c' (by omega) hs' r2 hr2
    refine ⟨c2, hs2, ?_⟩
    rw [(hok r2 c2 (by omega) hs2).pending_false, ha r2 (by omega), hb r2 (by omega)]
    exact fun p q hp hq => hbf p q (hdone p q hp hq)

/-- An entry of a list is an entry of a list it starts. -/
theorem getElem?_of_prefix {α : Type} {l l' : List α} (h : l <+: l') {q : Nat} {a : α}
    (hq : l[q]? = some a) : l'[q]? = some a := by
  obtain ⟨t, rfl⟩ := h
  rw [List.getElem?_append_left (lt_of_getElem? hq)]
  exact hq

/-- What the pushes of a side at one place of a group keep in a run: the
answers seen are answers of the side, the units and the cursor fit them, and
the answers filed of a table are answers of it. -/
def PushSound (σ : Nat → StateOf S N A) (L : Nat → List (Strat N A)) (m side r0 : Nat) : Prop :=
  ∀ (r : Nat) (kd : Kind) (left : Bool) (other : N) (subs : List (A × Option (Nat × Nat)))
    (dead : Option (List Nat)) (reads : List (Nat × Option Nat)) (c fc : Cursor), r0 ≤ r →
    (L r)[m]? = some (.push kd left side other subs dead reads c fc) →
    subs.length ≤ (σ r).len side ∧ PushFits subs (dead.getD []) reads c ∧
      ∀ (n : Nat) (x : A) (t : Nat × Nat), subs[n]? = some (x, some t) → t.2 ≤ (σ r).len t.1

section Push

variable {m : Nat} {kd : Kind} {left : Bool} {side : Nat} {other : N}

/-- A push stays a push of the same side into the same node, moved on. -/
theorem Line.push_kept (hL : Line need σ k r0 L) {ra : Nat}
    {sa : List (A × Option (Nat × Nat))} {da : Option (List Nat)} {rda : List (Nat × Option Nat)}
    {ca fca : Cursor} (hra : r0 ≤ ra)
    (hsa : (L ra)[m]? = some (.push kd left side other sa da rda ca fca)) {r : Nat} (hr : ra ≤ r) :
    ∃ subs dead reads c fc, (L r)[m]? = some (.push kd left side other subs dead reads c fc) ∧
      PAdv sa da rda ca subs dead reads c := by
  obtain ⟨_, hs, subs, dead, reads, c, fc, rfl, hp⟩ := hL.along_from
    (fun _ s => ∃ subs dead reads c fc, s = Strat.push kd left side other subs dead reads c fc ∧
      PAdv sa da rda ca subs dead reads c) hra hsa ⟨sa, da, rda, ca, fca, rfl, PAdv.refl _ _ _ _⟩
    (fun r s s' _ _ _ hq hadv => by
      obtain ⟨subs, dead, reads, c, fc, rfl, hp⟩ := hq
      cases hadv with
      | push a => exact ⟨_, _, _, _, _, rfl, hp.trans a⟩) hr
  exact ⟨subs, dead, reads, c, fc, hs, hp⟩

/-- **A push takes each unit of an answer that is never superseded.** -/
theorem Line.push_unit (hL : Line need σ k r0 L) {Ta : Nat} (hTa : r0 ≤ Ta)
    {sa : List (A × Option (Nat × Nat))} {da : Option (List Nat)} {rda : List (Nat × Option Nat)}
    {ca fca : Cursor} (ha : (L Ta)[m]? = some (.push kd left side other sa da rda ca fca)) {p q : Nat}
    (hin : (p, q) ∈ ca.todo ∨ ca.Before p q)
    (hlive : ∀ r subs dead reads c fc, Ta ≤ r →
      (L r)[m]? = some (.push kd left side other subs dead reads c fc) → p ∉ dead.getD []) :
    ∃ T', ∀ r, T' ≤ r → ∀ subs dead reads c fc,
      (L r)[m]? = some (.push kd left side other subs dead reads c fc) → c.Before p q := by
  have keep := fun rb sb db rdb cb fcb (hrb : r0 ≤ rb)
    (hsb : (L rb)[m]? = some (.push kd left side other sb db rdb cb fcb)) r (hr : rb ≤ r) =>
    hL.push_kept hrb hsb hr
  have inv : ∀ r subs dead reads c fc, Ta ≤ r →
      (L r)[m]? = some (.push kd left side other subs dead reads c fc) →
      (p, q) ∈ c.todo ∨ c.Before p q := by
    intro r subs dead reads c fc hr hs
    obtain ⟨subs', dead', reads', c', fc', hs', hA⟩ := keep Ta _ _ _ _ _ hTa ha r hr
    rw [hs] at hs'
    cases hs'
    rcases hin with h | h
    · rcases hA.rank p q h with h' | h' | ⟨h', -⟩
      · exact .inr h'
      · exact absurd h' (hlive r _ _ _ _ _ hr hs)
      · exact .inl h'
    · exact .inr (hA.before p q h)
  by_cases hex : ∃ rb sb db rdb cb fcb, Ta ≤ rb ∧
      (L rb)[m]? = some (.push kd left side other sb db rdb cb fcb) ∧ cb.Before p q
  · obtain ⟨rb, sb, db, rdb, cb, fcb, hrb, hsb, hbb⟩ := hex
    refine ⟨rb, fun r hr subs dead reads c fc hs => ?_⟩
    obtain ⟨subs', dead', reads', c', fc', hs', hA⟩ := keep rb _ _ _ _ _ (by omega) hsb r hr
    rw [hs] at hs'
    cases hs'
    exact hA.before p q hbb
  · exfalso
    have hno : ∀ r subs dead reads c fc, Ta ≤ r →
        (L r)[m]? = some (.push kd left side other subs dead reads c fc) →
        (p, q) ∈ c.todo ∧ ¬ c.Before p q := fun r subs dead reads c fc hr hs =>
      have hn : ¬ c.Before p q := fun hb => hex ⟨r, subs, dead, reads, c, fc, hr, hs, hb⟩
      ⟨(inv r subs dead reads c fc hr hs).resolve_right hn, hn⟩
    let f : Nat → List Nat := fun r =>
      match (L r)[m]? with
      | some (.push _ _ _ _ _ _ _ c fc) => c.rank p q
      | _ => []
    refine no_descent RankLt rankLt_wf (fun _ _ _ h1 h2 => RankLt.trans h1 h2) f
      Ta (fun r hr => ?_) (fun r' => ?_)
    · obtain ⟨subs, dead, reads, c, fc, hs, -⟩ := keep Ta _ _ _ _ _ hTa ha r hr
      obtain ⟨s', hs', hadv⟩ := (hL.adv r (by omega)).get hs
      cases hadv with
      | push hA =>
        simp only [f, hs, hs']
        rcases hA.rank p q (hno r _ _ _ _ _ hr hs).1 with h | h | ⟨-, h | h⟩
        · exact absurd h (hno (r + 1) _ _ _ _ _ (by omega) hs').2
        · exact absurd h (hlive (r + 1) _ _ _ _ _ (by omega) hs')
        · exact .inl h
        · exact .inr h
    · obtain ⟨r, hr', hr, hst⟩ := hL.step m (max r' Ta)
      obtain ⟨subs, dead, reads, c, fc, hs, -⟩ := keep Ta _ _ _ _ _ hTa ha r (by omega)
      obtain ⟨s', hs', hstep⟩ := hst _ hs
      cases hstep with
      | push hA hP =>
        refine ⟨r, by omega, ?_⟩
        simp only [f, hs, hs']
        rcases hP.rank p q (hno r _ _ _ _ _ (by omega) hs).1 with h | h | ⟨-, h⟩
        · exact absurd h (hno (r + 1) _ _ _ _ _ (by omega) hs').2
        · exact absurd h (hlive (r + 1) _ _ _ _ _ (by omega) hs')
        · exact h

/-- **The table a push opened for an answer that is never superseded has
rounds again and again.** Were it to wait for ever, the answer would come to
have a unit of the feed cursor, the unit would never be taken, and each time
the tables the push opened shared rounds it would be nearer to its turn. -/
theorem Line.push_fed (hL : Line need σ k r0 L) {Ta : Nat} (hTa : r0 ≤ Ta)
    {sa : List (A × Option (Nat × Nat))} {da : Option (List Nat)} {rda : List (Nat × Option Nat)}
    {ca fca : Cursor} (ha : (L Ta)[m]? = some (.push kd left side other sa da rda ca fca))
    {n : Nat} {x : A} {t : Nat × Nat} (he : sa[n]? = some (x, some t))
    (hlive : ∀ r subs dead reads c fc, Ta ≤ r →
      (L r)[m]? = some (.push kd left side other subs dead reads c fc) → n ∉ dead.getD []) :
    ∀ r', ∃ r, r' ≤ r ∧ Settled (σ (r + 1)) t.1 := by
  intro r'
  by_contra hno
  have hns : ∀ r, r' ≤ r → ¬ Settled (σ (r + 1)) t.1 := fun r hr h => hno ⟨r, hr, h⟩
  have keep := fun r (hr : Ta ≤ r) => hL.push_kept hTa ha hr
  -- what a request in which the tables shared rounds does for the units of the answer
  have step : ∀ r, Ta ≤ r → r' ≤ r → ∀ subs dead reads c fc subs' dead' reads' c' fc',
      (L r)[m]? = some (.push kd left side other subs dead reads c fc) →
      (L (r + 1))[m]? = some (.push kd left side other subs' dead' reads' c' fc') →
      FedP (σ (r + 1)) (.push kd left side other subs dead reads c fc : Strat N A)
        (.push kd left side other subs' dead' reads' c' fc') →
      (∃ q, (n, q) ∈ fc'.todo) ∧
        ∀ q, (n, q) ∈ fc.todo → (n, q) ∈ fc'.todo ∧ RankLt (fc'.rank n q) (fc.rank n q) := by
    intro r hr hr' subs dead reads c fc subs' dead' reads' c' fc' hs hs' hF
    simp only [FedP] at hF
    obtain ⟨subs0, dead0, reads0, c0, fc0, hs0, hA⟩ := keep r hr
    rw [hs] at hs0
    cases hs0
    obtain ⟨t1, he1, e1, -⟩ := hA.adv.get he
    obtain ⟨subs2, dead2, reads2, c2, fc2, hs2, hA2⟩ := keep (r + 1) (by omega)
    rw [hs'] at hs2
    cases hs2
    obtain ⟨t2, he2, e2, -⟩ := hA2.adv.get he
    have hd' := hlive (r + 1) _ _ _ _ _ (by omega) hs'
    refine ⟨?_, fun q hq => ?_⟩
    · rcases hF.2 n x t2 he2 hd' with h | h
      · rw [e2] at h
        exact absurd h (hns r hr')
      · exact h
    · rcases hF.1 n q hq with h | h | h
      · have := h x t1 he1
        rw [e1] at this
        exact absurd this (hns r hr')
      · exact absurd h hd'
      · exact h
  -- the answer comes to have a unit
  obtain ⟨r1, hr1, -, hmv⟩ := hL.moved (max r' Ta)
  obtain ⟨s1, d1, rd1, c1, f1, hs1, -⟩ := keep r1 (by omega)
  obtain ⟨s2, d2, rd2, c2, f2, hs2, -⟩ := keep (r1 + 1) (by omega)
  obtain ⟨⟨q, hq⟩, -⟩ := step r1 (by omega) (by omega) _ _ _ _ _ _ _ _ _ _ hs1 hs2
    (hmv m _ _ hs1 hs2)
  -- which is never taken
  have inv : ∀ r, r1 + 1 ≤ r → ∀ subs dead reads c fc,
      (L r)[m]? = some (.push kd left side other subs dead reads c fc) → (n, q) ∈ fc.todo := by
    intro r hr
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hr
    induction d with
    | zero =>
      intro subs dead reads c fc hs
      have hs0 : (L (r1 + 1))[m]? = some (.push kd left side other subs dead reads c fc) := hs
      rw [hs2] at hs0
      cases hs0
      exact hq
    | succ d ih =>
      intro subs dead reads c fc hs
      obtain ⟨sp, dp, rdp, cp, fp, hsp, -⟩ := keep (r1 + 1 + d) (by omega)
      have hs' : (L (r1 + 1 + d + 1))[m]? =
          some (.push kd left side other subs dead reads c fc) := hs
      rcases hL.shared (r1 + 1 + d) (by omega) with heq | hF
      · rw [heq, hsp] at hs'
        cases hs'
        exact ih (by omega) _ _ _ _ _ hsp
      · exact ((step (r1 + 1 + d) (by omega) (by omega) _ _ _ _ _ _ _ _ _ _ hsp hs'
          (hF m _ _ hsp hs')).2 q (ih (by omega) _ _ _ _ _ hsp)).1
  let f : Nat → List Nat := fun r =>
    match (L r)[m]? with
    | some (.push _ _ _ _ _ _ _ _ fc) => fc.rank n q
    | _ => []
  refine no_descent RankLt rankLt_wf (fun _ _ _ h1 h2 => RankLt.trans h1 h2) f
    (r1 + 1) (fun r hr => ?_) (fun r'' => ?_)
  · obtain ⟨sp, dp, rdp, cp, fp, hsp, -⟩ := keep r (by omega)
    obtain ⟨sn, dn, rdn, cn, fn, hsn, -⟩ := keep (r + 1) (by omega)
    rcases hL.shared r (by omega) with heq | hF
    · left
      simp only [f, heq]
    · right
      simp only [f, hsp, hsn]
      exact ((step r (by omega) (by omega) _ _ _ _ _ _ _ _ _ _ hsp hsn (hF m _ _ hsp hsn)).2 q
        (inv r hr _ _ _ _ _ hsp)).2
  · obtain ⟨r, hr, -, hmv'⟩ := hL.moved (max r'' (r1 + 1))
    obtain ⟨sp, dp, rdp, cp, fp, hsp, -⟩ := keep r (by omega)
    obtain ⟨sn, dn, rdn, cn, fn, hsn, -⟩ := keep (r + 1) (by omega)
    refine ⟨r, by omega, ?_⟩
    simp only [f, hsp, hsn]
    exact ((step r (by omega) (by omega) _ _ _ _ _ _ _ _ _ _ hsp hsn (hmv' m _ _ hsp hsn)).2 q
      (inv r (by omega) _ _ _ _ _ hsp)).2

/-- **A push sees every answer of its side** and has made its cover tests,
once the side is complete. -/
theorem Line.push_seen (hL : Line need σ k r0 L) (hS : PushSound σ L m side r0)
    {subs0 : List (A × Option (Nat × Nat))} {dead0 : Option (List Nat)}
    {reads0 : List (Nat × Option Nat)} {c0 fc0 : Cursor}
    (h0 : (L r0)[m]? = some (.push kd left side other subs0 dead0 reads0 c0 fc0)) {T : Nat}
    (hside : Still σ T side) (hdone : ∀ r, T ≤ r → (σ r).isDone side = true) :
    ∃ T1 subs1 dead1 reads1 c1 fc1, T ≤ T1 ∧ r0 ≤ T1 ∧
      (L T1)[m]? = some (.push kd left side other subs1 (some dead1) reads1 c1 fc1) ∧
      subs1.length = (σ T).len side := by
  obtain ⟨r, hr', hr, hst⟩ := hL.step m T
  obtain ⟨subs, dead, reads, c, fc, hs, -⟩ := hL.push_kept (Nat.le_refl _) h0 hr
  obtain ⟨s', hs', hstep⟩ := hst _ hs
  obtain ⟨subs', dead', reads', c', fc', hs2, -⟩ :=
    hL.push_kept (Nat.le_refl _) h0 (show r0 ≤ r + 1 by omega)
  rw [hs2] at hs'
  cases hs'
  cases hstep with
  | push hA hP =>
    obtain ⟨d, rfl⟩ := Option.isSome_iff_exists.1 (hP.sup (hdone r hr'))
    refine ⟨r + 1, _, d, _, _, _, by omega, by omega, hs2, ?_⟩
    have h1 := hP.seen
    have h2 := (hS (r + 1) _ _ _ _ _ _ _ _ (by omega) hs2).1
    rw [hside r hr'] at h1
    rw [hside (r + 1) (by omega)] at h2
    omega

/-- A push that has seen every answer of a side that gains no more, and has
made its cover tests, sees the same answers from then on, with the same ones
superseded. -/
theorem Line.push_fixed (hL : Line need σ k r0 L) (hS : PushSound σ L m side r0) {T T1 : Nat}
    (hside : Still σ T side) (hT : T ≤ T1) (hT1 : r0 ≤ T1)
    {subs1 : List (A × Option (Nat × Nat))} {dead1 : List Nat}
    {reads1 : List (Nat × Option Nat)} {c1 fc1 : Cursor}
    (h1 : (L T1)[m]? = some (.push kd left side other subs1 (some dead1) reads1 c1 fc1))
    (hl1 : subs1.length = (σ T).len side) {r : Nat} (hr : T1 ≤ r) :
    ∃ subs reads c fc, (L r)[m]? = some (.push kd left side other subs (some dead1) reads c fc) ∧
      PAdv subs1 (some dead1) reads1 c1 subs (some dead1) reads c ∧
      subs.length = subs1.length := by
  obtain ⟨subs, dead, reads, c, fc, hs, hA⟩ := hL.push_kept hT1 h1 hr
  obtain rfl := hA.fixed dead1 rfl
  have h2 := (hS r _ _ _ _ _ _ _ _ (by omega) hs).1
  rw [hside r (by omega)] at h2
  have h3 := hA.adv.1
  exact ⟨subs, reads, c, fc, hs, hA, by omega⟩

/-- **A push opens the goal of every answer that is not superseded**, once
it has seen every answer of a side that gains no more. -/
theorem Line.push_opened (hL : Line need σ k r0 L) (hS : PushSound σ L m side r0) {T T1 : Nat}
    (hside : Still σ T side) (hT : T ≤ T1) (hT1 : r0 ≤ T1)
    {subs1 : List (A × Option (Nat × Nat))} {dead1 : List Nat}
    {reads1 : List (Nat × Option Nat)} {c1 fc1 : Cursor}
    (h1 : (L T1)[m]? = some (.push kd left side other subs1 (some dead1) reads1 c1 fc1))
    (hl1 : subs1.length = (σ T).len side) :
    ∃ T2 subs2 reads2 c2 fc2, T1 ≤ T2 ∧
      (L T2)[m]? = some (.push kd left side other subs2 (some dead1) reads2 c2 fc2) ∧
      subs2.length = subs1.length ∧ ∀ n, n < subs2.length → n ∉ dead1 → IsOpen subs2 n := by
  have fx := fun r (hr : T1 ≤ r) => hL.push_fixed hS hside hT hT1 h1 hl1 hr
  have each : ∀ n, n < subs1.length → ∃ T', ∀ r, T' ≤ r → T1 ≤ r → ∀ subs dead reads c fc,
      (L r)[m]? = some (.push kd left side other subs dead reads c fc) → n ∉ dead1 →
      IsOpen subs n := by
    intro n hn
    by_cases hd : n ∈ dead1
    · exact ⟨0, fun _ _ _ _ _ _ _ _ _ h => absurd hd h⟩
    · obtain ⟨-, hF1, -⟩ := hS T1 _ _ _ _ _ _ _ _ hT1 h1
      obtain ⟨q, hq⟩ := hF1.2.opens n hn
      obtain ⟨T', hT'⟩ := hL.push_unit hT1 h1 (p := n) (q := q)
        (by
          by_cases hb : (n, q) ∈ c1.done
          · exact .inr hb
          · exact .inl ((hF1.2.todo (n, q)).2 ⟨⟨none, hq⟩, hb, hd⟩))
        (fun r subs dead reads c fc hr hs hdd => by
          obtain ⟨subs', reads', c', fc', hs', -, -⟩ := fx r hr
          rw [hs] at hs'
          cases hs'
          exact hd hdd)
      refine ⟨T', fun r hr hr1 subs dead reads c fc hs _ => ?_⟩
      obtain ⟨subs', reads', c', fc', hs', hA, -⟩ := fx r hr1
      rw [hs] at hs'
      cases hs'
      have hq' := getElem?_of_prefix hA.pre hq
      exact ((hS r _ _ _ _ _ _ _ _ (by omega) hs).2.1.2.isOpen q n hq').1 (hT' r hr _ _ _ _ _ hs)
  obtain ⟨T2, hT2⟩ := eventually_forall_lt subs1.length _ each
  obtain ⟨subs2, reads2, c2, fc2, hs2, hA, hl⟩ := fx (max T2 T1) (Nat.le_max_right _ _)
  exact ⟨max T2 T1, subs2, reads2, c2, fc2, Nat.le_max_right _ _, hs2, hl, fun n hn hd =>
    hT2 n (by omega) (max T2 T1) (Nat.le_max_left _ _) (Nat.le_max_right _ _) _ _ _ _ _ hs2 hd⟩

/-- **A push runs out of work.** Once it has seen every answer of a side
that gains no more and opened the goal of each that is not superseded, and
the tables of those goals gain no more answers, it has filed every answer of
each of them and has no unit left to take, from some state on. -/
theorem Line.push_done (hL : Line need σ k r0 L) (hS : PushSound σ L m side r0) {T T2 : Nat}
    (hside : Still σ T side) (hT : T ≤ T2) (hT2 : r0 ≤ T2)
    {subs2 : List (A × Option (Nat × Nat))} {dead2 : List Nat}
    {reads2 : List (Nat × Option Nat)} {c2 fc2 : Cursor}
    (h2 : (L T2)[m]? = some (.push kd left side other subs2 (some dead2) reads2 c2 fc2))
    (hl2 : subs2.length = (σ T).len side)
    (hopen : ∀ n, n < subs2.length → n ∉ dead2 → IsOpen subs2 n) {T3 : Nat}
    (hstill : ∀ (n : Nat) (x : A) (t : Nat × Nat), subs2[n]? = some (x, some t) → n ∉ dead2 →
      Still σ T3 t.1) :
    ∃ T', T2 ≤ T' ∧ ∀ r, T' ≤ r → ∃ subs reads c fc,
      (L r)[m]? = some (.push kd left side other subs (some dead2) reads c fc) ∧
      PAdv subs2 (some dead2) reads2 c2 subs (some dead2) reads c ∧
      subs.length = subs2.length ∧ c.todo = [] ∧
      ∀ (n : Nat) (x : A) (t : Nat × Nat), subs[n]? = some (x, some t) → n ∉ dead2 →
        (σ r).len t.1 ≤ t.2 := by
  have fx := fun r (hr : T2 ≤ r) => hL.push_fixed hS hside hT hT2 h2 hl2 hr
  -- the table of an answer that is not superseded gains no more answers
  have ent : ∀ r subs dead reads c fc, T2 ≤ r →
      (L r)[m]? = some (.push kd left side other subs dead reads c fc) →
      ∀ (n : Nat) (x : A) (t : Nat × Nat), subs[n]? = some (x, some t) → n ∉ dead2 →
        Still σ T3 t.1 := by
    intro r subs dead reads c fc hr hs n x t he hd
    obtain ⟨subs', reads', c', fc', hs', hA, hl⟩ := fx r hr
    rw [hs] at hs'
    cases hs'
    obtain ⟨x2, t2, he2⟩ := hopen n (by rw [← hl]; exact lt_of_getElem? he) hd
    obtain ⟨t', he', e1, -⟩ := hA.adv.get he2
    rw [he] at he'
    cases he'
    rw [e1]
    exact hstill n _ t2 he2 hd
  -- once the push has worked after the tables are still, it has filed every answer
  obtain ⟨ra, hra', hra, hst⟩ := hL.step m (max T3 T2)
  obtain ⟨sa, rda, ca, fca, hsa, hAa, hla⟩ := fx ra (by omega)
  obtain ⟨s', hs', hstep⟩ := hst _ hsa
  obtain ⟨sb, rdb, cb, fcb, hsb, hAb, hlb⟩ := fx (ra + 1) (by omega)
  rw [hsb] at hs'
  cases hs'
  cases hstep with
  | push hA hP =>
    have full : ∀ r subs dead reads c fc, ra + 1 ≤ r →
        (L r)[m]? = some (.push kd left side other subs dead reads c fc) →
        ∀ (n : Nat) (x : A) (t : Nat × Nat), subs[n]? = some (x, some t) → n ∉ dead2 →
          (σ r).len t.1 ≤ t.2 := by
      intro r subs dead reads c fc hr hs n x t he hd
      have hstl := ent r _ _ _ _ _ (by omega) hs n x t he hd
      obtain ⟨subs', reads', c', fc', hs'', -, hl⟩ := fx r (by omega)
      rw [hs] at hs''
      cases hs''
      obtain ⟨subs', dead', reads', c', fc', hs'', hAr⟩ :=
        hL.push_kept (show r0 ≤ ra + 1 by omega) hsb hr
      rw [hs] at hs''
      cases hs''
      obtain ⟨x2, t2, he2⟩ := hopen n (by rw [← hl]; exact lt_of_getElem? he) hd
      obtain ⟨ta, hea, -, -⟩ := hAa.adv.get he2
      obtain ⟨tb, heb, hfull⟩ := hP.filed n x2 ta hea hd
      obtain ⟨tb', heb', eb1, -⟩ := hA.adv.get hea
      rw [heb] at heb'
      cases heb'
      obtain ⟨tr, her, er1, ler⟩ := hAr.adv.get heb
      rw [he] at her
      cases her
      have s1 := hstl r (by omega)
      have s2 := hstl ra (by omega)
      rw [er1, eb1] at s1 s2
      rw [er1, eb1, s1, ← s2]
      omega
    obtain ⟨-, hFb, -⟩ := hS (ra + 1) _ _ _ _ _ _ _ _ (by omega) hsb
    have units : ∀ q, q < rdb.length → ∃ T', ∀ r, T' ≤ r → ∀ subs dead reads c fc,
        (L r)[m]? = some (.push kd left side other subs dead reads c fc) →
        ∀ (s : Nat) (ro : Option Nat), rdb[q]? = some (s, ro) → s ∉ dead2 → c.Before s q := by
      intro q hq
      have he : rdb[q]? = some rdb[q] := List.getElem?_eq_getElem hq
      generalize rdb[q] = e at he
      obtain ⟨s0, ro0⟩ := e
      by_cases hd : s0 ∈ dead2
      · refine ⟨0, fun r _ subs dead reads c fc _ s ro h hn => ?_⟩
        rw [he] at h
        cases h
        exact absurd hd hn
      · obtain ⟨T', hT'⟩ := hL.push_unit (show r0 ≤ ra + 1 by omega) hsb (p := s0) (q := q)
          (by
            by_cases hb : (s0, q) ∈ cb.done
            · exact .inr hb
            · exact .inl ((hFb.2.todo (s0, q)).2 ⟨⟨ro0, he⟩, hb, hd⟩))
          (fun r subs dead reads c fc hr hs hdd => by
            obtain ⟨subs', reads', c', fc', hs', -, -⟩ := fx r (by omega)
            rw [hs] at hs'
            cases hs'
            exact hd hdd)
        refine ⟨T', fun r hr subs dead reads c fc hs s ro h _ => ?_⟩
        rw [he] at h
        cases h
        exact hT' r hr _ _ _ _ _ hs
    obtain ⟨T5, hT5⟩ := eventually_forall_lt rdb.length _ units
    refine ⟨max T5 (ra + 1), by omega, fun r hr => ?_⟩
    obtain ⟨subs, reads, c, fc, hs, hA2, hl⟩ := fx r (by omega)
    obtain ⟨subs', dead', reads', c', fc', hs', hAr⟩ :=
      hL.push_kept (show r0 ≤ ra + 1 by omega) hsb (show ra + 1 ≤ r by omega)
    rw [hs] at hs'
    cases hs'
    obtain ⟨-, hFr, hcr⟩ := hS r _ _ _ _ _ _ _ _ (by omega) hs
    refine ⟨subs, reads, c, fc, hs, hA2, hl, ?_, fun n x t he hd =>
      full r _ _ _ _ _ (by omega) hs n x t he hd⟩
    refine List.eq_nil_iff_forall_not_mem.2 fun x hx => ?_
    obtain ⟨s, q⟩ := x
    obtain ⟨⟨ro, hro⟩, hnd, hdd⟩ := (hFr.2.todo (s, q)).1 hx
    have hsd : s ∉ dead2 := hdd
    have hq : ∃ q0 : Nat, rdb[q0]? = some (s, ro) := by
      cases ro with
      | none =>
        have := hFr.2.seen q s hro
        exact hFb.2.opens s (by omega)
      | some r' =>
        have h1 := hFr.2.filed q s r' hro
        have hc : cntOf subs s ≤ cntOf sb s := by
          cases hes : subs[s]? with
          | none => simp [cntOf, hes]
          | some e =>
            rcases e with ⟨x, _ | t⟩
            · simp [cntOf, hes]
            · obtain ⟨x2, t2, he2⟩ := hopen s (by rw [← hl]; exact lt_of_getElem? hes) hsd
              obtain ⟨tb, heb, -, -⟩ := hAb.adv.get he2
              obtain ⟨tr, her, er1, -⟩ := hAr.adv.get heb
              rw [hes] at her
              cases her
              have a1 := hcr s _ t hes
              have a2 := full (ra + 1) _ _ _ _ _ (Nat.le_refl _) hsb s _ tb heb hsd
              have stl := ent (ra + 1) _ _ _ _ _ (by omega) hsb s _ tb heb hsd
              rw [er1, stl r (by omega)] at a1
              rw [stl (ra + 1) (by omega)] at a2
              simp only [cntOf, hes, heb]
              omega
        exact hFb.2.all s r' (Nat.lt_of_lt_of_le h1 hc)
    obtain ⟨q0, hq0⟩ := hq
    have hq0' := getElem?_of_prefix hAr.pre hq0
    have e : q = q0 := by
      cases ro with
      | none => exact hFr.2.once q q0 s hro hq0'
      | some r' => exact hFr.2.onceR q q0 s r' hro hq0'
    subst e
    exact hnd (hT5 q (lt_of_getElem? hq0) r (by omega) _ _ _ _ _ hs s ro hq0 hsd)

end Push

/-- **A check reads its side.** The depth edges are read to doubles while it
has not, so it has from some state on, and is the same from then on. -/
theorem Line.check_read (hR : Requests need Rc σ) (hL : Line need σ k r0 L)
    (hd : 0 < (σ 0).depth) {m : Nat} {left : Bool} {side other : N} {c0 : Check}
    (h0 : (L r0)[m]? = some (.check left side other c0)) :
    ∃ T c1, r0 ≤ T ∧ c1 ≠ Check.reading ∧
      ∀ r, T ≤ r → (L r)[m]? = some (.check left side other c1) := by
  have al : ∀ r, r0 ≤ r → ∃ c, (L r)[m]? = some (.check left side other c) := fun r hr => by
    obtain ⟨_, hs, c, rfl⟩ := hL.along (fun _ s => ∃ c, s = Strat.check left side other c) h0
      ⟨c0, rfl⟩ (fun r s s' _ _ _ hq hadv => by
        obtain ⟨c, rfl⟩ := hq
        cases hadv
        exact ⟨_, rfl⟩) hr
    exact ⟨c, hs⟩
  have read : ∃ r1 c1, r0 ≤ r1 ∧ (L r1)[m]? = some (.check left side other c1) ∧
      c1 ≠ .reading := by
    by_contra hcon
    simp only [not_exists, not_and, not_not] at hcon
    have rd : ∀ r, r0 ≤ r → (L r)[m]? = some (.check left side other .reading) := fun r hr => by
      obtain ⟨c, hs⟩ := al r hr
      rw [hcon r c hr hs] at hs
      exact hs
    refine no_descent (· < ·) Nat.lt_wfRel.wf (fun _ _ _ h1 h2 => Nat.lt_trans h1 h2)
      (fun r => need side - (σ r).depth) r0 (fun r _ => ?_) (fun r' => ?_)
    · have := (hR.req r).depth
      omega
    · obtain ⟨r, hr', hr, hst⟩ := hL.step m r'
      obtain ⟨s', hs', hstep⟩ := hst _ (rd r hr)
      rw [rd (r + 1) (by omega)] at hs'
      cases hs'
      cases hstep with
      | check _ h2 =>
        refine ⟨r, hr', ?_⟩
        have h1 := hR.depth_le (Nat.zero_le r)
        rcases h2 rfl with hne | ⟨hdd, hlt⟩
        · exact absurd rfl hne
        · omega
  obtain ⟨r1, c1, hr1, hs1, hne⟩ := read
  refine ⟨r1, c1, hr1, hne, fun r hr => ?_⟩
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hr
  induction d with
  | zero => exact hs1
  | succ d ih =>
    have hs := ih (by omega)
    obtain ⟨s', hs', hadv⟩ := (hL.adv (r1 + d) (by omega)).get hs
    cases hadv with
    | check hc =>
      rcases hc with hc | hc
      · exact absurd hc hne
      · rw [hc] at hs'
        exact hs'

end Symmetric

end RwLog
