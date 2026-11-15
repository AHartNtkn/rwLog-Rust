/-
# A group that works for ever runs out of work

Of a group that works in infinitely many requests (`Line`), once the tables
a strategy of it reads gain no more answers (`Still`):

* a span has run (`Line.span_ran`);
* a call or a union has read every answer of every table it reads
  (`Line.copy_read`);
* a join has combined every pair, and has nothing left to combine
  (`Line.join_done`);
* a push whose side is complete has taken its maximal answers and opened a
  goal for each (`Line.push_empty`), and then reads every answer of every
  one of them (`Line.push_read`);
* a check has read its side, and is the same from then on
  (`Line.check_read`).

Each falls in a well-founded measure whenever the group works while the
strategy has work, and never rises.

Nothing here is about a kernel.
-/
import RwLog.Rungs.Symmetric.Lines

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
      SAdv (σ r).len s s' → Q (r + 1) s') {r : Nat} (hr : r1 ≤ r) :
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
combined and no fewer answers counted. -/
theorem Line.join_kept (hL : Line need σ k r0 L) {m : Nat} {kd : Kind} {a b ra : Nat}
    {ca : Cursor} (hra : r0 ≤ ra) (hsa : (L ra)[m]? = some (.join kd a b ca)) {r : Nat}
    (hr : ra ≤ r) :
    ∃ c, (L r)[m]? = some (.join kd a b c) ∧ (∀ p q, ca.Before p q → c.Before p q) ∧
      ca.na ≤ c.na ∧ ca.nb ≤ c.nb := by
  obtain ⟨_, hs, c, rfl, h1, h2⟩ := hL.along_from
    (fun _ s => ∃ c, s = Strat.join kd a b c ∧ (∀ p q, ca.Before p q → c.Before p q) ∧
      ca.na ≤ c.na ∧ ca.nb ≤ c.nb) hra hsa
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
      let f : Nat → Nat × Nat := fun r =>
        match (L r)[m]? with
        | some (.join _ _ _ c) => Cursor.rank (max p q + 1) c
        | _ => (0, 0)
      refine no_descent RankLt rankLt_wf (fun _ _ _ h1 h2 => RankLt.trans h1 h2) f
        T (fun r hr => ?_) (fun r' => ?_)
      · obtain ⟨c, hs, -⟩ := keep r0 c0 (Nat.le_refl _) h0 r (by omega)
        obtain ⟨s', hs', hadv⟩ := (hL.adv r (by omega)).get hs
        cases hadv with
        | join h1 h2 _ =>
          have hpa := ha r hr
          have hqb := hb r hr
          simp only [f, hs, hs']
          rcases h2 p q (max p q + 1) (by omega) (by omega) (by omega) (by omega) with
            hb' | he | hlt
          · exact absurd hb' (hno (r + 1) _ (by omega) hs')
          · exact .inl (by rw [he])
          · exact .inr hlt
      · obtain ⟨r, hr', hr, hst⟩ := hL.step m (max r' T)
        obtain ⟨c, hs, -⟩ := keep r0 c0 (Nat.le_refl _) h0 r hr
        obtain ⟨s', hs', hstep⟩ := hst _ hs
        cases hstep with
        | join h1 h2 _ _ =>
          have hpa := ha r (by omega)
          have hqb := hb r (by omega)
          refine ⟨r, by omega, ?_⟩
          simp only [f, hs, hs']
          rcases h2 p q (max p q + 1) (by omega) (by omega) (by omega) (by omega) with
            hb' | hlt
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
  | join h1 h2 h3 h4 =>
    rename_i c'
    have hpa := ha r (by omega)
    have hqb := hb r (by omega)
    have hpa' := ha (r + 1) (by omega)
    have hqb' := hb (r + 1) (by omega)
    have hdone : c'.pending ((σ T).len a) ((σ T).len b) = false := by
      rcases h4 with h4 | ⟨p, q, hn, hy⟩
      · rw [hpa, hqb] at h4
        exact h4
      · have hlt := (hok (r + 1) c' (by omega) hs').before_lt hy
        rw [hpa', hqb'] at hlt
        exact absurd (hT1 p hlt.1 r (by omega) q hlt.2 c hs) hn
    refine ⟨r + 1, by omega, fun r2 hr2 => ?_⟩
    obtain ⟨c2, hs2, -, hna, hnb⟩ := keep (r + 1) c' (by omega) hs' r2 hr2
    refine ⟨c2, hs2, ?_⟩
    rw [ha r2 (by omega), hb r2 (by omega)]
    simp only [Cursor.pending, Bool.or_eq_false_iff, decide_eq_false_iff_not] at hdone ⊢
    omega

/-- A push stays a push of the same side into the same node. -/
theorem Line.push_kept (hL : Line need σ k r0 L) {m : Nat} {kd : Kind} {left : Bool}
    {side : Nat} {other : N} {todo0 : Option (List A)} {subs0 : List (A × Nat × Nat)}
    (h0 : (L r0)[m]? = some (.push kd left side other todo0 subs0)) {r : Nat} (hr : r0 ≤ r) :
    ∃ todo subs, (L r)[m]? = some (.push kd left side other todo subs) := by
  obtain ⟨_, hs, todo, subs, rfl⟩ := hL.along
    (fun _ s => ∃ todo subs, s = Strat.push kd left side other todo subs) h0
    ⟨todo0, subs0, rfl⟩ (fun r s s' _ _ _ hq hadv => by
      obtain ⟨todo, subs, rfl⟩ := hq
      cases hadv
      exact ⟨_, _, rfl⟩) hr
  exact ⟨todo, subs, hs⟩

/-- **A push takes the answers of its side.** Once its side is complete,
it has taken the maximal answers of it and opened a goal for each. -/
theorem Line.push_empty (hL : Line need σ k r0 L) {m : Nat} {kd : Kind} {left : Bool}
    {side : Nat} {other : N} {todo0 : Option (List A)} {subs0 : List (A × Nat × Nat)}
    (h0 : (L r0)[m]? = some (.push kd left side other todo0 subs0)) {T : Nat} (hT : r0 ≤ T)
    (hd : ∀ r, T ≤ r → (σ r).isDone side = true) :
    ∃ T' subs1, T ≤ T' ∧ (L T')[m]? = some (.push kd left side other (some []) subs1) := by
  have al := fun r (hr : r0 ≤ r) => hL.push_kept h0 hr
  have someOn : ∀ ra l subs, r0 ≤ ra → (L ra)[m]? = some (.push kd left side other (some l) subs) →
      ∀ r, ra ≤ r → ∃ l' subs', (L r)[m]? = some (.push kd left side other (some l') subs') ∧
        l'.length ≤ l.length := by
    intro ra l subs hra hsa r hr
    obtain ⟨_, hs, l', subs', rfl, hl'⟩ := hL.along_from
      (fun _ s => ∃ l' subs', s = Strat.push kd left side other (some l') subs' ∧
        l'.length ≤ l.length) hra hsa ⟨l, subs, rfl, Nat.le_refl _⟩
      (fun r s s' _ _ _ hq hadv => by
        obtain ⟨l', subs', rfl, hl'⟩ := hq
        cases hadv with
        | push a1 _ _ =>
          obtain ⟨l1, e1, hl1⟩ := a1 l' rfl
          subst e1
          exact ⟨l1, _, rfl, hl1.trans hl'⟩) hr
    exact ⟨l', subs', hs, hl'⟩
  have main : ∀ n ra l subs, T ≤ ra →
      (L ra)[m]? = some (.push kd left side other (some l) subs) → l.length ≤ n →
      ∃ T' subs1, T ≤ T' ∧ (L T')[m]? = some (.push kd left side other (some []) subs1) := by
    intro n
    induction n with
    | zero =>
      intro ra l subs hra hs hl
      have : l = [] := List.length_eq_zero_iff.1 (Nat.le_zero.1 hl)
      subst this
      exact ⟨ra, subs, hra, hs⟩
    | succ n ih =>
      intro ra l subs hra hs hl
      obtain ⟨r, hr', hr, hst⟩ := hL.step m ra
      obtain ⟨l', subs', hs', hl'⟩ := someOn ra l subs (by omega) hs r hr'
      obtain ⟨s2, hs2, hstep⟩ := hst _ hs'
      cases hstep with
      | push h1 h2 h3 h4 =>
        cases l' with
        | nil => exact ⟨r, subs', by omega, hs'⟩
        | cons x rest =>
          obtain ⟨l1, e1, hl1⟩ := (h4 (hd r (by omega))).2.1 x rest rfl
          subst e1
          simp only [List.length_cons] at hl'
          exact ih (r + 1) l1 _ (by omega) hs2 (by omega)
  obtain ⟨r, hr', hr, hst⟩ := hL.step m T
  obtain ⟨todo, subs, hs⟩ := al r hr
  obtain ⟨s2, hs2, hstep⟩ := hst _ hs
  cases hstep with
  | push h1 h2 h3 h4 =>
    rename_i t' subs'
    cases todo with
    | none =>
      have hne := (h4 (hd r hr')).1 rfl
      cases t' with
      | none => exact absurd rfl hne
      | some l1 => exact main l1.length (r + 1) l1 subs' (by omega) hs2 (Nat.le_refl _)
    | some l0 =>
      obtain ⟨l1, e1, -⟩ := h1 l0 rfl
      subst e1
      exact main l1.length (r + 1) l1 subs' (by omega) hs2 (Nat.le_refl _)

/-- A push with nothing left to push stays so: it opens no more goals, and
reads those it opened no less far. -/
theorem Line.push_fixed (hL : Line need σ k r0 L) {m : Nat} {kd : Kind} {left : Bool}
    {side : Nat} {other : N} {ra : Nat} {subsa : List (A × Nat × Nat)} (hra : r0 ≤ ra)
    (hsa : (L ra)[m]? = some (.push kd left side other (some []) subsa)) {r : Nat}
    (hr : ra ≤ r) :
    ∃ subs, (L r)[m]? = some (.push kd left side other (some []) subs) ∧
      PushAdv subsa subs ∧ subs.length = subsa.length := by
  obtain ⟨_, hs, subs, rfl, hp, hlen⟩ := hL.along_from
    (fun _ s => ∃ subs, s = Strat.push kd left side other (some []) subs ∧
      PushAdv subsa subs ∧ subs.length = subsa.length) hra hsa
    ⟨subsa, rfl, PushAdv.refl _, rfl⟩
    (fun r s s' _ _ _ hq hadv => by
      obtain ⟨subs, rfl, hp, hlen⟩ := hq
      cases hadv with
      | push a1 a2 a3 =>
        obtain ⟨l1, e1, hl1⟩ := a1 [] rfl
        have : l1 = [] := List.length_eq_zero_iff.1 (Nat.le_zero.1 hl1)
        subst this
        subst e1
        exact ⟨_, rfl, hp.trans a2, (a3 rfl).trans hlen⟩) hr
  exact ⟨subs, hs, hp, hlen⟩

/-- **A push reads all there is.** With nothing left to push, once the
tables of the goals it opened gain no more answers, it has read every
answer of each from some state on. -/
theorem Line.push_read (hL : Line need σ k r0 L) {m : Nat} {kd : Kind} {left : Bool}
    {side : Nat} {other : N} {subs1 : List (A × Nat × Nat)} {T1 : Nat} (hT1 : r0 ≤ T1)
    (h1 : (L T1)[m]? = some (.push kd left side other (some []) subs1))
    (hd : ∀ r, T1 ≤ r → (σ r).isDone side = true) {T : Nat} (hT : T1 ≤ T)
    (hstill : ∀ e ∈ subs1, Still σ T e.2.1) :
    ∃ T', T ≤ T' ∧ ∀ r, T' ≤ r → ∃ subs,
      (L r)[m]? = some (.push kd left side other (some []) subs) ∧ PushAdv subs1 subs ∧
      subs.length = subs1.length ∧ ∀ e ∈ subs, (σ r).len e.2.1 ≤ e.2.2 := by
  have keep := fun ra subsa (hra : r0 ≤ ra)
    (hsa : (L ra)[m]? = some (.push kd left side other (some []) subsa)) r (hr : ra ≤ r) =>
    hL.push_fixed hra hsa hr
  have each : ∀ m', m' < subs1.length → ∃ T', ∀ r, T' ≤ r → ∀ subs e,
      (L r)[m]? = some (.push kd left side other (some []) subs) → subs[m']? = some e →
      (σ r).len e.2.1 ≤ e.2.2 := by
    intro m' hm'
    have he0 : subs1[m']? = some subs1[m'] := List.getElem?_eq_getElem hm'
    generalize subs1[m'] = e0 at he0
    have hst := hstill e0 (List.mem_of_getElem? he0)
    by_cases hex : ∃ ra subsa ea, T ≤ ra ∧
        (L ra)[m]? = some (.push kd left side other (some []) subsa) ∧
        subsa[m']? = some ea ∧ (σ T).len e0.2.1 ≤ ea.2.2
    · obtain ⟨ra, subsa, ea, hra, hsa, hma, hna⟩ := hex
      refine ⟨ra, fun r hr subs e hs he => ?_⟩
      obtain ⟨subs', hs', hadv, -⟩ := keep ra subsa (by omega) hsa r hr
      rw [hs] at hs'
      cases hs'
      obtain ⟨-, x2, x3⟩ := hadv.2 m' ea e hma he
      obtain ⟨subs2, hs2, hadv2, -⟩ := keep T1 subs1 hT1 h1 ra (by omega)
      rw [hsa] at hs2
      cases hs2
      obtain ⟨-, y2, -⟩ := hadv2.2 m' e0 ea he0 hma
      have h3 := hst r (by omega)
      rw [x2, y2, h3]
      omega
    · exfalso
      let f : Nat → Nat := fun r =>
        match (L r)[m]? with
        | some (.push _ _ _ _ _ subs) => behind ((σ T).len e0.2.1) (subs.map (·.2))
        | _ => 0
      refine no_descent (· < ·) Nat.lt_wfRel.wf (fun _ _ _ h1 h2 => Nat.lt_trans h1 h2) f
        T (fun r hr => ?_) (fun r' => ?_)
      · obtain ⟨subs, hs, -, -⟩ := keep T1 subs1 hT1 h1 r (by omega)
        obtain ⟨s', hs', hadv⟩ := (hL.adv r (by omega)).get hs
        cases hadv with
        | push a1 a2 a3 =>
          have := behind_le ((σ T).len e0.2.1) (a2.pointwise (a3 rfl))
          simp only [f, hs, hs']
          omega
      · obtain ⟨r, hr', hr, hstp⟩ := hL.step m (max r' T)
        obtain ⟨subs, hs, hadv, hlen⟩ := keep T1 subs1 hT1 h1 r (by omega)
        have hlt : m' < subs.length := by omega
        have he : subs[m']? = some subs[m'] := List.getElem?_eq_getElem hlt
        generalize subs[m'] = e at he
        obtain ⟨-, y2, -⟩ := hadv.2 m' e0 e he0 he
        obtain ⟨s', hs', hstep⟩ := hstp _ hs
        cases hstep with
        | push a1 a2 a3 a4 =>
          refine ⟨r, by omega, ?_⟩
          simp only [f, hs, hs']
          refine (a4 (hd r (by omega))).2.2 rfl _ m' e he ?_ ?_
          · by_contra hc
            exact hex ⟨r, subs, e, by omega, hs, he, by omega⟩
          · rw [y2, hst r (by omega)]
  obtain ⟨T', hT'⟩ := eventually_forall_lt subs1.length _ each
  refine ⟨max T' T, Nat.le_max_right _ _, fun r hr => ?_⟩
  obtain ⟨subs, hs, hp, hlen⟩ := keep T1 subs1 hT1 h1 r (by omega)
  refine ⟨subs, hs, hp, hlen, fun e he => ?_⟩
  obtain ⟨m', hm'⟩ := List.getElem?_of_mem he
  have hlt : m' < subs1.length := by
    rw [← hlen]
    exact (List.getElem?_eq_some_iff.1 hm').1
  exact hT' m' hlt r (by omega) subs e hs hm'

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
