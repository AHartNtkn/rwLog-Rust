/-
# Matching, coverage without constraints, and equality

`mmatch_spec`: the Rust `mmatch` decides `matchInto`. Table `A` holds, for
each node of the pattern already matched, the term it matched; for a variable
that is its binding. A node of the pattern is matched once however often it
occurs, so the cost is two ticks plus six for each distinct subterm of the
pattern, whatever the size of the term it is matched against.

`covers_plain_spec`: for a covering span with no constraints, `covers_plain`
decides `Span.covers?`.

`span_eq_spec`: `span_eq` decides equality of spans in three ticks, because
equal terms are the same node.
-/
import RwLogVerified.Chain
import RwLogVerified.MatchSpec

open Aeneas Aeneas.Std Result

namespace RwLogVerified

open rwlog_core RwLog RwLog.Term RwLog.Matching

variable {nm : Option Nat → Sym}

/-! ## Matching -/

/-- Table `A` and the bindings `θ` of the specification say the same. -/
structure MatchOK (nm : Option Nat → Sym) (nodes : List store.Node) (A : Nat → Option Nat)
    (θ : PSubst) (x : Option Nat) : Prop where
  /-- An entry is a pattern whose variables are bound, and what it is under
  the bindings. -/
  memo : ∀ k w, A k = some w → ∃ pk tw, Repr nm nodes k pk ∧ Repr nm nodes w tw ∧
    Bound θ pk ∧ pk.bind θ.apply = tw
  /-- A variable with no entry is unbound; the node `x` is excepted. -/
  free : ∀ k v, some k ≠ x → VarAt nodes k v → A k = none → θ.lookup v = none

/-- What `mmatch` leaves. -/
structure MatchPost (nm : Option Nat → Sym) (s s' : store.Store) (θ : PSubst) (tp tt : Pat)
    (S : Finset Pat) (b : Bool) : Prop where
  inv : Inv s'
  nodes : s'.nodes.val = s.nodes.val
  tblB : tbl s' .B = tbl s .B
  res : b = (matchInto tp tt θ).isSome
  ok : b = true → ∃ θ', matchInto tp tt θ = some θ' ∧
    MatchOK nm s'.nodes.val (tbl s' .A) θ' none
  grow : ∀ k, tbl s .A k ≠ none → tbl s' .A k ≠ none
  cost : s'.ticks.val + 6 * (if b then (pending nm s'.nodes.val (tbl s' .A) S).card else 0) ≤
    s.ticks.val + 2 + 6 * (pending nm s.nodes.val (tbl s .A) S).card

/-- The state after the node of the pattern is examined and before its entry
is written. -/
structure MatchMid (nm : Option Nat → Sym) (s s3 : store.Store) (θ : PSubst) (tp tt : Pat)
    (S : Finset Pat) (p : Nat) (ok1 : Bool) : Prop where
  inv : Inv s3
  nodes : s3.nodes.val = s.nodes.val
  tblB : tbl s3 .B = tbl s .B
  res : ok1 = (matchInto tp tt θ).isSome
  ok : ok1 = true → ∃ θ', matchInto tp tt θ = some θ' ∧
    MatchOK nm s3.nodes.val (tbl s3 .A) θ' (some p)
  grow : ∀ k, tbl s .A k ≠ none → tbl s3 .A k ≠ none
  cost : s3.ticks.val +
      6 * (if ok1 then (pending nm s3.nodes.val (tbl s3 .A) (S.erase tp)).card else 0) ≤
    s.ticks.val + 7 + 6 * (pending nm s.nodes.val (tbl s .A) (S.erase tp)).card

theorem MatchOK.weaken {nodes : List store.Node} {A : Nat → Option Nat} {θ : PSubst} {x : Option Nat}
    (h : MatchOK nm nodes A θ none) : MatchOK nm nodes A θ x :=
  ⟨h.memo, fun k v _ hv hk => h.free k v (by simp) hv hk⟩

/-- Writing the entry of the pattern node after a successful match. -/
theorem mmatch_finish (hnm : Function.Injective nm) {s s3 s' : store.Store} {θ : PSubst}
    {tp tt : Pat} {S : Finset Pat} {p t : store.TermId} (hI : Inv s)
    (hp : Repr nm s.nodes.val p.val tp) (ht : Repr nm s.nodes.val t.val tt)
    (hnone : tbl s .A p.val = none) (htS : tp ∈ S)
    (hmid : MatchMid nm s s3 θ tp tt S p.val true)
    (g1 : s'.nodes.val = s3.nodes.val) (g2 : s'.ticks.val = s3.ticks.val + 1) (g3 : Inv s')
    (g4 : tbl s' .A = Function.update (tbl s3 .A) p.val (some t.val))
    (g5 : ∀ t', t' ≠ store.Tbl.A → tbl s' t' = tbl s3 t') :
    MatchPost nm s s' θ tp tt S true := by
  obtain ⟨θ', hθ', hM⟩ := hmid.ok rfl
  obtain ⟨-, hb, hbind⟩ := matchInto_ext tp tt θ θ' hθ'
  have hn3 := hmid.nodes
  have hp3 : Repr nm s3.nodes.val p.val tp := by rw [hn3]; exact hp
  refine ⟨g3, by rw [g1, hn3], ?_, hmid.res, fun _ => ⟨θ', hθ', ?_⟩, ?_, ?_⟩
  · rw [g5 .B (by simp), hmid.tblB]
  · rw [g1, g4]
    refine ⟨fun k w hk => ?_, fun k v _ hv hk => ?_⟩
    · by_cases e : k = p.val
      · subst e
        simp only [Function.update_self, Option.some.injEq] at hk
        subst hk
        exact ⟨tp, tt, hp3, by rw [hn3]; exact ht, hb, hbind⟩
      · rw [Function.update_of_ne e] at hk
        exact hM.memo k w hk
    · by_cases e : k = p.val
      · subst e; simp at hk
      · rw [Function.update_of_ne e] at hk
        exact hM.free k v (by simpa using e) hv hk
  · intro k hk
    rw [g4]
    by_cases e : k = p.val
    · subst e; simp
    · rw [Function.update_of_ne e]; exact hmid.grow k hk
  · have hsub : pending nm s'.nodes.val (tbl s' .A) S ⊆
        pending nm s3.nodes.val (tbl s3 .A) (S.erase tp) := by
      have := pending_after_set (nm := nm) (nodes := s3.nodes.val) (more := []) (A := tbl s3 .A)
        (A' := tbl s' .A) (S := S) (t := tp) (p := p.val) (by simpa using hp3)
        (by rw [g4]; simp)
        (by
          intro k hk
          rw [g4]
          by_cases e : k = p.val
          · subst e; simp
          · rw [Function.update_of_ne e]; exact hk)
      simpa [g1] using this
    have h1 := Finset.card_le_card hsub
    have h2 := pending_erase_card (mem_pending_of_none hnm hI.nodesOK hp hnone htS)
    have h3 := hmid.cost
    simp only [↓reduceIte] at h3 ⊢
    omega

theorem mmatch_spec_aux (hnm : Function.Injective nm) (n : Nat) :
    ∀ (s : store.Store) (p t : store.TermId) (tp tt : Pat) (θ : PSubst) (S : Finset Pat),
      tp.size ≤ n → Inv s → Repr nm s.nodes.val p.val tp → Repr nm s.nodes.val t.val tt →
      MatchOK nm s.nodes.val (tbl s .A) θ none → tp.subs ⊆ S →
      Room s (2 + 6 * (pending nm s.nodes.val (tbl s .A) S).card) →
      cover.mmatch s p t ⦃ b s' => MatchPost nm s s' θ tp tt S b ⦄ := by
  induction n with
  | zero =>
    intro s p t tp tt θ S hsz
    cases tp <;> simp [Term.size] at hsz
  | succ n ih =>
    intro s p t tp tt θ S hsz hI hp ht hM hS hroom
    unfold cover.mmatch
    have hroom' := hroom
    unfold Room at hroom'
    step with get_spec s .A p hI hp.lt (by unfold Room; omega) as ⟨o, s1, ho, hK1⟩
    have ht1 := hK1.ticks
    have hn1 := hK1.nodes
    cases o with
    | some u =>
      simp only [Option.map_some] at ho
      simp only
      obtain ⟨pk, tw, hk, hw, hbd, hbind⟩ := hM.memo _ _ ho.symm
      have := hp.unique hk
      subst this
      refine WP.spec_mono (same_spec s1 u t hK1.inv (by unfold Room; omega)) ?_
      rintro ⟨b, s'⟩ ⟨hb, hK⟩
      have hmi := matchInto_bound tp tt θ hbd
      rw [hbind] at hmi
      have hres : b = (matchInto tp tt θ).isSome := by
        rw [hmi, hb]
        by_cases e : u.val = t.val
        · have : tw = tt := by rw [e] at hw; exact hw.unique ht
          simp [e, this]
        · have : tw ≠ tt := fun h => e (Repr.inj hnm hI.nodesOK hw (h ▸ ht))
          simp [e, this]
      refine ⟨hK.inv, by rw [hK.nodes, hn1], by rw [hK.tbl, hK1.tbl], hres, fun hbt => ?_,
        fun k hk => by rw [hK.tbl, hK1.tbl]; exact hk, ?_⟩
      · refine ⟨θ, ?_, by rw [hK.nodes, hn1, hK.tbl, hK1.tbl]; exact hM⟩
        rw [hmi]
        rw [hmi] at hres
        by_cases e : tw = tt
        · simp [e]
        · simp [e] at hres; simp [hres] at hbt
      · have := hK.ticks
        rw [hK.nodes, hn1, hK.tbl, hK1.tbl]
        split <;> omega
    | none =>
      simp only [Option.map_none] at ho
      have hnone : tbl s .A p.val = none := ho.symm
      have htS : tp ∈ S := hS (Term.self_mem_subs tp)
      have hpend := mem_pending_of_none hnm hI.nodesOK hp hnone htS
      have hP := pending_erase_card hpend
      simp only
      step with read_spec s1 p hK1.inv (by rw [hn1]; exact hp.lt) (by unfold Room; omega)
        as ⟨nd, s2, hnd, hK2⟩
      rw [hn1] at hnd
      have ht2 := hK2.ticks
      have hn2 : s2.nodes.val = s.nodes.val := by rw [hK2.nodes, hn1]
      have htb2 : tbl s2 = tbl s := by rw [hK2.tbl, hK1.tbl]
      refine WP.spec_bind (Pₘ := fun r => MatchMid nm s r.1 θ tp tt S p.val r.2) ?_ ?_
      · -- the node of the pattern
        have hvar : ∀ v, tp = Term.var v → VarAt s.nodes.val p.val v →
            MatchMid nm s s2 θ tp tt S p.val true := by
          intro v hv hva
          subst hv
          have hfree := hM.free p.val v (by simp) hva hnone
          have hmi : matchInto (Term.var v) tt θ = some ((v, tt) :: θ) := by
            simp [matchInto, hfree]
          refine ⟨hK2.inv, hn2, by rw [htb2], by rw [hmi]; rfl, fun _ => ⟨_, hmi, ?_⟩,
            fun k hk => by rw [htb2]; exact hk, ?_⟩
          · rw [hn2, htb2]
            refine ⟨fun k w hk => ?_, fun k v' hkp hv' hk => ?_⟩
            · obtain ⟨pk, tw, h1, h2, h3, h4⟩ := hM.memo k w hk
              have hext : ∀ x u, θ.lookup x = some u → ((v, tt) :: θ).lookup x = some u := by
                intro x u hx
                have : x ≠ v := by rintro rfl; rw [hfree] at hx; cases hx
                rw [lookup_cons_ne this]; exact hx
              obtain ⟨h3', h4'⟩ := bound_ext h3 hext
              exact ⟨pk, tw, h1, h2, h3', by rw [h4', h4]⟩
            · have hne : v' ≠ v := by
                rintro rfl
                exact hkp (by rw [hv'.inj hI.nodesOK hva])
              rw [lookup_cons_ne hne]
              exact hM.free k v' (by simp) hv' hk
          · simp only [↓reduceIte]
            rw [hn2, htb2]
            omega
        have hatom : ∀ f, tp = Term.sym f →
            (do
              let (ok2, s4) ← store.Store.same s2 p t
              ok (s4, ok2)) ⦃ r => MatchMid nm s r.1 θ tp tt S p.val r.2 ⦄ := by
          intro f hf
          subst hf
          step with same_spec s2 p t hK2.inv (by unfold Room; omega) as ⟨ok2, s4, hb, hK⟩
          have hres : ok2 = (matchInto (Term.sym f) tt θ).isSome := by
            rw [hb]
            by_cases e : p.val = t.val
            · have : tt = Term.sym f := by rw [e] at hp; exact ht.unique hp
              subst this
              simp [e, matchInto]
            · have hne : tt ≠ Term.sym f := fun h => e (Repr.inj hnm hI.nodesOK hp (h ▸ ht))
              cases tt with
              | var w => simp [e, matchInto]
              | app a b => simp [e, matchInto]
              | sym g =>
                have : f ≠ g := fun h => hne (by rw [h])
                simp [e, matchInto, this]
          have hn4 : s4.nodes.val = s.nodes.val := by rw [hK.nodes, hn2]
          have htb4 : tbl s4 = tbl s := by rw [hK.tbl, htb2]
          refine ⟨hK.inv, hn4, by rw [htb4], hres, fun hbt => ?_,
            fun k hk => by rw [htb4]; exact hk, ?_⟩
          · subst hbt
            have hmi : matchInto (Term.sym f) tt θ = some θ := by
              cases tt with
              | var w => simp [matchInto] at hres
              | app a b => simp [matchInto] at hres
              | sym g =>
                simp only [matchInto] at hres ⊢
                by_cases hfg : f = g
                · simp [hfg]
                · simp [hfg] at hres
            exact ⟨θ, hmi, by rw [hn4, htb4]; exact hM.weaken⟩
          · have := hK.ticks
            rw [hn4, htb4]
            split <;> omega
        cases nd with
        | V0 =>
          obtain ⟨v, hv, hva⟩ := hp.of_var hnd trivial
          simp only [WP.spec_ok]
          exact hvar v hv hva
        | VL a =>
          obtain ⟨v, hv, hva⟩ := hp.of_var hnd trivial
          simp only [WP.spec_ok]
          exact hvar v hv hva
        | VR a =>
          obtain ⟨v, hv, hva⟩ := hp.of_var hnd trivial
          simp only [WP.spec_ok]
          exact hvar v hv hva
        | Sym g => exact hatom _ (hp.of_sym hnd)
        | Nil => exact hatom _ (hp.of_nil hnd)
        | App p1 p2 =>
          obtain ⟨pa, pb, e, ha, hb⟩ := hp.of_app hnd
          subst e
          simp only [Term.size] at hsz
          have hSa := subs_left_erase hS
          have hSb := subs_right_erase hS
          simp only
          step with read_spec s2 t hK2.inv (by rw [hn2]; exact ht.lt) (by unfold Room; omega)
            as ⟨n1, s4, hnt, hK4⟩
          rw [hn2] at hnt
          have ht4 := hK4.ticks
          have hn4 : s4.nodes.val = s.nodes.val := by rw [hK4.nodes, hn2]
          have htb4 : tbl s4 = tbl s := by rw [hK4.tbl, htb2]
          have hfail : (∀ a b, tt ≠ Term.app a b) →
              MatchMid nm s s4 θ (Term.app pa pb) tt S p.val false := by
            intro hna
            have hmi : matchInto (Term.app pa pb) tt θ = none := by
              cases tt with
              | var w => simp [matchInto]
              | sym g => simp [matchInto]
              | app a b => exact absurd rfl (hna a b)
            exact ⟨hK4.inv, hn4, by rw [htb4], by rw [hmi]; rfl, (fun h => by cases h),
              (fun k hk => by rw [htb4]; exact hk),
              by simp only [Bool.false_eq_true, ↓reduceIte]; omega⟩
          cases n1 with
          | V0 =>
            obtain ⟨v, hv, -⟩ := ht.of_var hnt trivial
            simp only [WP.spec_ok]
            exact hfail (by rw [hv]; simp)
          | VL a =>
            obtain ⟨v, hv, -⟩ := ht.of_var hnt trivial
            simp only [WP.spec_ok]
            exact hfail (by rw [hv]; simp)
          | VR a =>
            obtain ⟨v, hv, -⟩ := ht.of_var hnt trivial
            simp only [WP.spec_ok]
            exact hfail (by rw [hv]; simp)
          | Sym g =>
            simp only [WP.spec_ok]
            exact hfail (by rw [ht.of_sym hnt]; simp)
          | Nil =>
            simp only [WP.spec_ok]
            exact hfail (by rw [ht.of_nil hnt]; simp)
          | App t1 t2 =>
            obtain ⟨ta, tb, e, hta, htb⟩ := ht.of_app hnt
            subst e
            simp only
            step with ih s4 p1 t1 pa ta θ (S.erase (Term.app pa pb)) (by omega) hK4.inv
              (by rw [hn4]; exact ha) (by rw [hn4]; exact hta) (by rw [hn4, htb4]; exact hM) hSa
              (by rw [hn4, htb4]; unfold Room; omega) as ⟨b1, s5, h5⟩
            have hc5 := h5.cost
            rw [hn4, htb4] at hc5
            have hn5 : s5.nodes.val = s.nodes.val := by rw [h5.nodes, hn4]
            cases b1 with
            | false =>
              simp only [Bool.false_eq_true, ↓reduceIte, WP.spec_ok]
              simp only [Bool.false_eq_true, ↓reduceIte] at hc5
              have hm1 : matchInto pa ta θ = none := by
                have := h5.res
                cases h : matchInto pa ta θ with
                | none => rfl
                | some _ => rw [h] at this; cases this
              refine ⟨h5.inv, hn5, by rw [h5.tblB, htb4], by simp [matchInto, hm1],
                (fun h => by cases h), (fun k hk => h5.grow k (by rw [htb4]; exact hk)), ?_⟩
              simp only [Bool.false_eq_true, ↓reduceIte]
              omega
            | true =>
              simp only [↓reduceIte] at hc5 ⊢
              obtain ⟨θ1, hm1, hM1⟩ := h5.ok rfl
              step with ih s5 p2 t2 pb tb θ1 (S.erase (Term.app pa pb)) (by omega) h5.inv
                (by rw [hn5]; exact hb) (by rw [hn5]; exact htb) hM1 hSb
                (by unfold Room; omega) as ⟨b2, s6, h6⟩
              have hc6 := h6.cost
              have hn6 : s6.nodes.val = s.nodes.val := by rw [h6.nodes, hn5]
              have hres : b2 = (matchInto (Term.app pa pb) (Term.app ta tb) θ).isSome := by
                simp only [matchInto, hm1, Option.bind_some]
                exact h6.res
              refine ⟨h6.inv, hn6, by rw [h6.tblB, h5.tblB, htb4], hres, fun hbt => ?_,
                fun k hk => h6.grow k (h5.grow k (by rw [htb4]; exact hk)), ?_⟩
              · obtain ⟨θ2, hm2, hM2⟩ := h6.ok hbt
                exact ⟨θ2, by simp only [matchInto, hm1, Option.bind_some, hm2], hM2.weaken⟩
              · cases b2 <;> simp only [Bool.false_eq_true, ↓reduceIte] at hc6 ⊢ <;> omega
      · -- writing the entry
        rintro ⟨s3, ok1⟩ hmid
        cases ok1 with
        | false =>
          simp only [uncurry_apply_pair, Bool.false_eq_true, ↓reduceIte, WP.spec_ok]
          have hc := hmid.cost
          simp only [Bool.false_eq_true, ↓reduceIte] at hc
          exact ⟨hmid.inv, hmid.nodes, hmid.tblB, hmid.res, (fun h => by cases h), hmid.grow,
            (by simp only [Bool.false_eq_true, ↓reduceIte]; omega)⟩
        | true =>
          simp only [uncurry_apply_pair, ↓reduceIte]
          have hc := hmid.cost
          simp only [↓reduceIte] at hc
          step with set_spec s3 .A p t hmid.inv (by rw [hmid.nodes]; exact hp.lt)
            (by unfold Room; omega) as ⟨s4, g1, g2, g3, g4, g5⟩
          exact mmatch_finish hnm hI hp ht hnone htS hmid g1 g2 g3 g4 g5

/-- `mmatch` decides one-way matching. It spends two ticks, and six more for
each term of `S` that had no table entry and gets one. -/
theorem mmatch_spec (hnm : Function.Injective nm) (s : store.Store) (p t : store.TermId)
    {tp tt : Pat} {θ : PSubst} (S : Finset Pat) (hI : Inv s) (hp : Repr nm s.nodes.val p.val tp)
    (ht : Repr nm s.nodes.val t.val tt) (hM : MatchOK nm s.nodes.val (tbl s .A) θ none)
    (hS : tp.subs ⊆ S) (hroom : Room s (2 + 6 * (pending nm s.nodes.val (tbl s .A) S).card)) :
    cover.mmatch s p t ⦃ b s' => MatchPost nm s s' θ tp tt S b ⦄ :=
  mmatch_spec_aux hnm tp.size s p t tp tt θ S (Nat.le_refl _) hI hp ht hM hS hroom

/-! ## Coverage by a span with no constraints -/

/-- The ticks `covers_plain` may spend: they depend on the covering span
only. -/
def coversPlainCost (a : Span) : Nat := 5 + 6 * (a.l.subs ∪ a.r.subs).card

theorem covers_plain_spec (hnm : Function.Injective nm) (s : store.Store) (a x : span.Span)
    {sa sx : Span} (hI : Inv s) (ha : SpanAt nm s.nodes.val a sa) (hx : SpanAt nm s.nodes.val x sx)
    (hc : sa.c = []) (hroom : Room s (coversPlainCost sa)) :
    cover.covers_plain s a x ⦃ b s' =>
      Inv s' ∧ s'.nodes.val = s.nodes.val ∧ b = sa.covers? sx ∧
        s'.ticks.val ≤ s.ticks.val + coversPlainCost sa ⦄ := by
  unfold cover.covers_plain
  have hroom' := hroom
  unfold Room coversPlainCost at hroom'
  unfold coversPlainCost
  step with clear_spec s .A hI (by unfold Room; omega) as ⟨s1, c1, c2, c3, c4, c5⟩
  have hpc := pending_card_le (nm := nm) s1.nodes.val (tbl s1 .A) (sa.l.subs ∪ sa.r.subs)
  have hM0 : MatchOK nm s1.nodes.val (tbl s1 .A) [] none :=
    ⟨(fun k w hk => by rw [c4] at hk; cases hk), fun _ _ _ _ _ => rfl⟩
  step with mmatch_spec hnm s1 a.l x.l (tp := sa.l) (tt := sx.l) (θ := [])
    (sa.l.subs ∪ sa.r.subs) c3 (by rw [c1]; exact ha.l) (by rw [c1]; exact hx.l) hM0
    Finset.subset_union_left (by unfold Room; omega) as ⟨b, s2, h2⟩
  have hc2 := h2.cost
  have hn2 : s2.nodes.val = s.nodes.val := by rw [h2.nodes, c1]
  cases b with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at hc2 ⊢
    have hm : matchInto sa.l sx.l [] = none := by
      have := h2.res
      cases h : matchInto sa.l sx.l [] with
      | none => rfl
      | some _ => rw [h] at this; cases this
    step*
    exact ⟨h2.inv, hn2, by simp [Span.covers?, hm], by omega⟩
  | true =>
    simp only [↓reduceIte] at hc2 ⊢
    obtain ⟨θ1, hm1, hM1⟩ := h2.ok rfl
    refine WP.spec_mono (mmatch_spec hnm s2 a.r x.r (tp := sa.r) (tt := sx.r) (θ := θ1)
      (sa.l.subs ∪ sa.r.subs) h2.inv (by rw [hn2]; exact ha.r) (by rw [hn2]; exact hx.r) hM1
      Finset.subset_union_right (by unfold Room; omega)) ?_
    rintro ⟨b2, s3⟩ h3
    have hc3 := h3.cost
    refine ⟨h3.inv, by rw [h3.nodes, hn2], ?_, ?_⟩
    · rw [h3.res]
      simp only [Span.covers?, hm1, Option.bind_some, hc]
      cases matchInto sa.r sx.r θ1 <;> simp [matchAll]
    · have : s3.ticks.val ≤ s2.ticks.val + 2 +
          6 * (pending nm s2.nodes.val (tbl s2 .A) (sa.l.subs ∪ sa.r.subs)).card := by
        have h0 : 0 ≤ 6 * (if b2 = true then
          (pending nm s3.nodes.val (tbl s3 .A) (sa.l.subs ∪ sa.r.subs)).card else 0) := Nat.zero_le _
        omega
      omega

/-! ## Equality of spans -/

theorem spanAt_eq_iff (hnm : Function.Injective nm) {s : store.Store} (hI : Inv s)
    {x y : span.Span} {sx sy : Span} (hx : SpanAt nm s.nodes.val x sx)
    (hy : SpanAt nm s.nodes.val y sy) :
    sx = sy ↔ x.l.val = y.l.val ∧ x.r.val = y.r.val ∧ x.c.val = y.c.val := by
  constructor
  · rintro rfl
    exact ⟨Repr.inj hnm hI.nodesOK hx.l hy.l, Repr.inj hnm hI.nodesOK hx.r hy.r,
      Repr.inj hnm hI.nodesOK hx.c hy.c⟩
  · rintro ⟨h1, h2, h3⟩
    have e1 : sx.l = sy.l := by have := hx.l; rw [h1] at this; exact this.unique hy.l
    have e2 : sx.r = sy.r := by have := hx.r; rw [h2] at this; exact this.unique hy.r
    have e3 : sx.c = sy.c := by
      have := hx.c; rw [h3] at this; exact encList_inj _ (this.unique hy.c)
    cases sx; cases sy
    simp only at e1 e2 e3
    rw [e1, e2, e3]

theorem span_eq_spec (hnm : Function.Injective nm) (s : store.Store) (x y : span.Span)
    {sx sy : Span} (hI : Inv s) (hx : SpanAt nm s.nodes.val x sx) (hy : SpanAt nm s.nodes.val y sy)
    (hroom : Room s 3) :
    cover.span_eq s x y ⦃ b s' =>
      Inv s' ∧ s'.nodes.val = s.nodes.val ∧ tbl s' = tbl s ∧ b = decide (sx = sy) ∧
        s'.ticks.val ≤ s.ticks.val + 3 ⦄ := by
  unfold cover.span_eq
  have hroom' := hroom
  unfold Room at hroom'
  have hiff := spanAt_eq_iff hnm hI hx hy
  step with same_spec s x.l y.l hI (by unfold Room; omega) as ⟨b, s1, hb, hK1⟩
  have ht1 := hK1.ticks
  by_cases e1 : x.l.val = y.l.val
  · have : b = true := by simp [hb, e1]
    subst this
    simp only [↓reduceIte]
    step with same_spec s1 x.r y.r hK1.inv (by unfold Room; omega) as ⟨b1, s2, hb1, hK2⟩
    have ht2 := hK2.ticks
    by_cases e2 : x.r.val = y.r.val
    · have : b1 = true := by simp [hb1, e2]
      subst this
      simp only [↓reduceIte]
      refine WP.spec_mono (same_spec s2 x.c y.c hK2.inv (by unfold Room; omega)) ?_
      rintro ⟨b2, s3⟩ ⟨hb2, hK3⟩
      have ht3 := hK3.ticks
      refine ⟨hK3.inv, by rw [hK3.nodes, hK2.nodes, hK1.nodes], by rw [hK3.tbl, hK2.tbl, hK1.tbl],
        ?_, by omega⟩
      rw [hb2]
      simp only [hiff, e1, e2, true_and]
    · have : b1 = false := by simp [hb1, e2]
      subst this
      simp only [Bool.false_eq_true, ↓reduceIte]
      step*
      refine ⟨hK2.inv, by rw [hK2.nodes, hK1.nodes], by rw [hK2.tbl, hK1.tbl], ?_, by omega⟩
      simp [hiff, e2]
  · have : b = false := by simp [hb, e1]
    subst this
    simp only [Bool.false_eq_true, ↓reduceIte]
    step*
    refine ⟨hK1.inv, hK1.nodes, hK1.tbl, ?_, by omega⟩
    simp [hiff, e1]

end RwLogVerified
