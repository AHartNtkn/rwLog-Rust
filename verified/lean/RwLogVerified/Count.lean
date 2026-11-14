/-
# How many members a conjunction of sorts has, on the store

`sorts::count` flags the conjunctions a conjunction reaches that have a
member (`flag_live_spec`), and then finds in rounds the one member of those
that have just one: a conjunction with a sort without a rest, whose
alternatives all flagged with yes are one alternative, and whose arguments
there all have their one member already. `count_spec` says it answers
`Sorts.count`, and what it spends.

Table `A` has the one member of a conjunction. `MembersA` says which.
-/
import RwLogVerified.Live
import RwLog.Sorts.ReachCount

open Aeneas Aeneas.Std Result

namespace RwLogVerified

open rwlog_core RwLog

variable {nm : Option Nat → RwLog.Sym}

/-! ## The one alternative all flagged with yes -/

/-- Every conjunction of the alternative is flagged with yes. -/
def Lv (m : Sorts.Conj → Option Bool) (a : Alt) : Prop := ∀ c ∈ a.2, m c = some true

instance (m : Sorts.Conj → Option Bool) (a : Alt) : Decidable (Lv m a) := by
  unfold Lv; infer_instance

/-- The alternative of the list all flagged with yes, when those that are,
and `p`, are one alternative. -/
def soleOf (m : Sorts.Conj → Option Bool) : Option Alt → List Alt → Option Alt
  | p, [] => p
  | p, a :: rest =>
    if Lv m a then
      match p with
      | none => soleOf m (some a) rest
      | some b => if a = b then soleOf m (some b) rest else none
    else soleOf m p rest

theorem soleOf_some {m : Sorts.Conj → Option Bool} {a b : Alt} : ∀ {rest : List Alt},
    soleOf m (some b) rest = some a ↔ a = b ∧ ∀ x ∈ rest, Lv m x → x = b
  | [] => by simp [soleOf, eq_comm]
  | y :: rest => by
    simp only [soleOf, List.mem_cons, forall_eq_or_imp]
    by_cases hy : Lv m y
    · by_cases e : y = b
      · simp [e, soleOf_some (rest := rest)]
      · simp [hy, e]
    · simp [hy, soleOf_some (rest := rest)]

theorem soleOf_none {m : Sorts.Conj → Option Bool} {a : Alt} : ∀ {rest : List Alt},
    soleOf m none rest = some a ↔ a ∈ rest ∧ Lv m a ∧ ∀ x ∈ rest, Lv m x → x = a
  | [] => by simp [soleOf]
  | y :: rest => by
    simp only [soleOf, List.mem_cons, forall_eq_or_imp]
    by_cases hy : Lv m y
    · simp only [hy, ↓reduceIte, soleOf_some, forall_const]
      constructor
      · rintro ⟨rfl, h⟩
        exact ⟨Or.inl rfl, hy, rfl, h⟩
      · rintro ⟨-, -, rfl, h⟩
        exact ⟨rfl, h⟩
    · simp only [hy, ↓reduceIte, soleOf_none (rest := rest), false_imp_iff, true_and]
      constructor
      · rintro ⟨h₁, h₂, h₃⟩
        exact ⟨Or.inr h₁, h₂, h₃⟩
      · rintro ⟨h₁ | h₁, h₂, h₃⟩
        · subst h₁; exact absurd h₂ hy
        · exact ⟨h₁, h₂, h₃⟩

theorem altPat_inj {z : Sym} {U : List Name} : ∀ {a b : List Sorts.Conj},
    (∀ c ∈ a, Sub U c) → (∀ c ∈ b, Sub U c) → altPat z U a = altPat z U b → a = b
  | [], [], _, _, _ => rfl
  | [], _ :: _, _, _, h => by simp [altPat, encList] at h
  | _ :: _, [], _, _, h => by simp [altPat, encList] at h
  | x :: a, y :: b, ha, hb, h => by
    simp only [altPat, List.map_cons, encList, Term.app.injEq] at h
    rw [cpat_inj (ha x List.mem_cons_self) (hb y List.mem_cons_self) h.1,
      altPat_inj (fun c hc => ha c (List.mem_cons_of_mem _ hc))
        (fun c hc => hb c (List.mem_cons_of_mem _ hc)) h.2]

theorem kaltPat_inj {z : Sym} {U : List Name} {a b : Alt} (ha : ∀ c ∈ a.2, Sub U c)
    (hb : ∀ c ∈ b.2, Sub U c) (h : kaltPat z U a = kaltPat z U b) : a = b := by
  simp only [kaltPat, Term.app.injEq, Term.sym.injEq] at h
  exact Prod.ext h.1 (altPat_inj ha hb h.2)

/-- An alternative, or none, as the store has it. -/
def AltAt (nm : Option Nat → RwLog.Sym) (U : List Name) (s : store.Store) :
    Option Alt → Option store.TermId → Prop
  | none, none => True
  | some a, some ai => Repr nm s.nodes.val ai.val (kaltPat (nm none) U a)
  | _, _ => False

theorem AltAt.mono {U : List Name} {s s' : store.Store} {p : Option Alt}
    {o : Option store.TermId} (h : AltAt nm U s p o) (hx : Extends s s') : AltAt nm U s' p o := by
  cases p <;> cases o <;> simp only [AltAt] at h ⊢
  exact hx.repr h

/-- The ticks looking for the one alternative may spend. -/
def soleCost (alts' : List Alt) : Nat := anyCost alts' + alts'.length

theorem sole_alt_done (s : store.Store) (alts : store.TermId) (sole : Option store.TermId) :
    sorts.sole_alt_loop s alts sole false ⦃ r => r = (sole, s) ⦄ := by
  unfold sorts.sole_alt_loop
  rw [loop]
  simp only [sorts.sole_alt_loop.body, Bool.false_eq_true, ↓reduceIte, bind_ok]
  step*

theorem sole_alt_loop_spec (hnm : Function.Injective nm) {U : List Name}
    {m : Sorts.Conj → Option Bool} :
    ∀ (alts' : List Alt) (s : store.Store) (alts : store.TermId) (sole : Option store.TermId)
      (p : Option Alt), Wf s → FlagsB nm s U m → (∀ a ∈ alts', ∀ c ∈ a.2, Sub U c) →
    (∀ b, p = some b → ∀ c ∈ b.2, Sub U c) →
    Repr nm s.nodes.val alts.val (altsPat (nm none) U alts') → AltAt nm U s p sole →
    Room s (soleCost alts') →
    sorts.sole_alt_loop s alts sole true ⦃ r =>
      Ran s r.2 (soleCost alts') ∧ AltAt nm U r.2 (soleOf m p alts') r.1 ⦄ := by
  intro alts'
  induction alts' with
  | nil =>
    intro s alts sole p hW hF hs hp hk hA hroom
    have hroom' := hroom
    unfold Room at hroom'
    simp only [soleCost, anyCost, List.length_nil] at hroom'
    unfold sorts.sole_alt_loop
    rw [loop]
    simp only [sorts.sole_alt_loop.body, ↓reduceIte]
    step with uncons_repr s alts hW hk (by unfold Room; omega) as ⟨r0, hK, hu⟩
    obtain ⟨o, s1⟩ := r0
    simp only [altsPat] at hu
    simp only at hK
    subst hu
    simp only [uncurry, bind_ok]
    have hdn := sole_alt_done s1 alts sole
    unfold sorts.sole_alt_loop at hdn
    refine WP.spec_mono hdn ?_
    rintro r rfl
    exact ⟨hK.ran.mono (by simp [soleCost, anyCost]), by
      simpa [soleOf] using hA.mono hK.ran.ext⟩
  | cons x alts' ih =>
    intro s alts sole p hW hF hs hp hk hA hroom
    have hroom' := hroom
    unfold Room at hroom'
    simp only [soleCost, anyCost, List.length_cons] at hroom'
    have hsx := hs x List.mem_cons_self
    have hs' : ∀ a ∈ alts', ∀ c ∈ a.2, Sub U c := fun a ha => hs a (List.mem_cons_of_mem _ ha)
    unfold sorts.sole_alt_loop
    rw [loop]
    simp only [sorts.sole_alt_loop.body, ↓reduceIte]
    step with uncons_repr s alts hW hk (by unfold Room; omega) as ⟨r0, hK, hu⟩
    obtain ⟨o, s1⟩ := r0
    simp only [altsPat] at hu
    simp only at hK
    obtain ⟨k, t, rfl, rk, rt⟩ := hu
    have ht1 := hK.ticks
    step with alt_live_spec hnm x s1 k hK.wf (hF.mono hK.ran.ext (by rw [hK.tbl])) hsx
      (by rw [hK.nodes]; exact rk) (by unfold Room; omega) as ⟨r1, hR2, hb⟩
    obtain ⟨b, s2⟩ := r1
    simp only at hR2 hb
    have ht2 := hR2.ticks
    have R2 : Ran s s2 (2 * x.2.length + 3) := (hK.ran.trans hR2).mono (by omega)
    have hF2 : FlagsB nm s2 U m := hF.mono R2.ext (by rw [R2.tbl])
    -- the rest of the alternatives
    have rest : ∀ (s' : store.Store) (sole' : Option store.TermId) (p' : Option Alt) (n : Nat),
        Ran s s' n → n ≤ 2 * x.2.length + 4 → (∀ b, p' = some b → ∀ c ∈ b.2, Sub U c) →
        AltAt nm U s' p' sole' → soleOf m p' alts' = soleOf m p (x :: alts') →
        loop (fun y => match y with
          | (s1, alts1, sole1, go1) => sorts.sole_alt_loop.body s1 alts1 sole1 go1)
          (s', t, sole', true) ⦃ r =>
          Ran s r.2 (soleCost (x :: alts')) ∧ AltAt nm U r.2 (soleOf m p (x :: alts')) r.1 ⦄ := by
      intro s' sole' p' n R0 hn hp' hA' he
      have := R0.ticks
      have IH := ih s' t sole' p' R0.wf (hF.mono R0.ext (by rw [R0.tbl])) hs' hp' (R0.ext.repr rt)
        hA' (by unfold Room; simp only [soleCost]; omega)
      unfold sorts.sole_alt_loop at IH
      refine WP.spec_mono IH ?_
      rintro r ⟨hR, hr⟩
      exact ⟨(R0.trans hR).mono (by simp only [soleCost, anyCost, List.length_cons]; omega),
        by rw [← he]; exact hr⟩
    cases b with
    | false =>
      have hx : ¬ Lv m x := fun h => by simpa using hb.2 h
      simp only [uncurry, Bool.false_eq_true, ↓reduceIte, bind_ok]
      exact rest s2 sole p _ R2 (by omega) hp (hA.mono R2.ext) (by simp [soleOf, hx])
    | true =>
      have hx : Lv m x := hb.1 rfl
      simp only [uncurry, ↓reduceIte]
      cases sole with
      | none =>
        cases p with
        | some b => simp [AltAt] at hA
        | none =>
          simp only [bind_ok]
          exact rest s2 (some k) (some x) _ R2 (by omega)
            (fun b hb c hc => by cases hb; exact hsx c hc) (R2.ext.repr rk) (by simp [soleOf, hx])
      | some bi =>
        cases p with
        | none => simp [AltAt] at hA
        | some b =>
          simp only [AltAt] at hA
          have rb := R2.ext.repr hA
          have rk2 := R2.ext.repr rk
          step with same_w s2 k bi hR2.wf (by unfold Room; omega) as ⟨r3, hsm, hK3⟩
          obtain ⟨b2, s3⟩ := r3
          simp only at hsm hK3
          have ht3 := hK3.ticks
          have R3 : Ran s s3 (2 * x.2.length + 4) := (R2.trans hK3.ran).mono (by omega)
          by_cases e : k.val = bi.val
          · have hxb : x = b := by
              rw [e] at rk2
              exact kaltPat_inj hsx (hp b rfl) (rk2.unique rb)
            simp only [hsm, e, decide_true, uncurry, ↓reduceIte, bind_ok]
            exact rest s3 (some bi) (some b) _ R3 (by omega) hp (by
              simp only [AltAt]; exact hK3.ran.ext.repr rb) (by simp [soleOf, hxb])
          · have hxb : x ≠ b := by
              rintro rfl
              exact e (Repr.inj hnm hR2.wf.nodesOK rk2 rb)
            simp only [hsm, e, decide_false, uncurry, Bool.false_eq_true, ↓reduceIte, bind_ok]
            have hdn := sole_alt_done s3 alts none
            unfold sorts.sole_alt_loop at hdn
            refine WP.spec_mono hdn ?_
            rintro r rfl
            exact ⟨R3.mono (by simp only [soleCost, anyCost, List.length_cons]; omega), by
              simp [soleOf, hx, hxb, AltAt]⟩

theorem sole_alt_spec (hnm : Function.Injective nm) {U : List Name}
    {m : Sorts.Conj → Option Bool} (alts' : List Alt) (s : store.Store) (alts : store.TermId)
    (hW : Wf s) (hF : FlagsB nm s U m) (hs : ∀ a ∈ alts', ∀ c ∈ a.2, Sub U c)
    (hk : Repr nm s.nodes.val alts.val (altsPat (nm none) U alts'))
    (hroom : Room s (soleCost alts')) :
    sorts.sole_alt s alts ⦃ r =>
      Ran s r.2 (soleCost alts') ∧ AltAt nm U r.2 (soleOf m none alts') r.1 ⦄ :=
  sole_alt_loop_spec hnm alts' s alts none none hW hF hs (fun _ h => by cases h) hk trivial hroom

/-! ## The members table `A` has -/

/-- Table `A` has for the conjunctions the members `M` says. -/
structure MembersA (nm : Option Nat → RwLog.Sym) (s : store.Store) (U : List Name)
    (M : Sorts.Conj → Option GTerm) : Prop where
  has : ∀ c t, M c = some t → Sub U c ∧ ∃ i j, Repr nm s.nodes.val i (cpat (nm none) U c) ∧
    tbl s .A i = some j ∧ Repr nm s.nodes.val j (GTerm.toPat t)
  back : ∀ i j, tbl s .A i = some j → ∃ c t, Sub U c ∧
    Repr nm s.nodes.val i (cpat (nm none) U c) ∧ M c = some t ∧
    Repr nm s.nodes.val j (GTerm.toPat t)

theorem MembersA.get_none (hnm : Function.Injective nm) {s : store.Store} {U : List Name}
    {M : Sorts.Conj → Option GTerm} (h : MembersA nm s U M) (hW : Wf s) {k : Nat}
    {c : Sorts.Conj} (hk : Repr nm s.nodes.val k (cpat (nm none) U c))
    (ht : tbl s .A k = none) : M c = none := by
  by_contra hne
  obtain ⟨t, ht'⟩ := Option.ne_none_iff_exists'.1 hne
  obtain ⟨-, i, j, ri, e, -⟩ := h.has c t ht'
  rw [Repr.inj hnm hW.nodesOK ri hk, ht] at e
  cases e

theorem MembersA.get_some {s : store.Store} {U : List Name}
    {M : Sorts.Conj → Option GTerm} (h : MembersA nm s U M) {k j : Nat}
    {c : Sorts.Conj} (hc : Sub U c) (hk : Repr nm s.nodes.val k (cpat (nm none) U c))
    (ht : tbl s .A k = some j) : ∃ t, M c = some t ∧ Repr nm s.nodes.val j (GTerm.toPat t) := by
  obtain ⟨d, t, hd, rd, e, rj⟩ := h.back k j ht
  have := cpat_inj hc hd (hk.unique rd)
  subst this
  exact ⟨t, e, rj⟩

theorem MembersA.mono {s s' : store.Store} {U : List Name} {M : Sorts.Conj → Option GTerm}
    (h : MembersA nm s U M) (hx : Extends s s') (ht : tbl s' .A = tbl s .A) :
    MembersA nm s' U M := by
  constructor
  · intro c t hc
    obtain ⟨hs, i, j, ri, e, rj⟩ := h.has c t hc
    exact ⟨hs, i, j, hx.repr ri, by rw [ht]; exact e, hx.repr rj⟩
  · intro i j hi
    rw [ht] at hi
    obtain ⟨c, t, hs, ri, e, rj⟩ := h.back i j hi
    exact ⟨c, t, hs, hx.repr ri, e, hx.repr rj⟩

theorem MembersA.set (hnm : Function.Injective nm) {s s' : store.Store} {U : List Name}
    {M : Sorts.Conj → Option GTerm} (h : MembersA nm s U M) (hW : Wf s) {k j : Nat}
    {c : Sorts.Conj} {t : GTerm} (hc : Sub U c) (hk : Repr nm s.nodes.val k (cpat (nm none) U c))
    (hj : Repr nm s.nodes.val j (GTerm.toPat t)) (hn : s'.nodes.val = s.nodes.val)
    (ht : tbl s' .A = Function.update (tbl s .A) k (some j)) :
    MembersA nm s' U (Function.update M c (some t)) := by
  constructor
  · intro d u hd
    by_cases hdc : d = c
    · subst hdc
      rw [Function.update_self] at hd
      cases hd
      exact ⟨hc, k, j, by rw [hn]; exact hk, by rw [ht, Function.update_self],
        by rw [hn]; exact hj⟩
    · rw [Function.update_of_ne hdc] at hd
      obtain ⟨hs, i, j', ri, e, rj⟩ := h.has d u hd
      have hik : i ≠ k := by
        rintro rfl
        exact hdc (cpat_inj hs hc (ri.unique hk))
      exact ⟨hs, i, j', by rw [hn]; exact ri, by rw [ht, Function.update_of_ne hik]; exact e,
        by rw [hn]; exact rj⟩
  · intro i j' hi
    by_cases hik : i = k
    · subst hik
      rw [ht, Function.update_self] at hi
      cases hi
      exact ⟨c, t, hc, by rw [hn]; exact hk, by rw [Function.update_self], by rw [hn]; exact hj⟩
    · rw [ht, Function.update_of_ne hik] at hi
      obtain ⟨d, u, hs, ri, e, rj⟩ := h.back i j' hi
      have hdc : d ≠ c := by
        rintro rfl
        exact hik (Repr.inj hnm hW.nodesOK ri hk)
      exact ⟨d, u, hs, by rw [hn]; exact ri, by rw [Function.update_of_ne hdc]; exact e,
        by rw [hn]; exact rj⟩

/-! ## A symbol applied to the members of conjunctions -/

theorem toPat_foldl : ∀ (ts : List GTerm) (g : GTerm),
    GTerm.toPat (ts.foldl .app g) = ts.foldl (fun acc t => .app acc (GTerm.toPat t)) (GTerm.toPat g)
  | [], _ => rfl
  | t :: ts, g => by
    simp only [List.foldl_cons]
    rw [toPat_foldl ts (.app g t)]
    simp [GTerm.toPat, Term.rename]

theorem toPat_mk (f : Sym) (ts : List GTerm) :
    GTerm.toPat (Term.mk f ts) = ts.foldl (fun acc t => .app acc (GTerm.toPat t)) (.sym f) := by
  unfold Term.mk
  rw [toPat_foldl]
  simp [GTerm.toPat, Term.rename]

theorem apply_members_done (s : store.Store) (term kids : store.TermId) (ok1 : Bool) :
    sorts.apply_members_loop s term kids ok1 false ⦃ r => r = (s, term, ok1) ⦄ := by
  unfold sorts.apply_members_loop
  rw [loop]
  simp only [sorts.apply_members_loop.body, Bool.false_eq_true, ↓reduceIte, bind_ok]
  step*

theorem apply_members_loop_spec (hnm : Function.Injective nm) {U : List Name}
    {M : Sorts.Conj → Option GTerm} :
    ∀ (a : List Sorts.Conj) (s : store.Store) (term kids : store.TermId) (p : Pat), Wf s →
    MembersA nm s U M → (∀ c ∈ a, Sub U c) → Repr nm s.nodes.val term.val p →
    Repr nm s.nodes.val kids.val (altPat (nm none) U a) → Room s (3 * a.length + 1) →
    sorts.apply_members_loop s term kids true true ⦃ r =>
      Ran s r.1 (3 * a.length + 1) ∧
        if r.2.2 = true then ∃ ts, List.Forall₂ (fun c t => M c = some t) a ts ∧
          Repr nm r.1.nodes.val r.2.1.val (ts.foldl (fun acc t => .app acc (GTerm.toPat t)) p)
        else ∃ c ∈ a, M c = none ⦄ := by
  intro a
  induction a with
  | nil =>
    intro s term kids p hW hM hs hterm hk hroom
    have hroom' := hroom
    unfold Room at hroom'
    simp only [List.length_nil] at hroom'
    unfold sorts.apply_members_loop
    rw [loop]
    simp only [sorts.apply_members_loop.body, ↓reduceIte]
    step with uncons_repr s kids hW hk (by unfold Room; omega) as ⟨r0, hK, hu⟩
    obtain ⟨o, s1⟩ := r0
    simp only [altPat] at hu
    simp only at hK
    subst hu
    simp only [uncurry, bind_ok]
    have hdn := apply_members_done s1 term kids true
    unfold sorts.apply_members_loop at hdn
    refine WP.spec_mono hdn ?_
    rintro r rfl
    exact ⟨hK.ran.mono (by simp), by
      simp only [↓reduceIte]
      exact ⟨[], .nil, hK.ran.ext.repr hterm⟩⟩
  | cons x a ih =>
    intro s term kids p hW hM hs hterm hk hroom
    have hroom' := hroom
    unfold Room at hroom'
    simp only [List.length_cons] at hroom'
    unfold sorts.apply_members_loop
    rw [loop]
    simp only [sorts.apply_members_loop.body, ↓reduceIte]
    step with uncons_repr s kids hW hk (by unfold Room; omega) as ⟨r0, hK, hu⟩
    obtain ⟨o, s1⟩ := r0
    simp only [altPat] at hu
    simp only at hK
    obtain ⟨k, t, rfl, rk, rt⟩ := hu
    have ht1 := hK.ticks
    step with get_w s1 .A k hK.wf (by rw [hK.nodes]; exact rk.lt) (by unfold Room; omega)
      as ⟨r1, hg, hK2⟩
    obtain ⟨o1, s2⟩ := r1
    simp only at hg hK2
    rw [hK.tbl] at hg
    have ht2 := hK2.ticks
    have R2 : Ran s s2 2 := hK.ran.trans hK2.ran
    cases o1 with
    | none =>
      have hx : M x = none := hM.get_none hnm hW rk (by simpa using hg.symm)
      simp only [uncurry, bind_ok]
      have hdn := apply_members_done s2 term kids false
      unfold sorts.apply_members_loop at hdn
      refine WP.spec_mono hdn ?_
      rintro r rfl
      exact ⟨R2.mono (by simp only [List.length_cons]; omega), by
        simp only [Bool.false_eq_true, ↓reduceIte]
        exact ⟨x, List.mem_cons_self, hx⟩⟩
    | some mi =>
      obtain ⟨u, hu, rmi⟩ := hM.get_some (hs x List.mem_cons_self) rk (by simpa using hg.symm)
      simp only [uncurry]
      step with alloc_w s2 (.App term mi) hK2.wf ⟨(R2.ext.repr hterm).lt, (R2.ext.repr rmi).lt⟩
        (by unfold Room; omega) as ⟨r3, hW3, ht3, htb3, hx3, hid, hst3⟩
      obtain ⟨term1, s3⟩ := r3
      simp only at hW3 ht3 htb3 hx3 hid hst3 ⊢
      have R3 : Ran s s3 3 :=
        ⟨hW3, R2.ext.trans hx3, by rw [htb3, R2.tbl], by rw [hst3, R2.stk], by
          have := R2.ticks; omega⟩
      have rterm1 : Repr nm s3.nodes.val term1.val (.app p (GTerm.toPat u)) :=
        .app hid (R3.ext.repr hterm) (hx3.repr (R2.ext.repr rmi))
      have IH := ih s3 term1 t (.app p (GTerm.toPat u)) hW3 (hM.mono R3.ext (by rw [R3.tbl]))
        (fun c hc => hs c (List.mem_cons_of_mem _ hc)) rterm1 (R3.ext.repr rt)
        (by unfold Room; omega)
      unfold sorts.apply_members_loop at IH
      simp only [uncurry, bind_ok]
      refine WP.spec_mono IH ?_
      rintro r ⟨hR, hr⟩
      refine ⟨(R3.trans hR).mono (by simp only [List.length_cons]; omega), ?_⟩
      split at hr
      · rename_i hok
        obtain ⟨ts, hts, rts⟩ := hr
        simp only [hok, ↓reduceIte]
        exact ⟨u :: ts, .cons hu hts, rts⟩
      · rename_i hok
        obtain ⟨c, hc, hcn⟩ := hr
        simp only [hok]
        exact ⟨c, List.mem_cons_of_mem _ hc, hcn⟩

theorem apply_members_spec (hnm : Function.Injective nm) {U : List Name}
    {M : Sorts.Conj → Option GTerm} (a : List Sorts.Conj) (s : store.Store)
    (f kids : store.TermId) (p : Pat) (hW : Wf s) (hM : MembersA nm s U M)
    (hs : ∀ c ∈ a, Sub U c) (hf : Repr nm s.nodes.val f.val p)
    (hk : Repr nm s.nodes.val kids.val (altPat (nm none) U a)) (hroom : Room s (3 * a.length + 1)) :
    sorts.apply_members s f kids ⦃ r =>
      Ran s r.2 (3 * a.length + 1) ∧
        match r.1 with
        | some ti => ∃ ts, List.Forall₂ (fun c t => M c = some t) a ts ∧
          Repr nm r.2.nodes.val ti.val (ts.foldl (fun acc t => .app acc (GTerm.toPat t)) p)
        | none => ∃ c ∈ a, M c = none ⦄ := by
  unfold sorts.apply_members
  step with apply_members_loop_spec hnm a s f kids p hW hM hs hf hk hroom as ⟨s1, term, ok1, hR, hr⟩
  cases ok1 with
  | true => simp only [↓reduceIte, WP.spec_ok]; exact ⟨hR, by simpa using hr⟩
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte, WP.spec_ok]
    exact ⟨hR, by simpa using hr⟩

/-! ## One root and the one member -/

theorem altOf_key_inj {S : Sorts} {d : Sorts.Conj} {f g : Sym} {k j : Nat}
    (h : ((f, altOf S d f k) : Alt) = (g, altOf S d g j)) : (f, k) = (g, j) := by
  have h₁ := congrArg Prod.fst h
  have h₂ := congrArg (fun a : Alt => a.2.length) h
  simp only [altOf, List.length_map, List.length_range] at h₁ h₂
  rw [h₁, h₂]

theorem lv_altOf {S : Sorts} {m : Sorts.Conj → Option Bool} {d : Sorts.Conj} {f : Sym} {k : Nat}
    (hL : ∀ c ∈ altOf S d f k, (m c = some true ↔ c ∈ Sorts.live S)) :
    Lv m (f, altOf S d f k) ↔ ∀ i < k, Sorts.kidC S d f k i ∈ Sorts.live S := by
  constructor
  · intro h i hi
    have hm : Sorts.kidC S d f k i ∈ altOf S d f k :=
      List.mem_map.2 ⟨i, List.mem_range.2 hi, rfl⟩
    exact (hL _ hm).1 (h _ hm)
  · intro h c hc
    have hc' : c ∈ altOf S d f k := hc
    obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hc'
    exact (hL _ hc').2 (h i (List.mem_range.1 hi))

/-- A root of members of a conjunction is an alternative of it all flagged
with yes. -/
theorem mem_liveKeys_iff {S : Sorts} {U : List Name} {m : Sorts.Conj → Option Bool}
    {d : Sorts.Conj} (hd : Sub U d)
    (hL : ∀ a ∈ dAlts S U d, ∀ k ∈ a.2, (m k = some true ↔ k ∈ Sorts.live S))
    (key : Sym × Nat) : key ∈ Sorts.liveKeys S d ↔
      (key.1, altOf S d key.1 key.2) ∈ dAlts S U d ∧ Lv m (key.1, altOf S d key.1 key.2) := by
  constructor
  · intro h
    obtain ⟨hkey, hacc, hkids⟩ := Finset.mem_filter.1 h
    have hmem : (key.1, altOf S d key.1 key.2) ∈ dAlts S U d :=
      (mem_dAlts hd).2 ⟨key, hkey, hacc, rfl⟩
    exact ⟨hmem, (lv_altOf (hL _ hmem)).2 hkids⟩
  · rintro ⟨hmem, hlv⟩
    obtain ⟨key', hkey, hacc, e⟩ := (mem_dAlts hd).1 hmem
    have : key = key' := by
      have := altOf_key_inj e
      exact Prod.ext (congrArg Prod.fst this) (congrArg Prod.snd this)
    subst this
    exact Finset.mem_filter.2 ⟨hkey, hacc, (lv_altOf (hL _ hmem)).1 hlv⟩

/-- When the alternatives all flagged with yes are one alternative and the
table has a member for each of its conjunctions, the conjunction has one
member. -/
theorem oneStep_of_sole {S : Sorts} {U : List Name} {m : Sorts.Conj → Option Bool}
    {M : Sorts.Conj → Option GTerm} {d : Sorts.Conj} (hd : Sub U d) (hnr : ¬ Sorts.RestOK S d)
    (hL : ∀ a ∈ dAlts S U d, ∀ k ∈ a.2, (m k = some true ↔ k ∈ Sorts.live S)) {a : Alt}
    {ts : List GTerm} (ha : soleOf m none (dAlts S U d) = some a)
    (hts : List.Forall₂ (fun c t => M c = some t) a.2 ts) :
    Sorts.OneStep S M d (Term.mk a.1 ts) := by
  obtain ⟨hmem, hlv, huniq⟩ := soleOf_none.1 ha
  obtain ⟨⟨f, k⟩, hkey, hacc, rfl⟩ := (mem_dAlts hd).1 hmem
  have hlen : ts.length = k := by
    have := hts.length_eq
    simpa [altOf] using this.symm
  subst hlen
  refine ⟨hnr, f, ts, ?_, ?_, rfl⟩
  · refine Finset.eq_singleton_iff_unique_mem.2
      ⟨(mem_liveKeys_iff hd hL (f, ts.length)).2 ⟨hmem, hlv⟩, fun key' hk' => ?_⟩
    obtain ⟨h₁, h₂⟩ := (mem_liveKeys_iff hd hL key').1 hk'
    have := altOf_key_inj (huniq _ h₁ h₂)
    exact Prod.ext (congrArg Prod.fst this) (congrArg Prod.snd this)
  · intro i hi
    have := (List.forall₂_iff_get.1 hts).2 i (by simpa [altOf] using hi) hi
    simpa [altOf] using this

/-- A conjunction a round would give a member has one alternative all
flagged with yes, and the table has a member for each of its conjunctions. -/
theorem sole_of_oneStep {S : Sorts} {U : List Name} {m : Sorts.Conj → Option Bool}
    {M : Sorts.Conj → Option GTerm} {d : Sorts.Conj} (hd : Sub U d)
    (hL : ∀ a ∈ dAlts S U d, ∀ k ∈ a.2, (m k = some true ↔ k ∈ Sorts.live S)) {t : GTerm}
    (h : Sorts.OneStep S M d t) :
    ∃ a, soleOf m none (dAlts S U d) = some a ∧ ∀ c ∈ a.2, M c ≠ none := by
  obtain ⟨-, f, ts, hk, hts, rfl⟩ := h
  have hin : (f, ts.length) ∈ Sorts.liveKeys S d := by rw [hk]; exact Finset.mem_singleton_self _
  obtain ⟨h₁, h₂⟩ := (mem_liveKeys_iff hd hL _).1 hin
  refine ⟨(f, altOf S d f ts.length), soleOf_none.2 ⟨h₁, h₂, fun x hx hlx => ?_⟩, ?_⟩
  · obtain ⟨key, hkey, hacc, rfl⟩ := (mem_dAlts hd).1 hx
    have := (mem_liveKeys_iff hd hL key).2 ⟨hx, hlx⟩
    rw [hk, Finset.mem_singleton] at this
    rw [this]
  · intro c hc
    have hc' : c ∈ altOf S d f ts.length := hc
    obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hc'
    rw [hts i (List.mem_range.1 hi)]
    exact Option.some_ne_none _

/-! ## One round -/

/-- What the rounds use of a conjunction with its alternatives: it has a sort
without a rest, the alternatives are its alternatives, and the flags of their
conjunctions say whether they have a member. -/
structure OneEntry (S : Sorts) (U : List Name) (m : Sorts.Conj → Option Bool) (e : Entry) :
    Prop where
  sub : Sub U e.1
  norest : ¬ Sorts.RestOK S e.1
  alts : e.2 = dAlts S U e.1
  subs : ∀ a ∈ e.2, ∀ c ∈ a.2, Sub U c
  live : ∀ a ∈ e.2, ∀ k ∈ a.2, (m k = some true ↔ k ∈ Sorts.live S)

/-- The second table has every member of the first. -/
def OneLe (M M' : Sorts.Conj → Option GTerm) : Prop := ∀ c t, M c = some t → M' c = some t

/-- No round gives a member to a conjunction of the list the table has none
for. -/
def OneStable (S : Sorts) (M : Sorts.Conj → Option GTerm) (G : List Entry) : Prop :=
  ∀ e ∈ G, M e.1 = none → ¬ ∃ t, Sorts.OneStep S M e.1 t

/-- The ticks one round may spend. -/
def passOneCost : List Entry → Nat
  | [] => 1
  | e :: G => 4 * anyCost e.2 + 6 + passOneCost G

theorem length_le_anyCost : ∀ l : List Alt, l.length ≤ anyCost l
  | [] => by simp [anyCost]
  | a :: l => by have := length_le_anyCost l; simp only [anyCost, List.length_cons]; omega

theorem alt_le_anyCost : ∀ {l : List Alt} {a : Alt}, a ∈ l → 2 * a.2.length + 3 ≤ anyCost l
  | [], _, h => by cases h
  | b :: l, a, h => by
    rcases List.mem_cons.1 h with rfl | h
    · simp only [anyCost]; omega
    · have := alt_le_anyCost h; simp only [anyCost]; omega

theorem passOneCost_le : ∀ G : List Entry, passOneCost G ≤ 4 * passCost G
  | [] => by simp [passOneCost, passCost]
  | e :: G => by have := passOneCost_le G; simp only [passOneCost, passCost]; omega

theorem pass_one_loop_spec (hnm : Function.Injective nm) (S : Sorts) {U : List Name}
    {m : Sorts.Conj → Option Bool} :
    ∀ (G : List Entry) (s : store.Store) (graph : store.TermId) (ch : Bool)
      (M : Sorts.Conj → Option GTerm), Wf s → FlagsB nm s U m → MembersA nm s U M →
    Sorts.OneSound S M → (∀ e ∈ G, OneEntry S U m e) →
    Repr nm s.nodes.val graph.val (graphPat (nm none) U G) → Room s (passOneCost G) →
    sorts.pass_one_loop graph s ch ⦃ r => ∃ M',
      RanB s r.2 (passOneCost G) ∧ FlagsB nm r.2 U m ∧ MembersA nm r.2 U M' ∧
        Sorts.OneSound S M' ∧ OneLe M M' ∧
        (r.1 = false → ch = false ∧ M' = M ∧ OneStable S M G) ∧
        (r.1 = true → ch = true ∨ ∃ e ∈ G, M e.1 = none ∧ M' e.1 ≠ none) ⦄ := by
  intro G
  induction G with
  | nil =>
    intro s graph ch M hW hF hM hSd hG hg hroom
    have hroom' := hroom
    unfold Room at hroom'
    simp only [passOneCost] at hroom'
    unfold sorts.pass_one_loop
    rw [loop]
    simp only [sorts.pass_one_loop.body]
    step with uncons_repr s graph hW hg (by unfold Room; omega) as ⟨r0, hK, hu⟩
    obtain ⟨o, s1⟩ := r0
    simp only [graphPat] at hu
    simp only at hK
    subst hu
    have hfin : ∃ M', RanB s s1 (passOneCost []) ∧ FlagsB nm s1 U m ∧ MembersA nm s1 U M' ∧
        Sorts.OneSound S M' ∧ OneLe M M' ∧ (ch = false → ch = false ∧ M' = M ∧ OneStable S M []) ∧
        (ch = true → ch = true ∨ ∃ e ∈ ([] : List Entry), M e.1 = none ∧ M' e.1 ≠ none) :=
      ⟨M, hK.ran.ranB, hF.mono hK.ran.ext (by rw [hK.tbl]), hM.mono hK.ran.ext (by rw [hK.tbl]),
        hSd, fun _ _ h => h, fun h => ⟨h, rfl, fun e he => by cases he⟩, fun h => Or.inl h⟩
    step*
  | cons e G ih =>
    intro s graph ch M hW hF hM hSd hG hg hroom
    have hroom' := hroom
    unfold Room at hroom'
    simp only [passOneCost] at hroom'
    have hE := hG e List.mem_cons_self
    have hGt : ∀ e' ∈ G, OneEntry S U m e' := fun e' he' => hG e' (List.mem_cons_of_mem _ he')
    have hL : ∀ a ∈ dAlts S U e.1, ∀ k ∈ a.2, (m k = some true ↔ k ∈ Sorts.live S) := by
      rw [← hE.alts]; exact hE.live
    have hlen := length_le_anyCost e.2
    unfold sorts.pass_one_loop
    rw [loop]
    simp only [sorts.pass_one_loop.body]
    step with uncons_repr s graph hW hg (by unfold Room; omega) as ⟨r0, hK, hu⟩
    obtain ⟨o, s1⟩ := r0
    simp only [graphPat] at hu
    simp only at hK
    obtain ⟨en, t, rfl, ren, rt⟩ := hu
    have ht1 := hK.ticks
    step with uncons_repr s1 en hK.wf (by rw [hK.nodes]; exact ren) (by unfold Room; omega)
      as ⟨r1, hK2, hu2⟩
    obtain ⟨o1, s2⟩ := r1
    simp only [entryPat] at hu2
    simp only at hK2
    obtain ⟨d, alts, rfl, rd, ralts⟩ := hu2
    rw [hK.nodes] at rd ralts
    have ht2 := hK2.ticks
    have hn2 : s2.nodes.val = s.nodes.val := by rw [hK2.nodes, hK.nodes]
    step with get_w s2 .A d hK2.wf (by rw [hn2]; exact rd.lt) (by unfold Room; omega)
      as ⟨r2, hg2, hK3⟩
    obtain ⟨o2, s3⟩ := r2
    simp only at hg2 hK3
    rw [hK2.tbl, hK.tbl] at hg2
    have ht3 := hK3.ticks
    have R3 : Ran s s3 3 := (hK.ran.trans hK2.ran).trans hK3.ran
    -- the rest of the round
    have rest : ∀ (s' : store.Store) (ch' : Bool) (M₁ : Sorts.Conj → Option GTerm) (k : Nat),
        RanB s s' k → k ≤ 4 * anyCost e.2 + 6 → FlagsB nm s' U m → MembersA nm s' U M₁ →
        Sorts.OneSound S M₁ → OneLe M M₁ →
        (ch' = false → ch = false ∧ M₁ = M ∧ (M e.1 = none → ¬ ∃ t, Sorts.OneStep S M e.1 t)) →
        (ch' = true → ch = true ∨ (M e.1 = none ∧ M₁ e.1 ≠ none)) →
        loop (fun x => match x with
          | (graph1, s1, changed1) => sorts.pass_one_loop.body graph1 s1 changed1)
          (t, s', ch') ⦃ r => ∃ M',
          RanB s r.2 (passOneCost (e :: G)) ∧ FlagsB nm r.2 U m ∧ MembersA nm r.2 U M' ∧
            Sorts.OneSound S M' ∧ OneLe M M' ∧
            (r.1 = false → ch = false ∧ M' = M ∧ OneStable S M (e :: G)) ∧
            (r.1 = true → ch = true ∨ ∃ e' ∈ e :: G, M e'.1 = none ∧ M' e'.1 ≠ none) ⦄ := by
      intro s' ch' M₁ k R0 hk hF' hM' hS' hLe hst hflip
      have htk' := R0.ticks
      have IH := ih s' t ch' M₁ R0.wf hF' hM' hS' hGt (R0.ext.repr rt) (by unfold Room; omega)
      unfold sorts.pass_one_loop at IH
      refine WP.spec_mono IH ?_
      rintro r ⟨M', hR, hFm, hMm, hSm, hLm, hs, hf⟩
      refine ⟨M', (R0.trans hR).mono (by simp only [passOneCost]; omega), hFm, hMm, hSm,
        fun c u h => hLm c u (hLe c u h), ?_, ?_⟩
      · intro hr
        obtain ⟨hc', hMM, hstG⟩ := hs hr
        obtain ⟨hc, hM1, hse⟩ := hst hc'
        subst hM1
        refine ⟨hc, hMM, fun e' he' => ?_⟩
        rcases List.mem_cons.1 he' with rfl | he'
        · exact hse
        · exact hstG e' he'
      · intro hr
        rcases hf hr with hc' | ⟨e', he', h₁, h₂⟩
        · rcases hflip hc' with hc | ⟨h₁, h₂⟩
          · exact Or.inl hc
          · refine Or.inr ⟨e, List.mem_cons_self, h₁, ?_⟩
            obtain ⟨u, hu⟩ := Option.ne_none_iff_exists'.1 h₂
            rw [hLm _ _ hu]; exact Option.some_ne_none _
        · refine Or.inr ⟨e', List.mem_cons_of_mem _ he', ?_, h₂⟩
          by_contra hne
          obtain ⟨u, hu⟩ := Option.ne_none_iff_exists'.1 hne
          rw [hLe _ _ hu] at h₁; cases h₁
    have hF3 : FlagsB nm s3 U m := hF.mono R3.ext (by rw [R3.tbl])
    have hM3 : MembersA nm s3 U M := hM.mono R3.ext (by rw [R3.tbl])
    cases o2 with
    | some j =>
      obtain ⟨u, hu, -⟩ := hM.get_some hE.sub rd (by simpa using hg2.symm)
      simp only [uncurry, bind_ok]
      exact rest s3 ch M 3 R3.ranB (by omega) hF3 hM3 hSd (fun _ _ h => h)
        (fun h => ⟨h, rfl, fun h0 => by rw [hu] at h0; cases h0⟩) (fun h => Or.inl h)
    | none =>
      have hMe : M e.1 = none := hM.get_none hnm hW rd (by simpa using hg2.symm)
      simp only [uncurry]
      step with sole_alt_spec hnm e.2 s3 alts hK3.wf hF3 hE.subs (R3.ext.repr ralts)
        (by unfold Room; simp only [soleCost]; omega) as ⟨r4, hR4, hA⟩
      obtain ⟨o3, s4⟩ := r4
      simp only at hR4 hA
      have ht4 := hR4.ticks
      simp only [soleCost] at ht4
      have R4 : Ran s s4 (anyCost e.2 + e.2.length + 3) := (R3.trans hR4).mono (by
        simp only [soleCost]; omega)
      have hF4 : FlagsB nm s4 U m := hF.mono R4.ext (by rw [R4.tbl])
      have hM4 : MembersA nm s4 U M := hM.mono R4.ext (by rw [R4.tbl])
      cases hsol : soleOf m none e.2 with
      | none =>
        rw [hsol] at hA
        cases o3 with
        | some ai => simp [AltAt] at hA
        | none =>
          simp only [uncurry, bind_ok]
          exact rest s4 ch M _ R4.ranB (by omega) hF4 hM4 hSd (fun _ _ h => h)
            (fun h => ⟨h, rfl, fun _ ⟨u, hu⟩ => by
              obtain ⟨a, ha, -⟩ := sole_of_oneStep hE.sub hL hu
              rw [← hE.alts, hsol] at ha; cases ha⟩) (fun h => Or.inl h)
      | some a =>
        rw [hsol] at hA
        cases o3 with
        | none => simp [AltAt] at hA
        | some ai =>
          simp only [AltAt] at hA
          have hae : a ∈ e.2 := (soleOf_none.1 hsol).1
          have hka := alt_le_anyCost hae
          simp only [uncurry]
          step with uncons_repr s4 ai hR4.wf hA (by unfold Room; omega) as ⟨r5, hK5, hu5⟩
          obtain ⟨o4, s5⟩ := r5
          simp only [kaltPat] at hu5
          simp only at hK5
          obtain ⟨f, kids, rfl, rf, rkids⟩ := hu5
          have ht5 := hK5.ticks
          have R5 : Ran s s5 (anyCost e.2 + e.2.length + 4) := (R4.trans hK5.ran).mono (by omega)
          step with apply_members_spec hnm a.2 s5 f kids (.sym a.1) hK5.wf
            (hM.mono R5.ext (by rw [R5.tbl])) (hE.subs a hae) (by rw [hK5.nodes]; exact rf)
            (by rw [hK5.nodes]; exact rkids) (by unfold Room; omega) as ⟨r6, hR6, hres⟩
          obtain ⟨o5, s6⟩ := r6
          simp only at hR6 hres
          have ht6 := hR6.ticks
          have R6 : Ran s s6 (anyCost e.2 + e.2.length + 3 * a.2.length + 5) :=
            (R5.trans hR6).mono (by omega)
          have hF6 : FlagsB nm s6 U m := hF.mono R6.ext (by rw [R6.tbl])
          have hM6 : MembersA nm s6 U M := hM.mono R6.ext (by rw [R6.tbl])
          cases o5 with
          | none =>
            obtain ⟨c, hc, hcn⟩ := hres
            simp only [uncurry, bind_ok]
            exact rest s6 ch M _ R6.ranB (by omega) hF6 hM6 hSd (fun _ _ h => h)
              (fun h => ⟨h, rfl, fun _ ⟨u, hu⟩ => by
                obtain ⟨a', ha', hall⟩ := sole_of_oneStep (M := M) hE.sub hL hu
                rw [← hE.alts, hsol] at ha'; cases ha'
                exact hall c hc hcn⟩) (fun h => Or.inl h)
          | some mi =>
            obtain ⟨ts, hts, rmi⟩ := hres
            rw [← toPat_mk] at rmi
            have hstep : Sorts.OneStep S M e.1 (Term.mk a.1 ts) :=
              oneStep_of_sole hE.sub hE.norest hL (by rw [← hE.alts]; exact hsol) hts
            simp only [uncurry]
            step with set_w s6 .A d mi hR6.wf (R6.ext.repr rd).lt (by unfold Room; omega)
              as ⟨s7, hn7, ht7, hW7, htb7, htbo7, hst7⟩
            have hx67 : Extends s6 s7 := Extends.of_eq hn7 (by omega)
            have R7 : RanB s s7 (anyCost e.2 + e.2.length + 3 * a.2.length + 6) :=
              ⟨hW7, R6.ext.trans hx67, by rw [hst7, R6.stk], by have := R6.ticks; omega⟩
            have hF7 : FlagsB nm s7 U m :=
              hF6.mono hx67 (htbo7 .B (by intro h; cases h))
            have hM7 := hM6.set hnm hR6.wf hE.sub (R6.ext.repr rd) rmi hn7 htb7
            have hS7 : Sorts.OneSound S (Function.update M e.1 (some (Term.mk a.1 ts))) := by
              intro c u hc
              by_cases hce : c = e.1
              · subst hce
                rw [Function.update_self] at hc
                cases hc
                exact hstep.sound hSd
              · rw [Function.update_of_ne hce] at hc
                exact hSd c u hc
            have hLe7 : OneLe M (Function.update M e.1 (some (Term.mk a.1 ts))) := by
              intro c u hc
              have hce : c ≠ e.1 := by rintro rfl; rw [hMe] at hc; cases hc
              rw [Function.update_of_ne hce]; exact hc
            exact rest s7 true _ _ R7 (by omega) hF7 hM7 hS7 hLe7 (fun h => by cases h)
              (fun _ => Or.inr ⟨hMe, by simp⟩)

theorem pass_one_spec (hnm : Function.Injective nm) (S : Sorts) {U : List Name}
    {m : Sorts.Conj → Option Bool} (G : List Entry) (s : store.Store) (graph : store.TermId)
    (M : Sorts.Conj → Option GTerm) (hW : Wf s) (hF : FlagsB nm s U m) (hM : MembersA nm s U M)
    (hSd : Sorts.OneSound S M) (hG : ∀ e ∈ G, OneEntry S U m e)
    (hg : Repr nm s.nodes.val graph.val (graphPat (nm none) U G)) (hroom : Room s (passOneCost G)) :
    sorts.pass_one s graph ⦃ r => ∃ M',
      RanB s r.2 (passOneCost G) ∧ FlagsB nm r.2 U m ∧ MembersA nm r.2 U M' ∧
        Sorts.OneSound S M' ∧ OneLe M M' ∧ (r.1 = false → M' = M ∧ OneStable S M G) ∧
        (r.1 = true → ∃ e ∈ G, M e.1 = none ∧ M' e.1 ≠ none) ⦄ := by
  refine WP.spec_mono (pass_one_loop_spec hnm S G s graph false M hW hF hM hSd hG hg hroom) ?_
  rintro r ⟨M', hR, hFm, hMm, hSm, hLm, hs, hf⟩
  exact ⟨M', hR, hFm, hMm, hSm, hLm, fun h => (hs h).2, fun h => (hf h).resolve_left (by simp)⟩

/-! ## The rounds -/

/-- The conjunctions of the graph the table has no member for. -/
noncomputable def nones (G : List Entry) (M : Sorts.Conj → Option GTerm) : Nat :=
  ((G.map Prod.fst).toFinset.filter fun c => M c = none).card

theorem nones_lt {G : List Entry} {M M' : Sorts.Conj → Option GTerm} (hLe : OneLe M M')
    {e : Entry} (he : e ∈ G) (h₁ : M e.1 = none) (h₂ : M' e.1 ≠ none) :
    nones G M' < nones G M := by
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_of_subset]
  · refine ⟨e.1, ?_, ?_⟩
    · simp only [Finset.mem_filter, List.mem_toFinset, List.mem_map]
      exact ⟨⟨e, he, rfl⟩, h₁⟩
    · simp [h₂]
  · intro c hc
    simp only [Finset.mem_filter] at hc ⊢
    refine ⟨hc.1, ?_⟩
    by_contra hne
    obtain ⟨u, hu⟩ := Option.ne_none_iff_exists'.1 hne
    rw [hLe _ _ hu] at hc
    exact Option.some_ne_none _ hc.2

theorem nones_le (G : List Entry) (M : Sorts.Conj → Option GTerm) : nones G M ≤ G.length := by
  unfold nones
  refine (Finset.card_filter_le _ _).trans ?_
  exact (List.toFinset_card_le _).trans (by simp)

theorem count_loop_done (s : store.Store) (graph : store.TermId) :
    sorts.count_loop s graph false ⦃ r => r = s ⦄ := by
  unfold sorts.count_loop
  rw [loop]
  simp only [sorts.count_loop.body, Bool.false_eq_true, ↓reduceIte, bind_ok]
  step*

theorem count_loop_spec (hnm : Function.Injective nm) (S : Sorts) {U : List Name}
    {m : Sorts.Conj → Option Bool} (G : List Entry) (graph : store.TermId)
    (hG : ∀ e ∈ G, OneEntry S U m e) :
    ∀ (n : Nat) (s : store.Store) (M : Sorts.Conj → Option GTerm), nones G M < n → Wf s →
    FlagsB nm s U m → MembersA nm s U M → Sorts.OneSound S M →
    Repr nm s.nodes.val graph.val (graphPat (nm none) U G) → Room s (n * passOneCost G) →
    sorts.count_loop s graph true ⦃ s' => ∃ M',
      RanB s s' (n * passOneCost G) ∧ MembersA nm s' U M' ∧ Sorts.OneSound S M' ∧
        OneStable S M' G ⦄ := by
  intro n
  induction n with
  | zero => intro s M h; cases h
  | succ n ih =>
    intro s M hlt hW hF hM hSd hg hroom
    have hroom' := hroom
    unfold Room at hroom'
    rw [Nat.add_mul, Nat.one_mul] at hroom'
    unfold sorts.count_loop
    rw [loop]
    simp only [sorts.count_loop.body, ↓reduceIte]
    step with pass_one_spec hnm S G s graph M hW hF hM hSd hG hg (by unfold Room; omega)
      as ⟨r1, M₁, hR, hF₁, hM₁, hS₁, hLe, hs, hf⟩
    obtain ⟨go1, s1⟩ := r1
    simp only at hR hF₁ hM₁ hs hf
    have ht1 := hR.ticks
    cases go1 with
    | false =>
      obtain ⟨rfl, hst⟩ := hs rfl
      have hdn := count_loop_done s1 graph
      unfold sorts.count_loop at hdn
      simp only [uncurry, bind_ok]
      refine WP.spec_mono hdn ?_
      rintro r rfl
      exact ⟨M₁, hR.mono (by rw [Nat.add_mul, Nat.one_mul]; omega), hM₁, hS₁, hst⟩
    | true =>
      obtain ⟨e, he, h₁, h₂⟩ := hf rfl
      have hlt' : nones G M₁ < n := by
        have := nones_lt hLe he h₁ h₂; omega
      have IH := ih s1 M₁ hlt' hR.wf hF₁ hM₁ hS₁ (hR.ext.repr hg) (by unfold Room; omega)
      unfold sorts.count_loop at IH
      simp only [uncurry, bind_ok]
      refine WP.spec_mono IH ?_
      rintro r ⟨M', hR', hM', hS', hst⟩
      exact ⟨M', (hR.trans hR').mono (by rw [Nat.add_mul, Nat.one_mul]; omega), hM', hS', hst⟩

/-! ## How many members -/

/-- The ticks counting the members of a conjunction that reaches `r`
conjunctions may spend, with `u` names. -/
def countCost (S : Sorts) (u r : Nat) : Nat :=
  flagCost S u r + (r + 1) * (4 * (r * (u * altW S + 5) + 1)) + 3

/-- `count` answers how many members the conjunction has (`Sorts.count`),
with the member when there is one. It spends a number of ticks that is
polynomial in the size of the sorts and in the number of conjunctions the
conjunction reaches. -/
theorem count_spec {S : Sorts} {sp : Pat} {U : List Name} (hC : Ctx nm S sp U)
    (c₀ : Sorts.Conj) (hc : Sub U c₀) (s : store.Store) (decls names ci : store.TermId)
    (hI : Inv s) (hde : Repr nm s.nodes.val decls.val sp)
    (hU : Repr nm s.nodes.val names.val (namesPat (nm none) U))
    (hci : Repr nm s.nodes.val ci.val (cpat (nm none) U c₀))
    (hroom : Room s (countCost S U.length (Sorts.reachSet S c₀).card)) :
    sorts.count s decls names ci ⦃ r s' =>
      Inv s' ∧ Extends s s' ∧
        s'.ticks.val ≤ s.ticks.val + countCost S U.length (Sorts.reachSet S c₀).card ∧
        match r with
        | .None => Sorts.count S c₀ = .none
        | .One ti => ∃ t, Sorts.count S c₀ = .one t ∧ Repr nm s'.nodes.val ti.val (GTerm.toPat t)
        | .Many => Sorts.count S c₀ = .many ⦄ := by
  unfold sorts.count
  have hroom' := hroom
  unfold Room at hroom'
  simp only [countCost] at hroom'
  step with flag_live_spec hC c₀ hc s decls names ci hI hde hU hci (by unfold Room; omega)
    as ⟨graph, s3, m, m', G, Dn, R3, hF3, rg, hInv, hsub, hLe, hS3, hst, hpc⟩
  have ht3 := R3.ticks
  have rci := R3.ext.repr hci
  step with get_flag_w s3 .B ci R3.wf rci.lt (by unfold Room; omega) as ⟨o, s4, hfl4, hK4⟩
  have ht4 := hK4.ticks
  have R4 : RanB s s4 (flagCost S U.length (Sorts.reachSet S c₀).card + 1) :=
    ⟨hK4.wf, R3.ext.trans hK4.ran.ext, by rw [hK4.stk, R3.stk], by omega⟩
  have ho : o = m' c₀ := by
    rw [hfl4]
    have := hF3.get hC.inj R3.wf hc rci
    simpa only [flagB, flagT] using this
  have hiff := hInv.live_iff hsub hLe hS3 hst .refl
  rw [← ho] at hiff
  have hnone : o ≠ some true → Inv s4 ∧ Extends s s4 ∧
      s4.ticks.val ≤ s.ticks.val + countCost S U.length (Sorts.reachSet S c₀).card ∧
      Sorts.count S c₀ = .none := fun hne =>
    ⟨R4.inv hI, R4.ext, by have := R4.ticks; simp only [countCost]; omega,
      Sorts.count_none.2 fun hm => hne (hiff.2 (Sorts.mem_live_iff.2 hm))⟩
  cases o with
  | none => simp only [WP.spec_ok]; exact hnone (by simp)
  | some b =>
    cases b with
    | false => simp only [Bool.false_eq_true, ↓reduceIte, WP.spec_ok]; exact hnone (by simp)
    | true =>
      have hlive : c₀ ∈ Sorts.live S := hiff.1 rfl
      simp only [↓reduceIte]
      step with clear_w s4 .A hK4.wf (by unfold Room; omega) as ⟨s5, hn5, ht5, hW5, hcl, hoth, hst5⟩
      have hx45 : Extends s4 s5 := Extends.of_eq hn5 (by omega)
      have R5 : RanB s s5 (flagCost S U.length (Sorts.reachSet S c₀).card + 2) :=
        ⟨hW5, R4.ext.trans hx45, by rw [hst5, R4.stk], by have := R4.ticks; omega⟩
      have hF5 : FlagsB nm s5 U m' :=
        (hF3.mono hK4.ran.ext (by rw [hK4.tbl])).mono hx45 (hoth .B (by intro h; cases h))
      have hM5 : MembersA nm s5 U fun _ => none :=
        ⟨fun c t h => (by cases h), fun i j h => (by rw [hcl] at h; cases h)⟩
      have hS5 : Sorts.OneSound S fun _ => none := fun c t h => by cases h
      have hEok := hInv.entryOK hC hsub
      have hG : ∀ e ∈ G, OneEntry S U m' e := by
        intro e he
        obtain ⟨hd, hal⟩ := hInv.graph e he
        have hnr := hInv.norest e he
        have hre : Sorts.Reach S c₀ e.1 := hInv.reach e.1 ((hInv.dom e.1).2 (Or.inr hd))
        refine ⟨hsub _ hd, hnr, hal, fun a ha => ((hEok e he).2 a ha).1, fun a ha k hk => ?_⟩
        rw [hal] at ha
        obtain ⟨key, hkey, hacc, rfl⟩ := (mem_dAlts (hsub _ hd)).1 ha
        have hk' : k ∈ altOf S e.1 key.1 key.2 := hk
        obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hk'
        exact hInv.live_iff hsub hLe hS3 hst
          (hre.step ⟨hnr, key, hkey, hacc, i, List.mem_range.1 hi, rfl⟩)
      have hGl : G.length ≤ (Sorts.reachSet S c₀).card := hInv.glen.trans hInv.len_le
      have hn0 : nones G (fun _ => none) + 1 ≤ (Sorts.reachSet S c₀).card + 1 := by
        have := nones_le G fun _ => none; omega
      have hpo : passOneCost G ≤ 4 * ((Sorts.reachSet S c₀).card * (U.length * altW S + 5) + 1) := by
        have := passOneCost_le G; omega
      have hloop : (nones G (fun _ => none) + 1) * passOneCost G ≤
          ((Sorts.reachSet S c₀).card + 1) *
            (4 * ((Sorts.reachSet S c₀).card * (U.length * altW S + 5) + 1)) :=
        Nat.mul_le_mul hn0 hpo
      step with count_loop_spec hC.inj S G graph hG (nones G (fun _ => none) + 1) s5
        (fun _ => none) (Nat.lt_succ_self _) hW5 hF5 hM5 hS5 (hx45.repr (hK4.ran.ext.repr rg)) (by unfold Room; omega)
        as ⟨s6, M', hR6, hM6, hS6, hst6⟩
      have ht6 := hR6.ticks
      have R6 := R5.trans hR6
      have rci6 := R6.ext.repr hci
      step with get_w s6 .A ci hR6.wf rci6.lt (by unfold Room; omega) as ⟨o1, s7, hg7, hK7⟩
      have ht7 := hK7.ticks
      have hfin : Inv s7 ∧ Extends s s7 ∧
          s7.ticks.val ≤ s.ticks.val + countCost S U.length (Sorts.reachSet S c₀).card :=
        ⟨⟨hK7.wf, by rw [hK7.stk, R6.stk]; exact hI.empty⟩, R6.ext.trans hK7.ran.ext, by
          have := R6.ticks; simp only [countCost]; omega⟩
      have hstable : ∀ c t, Sorts.Reach S c₀ c → Sorts.OneStep S M' c t → (M' c).isSome = true := by
        intro c t hrc hos
        have hcd := hInv.reached hsub hrc
        rcases hInv.done c hcd with ⟨h₁, -⟩ | ⟨-, hGc, -⟩
        · exact absurd h₁ hos.1
        · by_contra hne
          have : M' c = none := by simpa using hne
          exact hst6 _ hGc this ⟨t, hos⟩
      cases o1 with
      | none =>
        have hMc : M' c₀ = none := hM6.get_none hC.inj hR6.wf rci6 (by simpa using hg7.symm)
        have := Sorts.count_ne_one_of_stable hS6 hstable hMc
        simp only [hlive, ↓reduceIte] at this
        simp only [WP.spec_ok]
        exact ⟨hfin.1, hfin.2.1, hfin.2.2, this⟩
      | some mi =>
        obtain ⟨t, htc, rmi⟩ := hM6.get_some hc rci6 (by simpa using hg7.symm)
        simp only [WP.spec_ok]
        exact ⟨hfin.1, hfin.2.1, hfin.2.2, t, (Sorts.count_one_iff_of_stable hS6 hstable t).1 htc,
          by rw [hK7.nodes]; exact rmi⟩

end RwLogVerified
