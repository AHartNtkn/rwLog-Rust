/-
# Every name of the declarations, on the store

`names` (`rust/src/sorts.rs`) lists every name the declarations declare or
say of an argument, each once. This file proves it against `namesList`, a
list with no repeat whose members are `Sorts.names`.

Table `A` flags the names already listed (`FlagAcc`).
-/
import RwLogVerified.Conj
import RwLog.Sorts.Empty

open Aeneas Aeneas.Std Result

namespace RwLogVerified

open rwlog_core RwLog

variable {nm : Option Nat → RwLog.Sym}

/-! ## The list, in the specification -/

/-- Put a sort in front of the list unless the list has it. Any term is not
a sort. -/
def noteKid (acc : List Name) : Option Name → List Name
  | none => acc
  | some m => if m ∈ acc then acc else m :: acc

def noteKids (acc : List Name) (ks : List (Option Name)) : List Name := ks.foldl noteKid acc

def noteCases (acc : List Name) (cs : List (Sym × List (Option Name))) : List Name :=
  cs.foldl (fun a c => noteKids a c.2) acc

def noteDef (acc : List Name) (d : Name × SortDef) : List Name :=
  match d.2.rest with
  | none => noteCases (noteKid acc (some d.1)) d.2.cases
  | some r => noteKid (noteCases (noteKid acc (some d.1)) d.2.cases) r.2

/-- Every name declared or said of an argument, each once: the first to
occur comes last. -/
def namesList (S : Sorts) : List Name := S.foldl noteDef []

theorem mem_noteKid {acc : List Name} {k : Option Name} {n : Name} :
    n ∈ noteKid acc k ↔ n ∈ acc ∨ k = some n := by
  cases k with
  | none => simp [noteKid]
  | some m =>
    simp only [noteKid, Option.some.injEq]
    by_cases h : m ∈ acc
    · simp only [h, ↓reduceIte]
      constructor
      · exact Or.inl
      · rintro (h' | rfl)
        · exact h'
        · exact h
    · simp only [h, ↓reduceIte, List.mem_cons]
      constructor
      · rintro (rfl | h')
        · exact Or.inr rfl
        · exact Or.inl h'
      · rintro (h' | rfl)
        · exact Or.inr h'
        · exact Or.inl rfl

theorem nodup_noteKid {acc : List Name} (h : acc.Nodup) (k : Option Name) :
    (noteKid acc k).Nodup := by
  cases k with
  | none => exact h
  | some m =>
    simp only [noteKid]
    by_cases hm : m ∈ acc
    · simpa [hm] using h
    · simpa [hm] using h

theorem mem_noteKids {n : Name} : ∀ {ks : List (Option Name)} {acc : List Name},
    n ∈ noteKids acc ks ↔ n ∈ acc ∨ some n ∈ ks
  | [], acc => by simp [noteKids]
  | k :: ks, acc => by
    have := mem_noteKids (n := n) (ks := ks) (acc := noteKid acc k)
    simp only [noteKids, List.foldl_cons] at this ⊢
    rw [this, mem_noteKid, List.mem_cons]
    constructor
    · rintro ((h | h) | h)
      · exact Or.inl h
      · exact Or.inr (Or.inl h.symm)
      · exact Or.inr (Or.inr h)
    · rintro (h | h | h)
      · exact Or.inl (Or.inl h)
      · exact Or.inl (Or.inr h.symm)
      · exact Or.inr h

theorem nodup_noteKids : ∀ {ks : List (Option Name)} {acc : List Name}, acc.Nodup →
    (noteKids acc ks).Nodup
  | [], _, h => h
  | k :: ks, acc, h => by
    simp only [noteKids, List.foldl_cons]
    exact nodup_noteKids (ks := ks) (nodup_noteKid h k)

theorem mem_noteCases {n : Name} : ∀ {cs : List (Sym × List (Option Name))} {acc : List Name},
    n ∈ noteCases acc cs ↔ n ∈ acc ∨ ∃ c ∈ cs, some n ∈ c.2
  | [], acc => by simp [noteCases]
  | c :: cs, acc => by
    have := mem_noteCases (n := n) (cs := cs) (acc := noteKids acc c.2)
    simp only [noteCases, List.foldl_cons] at this ⊢
    rw [this, mem_noteKids]
    simp only [List.mem_cons, exists_eq_or_imp]
    tauto

theorem nodup_noteCases : ∀ {cs : List (Sym × List (Option Name))} {acc : List Name},
    acc.Nodup → (noteCases acc cs).Nodup
  | [], _, h => h
  | c :: cs, acc, h => by
    simp only [noteCases, List.foldl_cons]
    exact nodup_noteCases (cs := cs) (nodup_noteKids h)

theorem mem_noteDef {n : Name} {acc : List Name} {d : Name × SortDef} :
    n ∈ noteDef acc d ↔ n ∈ acc ∨ n = d.1 ∨ n ∈ d.2.kidNames := by
  have hk : n ∈ d.2.kidNames ↔
      (∃ c ∈ d.2.cases, some n ∈ c.2) ∨ ∃ r, d.2.rest = some r ∧ r.2 = some n := by
    simp only [SortDef.kidNames, List.mem_append, List.mem_flatMap, List.mem_filterMap, id,
      exists_eq_right, Option.mem_toList, Option.bind_eq_some_iff]
  rw [hk]
  unfold noteDef
  cases hr : d.2.rest with
  | none =>
    simp only [mem_noteCases, mem_noteKid, Option.some.injEq, reduceCtorEq, false_and,
      exists_false, or_false]
    constructor
    · rintro ((h | h) | h)
      · exact Or.inl h
      · exact Or.inr (Or.inl h.symm)
      · exact Or.inr (Or.inr h)
    · rintro (h | h | h)
      · exact Or.inl (Or.inl h)
      · exact Or.inl (Or.inr h.symm)
      · exact Or.inr h
  | some r =>
    simp only [mem_noteCases, mem_noteKid, Option.some.injEq, exists_eq_left']
    constructor
    · rintro (((h | h) | h) | h)
      · exact Or.inl h
      · exact Or.inr (Or.inl h.symm)
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inr (Or.inr (Or.inr h))
    · rintro (h | h | h | h)
      · exact Or.inl (Or.inl (Or.inl h))
      · exact Or.inl (Or.inl (Or.inr h.symm))
      · exact Or.inl (Or.inr h)
      · exact Or.inr h

theorem nodup_noteDef {acc : List Name} (h : acc.Nodup) (d : Name × SortDef) :
    (noteDef acc d).Nodup := by
  unfold noteDef
  cases d.2.rest with
  | none => exact nodup_noteCases (nodup_noteKid h _)
  | some r => exact nodup_noteKid (nodup_noteCases (nodup_noteKid h _)) _

theorem mem_foldl_noteDef {n : Name} : ∀ {S : Sorts} {acc : List Name},
    n ∈ S.foldl noteDef acc ↔ n ∈ acc ∨ ∃ d ∈ S, n = d.1 ∨ n ∈ d.2.kidNames
  | [], acc => by simp
  | d :: S, acc => by
    rw [List.foldl_cons, mem_foldl_noteDef (S := S), mem_noteDef]
    simp only [List.mem_cons, exists_eq_or_imp, or_assoc]

theorem nodup_foldl_noteDef : ∀ {S : Sorts} {acc : List Name}, acc.Nodup →
    (S.foldl noteDef acc).Nodup
  | [], _, h => h
  | d :: S, acc, h => by
    rw [List.foldl_cons]
    exact nodup_foldl_noteDef (S := S) (nodup_noteDef h d)

/-- The members of the list are the names declared or said of an argument. -/
theorem mem_namesList {S : Sorts} {n : Name} : n ∈ namesList S ↔ n ∈ Sorts.names S := by
  simp only [namesList, mem_foldl_noteDef, List.not_mem_nil, false_or, Sorts.names,
    List.mem_toFinset, List.mem_flatMap, List.mem_cons]

theorem nodup_namesList (S : Sorts) : (namesList S).Nodup := nodup_foldl_noteDef List.nodup_nil

/-! ## The flags of the names already listed -/

/-- Table `A` flags exactly the symbols of the list. -/
def FlagAcc (nm : Option Nat → RwLog.Sym) (s : store.Store) (acc : List Name) : Prop :=
  ∀ i n, Repr nm s.nodes.val i (.sym n) → ((tbl s .A i).isSome ↔ n ∈ acc)

theorem FlagAcc.kept {s s' : store.Store} {acc : List Name} (h : FlagAcc nm s acc)
    (hn : s'.nodes.val = s.nodes.val) (ht : tbl s' .A = tbl s .A) : FlagAcc nm s' acc := by
  intro i n hi
  rw [ht]
  exact h i n (by rw [← hn]; exact hi)

/-- Nodes added to the store are not flagged, and are not symbols of the
list, whose members the store already had. -/
theorem FlagAcc.mono (hnm : Function.Injective nm) {s s' : store.Store} {acc : List Name}
    (h : FlagAcc nm s acc) (hW : Wf s) (hW' : Wf s') (hx : Extends s s')
    (ht : tbl s' .A = tbl s .A) (hacc : ∀ n ∈ acc, ∃ j, Repr nm s.nodes.val j (.sym n)) :
    FlagAcc nm s' acc := by
  intro i n hi
  rw [ht]
  obtain ⟨more, hmore, -⟩ := hx
  by_cases hlt : i < s.nodes.val.length
  · have hget : s'.nodes.val[i]? = s.nodes.val[i]? := by
      rw [hmore, List.getElem?_append_left hlt]
    have hi0 : Repr nm s.nodes.val i (.sym n) := by
      rcases hi.sym_node with ⟨h1, rfl⟩ | ⟨f, h1, rfl⟩
      · exact .nil (by rw [← hget]; exact h1)
      · exact .sym (by rw [← hget]; exact h1)
    exact h i n hi0
  · have hnone : tbl s .A i = none := by
      have : s.slots.val[i]? = none :=
        List.getElem?_eq_none (by rw [hW.shape.slots]; omega)
      simp [tbl, this]
    rw [hnone]
    constructor
    · intro hh; cases hh
    · intro hn
      obtain ⟨j, hj⟩ := hacc n hn
      have hj' : Repr nm s'.nodes.val j (.sym n) := by rw [hmore]; exact hj.append more
      have := Repr.inj hnm hW'.nodesOK hi hj'
      have := hj.lt
      omega

theorem FlagAcc.set (hnm : Function.Injective nm) {s s' : store.Store} {acc : List Name}
    (h : FlagAcc nm s acc) (hW : Wf s) (hn : s'.nodes.val = s.nodes.val) {k v : Nat}
    (ht : tbl s' .A = Function.update (tbl s .A) k (some v)) {n : Name}
    (hk : Repr nm s.nodes.val k (.sym n)) : FlagAcc nm s' (n :: acc) := by
  intro i m hi
  rw [hn] at hi
  rw [ht]
  by_cases e : i = k
  · subst e
    have := Repr.unique hi hk
    cases this
    simp
  · have hne : m ≠ n := by
      rintro rfl
      exact e (Repr.inj hnm hW.nodesOK hi hk)
    simp [Function.update, e, hne, h i m hi]

/-! ## Listing one sort -/

/-- `note` puts a sort in front of the list unless it is flagged, and flags
it. -/
theorem note_spec (hnm : Function.Injective nm) (s : store.Store) (acc nd : store.TermId)
    {accL : List Name} {k : Option Name} (hW : Wf s)
    (ha : Repr nm s.nodes.val acc.val (namesPat (nm none) accL))
    (hn : Repr nm s.nodes.val nd.val (kidPat (nm none) k)) (hk : ∀ m, k = some m → m ≠ nm none)
    (hF : FlagAcc nm s accL) (hroom : Room s 4) :
    sorts.note s acc nd ⦃ r s' =>
      RanA s s' 4 ∧ FlagAcc nm s' (noteKid accL k) ∧
        Repr nm s'.nodes.val r.val (namesPat (nm none) (noteKid accL k)) ⦄ := by
  unfold sorts.note
  have hroom' := hroom
  unfold Room at hroom'
  step with is_nil_kid hnm s nd hW hn hk (by unfold Room; omega) as ⟨b, s1, hb, hK⟩
  have ht1 := hK.ticks
  have hF1 : FlagAcc nm s1 accL := hF.kept hK.nodes (by rw [hK.tbl])
  cases k with
  | none =>
    rw [show b = true from hb.2 rfl]
    simp only [↓reduceIte, WP.spec_ok]
    exact ⟨hK.ran.ranA.mono (by omega), hF1, by rw [hK.nodes]; exact ha⟩
  | some m =>
    have hbf : b = false := by
      cases b with
      | false => rfl
      | true => cases hb.1 rfl
    rw [hbf]
    simp only [Bool.false_eq_true, ↓reduceIte]
    have rn : Repr nm s.nodes.val nd.val (.sym m) := by simpa [kidPat] using hn
    have rn1 : Repr nm s1.nodes.val nd.val (.sym m) := by rw [hK.nodes]; exact rn
    step with get_flag_w s1 .A nd hK.wf rn1.lt (by unfold Room; omega) as ⟨o, s2, hfl, hK2⟩
    have ht2 := hK2.ticks
    have R2 := hK.ran.trans hK2.ran
    have hfm := hF1 nd.val m rn1
    by_cases hm : m ∈ accL
    · obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 (hfm.2 hm)
      rw [hv] at hfl
      simp only [Option.map_some] at hfl
      subst hfl
      simp only [WP.spec_ok, noteKid, hm, ↓reduceIte]
      exact ⟨R2.ranA.mono (by omega), hF1.kept hK2.nodes (by rw [hK2.tbl]), R2.ext.repr ha⟩
    · have hnone : tbl s1 .A nd.val = none := by
        cases hv : tbl s1 .A nd.val with
        | none => rfl
        | some v => exact absurd (hfm.1 (by simp [hv])) hm
      rw [hnone] at hfl
      simp only [Option.map_none] at hfl
      subst hfl
      simp only
      have rn2 : Repr nm s2.nodes.val nd.val (.sym m) := R2.ext.repr rn
      step with set_flag_w s2 .A nd true hK2.wf rn2.lt (by unfold Room; omega)
        as ⟨s3, hn3, ht3, hW3, hA3, hB3, hst3⟩
      have hF2 : FlagAcc nm s2 accL := hF1.kept hK2.nodes (by rw [hK2.tbl])
      have hF3 : FlagAcc nm s3 (m :: accL) := hF2.set hnm hK2.wf hn3 hA3 rn2
      have hx3 : Extends s s3 := R2.ext.trans (Extends.of_eq hn3 (by omega))
      step with alloc_w s3 (.App nd acc) hW3 ⟨(hx3.repr rn).lt, (hx3.repr ha).lt⟩
        (by unfold Room; omega) as ⟨out, s4, hW4, ht4, htb4, hx4, hid, hst4⟩
      have hacc : ∀ n ∈ m :: accL, ∃ j, Repr nm s3.nodes.val j (.sym n) := by
        intro n hn'
        rcases List.mem_cons.1 hn' with rfl | hn'
        · exact ⟨_, hx3.repr rn⟩
        · exact namesPat_mem (hx3.repr ha) n hn'
      refine ⟨⟨hW4, hx3.trans hx4, by rw [htb4, hB3 .B (by intro h; cases h), R2.tbl],
        by rw [hst4, hst3, R2.stk], by omega⟩, ?_, ?_⟩
      · simp only [noteKid, hm, ↓reduceIte]
        exact hF3.mono hnm hW3 hW4 hx4 (by rw [htb4]) hacc
      · simp only [noteKid, hm, ↓reduceIte, namesPat, List.map_cons, encList]
        exact .app hid ((hx3.trans hx4).repr rn) ((hx3.trans hx4).repr ha)

/-! ## Listing the sorts of a declaration -/

/-- The list so far is in the store, and table `A` flags its members. -/
structure Noted (nm : Option Nat → RwLog.Sym) (s : store.Store) (acc : store.TermId)
    (accL : List Name) : Prop where
  flags : FlagAcc nm s accL
  list : Repr nm s.nodes.val acc.val (namesPat (nm none) accL)

theorem Noted.kept {s s' : store.Store} {acc : store.TermId} {accL : List Name} {n : Nat}
    (h : Noted nm s acc accL) (hK : KeptW s s' n) : Noted nm s' acc accL :=
  ⟨h.flags.kept hK.nodes (by rw [hK.tbl]), by rw [hK.nodes]; exact h.list⟩

theorem note_kids_loop_spec (hnm : Function.Injective nm) :
    ∀ (ks : List (Option Name)) (s : store.Store) (kids acc : store.TermId) (accL : List Name),
    Wf s → Repr nm s.nodes.val kids.val (rowPat (nm none) ks) →
    (∀ m, some m ∈ ks → m ≠ nm none) → Noted nm s acc accL → Room s (5 * ks.length + 1) →
    sorts.note_kids_loop kids s acc ⦃ r s' =>
      RanA s s' (5 * ks.length + 1) ∧ Noted nm s' r (noteKids accL ks) ⦄ := by
  intro ks
  induction ks with
  | nil =>
    intro s kids acc accL hW hl hz hN hroom
    unfold sorts.note_kids_loop
    rw [loop]
    simp only [sorts.note_kids_loop.body]
    step with uncons_repr s kids hW hl (by unfold Room at hroom ⊢; omega) as ⟨r0, hK, hu⟩
    obtain ⟨o, s1⟩ := r0
    simp only [rowPat] at hu
    simp only at hK
    subst hu
    have hfin : RanA s s1 (5 * ([] : List (Option Name)).length + 1) ∧
        Noted nm s1 acc (noteKids accL []) := ⟨hK.ran.ranA, hN.kept hK⟩
    step*
  | cons k ks ih =>
    intro s kids acc accL hW hl hz hN hroom
    have hroom' := hroom
    unfold Room at hroom'
    simp only [List.length_cons] at hroom'
    unfold sorts.note_kids_loop
    rw [loop]
    simp only [sorts.note_kids_loop.body]
    step with uncons_repr s kids hW hl (by unfold Room; omega) as ⟨r0, hK, hu⟩
    obtain ⟨o, s1⟩ := r0
    simp only [rowPat] at hu
    simp only at hK
    obtain ⟨h, t, rfl, rh, rt⟩ := hu
    have ht1 := hK.ticks
    have hN1 := hN.kept hK
    step with note_spec hnm s1 acc h hK.wf hN1.list (by rw [hK.nodes]; exact rh)
      (fun m e => hz m (by rw [e]; exact List.mem_cons_self ..)) hN1.flags
      (by unfold Room; omega) as ⟨r1, hR2, hF2, hr2⟩
    obtain ⟨acc1, s2⟩ := r1
    simp only at hR2 hF2 hr2
    have ht2 := hR2.ticks
    have R2 := hK.ran.ranA.trans hR2
    have IH := ih s2 t acc1 (noteKid accL k) hR2.wf (R2.ext.repr rt)
      (fun m hm => hz m (List.mem_cons_of_mem _ hm)) ⟨hF2, hr2⟩ (by unfold Room; omega)
    unfold sorts.note_kids_loop at IH
    simp only [uncurry, bind_ok]
    refine WP.spec_mono IH ?_
    rintro ⟨r, s'⟩ ⟨hR, hN'⟩
    exact ⟨(R2.trans hR).mono (by simp only [List.length_cons]; omega), hN'⟩

/-- The ticks listing the sorts of the cases may spend. -/
def noteCasesCost : List (Sym × List (Option Name)) → Nat
  | [] => 1
  | c :: cs => 3 + 5 * c.2.length + noteCasesCost cs

theorem note_cases_loop_spec (hnm : Function.Injective nm) :
    ∀ (cs : List (Sym × List (Option Name))) (s : store.Store) (cases acc : store.TermId)
      (accL : List Name), Wf s →
    Repr nm s.nodes.val cases.val
      (encList (nm none) ((cs.map (caseEnt (nm none))).map (entPat (nm none)))) →
    (∀ c ∈ cs, ∀ m, some m ∈ c.2 → m ≠ nm none) → Noted nm s acc accL →
    Room s (noteCasesCost cs) →
    sorts.note_cases_loop cases s acc ⦃ r s' =>
      RanA s s' (noteCasesCost cs) ∧ Noted nm s' r (noteCases accL cs) ⦄ := by
  intro cs
  induction cs with
  | nil =>
    intro s cases acc accL hW hl hz hN hroom
    unfold sorts.note_cases_loop
    rw [loop]
    simp only [sorts.note_cases_loop.body]
    step with uncons_repr s cases hW hl (by unfold Room at hroom ⊢; simp only [noteCasesCost] at hroom; omega)
      as ⟨r0, hK, hu⟩
    obtain ⟨o, s1⟩ := r0
    simp only at hu hK
    subst hu
    have hfin : RanA s s1 (noteCasesCost []) ∧ Noted nm s1 acc (noteCases accL []) :=
      ⟨hK.ran.ranA, hN.kept hK⟩
    step*
  | cons c cs ih =>
    intro s cases acc accL hW hl hz hN hroom
    have hroom' := hroom
    unfold Room at hroom'
    simp only [noteCasesCost] at hroom'
    unfold sorts.note_cases_loop
    rw [loop]
    simp only [sorts.note_cases_loop.body]
    step with uncons_repr s cases hW hl (by unfold Room; omega) as ⟨r0, hK, hu⟩
    obtain ⟨o, s1⟩ := r0
    simp only at hu hK
    obtain ⟨e, t, rfl, re, rt⟩ := hu
    have ht1 := hK.ticks
    step with uncons_repr s1 e hK.wf (by rw [hK.nodes]; exact re) (by unfold Room; omega)
      as ⟨r1, hK2, hu2⟩
    obtain ⟨o1, s2⟩ := r1
    simp only [entPat, caseEnt] at hu2
    simp only at hK2
    obtain ⟨f, kids, rfl, -, rkids⟩ := hu2
    have ht2 := hK2.ticks
    have hN2 := (hN.kept hK).kept hK2
    have R2 := hK.ran.trans hK2.ran
    step with note_kids_loop_spec hnm c.2 s2 kids acc accL hK2.wf
      (by rw [hK2.nodes]; exact rkids) (hz c (List.mem_cons_self ..)) hN2
      (by unfold Room; omega) as ⟨r3, hR3, hN3⟩
    obtain ⟨acc1, s3⟩ := r3
    simp only at hR3 hN3
    have ht3 := hR3.ticks
    have R3 := R2.ranA.trans hR3
    have IH := ih s3 t acc1 (noteKids accL c.2) hR3.wf (R3.ext.repr rt)
      (fun c' hc' => hz c' (List.mem_cons_of_mem _ hc')) hN3 (by unfold Room; omega)
    unfold sorts.note_cases_loop at IH
    simp only [uncurry, bind_ok]
    refine WP.spec_mono IH ?_
    rintro ⟨r, s'⟩ ⟨hR, hN'⟩
    exact ⟨(R3.trans hR).mono (by simp only [noteCasesCost]; omega), hN'⟩

/-! ## Every name of the declarations -/

/-- No name of the declarations is the symbol `z`. -/
def NamesOK (z : Sym) (S : Sorts) : Prop :=
  ∀ d ∈ S, d.1 ≠ z ∧ (∀ c ∈ d.2.cases, ∀ m, some m ∈ c.2 → m ≠ z) ∧
    ∀ r, d.2.rest = some r → ∀ m, r.2 = some m → m ≠ z

theorem mem_kidNames {d : SortDef} {n : Name} : n ∈ d.kidNames ↔
    (∃ c ∈ d.cases, some n ∈ c.2) ∨ ∃ r, d.rest = some r ∧ r.2 = some n := by
  simp only [SortDef.kidNames, List.mem_append, List.mem_flatMap, List.mem_filterMap, id,
    exists_eq_right, Option.mem_toList, Option.bind_eq_some_iff]

theorem namesOK_of_names {z : Sym} {S : Sorts} (h : ∀ n ∈ Sorts.names S, n ≠ z) : NamesOK z S := by
  have key : ∀ d ∈ S, ∀ n, (n = d.1 ∨ n ∈ d.2.kidNames) → n ≠ z := by
    intro d hd n hn
    apply h
    simp only [Sorts.names, List.mem_toFinset, List.mem_flatMap, List.mem_cons]
    exact ⟨d, hd, hn⟩
  intro d hd
  refine ⟨key d hd _ (Or.inl rfl), ?_, ?_⟩
  · intro c hc m hm
    exact key d hd m (Or.inr (mem_kidNames.2 (Or.inl ⟨c, hc, hm⟩)))
  · intro r hr m hm
    exact key d hd m (Or.inr (mem_kidNames.2 (Or.inr ⟨r, hr, hm⟩)))

/-- The ticks listing the names of the declarations may spend. -/
def namesCost : Sorts → Nat
  | [] => 1
  | d :: S => 12 + noteCasesCost d.2.cases + namesCost S

theorem names_loop_spec (hnm : Function.Injective nm) :
    ∀ (S : Sorts) (ds : List Pat) (s : store.Store) (decls acc : store.TermId)
      (accL : List Name), Wf s → List.Forall₂ (DefAt (nm none)) S ds →
    Repr nm s.nodes.val decls.val (encList (nm none) ds) → NamesOK (nm none) S →
    Noted nm s acc accL → Room s (namesCost S) →
    sorts.names_loop decls s acc ⦃ r s' =>
      RanA s s' (namesCost S) ∧ Noted nm s' r (S.foldl noteDef accL) ⦄ := by
  intro S
  induction S with
  | nil =>
    intro ds s decls acc accL hW hF hl hz hN hroom
    cases hF
    unfold sorts.names_loop
    rw [loop]
    simp only [sorts.names_loop.body]
    step with uncons_repr s decls hW hl
      (by unfold Room at hroom ⊢; simp only [namesCost] at hroom; omega) as ⟨r0, hK, hu⟩
    obtain ⟨o, s1⟩ := r0
    simp only [encList] at hu
    simp only at hK
    subst hu
    have hfin : RanA s s1 (namesCost []) ∧ Noted nm s1 acc (([] : Sorts).foldl noteDef accL) :=
      ⟨hK.ran.ranA, hN.kept hK⟩
    step*
  | cons d S ih =>
    intro ds s decls acc accL hW hF hl hz hN hroom
    cases hF with
    | cons hd hF' =>
    rename_i dp ds'
    obtain ⟨rp, hrest, rfl⟩ := hd
    obtain ⟨hz1, hz2, hz3⟩ := hz d (List.mem_cons_self ..)
    have hroom' := hroom
    unfold Room at hroom'
    simp only [namesCost] at hroom'
    unfold sorts.names_loop
    rw [loop]
    simp only [sorts.names_loop.body]
    step with uncons_repr s decls hW hl (by unfold Room; omega) as ⟨r0, hK, hu⟩
    obtain ⟨o, s1⟩ := r0
    simp only [encList] at hu
    simp only at hK
    obtain ⟨e, more, rfl, re, rmore⟩ := hu
    have ht1 := hK.ticks
    step with uncons_repr s1 e hK.wf (by rw [hK.nodes]; exact re) (by unfold Room; omega)
      as ⟨r1, hK2, hu2⟩
    obtain ⟨o1, s2⟩ := r1
    simp only at hu2 hK2
    obtain ⟨n, d', rfl, rn, rd⟩ := hu2
    have ht2 := hK2.ticks
    step with uncons_repr s2 d' hK2.wf (by rw [hK2.nodes]; exact rd) (by unfold Room; omega)
      as ⟨r2, hK3, hu3⟩
    obtain ⟨o2, s3⟩ := r2
    simp only at hu3 hK3
    obtain ⟨cases, rest, rfl, rcases, rrest⟩ := hu3
    have ht3 := hK3.ticks
    have R3 := (hK.ran.trans hK2.ran).trans hK3.ran
    have hN3 := ((hN.kept hK).kept hK2).kept hK3
    simp only [hK2.nodes, hK.nodes] at rn rd rcases rrest
    step with note_spec hnm s3 acc n (k := some d.1) R3.wf hN3.list (R3.ext.repr rn)
      (fun m e => by cases e; exact hz1) hN3.flags (by unfold Room; omega)
      as ⟨r4, hR4, hF4, hr4⟩
    obtain ⟨acc1, s4⟩ := r4
    simp only at hR4 hF4 hr4
    have ht4 := hR4.ticks
    have R4 := R3.ranA.trans hR4
    step with note_cases_loop_spec hnm d.2.cases s4 cases acc1 _ hR4.wf (R4.ext.repr rcases)
      hz2 ⟨hF4, hr4⟩ (by unfold Room; omega) as ⟨r5, hR5, hN5⟩
    obtain ⟨acc2, s5⟩ := r5
    simp only at hR5 hN5
    have ht5 := hR5.ticks
    have R5 := R4.trans hR5
    step with uncons_repr s5 rest hR5.wf (R5.ext.repr rrest) (by unfold Room; omega)
      as ⟨r6, hK6, hu6⟩
    obtain ⟨o6, s6⟩ := r6
    simp only at hK6
    have ht6 := hK6.ticks
    have R6 := R5.trans hK6.ran.ranA
    have hN6 := hN5.kept hK6
    have hz' : NamesOK (nm none) S := fun d' hd' => hz d' (List.mem_cons_of_mem _ hd')
    cases hdr : d.2.rest with
    | none =>
      rw [hdr] at hrest
      simp only [RestAt] at hrest
      subst hrest
      simp only at hu6
      subst hu6
      have hN6' : Noted nm s6 acc2 (noteDef accL d) := by
        simpa [noteDef, hdr] using hN6
      have IH := ih ds' s6 more acc2 _ hK6.wf hF' (R6.ext.repr rmore) hz' hN6'
        (by unfold Room; omega)
      unfold sorts.names_loop at IH
      simp only [uncurry, bind_ok]
      refine WP.spec_mono IH ?_
      rintro ⟨r, s'⟩ ⟨hR, hN'⟩
      exact ⟨(R6.trans hR).mono (by simp only [namesCost]; omega), by simpa using hN'⟩
    | some rk =>
      rw [hdr] at hrest
      obtain ⟨xs, -, rfl⟩ := hrest
      simp only at hu6
      obtain ⟨exid, kid, rfl, -, rkid⟩ := hu6
      step with note_spec hnm s6 acc2 kid (k := rk.2) hK6.wf hN6.list
        (by rw [hK6.nodes]; exact rkid) (hz3 rk hdr) hN6.flags (by unfold Room; omega)
        as ⟨r7, hR7, hF7, hr7⟩
      obtain ⟨acc3, s7⟩ := r7
      simp only at hR7 hF7 hr7
      have ht7 := hR7.ticks
      have R7 := R6.trans hR7
      have hN7 : Noted nm s7 acc3 (noteDef accL d) := by
        simpa [noteDef, hdr] using (⟨hF7, hr7⟩ : Noted nm s7 acc3 _)
      have IH := ih ds' s7 more acc3 _ hR7.wf hF' (R7.ext.repr rmore) hz' hN7
        (by unfold Room; omega)
      unfold sorts.names_loop at IH
      simp only [uncurry, bind_ok]
      refine WP.spec_mono IH ?_
      rintro ⟨r, s'⟩ ⟨hR, hN'⟩
      exact ⟨(R7.trans hR).mono (by simp only [namesCost]; omega), by simpa using hN'⟩

/-- `names` lists every name the declarations declare or say of an argument,
each once (`namesList`, `mem_namesList`, `nodup_namesList`). No name is the
end of a list. Table `B` and the stack are left as they were. -/
theorem names_spec (hnm : Function.Injective nm) (S : Sorts) {sp : Pat}
    (hS : SortsAt (nm none) S sp) (s : store.Store) (decls : store.TermId) (hW : Wf s)
    (hd : Repr nm s.nodes.val decls.val sp) (hz : ∀ n ∈ Sorts.names S, n ≠ nm none)
    (hroom : Room s (namesCost S + 2)) :
    sorts.names s decls ⦃ r s' =>
      RanA s s' (namesCost S + 2) ∧
        Repr nm s'.nodes.val r.val (namesPat (nm none) (namesList S)) ⦄ := by
  obtain ⟨ds, hF, rfl⟩ := hS
  unfold sorts.names
  have hroom' := hroom
  unfold Room at hroom'
  step with clear_w s .A hW (by unfold Room; omega) as ⟨s1, hn1, ht1, hW1, hA1, hB1, hst1⟩
  have hx1 : Extends s s1 := Extends.of_eq hn1 (by omega)
  step with alloc_w s1 .Nil hW1 trivial (by unfold Room; omega)
    as ⟨acc, s2, hW2, ht2, htb2, hx2, hid, hst2⟩
  have hN2 : Noted nm s2 acc [] :=
    ⟨fun i n _ => by rw [htb2]; simp [hA1 i], .nil hid⟩
  have IH := names_loop_spec hnm S ds s2 decls acc [] hW2 hF ((hx1.trans hx2).repr hd)
    (namesOK_of_names hz) hN2 (by unfold Room; omega)
  refine WP.spec_mono IH ?_
  rintro ⟨r, s'⟩ ⟨hR, hN'⟩
  have hR2 : RanA s s2 2 :=
    ⟨hW2, hx1.trans hx2, by rw [htb2, hB1 .B (by intro h; cases h)], by rw [hst2, hst1],
      by omega⟩
  exact ⟨(hR2.trans hR).mono (by omega), hN'.list⟩

end RwLogVerified
