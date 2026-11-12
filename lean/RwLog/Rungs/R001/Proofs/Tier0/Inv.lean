/-
# Tier 0 proofs, part 8: what every table holds

The invariant of reachable tables (`TInv`): goals have interface boundaries
the theory does not refute; every answer is unrefuted and stands, up to the
theory, for one derivation of its goal; no answer of a table covers a later
one; and a complete table covers every derivation of its goal. A round
preserves it.
-/
import RwLog.Rungs.R001.Proofs.Tier0.Round

namespace RwLog

namespace R001

namespace Tier0

variable {P : Program}

/-- The boundaries of a goal are unrefuted. -/
def BU (T : Theory) (g : Goal) : Prop :=
  (∀ b, g.lb = some b → T.refutes? b.c = false) ∧ (∀ b, g.rb = some b → T.refutes? b.c = false)

theorem bu_map_swap {T : Theory} {o : Option Span} (h : ∀ b, o = some b → T.refutes? b.c = false) :
    ∀ b, o.map Span.swap = some b → T.refutes? b.c = false := by
  intro b hb
  obtain ⟨b', hb', rfl⟩ := Option.map_eq_some_iff.1 hb
  exact h b' hb'

theorem bu_convGoal {T : Theory} {g : Goal} (h : BU T g) (a : Rel) : BU T (convGoal g a) :=
  ⟨bu_map_swap h.2, bu_map_swap h.1⟩

theorem bu_strip {T : Theory} : ∀ (e : Rel) (lb rb : Option Span), BU T ⟨lb, e, rb⟩ →
    BU T (Goal.stripConv ⟨lb, e, rb⟩).2
  | .conv a, lb, rb, h => by
    rw [strip_conv]
    exact bu_strip a _ _ ⟨bu_map_swap h.2, bu_map_swap h.1⟩
  | .zero, _, _, h => by rw [strip_nc _ (by simp)]; exact h
  | .span _, _, _, h => by rw [strip_nc _ (by simp)]; exact h
  | .or _ _, _, _, h => by rw [strip_nc _ (by simp)]; exact h
  | .and _ _, _, _, h => by rw [strip_nc _ (by simp)]; exact h
  | .seq _ _, _, _, h => by rw [strip_nc _ (by simp)]; exact h
  | .call _, _, _, h => by rw [strip_nc _ (by simp)]; exact h

theorem bu_norm {T : Theory} {g : Goal} (h : BU T g) : BU T g.norm.2 :=
  bu_strip (canon g.e) g.lb g.rb h

/-- The invariant of the tables of a reachable state. -/
structure TInv (P : Program) (ts : Tables) : Prop where
  good : ∀ t ∈ ts, GoodG t.goal
  bu : ∀ t ∈ ts, BU P.theory t.goal
  unref : ∀ t ∈ ts, ∀ a ∈ t.answers, P.theory.refutes? a.c = false
  ref : ∀ t ∈ ts, ∀ a ∈ t.answers, ∃ s, Derives P t.goal.e s ∧ Ref P.theory a (GDen t.goal s.den)
  pw : ∀ t ∈ ts, t.answers.Pairwise fun a b => a.covers? b = false
  comp : ∀ t ∈ ts, t.done = true → ∀ s, Derives P t.goal.e s →
    DC P.theory t.answers (GDen t.goal s.den)

/-! ## Reading the tables -/

theorem answersOf_mem {ts : Tables} {d : Goal} {a : Span} (h : a ∈ answersOf ts d) :
    ∃ t, findTable ts d.norm.2 = some t ∧ ∃ a₀ ∈ t.answers, a = oS d.norm.1 a₀ := by
  unfold answersOf at h
  simp only at h
  cases ht : findTable ts d.norm.2 with
  | none => rw [ht] at h; simp at h
  | some t =>
    rw [ht] at h
    simp only [orient_eq, List.mem_map] at h
    obtain ⟨a₀, ha₀, rfl⟩ := h
    exact ⟨t, rfl, a₀, ha₀, rfl⟩

theorem answersOf_eq {ts : Tables} {d : Goal} {t : Table} (h : findTable ts d.norm.2 = some t) :
    answersOf ts d = orient d.norm.1 t.answers := by
  unfold answersOf; simp only [h]

theorem findTable_spec {ts : Tables} {g : Goal} {t : Table} (h : findTable ts g = some t) :
    t ∈ ts ∧ t.goal.same g = true := by
  unfold findTable at h
  have hp := List.find?_some h
  exact ⟨List.mem_of_find?_eq_some h, hp⟩

theorem oS_c (f : Bool) (a : Span) : (oS f a).c = a.c := by cases f <;> rfl

theorem ansRef_of {ts : Tables} (hI : TInv P ts) : AnsRef P ts := by
  intro d hd a ha
  obtain ⟨t, hf, a₀, ha₀, rfl⟩ := answersOf_mem ha
  obtain ⟨ht, hs⟩ := findTable_spec hf
  obtain ⟨s, hds, hr⟩ := hI.ref t ht a₀ ha₀
  rw [same_e hs] at hds
  obtain ⟨hd', heq⟩ := norm_back d hds
  refine ⟨oS d.norm.1 s, hd', ?_⟩
  rw [heq, ← same_gden hs (hI.good t ht) (goodG_norm hd)]
  exact ref_oS _ hr

theorem answersOf_unref {ts : Tables} (hI : TInv P ts) {d : Goal} {a : Span} (h : a ∈ answersOf ts d) :
    P.theory.refutes? a.c = false := by
  obtain ⟨t, hf, a₀, ha₀, rfl⟩ := answersOf_mem h
  rw [oS_c]
  exact hI.unref t (findTable_spec hf).1 a₀ ha₀

/-! ## Candidates are unrefuted -/

section
variable (hSS : Obligation.simplify_stable) (hwf : ∀ ρ ∈ P.theory, ρ.WellFormed)
include hSS hwf

theorem live_unref {z c : Span} (h : c ∈ live P.theory z) : P.theory.refutes? c.c = false := by
  simp only [live, Option.mem_toList] at h
  exact (hSS P.theory z c _ hwf h).1

theorem composeLive_unref {x y c : Span} (h : c ∈ composeLive P.theory x y) :
    P.theory.refutes? c.c = false := by
  unfold composeLive at h
  split at h
  · exact live_unref hSS hwf h
  · simp at h

theorem meetLive_unref {x y c : Span} (h : c ∈ meetLive P.theory x y) :
    P.theory.refutes? c.c = false := by
  unfold meetLive at h
  split at h
  · exact live_unref hSS hwf h
  · simp at h

theorem cands_unref {dd : Nat} {ts : Tables} (hI : TInv P ts) {g : Goal} {c : Span}
    (hc : c ∈ (produce P dd ts g).1) : P.theory.refutes? c.c = false := by
  simp only [produce, List.mem_append] at hc
  rcases hc with hc | hc
  · unfold unfoldAnswers at hc
    split at hc
    · obtain ⟨z, -, hz⟩ := List.mem_flatMap.1 hc
      exact live_unref hSS hwf hz
    · simp at hc
  obtain ⟨lb, e, rb⟩ := g
  cases e with
  | zero => simp [produce.produceStrategies] at hc
  | span s =>
    simp only [produce.produceStrategies] at hc
    obtain ⟨w, hw, -⟩ := spanAnswer_den hc
    exact live_unref hSS hwf hw
  | or a b =>
    simp only [produce.produceStrategies, List.mem_flatMap] at hc
    obtain ⟨d, -, hc⟩ := hc
    exact answersOf_unref hI hc
  | call n =>
    simp only [produce.produceStrategies] at hc
    exact answersOf_unref hI hc
  | conv a =>
    simp only [produce.produceStrategies, List.mem_map] at hc
    obtain ⟨c', hc', rfl⟩ := hc
    have := answersOf_unref hI hc'
    exact this
  | seq a b =>
    simp only [produce.produceStrategies, List.mem_append, List.mem_flatMap] at hc
    rcases hc with (⟨x, -, y, -, hc⟩ | ⟨p, -, y, -, hc⟩) | ⟨p, -, x, -, hc⟩ <;>
      exact composeLive_unref hSS hwf hc
  | and a b =>
    simp only [produce.produceStrategies, List.mem_append, List.mem_flatMap] at hc
    rcases hc with (⟨x, -, y, -, hc⟩ | ⟨p, -, y, -, hc⟩) | ⟨p, -, x, -, hc⟩ <;>
      exact meetLive_unref hSS hwf hc

end

/-! ## The goals a table reads -/

theorem deps_good {dd : Nat} {ts : Tables} {g d : Goal} (hg : GoodG g)
    (hd : d ∈ (produce P dd ts g).2) : GoodG d := by
  obtain ⟨lb, e, rb⟩ := g
  simp only [produce] at hd
  cases e with
  | zero => simp [produce.produceStrategies] at hd
  | span s => simp [produce.produceStrategies] at hd
  | or a b =>
    simp only [produce.produceStrategies, orLeaves, List.mem_map] at hd
    obtain ⟨l, -, rfl⟩ := hd
    exact hg
  | call n =>
    simp only [produce.produceStrategies, List.mem_singleton] at hd
    subst hd; exact hg
  | conv a =>
    simp only [produce.produceStrategies, List.mem_singleton] at hd
    subst hd; exact goodG_convGoal hg a
  | seq a b =>
    simp only [produce.produceStrategies, List.mem_append, List.mem_cons, List.mem_map,
      List.not_mem_nil, or_false] at hd
    rcases hd with ((rfl | rfl) | ⟨p, hp, rfl⟩) | ⟨p, hp, rfl⟩
    · exact ⟨hg.1, trivial⟩
    · exact ⟨trivial, hg.2⟩
    · split at hp
      · obtain ⟨x, -, rfl⟩ := List.mem_map.1 hp
        exact goodG_pushL hg b x
      · simp at hp
    · split at hp
      · obtain ⟨y, -, rfl⟩ := List.mem_map.1 hp
        exact goodG_pushR hg a y
      · simp at hp
  | and a b =>
    simp only [produce.produceStrategies, List.mem_append, List.mem_cons, List.mem_map,
      List.not_mem_nil, or_false] at hd
    rcases hd with ((rfl | rfl) | ⟨p, hp, rfl⟩) | ⟨p, hp, rfl⟩
    · exact hg
    · exact hg
    · split at hp
      · obtain ⟨x, -, rfl⟩ := List.mem_map.1 hp
        exact goodG_andPush b x
      · simp at hp
    · split at hp
      · obtain ⟨y, -, rfl⟩ := List.mem_map.1 hp
        exact goodG_andPush a y
      · simp at hp

/-- The store of an interface of an unrefuted answer is unrefuted. -/
theorem iface_unref (hRM : Obligation.refutes_mono) (hwf : ∀ ρ ∈ P.theory, ρ.WellFormed)
    {x : Span} (hx : P.theory.refutes? x.c = false) (p : Pat) :
    P.theory.refutes? (x.storeOn p) = false := by
  by_contra h
  rw [Bool.not_eq_false] at h
  have := hRM P.theory P.theory (x.storeOn p) x.c Term.var hwf (fun _ h => h)
    (fun a ha => by rw [Term.bind_var_id]; exact (mem_storeOn.1 ha).1) h
  rw [hx] at this; exact Bool.false_ne_true this

theorem bound_unref (hRM : Obligation.refutes_mono) (hwf : ∀ ρ ∈ P.theory, ρ.WellFormed)
    {x : Span} (hx : P.theory.refutes? x.c = false) :
    (∀ b, bound x.rightIface = some b → P.theory.refutes? b.c = false) ∧
      (∀ b, bound x.leftIface = some b → P.theory.refutes? b.c = false) := by
  constructor <;> intro b hb <;> rw [bound_some hb] <;> exact iface_unref hRM hwf hx _

theorem deps_bu (hRM : Obligation.refutes_mono) (hwf : ∀ ρ ∈ P.theory, ρ.WellFormed)
    {dd : Nat} {ts : Tables} (hI : TInv P ts) {g d : Goal} (hg : BU P.theory g)
    (hd : d ∈ (produce P dd ts g).2) : BU P.theory d := by
  obtain ⟨lb, e, rb⟩ := g
  simp only [produce] at hd
  cases e with
  | zero => simp [produce.produceStrategies] at hd
  | span s => simp [produce.produceStrategies] at hd
  | or a b =>
    simp only [produce.produceStrategies, orLeaves, List.mem_map] at hd
    obtain ⟨l, -, rfl⟩ := hd
    exact hg
  | call n =>
    simp only [produce.produceStrategies, List.mem_singleton] at hd
    subst hd; exact hg
  | conv a =>
    simp only [produce.produceStrategies, List.mem_singleton] at hd
    subst hd; exact bu_convGoal hg a
  | seq a b =>
    simp only [produce.produceStrategies, List.mem_append, List.mem_cons, List.mem_map,
      List.not_mem_nil, or_false] at hd
    rcases hd with ((rfl | rfl) | ⟨p, hp, rfl⟩) | ⟨p, hp, rfl⟩
    · exact ⟨hg.1, fun _ h => by cases h⟩
    · exact ⟨fun _ h => (by cases h), hg.2⟩
    · split at hp
      · obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hp
        exact ⟨(bound_unref hRM hwf (answersOf_unref hI (maxima_sub hx))).1, hg.2⟩
      · simp at hp
    · split at hp
      · obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hp
        exact ⟨hg.1, (bound_unref hRM hwf (answersOf_unref hI (maxima_sub hy))).2⟩
      · simp at hp
  | and a b =>
    simp only [produce.produceStrategies, List.mem_append, List.mem_cons, List.mem_map,
      List.not_mem_nil, or_false] at hd
    rcases hd with ((rfl | rfl) | ⟨p, hp, rfl⟩) | ⟨p, hp, rfl⟩
    · exact hg
    · exact hg
    · split at hp
      · obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hp
        have := bound_unref hRM hwf (answersOf_unref hI (maxima_sub hx))
        exact ⟨this.2, this.1⟩
      · simp at hp
    · split at hp
      · obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hp
        have := bound_unref hRM hwf (answersOf_unref hI (maxima_sub hy))
        exact ⟨this.2, this.1⟩
      · simp at hp

/-! ## Fresh answers keep a table free of covered answers -/

theorem pw_fresh {old cands : List Span} (h : old.Pairwise fun a b => a.covers? b = false) :
    (old ++ fresh old cands).Pairwise fun a b => a.covers? b = false := by
  rw [List.pairwise_append]
  exact ⟨h, fresh_pairwise old cands, fun a ha b hb => (fresh_sub hb).2 a ha⟩

end Tier0

end R001

end RwLog
