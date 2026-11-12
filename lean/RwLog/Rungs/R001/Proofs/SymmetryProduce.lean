/-
# Rung R001, Symmetry: what mirrored goals compute in a round

For a table of the run and the corresponding table of the mirrored run, the
candidates computed in a round have the same classes of equivalent answers
up to swapping, the goals they request correspond as mirrors, and so do the
strategies through which they may complete.

`;` swaps its sides under the mirror: the left sub-goal of the mirror is the
mirror of the right sub-goal, and pushing a left answer into the right side
corresponds to pushing a right answer into the left side. `&` keeps its
sides.
-/
import RwLog.Rungs.R001.Proofs.SymmetryUnfold

namespace RwLog

namespace R001

/-! ## Lists of swapped answers -/

/-- Spans of the mirrored run corresponding, up to equivalence, to the swaps
of spans of the run. -/
def SwC (xs xs' : List Span) : Prop :=
  (∀ x ∈ xs, ∃ x' ∈ xs', x'.Equiv x.swap) ∧ (∀ x' ∈ xs', ∃ x ∈ xs, x'.Equiv x.swap)

theorem SwC.of_stepEquiv {xs xs' : List Span} (h : StepEquiv xs' (xs.map Span.swap)) : SwC xs xs' := by
  constructor
  · intro x hx
    obtain ⟨x', hx', e⟩ := h.symm.mem (List.mem_map_of_mem hx)
    exact ⟨x', hx', Span.Equiv.symm e⟩
  · intro x' hx'
    obtain ⟨y, hy, e⟩ := h.mem hx'
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hy
    exact ⟨x, hx, e⟩

theorem classEq_flatMap_sw {xs xs' : List Span} (h : SwC xs xs') {F F' : Span → List Span}
    (hF : ∀ x ∈ xs, ∀ x' ∈ xs', x'.Equiv x.swap → ClassEq (F' x') ((F x).map Span.swap)) :
    ClassEq (xs'.flatMap F') ((xs.flatMap F).map Span.swap) := by
  constructor
  · intro z hz
    obtain ⟨x', hx', hz⟩ := List.mem_flatMap.1 hz
    obtain ⟨x, hx, e⟩ := h.2 x' hx'
    obtain ⟨w, hw, ew⟩ := (hF x hx x' hx' e).1 z hz
    obtain ⟨w₀, hw₀, rfl⟩ := List.mem_map.1 hw
    exact ⟨_, List.mem_map_of_mem (List.mem_flatMap.2 ⟨x, hx, hw₀⟩), ew⟩
  · intro w hw
    obtain ⟨w₀, hw₀, rfl⟩ := List.mem_map.1 hw
    obtain ⟨x, hx, hw₀⟩ := List.mem_flatMap.1 hw₀
    obtain ⟨x', hx', e⟩ := h.1 x hx
    obtain ⟨z, hz, ez⟩ := (hF x hx x' hx' e).2 _ (List.mem_map_of_mem hw₀)
    exact ⟨z, List.mem_flatMap.2 ⟨x', hx', hz⟩, ez⟩

/-- Three groups of candidates, the last two matched crosswise. -/
theorem classEq_cross {a b c a' b' c' : List Span} (ha : ClassEq a' (a.map Span.swap))
    (hb : ClassEq b' (c.map Span.swap)) (hc : ClassEq c' (b.map Span.swap)) :
    ClassEq (a' ++ b' ++ c') ((a ++ b ++ c).map Span.swap) := by
  refine ((ha.append hb).append hc).trans (ClassEq.of_mem_iff fun z => ?_)
  simp only [List.mem_append, List.map_append]
  tauto

/-! ## Fusions of mirrored answers -/

variable {T : Theory}

theorem composeLive_mirror (hK : Obligation.SimplifyRespectsEquiv T) {x y x' y' : Span}
    (hx : x'.Equiv y.swap) (hy : y'.Equiv x.swap) :
    ClassEq (composeLive T x' y') ((composeLive T x y).map Span.swap) := by
  rw [composeLive_eq, composeLive_eq]
  apply liveO_mirror hK
  rw [compose_den, compose_den, GRel.inv_comp]
  exact ((Span.Equiv.geq hx).trans (swap_geq y)).comp ((Span.Equiv.geq hy).trans (swap_geq x))

theorem meetLive_mirror (hK : Obligation.SimplifyRespectsEquiv T) {x y x' y' : Span}
    (hx : x'.Equiv x.swap) (hy : y'.Equiv y.swap) :
    ClassEq (meetLive T x' y') ((meetLive T x y).map Span.swap) := by
  rw [meetLive_eq, meetLive_eq]
  apply liveO_mirror hK
  rw [meet_den, meet_den, GRel.inv_meet]
  exact ((Span.Equiv.geq hx).trans (swap_geq x)).meet ((Span.Equiv.geq hy).trans (swap_geq y))

/-- The meaning of `lb ; s ; rb` as `spanAnswer` fuses it. -/
def bden : Option Span → GRel
  | none => GRel.id
  | some l => l.den

def spanBoth (lb : Option Span) (s : Span) (rb : Option Span) : Option Span :=
  let left : Option Span := match lb with
    | none => some s
    | some l => l.compose s
  left.bind fun s' => match rb with
    | none => some s'
    | some r => s'.compose r

theorem spanAnswer_eq (lb : Option Span) (s : Span) (rb : Option Span) :
    spanAnswer T lb s rb = liveO T (spanBoth lb s rb) := by
  show (match spanBoth lb s rb with | some z => live T z | none => []) = _
  cases spanBoth lb s rb <;> rfl

theorem comp_empty (R : GRel) : R.comp ∅ = ∅ := by
  ext ⟨a, b, X⟩; simp [GRel.comp]

theorem empty_comp (R : GRel) : (∅ : GRel).comp R = ∅ := by
  ext ⟨a, b, X⟩; simp [GRel.comp]

theorem spanBoth_den (lb : Option Span) (s : Span) (rb : Option Span) :
    Span.denO (spanBoth lb s rb) = ((bden lb).comp s.den).comp (bden rb) := by
  have hleft : Span.denO (match lb with | none => some s | some l => l.compose s) =
      (bden lb).comp s.den := by
    cases lb with
    | none => simp [Span.denO, bden, GRel.id_comp]
    | some l => exact compose_den l s
  unfold spanBoth
  revert hleft
  cases (match lb with | none => some s | some l => l.compose s) with
  | none =>
    intro hleft
    simp only [Option.bind_none, Span.denO] at hleft ⊢
    rw [← hleft, empty_comp]
  | some s' =>
    intro hleft
    simp only [Option.bind_some, Span.denO] at hleft ⊢
    rw [← hleft]
    cases rb with
    | none => simp [bden, GRel.comp_id]
    | some r => exact compose_den s' r

theorem bden_mirror {o o' : Option Span} (h : boundEq (o.map Span.swap) o' = true) :
    GEq (bden o') (bden o).inv := by
  have := boundEq_equiv h
  cases o with
  | none =>
    cases this
    simp only [bden]; exact GEq.of_eq id_inv.symm
  | some l =>
    cases this with
    | some e => exact (Span.Equiv.geq e).symm.trans (swap_geq l)

theorem spanAnswer_mirror (hK : Obligation.SimplifyRespectsEquiv T) {lb rb lb' rb' : Option Span}
    (s : Span) (hl : boundEq (rb.map Span.swap) lb' = true) (hr : boundEq (lb.map Span.swap) rb' = true) :
    ClassEq (spanAnswer T lb' s.swap rb') ((spanAnswer T lb s rb).map Span.swap) := by
  rw [spanAnswer_eq, spanAnswer_eq]
  apply liveO_mirror hK
  rw [spanBoth_den, spanBoth_den, GRel.inv_comp, GRel.inv_comp, swap_den, ← GRel.comp_assoc]
  exact ((bden_mirror hl).comp (GEq.refl _)).comp (bden_mirror hr)

/-! ## Mirrored requests and strategies -/

/-- Goals of the run and of the mirrored run that are mirrors of each
other, both ways. -/
def MSet (gs hs : List Goal) : Prop :=
  (∀ g ∈ gs, ∃ h ∈ hs, Mirror g h) ∧ (∀ h ∈ hs, ∃ g ∈ gs, Mirror g h)

theorem MSet.append {gs hs gs' hs' : List Goal} (h : MSet gs hs) (h' : MSet gs' hs') :
    MSet (gs ++ gs') (hs ++ hs') := by
  constructor
  · intro g hg
    rcases List.mem_append.1 hg with hg | hg
    · obtain ⟨k, hk, e⟩ := h.1 g hg; exact ⟨k, List.mem_append_left _ hk, e⟩
    · obtain ⟨k, hk, e⟩ := h'.1 g hg; exact ⟨k, List.mem_append_right _ hk, e⟩
  · intro k hk
    rcases List.mem_append.1 hk with hk | hk
    · obtain ⟨g, hg, e⟩ := h.2 k hk; exact ⟨g, List.mem_append_left _ hg, e⟩
    · obtain ⟨g, hg, e⟩ := h'.2 k hk; exact ⟨g, List.mem_append_right _ hg, e⟩

theorem MSet.of_mem_iff {gs hs hs' : List Goal} (h : MSet gs hs) (e : ∀ k, k ∈ hs ↔ k ∈ hs') :
    MSet gs hs' :=
  ⟨fun g hg => let ⟨k, hk, m⟩ := h.1 g hg; ⟨k, (e k).1 hk, m⟩,
   fun k hk => h.2 k ((e k).2 hk)⟩

theorem MSet.pair {g₁ g₂ h₁ h₂ : Goal} (e₁ : Mirror g₁ h₂) (e₂ : Mirror g₂ h₁) :
    MSet [g₁, g₂] [h₁, h₂] := by
  constructor
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl
    · exact ⟨h₂, by simp, e₁⟩
    · exact ⟨h₁, by simp, e₂⟩
  · intro k hk
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl
    · exact ⟨g₂, by simp, e₂⟩
    · exact ⟨g₁, by simp, e₁⟩

theorem MSet.map {xs xs' : List Span} (h : SwC xs xs') {f f' : Span → Goal}
    (hf : ∀ x x', x'.Equiv x.swap → Mirror (f x) (f' x')) : MSet (xs.map f) (xs'.map f') := by
  constructor
  · intro g hg
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hg
    obtain ⟨x', hx', e⟩ := h.1 x hx
    exact ⟨f' x', List.mem_map_of_mem hx', hf x x' e⟩
  · intro k hk
    obtain ⟨x', hx', rfl⟩ := List.mem_map.1 hk
    obtain ⟨x, hx, e⟩ := h.2 x' hx'
    exact ⟨f x, List.mem_map_of_mem hx, hf x x' e⟩

/-- Strategies of the run and of the mirrored run with mirrored
dependencies, both ways. -/
def SRel (SA SB : List (List Goal)) : Prop :=
  (∀ s ∈ SA, ∃ s' ∈ SB, MSet s s') ∧ (∀ s' ∈ SB, ∃ s ∈ SA, MSet s s')

theorem SRel.append {SA SB SA' SB' : List (List Goal)} (h : SRel SA SB) (h' : SRel SA' SB') :
    SRel (SA ++ SA') (SB ++ SB') := by
  constructor
  · intro g hg
    rcases List.mem_append.1 hg with hg | hg
    · obtain ⟨k, hk, e⟩ := h.1 g hg; exact ⟨k, List.mem_append_left _ hk, e⟩
    · obtain ⟨k, hk, e⟩ := h'.1 g hg; exact ⟨k, List.mem_append_right _ hk, e⟩
  · intro k hk
    rcases List.mem_append.1 hk with hk | hk
    · obtain ⟨g, hg, e⟩ := h.2 k hk; exact ⟨g, List.mem_append_left _ hg, e⟩
    · obtain ⟨g, hg, e⟩ := h'.2 k hk; exact ⟨g, List.mem_append_right _ hg, e⟩

theorem SRel.single {s s' : List Goal} (h : MSet s s') : SRel [s] [s'] :=
  ⟨fun t ht => ⟨s', List.mem_singleton_self _, by rw [List.mem_singleton.1 ht]; exact h⟩,
   fun t ht => ⟨s, List.mem_singleton_self _, by rw [List.mem_singleton.1 ht]; exact h⟩⟩

theorem SRel.nil : SRel [] [] := ⟨fun _ h => absurd h List.not_mem_nil, fun _ h => absurd h List.not_mem_nil⟩

theorem SRel.ite {c : Bool} {s s' : List Goal} (h : MSet s s') :
    SRel (if c then [s] else []) (if c then [s'] else []) := by
  cases c
  · exact SRel.nil
  · exact SRel.single h

theorem SRel.of_mem_iff {SA SB SB' : List (List Goal)} (h : SRel SA SB) (e : ∀ k, k ∈ SB ↔ k ∈ SB') :
    SRel SA SB' :=
  ⟨fun g hg => let ⟨k, hk, m⟩ := h.1 g hg; ⟨k, (e k).1 hk, m⟩,
   fun k hk => h.2 k ((e k).2 hk)⟩

/-! ## Pushed boundaries -/

theorem bound_iface_swap_r (x : Span) : (bound x.rightIface).map Span.swap = bound x.swap.leftIface := by
  have : x.swap.leftIface = x.rightIface := by rw [leftIface_eq, Span.swap_swap]
  rw [this]
  cases h : bound x.rightIface with
  | none => rfl
  | some s => obtain rfl := bound_some h; rfl

theorem bound_iface_swap_l (x : Span) : (bound x.leftIface).map Span.swap = bound x.swap.rightIface := by
  rw [← leftIface_eq]
  cases h : bound x.leftIface with
  | none => rfl
  | some s => obtain rfl := bound_some h; rfl

theorem push_r_mirror {x x' : Span} (e : x'.Equiv x.swap) :
    boundEq ((bound x.rightIface).map Span.swap) (bound x'.leftIface) = true := by
  rw [bound_iface_swap_r]; exact (iface_equiv _ _ (Span.Equiv.symm e)).2

theorem push_l_mirror {x x' : Span} (e : x'.Equiv x.swap) :
    boundEq ((bound x.leftIface).map Span.swap) (bound x'.rightIface) = true := by
  rw [bound_iface_swap_l]; exact (iface_equiv _ _ (Span.Equiv.symm e)).1

/-! ## Corresponding goals -/

variable {P : Program} {tsA tsB : Tables}

/-- Goals of the run and of the mirrored run whose answers are read
together: their answer lists are swaps of each other up to equivalence. -/
theorem classEq_goals (R : TabsRel tsA tsB) {gs hs : List Goal} (h : MSet gs hs) :
    ClassEq (hs.flatMap (answersOf tsB)) ((gs.flatMap (answersOf tsA)).map Span.swap) := by
  constructor
  · intro z hz
    obtain ⟨k, hk, hz⟩ := List.mem_flatMap.1 hz
    obtain ⟨g, hg, m⟩ := h.2 k hk
    obtain ⟨w, hw, e⟩ := (ClassEq.of_stepEquiv (answersOf_mirror R m)).1 z hz
    obtain ⟨w₀, hw₀, rfl⟩ := List.mem_map.1 hw
    exact ⟨_, List.mem_map_of_mem (List.mem_flatMap.2 ⟨g, hg, hw₀⟩), e⟩
  · intro w hw
    obtain ⟨w₀, hw₀, rfl⟩ := List.mem_map.1 hw
    obtain ⟨g, hg, hw₀⟩ := List.mem_flatMap.1 hw₀
    obtain ⟨k, hk, m⟩ := h.1 g hg
    obtain ⟨z, hz, e⟩ := (ClassEq.of_stepEquiv (answersOf_mirror R m)).2 _ (List.mem_map_of_mem hw₀)
    exact ⟨z, List.mem_flatMap.2 ⟨k, hk, hz⟩, e⟩

theorem swc_answers (R : TabsRel tsA tsB) {g h : Goal} (m : Mirror g h) :
    SwC (answersOf tsA g) (answersOf tsB h) := SwC.of_stepEquiv (answersOf_mirror R m)

theorem swc_maxima (R : TabsRel tsA tsB) {g h : Goal} (m : Mirror g h) :
    SwC (maxima (answersOf tsA g)) (maxima (answersOf tsB h)) := by
  apply SwC.of_stepEquiv
  rw [← maxima_map_swap]
  exact maxima_stepEquiv (ClassEq.of_stepEquiv (answersOf_mirror R m))

/-- What a goal computes and needs in a round, as `produceStrategies` and
`tableStrategies` give it, corresponds for mirrored goals. -/
def StepMirror (P : Program) (tsA tsB : Tables) (G H : Goal) : Prop :=
  ClassEq (produce.produceStrategies P.dual tsB H).1
      ((produce.produceStrategies P tsA G).1.map Span.swap) ∧
    MSet (produce.produceStrategies P tsA G).2 (produce.produceStrategies P.dual tsB H).2 ∧
    SRel (strategies.tableStrategies P tsA G) (strategies.tableStrategies P.dual tsB H)

theorem MSet.cons {g h : Goal} {gs hs : List Goal} (m : Mirror g h) (e : MSet gs hs) :
    MSet (g :: gs) (h :: hs) := by
  have := (MSet.pair (g₂ := g) (h₁ := h) (g₁ := g) (h₂ := h) m m).append e
  refine ⟨fun x hx => ?_, fun y hy => ?_⟩
  · rcases List.mem_cons.1 hx with rfl | hx
    · exact ⟨h, List.mem_cons_self .., m⟩
    · obtain ⟨k, hk, mk⟩ := e.1 x hx; exact ⟨k, List.mem_cons_of_mem _ hk, mk⟩
  · rcases List.mem_cons.1 hy with rfl | hy
    · exact ⟨g, List.mem_cons_self .., m⟩
    · obtain ⟨k, hk, mk⟩ := e.2 y hy; exact ⟨k, List.mem_cons_of_mem _ hk, mk⟩

theorem seq_step (hK : Obligation.SimplifyRespectsEquiv P.theory) (R : TabsRel tsA tsB) {G H : Goal}
    {a b a' b' : Rel} (hG : G.e = .seq a b) (hH : H.e = .seq a' b') (ha : canon a' = canon b.dual)
    (hb : canon b' = canon a.dual) (hl : boundEq (G.rb.map Span.swap) H.lb = true)
    (hr : boundEq (G.lb.map Span.swap) H.rb = true) : StepMirror P tsA tsB G H := by
  have mRL : Mirror (seqRight G b) (seqLeft H a') := mirror_mk ha hl rfl
  have mLR : Mirror (seqLeft G a) (seqRight H b') := mirror_mk hb rfl hr
  have dRL := doneOf_mirror R mRL
  have dLR := doneOf_mirror R mLR
  have pushRL : ∀ y x', x'.Equiv y.swap → Mirror (seqPushR G a y) (seqPushL H b' x') :=
    fun y x' e => mirror_mk hb (push_l_mirror e) hr
  have pushLR : ∀ x y', y'.Equiv x.swap → Mirror (seqPushL G b x) (seqPushR H a' y') :=
    fun x y' e => mirror_mk ha hl (push_r_mirror e)
  simp only [StepMirror, produce.produceStrategies, strategies.tableStrategies, hG, hH,
    Program.dual_theory]
  generalize hxs : answersOf tsA (seqLeft G a) = xs
  generalize hys : answersOf tsA (seqRight G b) = ys
  generalize hxs' : answersOf tsB (seqLeft H a') = xs'
  generalize hys' : answersOf tsB (seqRight H b') = ys'
  have sY : SwC ys xs' := hys ▸ hxs' ▸ swc_answers R mRL
  have sX : SwC xs ys' := hxs ▸ hys' ▸ swc_answers R mLR
  have mY : SwC (maxima ys) (maxima xs') := hys ▸ hxs' ▸ swc_maxima R mRL
  have mX : SwC (maxima xs) (maxima ys') := hxs ▸ hys' ▸ swc_maxima R mLR
  rw [dRL, dLR]
  refine ⟨?_, ?_, ?_⟩
  · refine classEq_cross ?_ ?_ ?_
    · -- the joins: the mirror's left answers are the swaps of the right answers
      have hj : ClassEq (xs'.flatMap fun x' => ys'.flatMap fun y' => composeLive P.theory x' y')
          ((ys.flatMap fun y => xs.flatMap fun x => composeLive P.theory x y).map Span.swap) :=
        classEq_flatMap_sw sY fun y _ x' _ ey =>
          classEq_flatMap_sw sX fun x _ y' _ ex => composeLive_mirror hK ey ex
      refine hj.trans (ClassEq.map_swap (ClassEq.of_mem_iff fun z => ?_))
      simp only [List.mem_flatMap]
      constructor
      · rintro ⟨y, hy, x, hx, h⟩; exact ⟨x, hx, y, hy, h⟩
      · rintro ⟨x, hx, y, hy, h⟩; exact ⟨y, hy, x, hx, h⟩
    · cases doneOf tsA (seqRight G b)
      · exact ClassEq.refl _
      · simp only [ite_true, List.flatMap_map]
        refine classEq_flatMap_sw mY fun y _ x' _ e => ?_
        exact classEq_flatMap_sw (swc_answers R (pushRL y x' e)) fun x _ y' _ e' =>
          composeLive_mirror hK e e'
    · cases doneOf tsA (seqLeft G a)
      · exact ClassEq.refl _
      · simp only [ite_true, List.flatMap_map]
        refine classEq_flatMap_sw mX fun x _ y' _ e => ?_
        exact classEq_flatMap_sw (swc_answers R (pushLR x y' e)) fun y _ x' _ e' =>
          composeLive_mirror hK e' e
  · have pl : MSet ((maxima xs).map (seqPushL G b)) ((maxima ys').map (seqPushR H a')) :=
      MSet.map mX pushLR
    have pr : MSet ((maxima ys).map (seqPushR G a)) ((maxima xs').map (seqPushL H b')) :=
      MSet.map mY pushRL
    have e0 := MSet.pair mLR mRL
    cases doneOf tsA (seqLeft G a) <;> cases doneOf tsA (seqRight G b) <;>
      simp only [Bool.false_eq_true, ite_false, ite_true, List.map_nil, List.append_nil, List.map_map,
        Function.comp_def]
    · exact e0
    · exact e0.append pr
    · exact e0.append pl
    · refine (e0.append (pl.append pr)).of_mem_iff fun k => ?_
      simp only [List.mem_append]; tauto
  · have pl : MSet (seqLeft G a :: (maxima xs).map (seqPushL G b))
        (seqRight H b' :: (maxima ys').map (seqPushR H a')) := MSet.cons mLR (MSet.map mX pushLR)
    have pr : MSet (seqRight G b :: (maxima ys).map (seqPushR G a))
        (seqLeft H a' :: (maxima xs').map (seqPushL H b')) := MSet.cons mRL (MSet.map mY pushRL)
    have e0 := SRel.single (MSet.pair mLR mRL)
    cases doneOf tsA (seqLeft G a) <;> cases doneOf tsA (seqRight G b) <;>
      simp only [Bool.false_eq_true, ite_false, ite_true, List.append_nil]
    · exact e0
    · exact e0.append (SRel.single pr)
    · exact e0.append (SRel.single pl)
    · refine (e0.append ((SRel.single pl).append (SRel.single pr))).of_mem_iff fun k => ?_
      simp only [List.mem_append]; tauto

theorem and_step (hK : Obligation.SimplifyRespectsEquiv P.theory) (R : TabsRel tsA tsB) {G H : Goal}
    {a b a' b' : Rel} (hG : G.e = .and a b) (hH : H.e = .and a' b') (ha : canon a' = canon a.dual)
    (hb : canon b' = canon b.dual) (hl : boundEq (G.rb.map Span.swap) H.lb = true)
    (hr : boundEq (G.lb.map Span.swap) H.rb = true) : StepMirror P tsA tsB G H := by
  have mL : Mirror (andLeft G a) (andLeft H a') := mirror_mk ha hl hr
  have mR : Mirror (andRight G b) (andRight H b') := mirror_mk hb hl hr
  have dL := doneOf_mirror R mL
  have dR := doneOf_mirror R mR
  have pushB : ∀ x x', x'.Equiv x.swap → Mirror (andPush b x) (andPush b' x') :=
    fun x x' e => mirror_mk hb (push_r_mirror e) (push_l_mirror e)
  have pushA : ∀ y y', y'.Equiv y.swap → Mirror (andPush a y) (andPush a' y') :=
    fun y y' e => mirror_mk ha (push_r_mirror e) (push_l_mirror e)
  simp only [StepMirror, produce.produceStrategies, strategies.tableStrategies, hG, hH,
    Program.dual_theory]
  generalize hxs : answersOf tsA (andLeft G a) = xs
  generalize hys : answersOf tsA (andRight G b) = ys
  generalize hxs' : answersOf tsB (andLeft H a') = xs'
  generalize hys' : answersOf tsB (andRight H b') = ys'
  have sX : SwC xs xs' := hxs ▸ hxs' ▸ swc_answers R mL
  have sY : SwC ys ys' := hys ▸ hys' ▸ swc_answers R mR
  have mX : SwC (maxima xs) (maxima xs') := hxs ▸ hxs' ▸ swc_maxima R mL
  have mY : SwC (maxima ys) (maxima ys') := hys ▸ hys' ▸ swc_maxima R mR
  rw [dL, dR]
  refine ⟨?_, ?_, ?_⟩
  · rw [List.map_append, List.map_append]
    refine ClassEq.append (ClassEq.append ?_ ?_) ?_
    · exact classEq_flatMap_sw sX fun x _ x' _ ex =>
        classEq_flatMap_sw sY fun y _ y' _ ey => meetLive_mirror hK ex ey
    · cases doneOf tsA (andLeft G a)
      · exact ClassEq.refl _
      · simp only [ite_true, List.flatMap_map]
        refine classEq_flatMap_sw mX fun x _ x' _ e => ?_
        exact classEq_flatMap_sw (swc_answers R (pushB x x' e)) fun y _ y' _ e' =>
          meetLive_mirror hK e e'
    · cases doneOf tsA (andRight G b)
      · exact ClassEq.refl _
      · simp only [ite_true, List.flatMap_map]
        refine classEq_flatMap_sw mY fun y _ y' _ e => ?_
        exact classEq_flatMap_sw (swc_answers R (pushA y y' e)) fun x _ x' _ e' =>
          meetLive_mirror hK e' e
  · have pl : MSet ((maxima xs).map (andPush b)) ((maxima xs').map (andPush b')) := MSet.map mX pushB
    have pr : MSet ((maxima ys).map (andPush a)) ((maxima ys').map (andPush a')) := MSet.map mY pushA
    have e0 : MSet [andLeft G a, andRight G b] [andLeft H a', andRight H b'] :=
      (MSet.cons mL (MSet.cons mR ⟨fun _ h => absurd h List.not_mem_nil, fun _ h => absurd h List.not_mem_nil⟩))
    cases doneOf tsA (andLeft G a) <;> cases doneOf tsA (andRight G b) <;>
      simp only [Bool.false_eq_true, ite_false, ite_true, List.map_nil, List.append_nil, List.map_map,
        Function.comp_def]
    · exact e0
    · exact e0.append pr
    · exact e0.append pl
    · exact (e0.append pl).append pr
  · have pl : MSet (andLeft G a :: (maxima xs).map (andPush b))
        (andLeft H a' :: (maxima xs').map (andPush b')) := MSet.cons mL (MSet.map mX pushB)
    have pr : MSet (andRight G b :: (maxima ys).map (andPush a))
        (andRight H b' :: (maxima ys').map (andPush a')) := MSet.cons mR (MSet.map mY pushA)
    have e0 : SRel [[andLeft G a, andRight G b]] [[andLeft H a', andRight H b']] :=
      SRel.single (MSet.cons mL (MSet.cons mR ⟨fun _ h => absurd h List.not_mem_nil,
        fun _ h => absurd h List.not_mem_nil⟩))
    cases doneOf tsA (andLeft G a) <;> cases doneOf tsA (andRight G b) <;>
      simp only [Bool.false_eq_true, ite_false, ite_true, List.append_nil]
    · exact e0
    · exact e0.append (SRel.single pr)
    · exact e0.append (SRel.single pl)
    · exact (e0.append (SRel.single pl)).append (SRel.single pr)

theorem call_step (R : TabsRel tsA tsB) {G H : Goal} {n : Name} (hG : G.e = .call n) (hH : H.e = .call n)
    (hl : boundEq (G.rb.map Span.swap) H.lb = true) (hr : boundEq (G.lb.map Span.swap) H.rb = true) :
    StepMirror P tsA tsB G H := by
  have m : Mirror (callGoal P G n) (callGoal P.dual H n) :=
    mirror_mk (by simp only [callGoal, Program.dual_body]) hl hr
  simp only [StepMirror, produce.produceStrategies, strategies.tableStrategies, hG, hH]
  refine ⟨ClassEq.of_stepEquiv (answersOf_mirror R m), MSet.cons m ?_, SRel.single (MSet.cons m ?_)⟩ <;>
    exact ⟨fun _ h => absurd h List.not_mem_nil, fun _ h => absurd h List.not_mem_nil⟩

theorem span_step (hK : Obligation.SimplifyRespectsEquiv P.theory) {G H : Goal} {s : Span}
    (hG : G.e = .span s) (hH : H.e = .span s.swap)
    (hl : boundEq (G.rb.map Span.swap) H.lb = true) (hr : boundEq (G.lb.map Span.swap) H.rb = true) :
    StepMirror P tsA tsB G H := by
  simp only [StepMirror, produce.produceStrategies, strategies.tableStrategies, hG, hH,
    Program.dual_theory]
  have e : MSet [] [] := ⟨fun _ h => absurd h List.not_mem_nil, fun _ h => absurd h List.not_mem_nil⟩
  exact ⟨spanAnswer_mirror hK s hl hr, e, SRel.single e⟩

theorem zero_step {G H : Goal} (hG : G.e = .zero) (hH : H.e = .zero) : StepMirror P tsA tsB G H := by
  simp only [StepMirror, produce.produceStrategies, strategies.tableStrategies, hG, hH]
  have e : MSet [] [] := ⟨fun _ h => absurd h List.not_mem_nil, fun _ h => absurd h List.not_mem_nil⟩
  exact ⟨ClassEq.refl _, e, SRel.single e⟩

theorem orBranches_mkOr_eq : ∀ {L : List Rel}, (∀ x ∈ L, NotOr x) → L ≠ [] → orBranches (mkOr L) = L
  | [], _, h => absurd rfl h
  | [e], hL, _ => by rw [mkOr, orBranches_notOr (hL e (by simp))]
  | e :: e' :: es, hL, _ => by
    rw [show mkOr (e :: e' :: es) = .or e (mkOr (e' :: es)) from rfl, orBranches,
      orBranches_notOr (hL e (by simp)), orBranches_mkOr_eq (fun x hx => hL x (by simp_all)) (by simp)]
    rfl

theorem notOr_sorted {L : List Rel} (h : ∀ x ∈ L, NotOr x) : ∀ x ∈ sortedBranches L, NotOr x :=
  fun x hx => h x (mem_sortedBranches.1 hx).1

/-- The branches of a canonical `|` are canonical and not `0`. -/
theorem branches_canonical {a b : Rel} (hc : canon (Rel.or a b) = Rel.or a b) {c : Rel}
    (h : c ∈ orBranches (Rel.or a b)) : c ≠ .zero ∧ canon c = c := by
  have hE := hc
  rw [show canon (Rel.or a b) = mkOr (sortedBranches (orBranches (canon a) ++ orBranches (canon b)))
    from rfl] at hE
  have hT : ∀ x ∈ sortedBranches (orBranches (canon a) ++ orBranches (canon b)), NotOr x :=
    notOr_sorted fun x hx => (List.mem_append.1 hx).elim notOr_of_mem_orBranches notOr_of_mem_orBranches
  have hne : sortedBranches (orBranches (canon a) ++ orBranches (canon b)) ≠ [] := by
    intro h0; rw [h0] at hE; cases hE
  have hbr := orBranches_mkOr_eq hT hne
  rw [hE] at hbr
  rw [hbr] at h
  have h0 := (mem_sortedBranches.1 h).2
  refine ⟨h0, ?_⟩
  have : c ∈ orBranches (canon (Rel.or a b)) := by rw [hc, hbr]; exact h
  obtain ⟨l, _, rfl⟩ := (mem_orBranches_canon (.or a b) h0).1 this
  exact canon_idem l

theorem canon_dual_ne_zero {c : Rel} (h0 : c ≠ .zero) (hc : canon c = c) : canon c.dual ≠ .zero := by
  intro h
  apply h0
  rw [← hc, ← canon_dual_canon c, ← canon_dual c, h]; rfl

theorem or_step (R : TabsRel tsA tsB) {G H : Goal} {a b : Rel} (hG : G.e = .or a b)
    (hc : canon (Rel.or a b) = Rel.or a b) (hH : H.e = canon (Rel.or a b).dual)
    (hl : boundEq (G.rb.map Span.swap) H.lb = true) (hr : boundEq (G.lb.map Span.swap) H.rb = true) :
    StepMirror P tsA tsB G H := by
  obtain ⟨u, v, rest, hs⟩ := canon_dual_or_two hc
  have hT : ∀ x ∈ sortedBranches (orBranches (canon (Rel.or a b).dual)), NotOr x :=
    notOr_sorted fun x hx => notOr_of_mem_orBranches hx
  have hH' : H.e = .or u (mkOr (v :: rest)) := by
    rw [hH, canon_eq_mkOr, hs]; rfl
  have hbr : orBranches (Rel.or u (mkOr (v :: rest))) = u :: v :: rest := by
    rw [← hs, ← orBranches_mkOr_eq hT (by rw [hs]; simp), hs]; rfl
  have memB : ∀ z, z ∈ u :: v :: rest ↔ z ≠ .zero ∧ ∃ c ∈ orBranches (Rel.or a b), canon c.dual = z := by
    intro z
    rw [← hs, mem_sortedBranches]
    constructor
    · rintro ⟨hz, h0⟩
      obtain ⟨l, hl', rfl⟩ := (mem_orBranches_canon _ h0).1 hz
      rw [orBranches_dual] at hl'
      obtain ⟨c, hc', rfl⟩ := List.mem_map.1 hl'
      exact ⟨h0, c, hc', rfl⟩
    · rintro ⟨h0, c, hc', rfl⟩
      refine ⟨(mem_orBranches_canon _ h0).2 ⟨c.dual, ?_, rfl⟩, h0⟩
      rw [orBranches_dual]; exact List.mem_map_of_mem hc'
  have leaves : MSet (orLeaves G a b) (orLeaves H u (mkOr (v :: rest))) := by
    unfold orLeaves
    rw [hbr]
    constructor
    · intro g hg
      obtain ⟨c, hc', rfl⟩ := List.mem_map.1 hg
      obtain ⟨h0, hcc⟩ := branches_canonical hc hc'
      refine ⟨⟨H.lb, canon c.dual, H.rb⟩, List.mem_map_of_mem
        ((memB _).2 ⟨canon_dual_ne_zero h0 hcc, c, hc', rfl⟩), ?_⟩
      exact mirror_mk (canon_idem _) hl hr
    · intro k hk
      obtain ⟨z, hz, rfl⟩ := List.mem_map.1 hk
      obtain ⟨_, c, hc', rfl⟩ := (memB z).1 hz
      exact ⟨⟨G.lb, c, G.rb⟩, List.mem_map_of_mem hc', mirror_mk (canon_idem _) hl hr⟩
  simp only [StepMirror, produce.produceStrategies, strategies.tableStrategies, hG, hH']
  exact ⟨classEq_goals R leaves, leaves, SRel.single leaves⟩

theorem step_mirror (hK : Obligation.SimplifyRespectsEquiv P.theory) (R : TabsRel tsA tsB) {G H : Goal}
    (hG : IsKey G) (he : H.e = canon G.e.dual) (hl : boundEq (G.rb.map Span.swap) H.lb = true)
    (hr : boundEq (G.lb.map Span.swap) H.rb = true) : StepMirror P tsA tsB G H := by
  obtain ⟨hc, hn⟩ := hG.canonical
  cases hGe : G.e with
  | zero => rw [hGe] at he; exact zero_step hGe he
  | span s => rw [hGe] at he; exact span_step hK hGe he hl hr
  | or a b => rw [hGe] at he hc; exact or_step R hGe hc he hl hr
  | and a b => rw [hGe] at he; exact and_step hK R hGe he (canon_idem _) (canon_idem _) hl hr
  | seq a b => rw [hGe] at he; exact seq_step hK R hGe he (canon_idem _) (canon_idem _) hl hr
  | conv a => exact absurd hGe (hn a)
  | call n => rw [hGe] at he; exact call_step R hGe he hl hr

/-- **What mirrored tables compute in a round.** The candidates of a table of
the mirrored run have the same classes as the swapped candidates of the
corresponding table of the run, their requests are mirrors, and so are their
strategies. -/
theorem produce_mirror (hK : Obligation.SimplifyRespectsEquiv P.theory) (R : TabsRel tsA tsB)
    {G H : Goal} (hG : IsKey G) (hm : H.same (KD G) = true) (d : Nat) :
    ClassEq (produce P.dual d tsB H).1 ((produce P d tsA G).1.map Span.swap) ∧
      MSet (produce P d tsA G).2 (produce P.dual d tsB H).2 ∧
      SRel (strategies P d tsA G) (strategies P.dual d tsB H) := by
  rw [Goal.same_iff] at hm
  obtain ⟨he, hl, hr⟩ := hm
  simp only [KD] at he hl hr
  have hl' := boundEq_symm hl
  have hr' := boundEq_symm hr
  obtain ⟨hc, hp, hs⟩ := step_mirror hK R hG he hl' hr'
  obtain ⟨hf, hu⟩ := unfold_mirror hK he hl' hr' d
  refine ⟨?_, hp, ?_⟩
  · simp only [produce, List.map_append]
    exact hu.append hc
  · simp only [strategies, hf]
    exact (SRel.ite ⟨fun _ h => absurd h List.not_mem_nil, fun _ h => absurd h List.not_mem_nil⟩).append hs

end R001

end RwLog
