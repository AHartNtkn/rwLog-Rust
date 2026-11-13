/-
# The walk meets the specification of the unfolding race

`walk_ok`: the items of a walk are the unfolding of the goal between its near
and its far boundary (`WOk`), in either direction and whatever was pushed on
the near side. A meet is the case this file adds to
`Unfolding/WalkChain.lean`: its answers are the `meetA` of one answer of
every member, and it is handed on as an open product when every member has an
item between the boundaries the meet stands between and one of them an open
one.

`walkRace_ok`: so the race answered by a walk, which says the unfolding is
final when it met no open item, meets the specification the tabled machine
asks of an unfolding race (`UOk`).
-/
import RwLog.Rungs.Tabled.Unfolding.WalkChain

namespace RwLog

namespace Tabled

namespace Unfold

open Answer

variable {R : Type} [Answer R] [DecidableEq R] {D : Domain R} {P : Program}

variable (hL : D.Lawful P.sorts.interp) (K : Kernel R Cost) (hK : K.Refines D)

/-! ## A meet -/

section meet

variable (rev : Bool) (cl opq : Bool) (wv : Rel → List (It D P)) (near far : Option R)

theorem metNext_opn {pre : Met (Ans D P)} {it : It D P} :
    metNext K hK cl pre it = .opn ↔ pre = .opn ∨ ∃ t, it = .opn t := by
  cases it with
  | opn t => simp [metNext]
  | closed b =>
    cases pre with
    | start => cases cl <;> simp [metNext]
    | closed a => simp only [metNext]; split <;> simp
    | dead => simp [metNext]
    | opn => simp [metNext]

theorem andV_cons {pre : Met (Ans D P)} {x : Rel} {xs : List Rel}
    (h : opq = true ∨ (pre ≠ .opn ∧ pre ≠ .dead)) :
    andV K hK cl opq wv far pre (x :: xs) =
      (wv x).flatMap fun it => andV K hK cl opq wv far (metNext K hK cl pre it) xs := by
  cases opq with
  | true => cases pre <;> rfl
  | false =>
    obtain ⟨h₁, h₂⟩ := h.resolve_left (by simp)
    cases pre with
    | start => rfl
    | closed a => rfl
    | dead => exact absurd rfl h₂
    | opn => exact absurd rfl h₁

/-- The meet is handed on as an open product exactly when open products are
asked for, every member still to walk has an item, and a member walked or
still to walk has an open one. -/
theorem mem_andV_opn : ∀ (xs : List Rel) (pre : Met (Ans D P)) (t : Option R),
    Item.opn t ∈ andV K hK cl opq wv far pre xs ↔
      t = far ∧ opq = true ∧ (∀ x ∈ xs, wv x ≠ []) ∧
        (pre = .opn ∨ ∃ x ∈ xs, ∃ t', Item.opn t' ∈ wv x)
  | [], pre, t => by
    cases pre <;> cases cl <;> cases opq <;> simp [andV, eq_comm]
  | x :: xs, pre, t => by
    have ih := fun pre => mem_andV_opn xs pre t
    by_cases h : opq = true ∨ (pre ≠ .opn ∧ pre ≠ .dead)
    · rw [andV_cons K hK cl opq wv far h, List.mem_flatMap]
      simp only [ih, metNext_opn]
      constructor
      · rintro ⟨it, hit, rfl, ho, hall, hex⟩
        refine ⟨rfl, ho, fun y hy => ?_, ?_⟩
        · rcases List.mem_cons.1 hy with rfl | hy
          · exact List.ne_nil_of_mem hit
          · exact hall y hy
        · rcases hex with (hp | ⟨t', rfl⟩) | ⟨y, hy, t', ht'⟩
          · exact .inl hp
          · exact .inr ⟨_, by simp, t', hit⟩
          · exact .inr ⟨y, List.mem_cons_of_mem _ hy, t', ht'⟩
      · rintro ⟨rfl, ho, hall, hex⟩
        have hall' : ∀ y ∈ xs, wv y ≠ [] := fun y hy => hall y (List.mem_cons_of_mem _ hy)
        rcases hex with hp | ⟨y, hy, t', ht'⟩
        · obtain ⟨it, hit⟩ := List.exists_mem_of_ne_nil _ (hall x (by simp))
          exact ⟨it, hit, rfl, ho, hall', .inl (.inl hp)⟩
        · rcases List.mem_cons.1 hy with rfl | hy
          · exact ⟨_, ht', rfl, ho, hall', .inl (.inr ⟨t', rfl⟩)⟩
          · obtain ⟨it, hit⟩ := List.exists_mem_of_ne_nil _ (hall x (by simp))
            exact ⟨it, hit, rfl, ho, hall', .inr ⟨y, hy, t', ht'⟩⟩
    · have ho : opq = false := by
        cases opq
        · rfl
        · exact absurd (.inl rfl) h
      subst ho
      have : andV K hK cl false wv far pre (x :: xs) = [] := by
        cases pre with
        | start => exact absurd (.inr ⟨by simp, by simp⟩) h
        | closed a => exact absurd (.inr ⟨by simp, by simp⟩) h
        | dead => rfl
        | opn => rfl
      rw [this]
      simp

/-- After an open member, or when the answers walked relate nothing, nothing
is an answer. -/
theorem and_noclosed : ∀ (xs : List Rel) (pre : Met (Ans D P)) (a : Ans D P),
    pre = .opn ∨ pre = .dead → Item.closed a ∉ andV K hK cl opq wv far pre xs
  | [], pre, a, h => by
    rcases h with rfl | rfl <;> cases opq <;> simp [andV]
  | x :: xs, pre, a, h => by
    have ih := fun pre h => and_noclosed xs pre a h
    cases opq with
    | false => rcases h with rfl | rfl <;> simp [andV]
    | true =>
      rw [andV_cons K hK cl true wv far (.inl rfl), List.mem_flatMap]
      rintro ⟨it, -, h'⟩
      refine ih _ ?_ h'
      rcases h with rfl | rfl
      · cases it <;> exact .inl rfl
      · cases it
        · exact .inr rfl
        · exact .inl rfl

theorem mem_andV_closed_cons {pre : Met (Ans D P)} {x : Rel} {xs : List Rel} {c : Ans D P} :
    Item.closed c ∈ andV K hK cl opq wv far pre (x :: xs) ↔
      ∃ it ∈ wv x, Item.closed c ∈ andV K hK cl opq wv far (metNext K hK cl pre it) xs := by
  by_cases h : opq = true ∨ (pre ≠ .opn ∧ pre ≠ .dead)
  · rw [andV_cons K hK cl opq wv far h, List.mem_flatMap]
  · have hp : pre = .opn ∨ pre = .dead := by
      cases pre with
      | start => exact absurd (.inr ⟨by simp, by simp⟩) h
      | closed a => exact absurd (.inr ⟨by simp, by simp⟩) h
      | dead => exact .inr rfl
      | opn => exact .inl rfl
    constructor
    · intro hc
      exact absurd hc (and_noclosed K hK cl opq wv far _ pre c hp)
    · rintro ⟨it, -, hc⟩
      refine absurd hc (and_noclosed K hK cl opq wv far xs _ c ?_)
      rcases hp with rfl | rfl
      · cases it <;> exact .inl rfl
      · cases it
        · exact .inr rfl
        · exact .inl rfl

theorem mem_andV_closed_nil {pre : Met (Ans D P)} {c : Ans D P} :
    Item.closed c ∈ andV K hK cl opq wv far pre [] ↔ cl = true ∧ pre = .closed c := by
  cases pre <;> cases cl <;> cases opq <;> simp [andV, eq_comm]

/-- After an answer, an answer of the meet is the `meetA` with an answer of
the next member, carried on. -/
theorem mem_andV_closed {x : Rel} {xs : List Rel} {a c : Ans D P} :
    Item.closed c ∈ andV K hK cl opq wv far (.closed a) (x :: xs) ↔
      ∃ b c', Item.closed b ∈ wv x ∧ (Ans.meetA D P K hK a b).val = some c' ∧
        Item.closed c ∈ andV K hK cl opq wv far (.closed c') xs := by
  rw [mem_andV_closed_cons]
  constructor
  · rintro ⟨it, hit, hc⟩
    cases it with
    | closed b =>
      simp only [metNext] at hc
      cases hm : (Ans.meetA D P K hK a b).val with
      | none =>
        rw [hm] at hc
        exact absurd hc (and_noclosed K hK cl opq wv far xs _ c (.inr rfl))
      | some c' =>
        rw [hm] at hc
        exact ⟨b, c', hit, hm, hc⟩
    | opn t => exact absurd hc (and_noclosed K hK cl opq wv far xs _ c (.inl rfl))
  · rintro ⟨b, c', hb, hm, hc⟩
    refine ⟨_, hb, ?_⟩
    simp only [metNext]
    rw [hm]
    exact hc

/-- When the answers are not asked for, none is handed on. -/
theorem and_noclosed_flag : ∀ (xs : List Rel) (pre : Met (Ans D P)) (a : Ans D P),
    Item.closed a ∉ andV K hK false opq wv far pre xs
  | [], pre, a => by
    rw [mem_andV_closed_nil]
    simp
  | x :: xs, pre, a => by
    rw [mem_andV_closed_cons]
    rintro ⟨it, -, h⟩
    exact and_noclosed_flag xs _ a h

/-- The answers of a meet are answers of its goal. -/
theorem and_goal : ∀ (xs : List Rel) (pm : List Rel) (a : Ans D P), pm ≠ [] →
    (∀ y ∈ pm, NotAnd y) → a.goal = goalD rev near (mkAnd (sortedParts pm)) far →
    (∀ x ∈ xs, NotAnd x ∧ ∀ b, Item.closed b ∈ wv x → b.goal = goalD rev near x far) →
    ∀ c, Item.closed c ∈ andV K hK cl opq wv far (.closed a) xs →
      c.goal = goalD rev near (mkAnd (sortedParts (pm ++ xs))) far
  | [], pm, a, _, _, ha, _, c, hc => by
    obtain ⟨-, e⟩ := (mem_andV_closed_nil K hK cl opq wv far).1 hc
    obtain rfl : a = c := by simpa using e
    rw [List.append_nil]
    exact ha
  | x :: xs, pm, a, hpm, hns, ha, H, c, hc => by
    obtain ⟨b, c', h₀, hm, h'⟩ := (mem_andV_closed K hK cl opq wv far).1 hc
    have hx := (H x (by simp)).1
    have hg := meetD_goal K hK rev hm ha ((H x (by simp)).2 b h₀)
    rw [andParts_mkAnd (sortedParts_ne_nil hpm)
        (fun z hz => hns z ((sortedParts_perm _).mem_iff.1 hz)),
      andParts_notAnd (H x (by simp)).1,
      sortedParts_eq ((sortedParts_perm pm).append_right [x])] at hg
    have := and_goal xs (pm ++ [x]) c' (by simp)
      (fun y hy => by
        rcases List.mem_append.1 hy with h | h
        · exact hns y h
        · obtain rfl : y = x := by simpa using h
          exact hx) hg
      (fun y hy => H y (List.mem_cons_of_mem _ hy)) c h'
    rwa [List.append_assoc, List.singleton_append] at this

variable {W : PRel} (hW : W.Nonempty)

include hL hW in
/-- When every member has an answer that relates the pairs, the meet has
one. -/
theorem and_closed : ∀ (xs : List Rel) (a : Ans D P) (n₀ : Rel),
    a.goal = goalD rev near n₀ far → W ⊆ den P.sorts.interp a.span →
    (∀ x ∈ xs, ∃ b, Item.closed b ∈ wv x ∧ b.goal = goalD rev near x far ∧
      W ⊆ den P.sorts.interp b.span) →
    ∃ c, Item.closed c ∈ andV K hK true opq wv far (.closed a) xs ∧
      W ⊆ den P.sorts.interp c.span
  | [], a, _, _, hWa, _ => ⟨a, (mem_andV_closed_nil K hK true opq wv far).2 ⟨rfl, rfl⟩, hWa⟩
  | x :: xs, a, n₀, ha, hWa, H => by
    obtain ⟨b, hb, hbg, hWb⟩ := H x (by simp)
    obtain ⟨c', hm, hWc, hcg⟩ := meetD hL K hK rev ha hbg hWa hWb hW
    obtain ⟨c, hc, hWc'⟩ := and_closed xs c' _ hcg hWc
      (fun y hy => H y (List.mem_cons_of_mem _ hy))
    exact ⟨c, (mem_andV_closed K hK true opq wv far).2 ⟨b, c', hb, hm, hc⟩, hWc'⟩

end meet

section meetNode

variable (rev : Bool) {near far : Option R} (hn : IsBound D near) (hf : IsBound D far)
  {xs : List Rel} (h2 : 2 ≤ xs.length) (hna : ∀ x ∈ xs, NotAnd x) (hs : xs.Pairwise RelLE)
  (C O : Rel → Set GRel)

include h2 hna hs in
/-- The answers a meet hands on are answers of its goal. -/
theorem meet_goal_part (cl opq : Bool) (wv : Rel → List (It D P))
    (hw : ∀ x ∈ xs, WOk rev near x far (C x) (O x) (wv x)) (c : Ans D P)
    (hc : Item.closed c ∈ andV K hK cl opq wv far .start xs) :
    c.goal = goalD rev near (mkAnd xs) far := by
  obtain ⟨x₀, tl, rfl⟩ : ∃ x₀ tl, xs = x₀ :: tl := by
    cases xs with
    | nil => simp at h2
    | cons a b => exact ⟨a, b, rfl⟩
  obtain ⟨it₀, h₀, h'⟩ := (mem_andV_closed_cons K hK cl opq wv far).1 hc
  cases it₀ with
  | closed b =>
    cases cl with
    | false => exact absurd h' (and_noclosed K hK false opq wv far _ _ c (.inr rfl))
    | true =>
      have hb : b.goal = goalD rev near (mkAnd (sortedParts [x₀])) far := by
        rw [sortedParts_of_sorted (List.pairwise_singleton _ _)]
        exact (hw x₀ (by simp)).goal b h₀
      have := and_goal K hK rev true opq wv near far tl [x₀] b (by simp)
        (fun y hy => by
          obtain rfl : y = x₀ := by simpa using hy
          exact hna _ (by simp)) hb
        (fun y hy => ⟨hna y (List.mem_cons_of_mem _ hy),
          (hw y (List.mem_cons_of_mem _ hy)).goal⟩) c h'
      rwa [List.singleton_append, sortedParts_of_sorted hs] at this
  | opn t => exact absurd h' (and_noclosed K hK cl opq wv far _ _ c (.inl rfl))

include hL h2 in
/-- A derivation of a meet whose members are read whole is covered by an
answer the meet hands on. -/
theorem meet_closed_part (opq : Bool) (wv : Rel → List (It D P))
    (hw : ∀ x ∈ xs, WOk rev near x far (C x) (O x) (wv x)) {G : GRel}
    (hG : G ∈ RwLog.andAll (xs.map C))
    (hne : (wrapD P.sorts.interp rev near (G.at P.sorts.interp) far).Nonempty) :
    ∃ a, Item.closed a ∈ andV K hK true opq wv far .start xs ∧
      wrapD P.sorts.interp rev near (G.at P.sorts.interp) far ⊆ den P.sorts.interp a.span := by
  obtain ⟨x₀, tl, rfl⟩ : ∃ x₀ tl, xs = x₀ :: tl := by
    cases xs with
    | nil => simp at h2
    | cons a b => exact ⟨a, b, rfl⟩
  have hsub := andAll_sub P.sorts.interp C _ G hG
  have mem : ∀ x ∈ x₀ :: tl, ∃ b, Item.closed b ∈ wv x ∧ b.goal = goalD rev near x far ∧
      wrapD P.sorts.interp rev near (G.at P.sorts.interp) far ⊆ den P.sorts.interp b.span := by
    intro x hx
    obtain ⟨g, hg, hs'⟩ := hsub x hx
    have hsub' := wrapD_mono (M := P.sorts.interp) rev near far hs'
    obtain ⟨b, hb, hWb⟩ := (hw x hx).closed g hg (hne.mono hsub')
    exact ⟨b, hb, (hw x hx).goal b hb, hsub'.trans hWb⟩
  obtain ⟨b, hb, hbg, hWb⟩ := mem x₀ (by simp)
  obtain ⟨c, hc, hWc⟩ := and_closed hL K hK rev opq wv near far hne tl b _ hbg hWb
    (fun y hy => mem y (List.mem_cons_of_mem _ hy))
  exact ⟨c, (mem_andV_closed_cons K hK true opq wv far).2 ⟨_, hb, hc⟩, hWc⟩

include h2 in
/-- A derivation of a meet with a member not read whole makes the meet an
open product. -/
theorem meet_open_part (cl : Bool) (wv : Rel → List (It D P))
    (hw : ∀ x ∈ xs, WOk rev near x far (C x) (O x) (wv x)) {G : GRel}
    (hG : G ∈ RwLog.andAll (xs.map O)) (hnC : G ∉ RwLog.andAll (xs.map C))
    (hne : (wrapD P.sorts.interp rev near (G.at P.sorts.interp) far).Nonempty) :
    Item.opn far ∈ andV K hK cl true wv far .start xs := by
  obtain ⟨x₀, tl, rfl⟩ : ∃ x₀ tl, xs = x₀ :: tl := by
    cases xs with
    | nil => simp at h2
    | cons a b => exact ⟨a, b, rfl⟩
  have hsub := andAll_sub P.sorts.interp O _ G hG
  have mem : ∀ x ∈ x₀ :: tl, (∃ b, Item.closed b ∈ wv x ∧ b.goal = goalD rev near x far ∧
      wrapD P.sorts.interp rev near (G.at P.sorts.interp) far ⊆ den P.sorts.interp b.span) ∨
      ∃ t, Item.opn t ∈ wv x := by
    intro x hx
    obtain ⟨g, hg, hs'⟩ := hsub x hx
    have hsub' := wrapD_mono (M := P.sorts.interp) rev near far hs'
    by_cases hc : g ∈ C x
    · obtain ⟨b, hb, hWb⟩ := (hw x hx).closed g hc (hne.mono hsub')
      exact .inl ⟨b, hb, (hw x hx).goal b hb, hsub'.trans hWb⟩
    · obtain ⟨t, ht, -⟩ := (hw x hx).opn g hg hc (hne.mono hsub')
      exact .inr ⟨t, ht⟩
  have hex : ∃ x ∈ x₀ :: tl, ∃ t, Item.opn t ∈ wv x := by
    rcases andAll_cases P.sorts.interp C O _ G hG with hc | ⟨x, hx, g, hg, hn', hs'⟩
    · exact absurd hc hnC
    · obtain ⟨t, ht, -⟩ := (hw x hx).opn g hg hn'
        (hne.mono (wrapD_mono (M := P.sorts.interp) rev near far hs'))
      exact ⟨x, hx, t, ht⟩
  refine (mem_andV_opn K hK cl true wv far _ _ _).2 ⟨rfl, rfl, fun y hy => ?_, .inr hex⟩
  rcases mem y hy with ⟨b, hb, -⟩ | ⟨t, ht⟩
  · exact List.ne_nil_of_mem hb
  · exact List.ne_nil_of_mem ht

include hL h2 hna hs in
/-- The items of a meet where nothing was pushed. -/
theorem meet_wok_plain (wv : Rel → List (It D P))
    (hw : ∀ x ∈ xs, WOk rev near x far (C x) (O x) (wv x)) :
    WOk rev near (mkAnd xs) far (RwLog.andAll (xs.map C)) (RwLog.andAll (xs.map O))
      (andV K hK true true wv far .start xs) :=
  ⟨meet_goal_part K hK rev h2 hna hs C O true true wv hw,
    fun _ hG hne => meet_closed_part hL K hK rev h2 C O true wv hw hG hne,
    fun _ hG hnC hne => ⟨far, meet_open_part K hK rev h2 C O true wv hw hG hnC hne,
      fun _ hp => adm_far rev hp⟩⟩

include hL hn h2 hna hs in
/-- The items of a meet under a pushed boundary: its answers under it, and
whether it is opaque without it. -/
theorem meet_wok_pushed (wv wvo : Rel → List (It D P))
    (hw : ∀ x ∈ xs, WOk rev near x far (C x) (O x) (wv x))
    (hwo : ∀ x ∈ xs, WOk rev none x far (C x) (O x) (wvo x)) :
    WOk rev near (mkAnd xs) far (RwLog.andAll (xs.map C)) (RwLog.andAll (xs.map O))
      (andV K hK true false wv far .start xs ++ andV K hK false true wvo far .start xs) := by
  refine ⟨fun c hc => ?_, fun G hG hne => ?_, fun G hG hnC hne => ?_⟩
  · rcases List.mem_append.1 hc with h | h
    · exact meet_goal_part K hK rev h2 hna hs C O true false wv hw c h
    · exact absurd h (and_noclosed_flag K hK true wvo far _ _ c)
  · obtain ⟨a, ha, hX⟩ := meet_closed_part hL K hK rev h2 C O false wv hw hG hne
    exact ⟨a, List.mem_append_left _ ha, hX⟩
  · exact ⟨far, List.mem_append_right _
      (meet_open_part K hK rev h2 C O false wvo hwo hG hnC
        (hne.mono (wrapD_none_sub hL rev hn _ far))), fun _ hp => adm_far rev hp⟩

end meetNode

/-! ## The walk -/

theorem nodeD_walk (rev : Bool) (xs : List Rel) :
    nodeD rev (if rev then xs.reverse else xs) = mkSeq xs := by
  cases rev
  · rfl
  · simp [nodeD]

include hL in
/-- The items of a walk are the unfolding of the goal between its near and
its far boundary. -/
theorem walk_ok (hP : ProgFO P) (rev : Bool) : ∀ (d : Nat) (c : Near R) (n : Rel)
    (far : Option R), IsBound D c.bound → IsBound D far → Normal n → n.FO →
    WOk rev c.bound n far (GR P d n) (GD P n) (walkV (P := P) K hK rev d c n far)
  | 0, c, n, far, _, _, _, _ =>
    ⟨fun a ha => by simp [walkV] at ha, fun G hG => by simp at hG,
      fun G _ _ _ => ⟨far, by simp [walkV], fun _ hp => adm_far rev hp⟩⟩
  | d + 1, c, n, far, hc, hf, hn, hfo => by
    cases hv : n.view.forget with
    | span u =>
      obtain ⟨s, rfl⟩ := forget_span hv
      have e : walkV (P := P) K hK rev (d + 1) c (.span s) far =
          (leafAtV (P := P) K hK rev c.bound (.span s) far).toList.map .closed := by
        simp only [walkV, hv]
      rw [e, gr_span P hv, (gd_laws P).span]
      exact leaf_wok hL K hK rev hc hf (hfo s (by simp [RelOf.spans]))
    | call m f =>
      obtain ⟨b, hb⟩ := forget_call (P := P) hv
      have e : walkV (P := P) K hK rev (d + 1) c n far =
          (walkV K hK rev d c b far).flatMap fun it =>
            (liftItemV (fun a => (Ans.unfold D P a n).val) it).toList := by
        simp only [walkV, hv, hb]
      rw [e, gr_call P hv hb, gd_of_body P hb]
      refine lift_wok (walk_ok hP rev d c b far hc hf (bodyOf_normal hb) (bodyOf_fo hP hb))
        (fun a c e => (Ans.unfold_val.1 e).2.2) (fun a ha => ?_)
      obtain ⟨c', hc', hs, -⟩ := Ans.unfold_ok (a := a) (n := n) (by
        rw [hb, ha]; cases rev <;> rfl)
      exact ⟨c', hc', hs⟩
    | union xs =>
      have hvu := forget_union hv
      have hparts := hn.view_union_eq hvu
      have e : walkV (P := P) K hK rev (d + 1) c n far =
          xs.zipIdx.flatMap fun p => (walkV K hK rev d c p.1 far).flatMap fun it =>
            (liftItemV (fun a => (Ans.inj D P a n p.2).val) it).toList := by
        simp only [walkV, hv]
      rw [e, gr_union P hv]
      have hzip : ∀ (S : Rel → Set GRel) (G : GRel),
          (∃ p ∈ xs.zipIdx, G ∈ S p.1) ↔ ∃ x ∈ xs, G ∈ S x := by
        intro S G
        constructor
        · rintro ⟨⟨x, i⟩, hp, hG⟩
          exact ⟨x, List.mem_of_getElem? (List.mem_zipIdx_iff_getElem?.1 hp), hG⟩
        · rintro ⟨x, hx, hG⟩
          obtain ⟨i, hi⟩ := List.getElem?_of_mem hx
          exact ⟨(x, i), List.mem_zipIdx_iff_getElem?.2 hi, hG⟩
      refine (union_wok xs.zipIdx (fun p => GR P d p.1) (fun p => GD P p.1)
        (fun p => (walkV K hK rev d c p.1 far).flatMap fun it =>
          (liftItemV (fun a => (Ans.inj D P a n p.2).val) it).toList) (fun p hp => ?_)).of_eq
        (by ext G; exact (hzip _ G).symm)
        (by ext G; rw [gd_of_union P hn hvu]; exact (hzip _ G).symm)
      have hx : xs[p.2]? = some p.1 := List.mem_zipIdx_iff_getElem?.1 hp
      have hm : p.1 ∈ n.view.members := by rw [hvu]; exact List.mem_of_getElem? hx
      refine lift_wok (walk_ok hP rev d c p.1 far hc hf (hn.view_members hm)
        (hfo.view_members hm)) (fun a c e => (Ans.inj_val.1 e).2.2) (fun a ha => ?_)
      obtain ⟨c', hc', hs, -⟩ := Ans.inj_ok (a := a) (u := n) (i := p.2) (by
        rw [← hparts, ha]; cases rev <;> exact hx)
      exact ⟨c', hc', hs⟩
    | chain xs =>
      have hvc := forget_chain hv
      obtain ⟨h2, hmem, hmk⟩ := hn.view_chain hvc
      have e : walkV (P := P) K hK rev (d + 1) c n far =
          seqV K hK rev (walkV K hK rev d) far none c (if rev then xs.reverse else xs) := by
        simp only [walkV, hv]
      have hxs : xs ≠ [] := by rintro rfl; simp at h2
      have hin : ∀ x, x ∈ (if rev then xs.reverse else xs) → x ∈ xs := fun x hx => by
        cases rev
        · exact hx
        · exact List.mem_reverse.1 hx
      have key := chain_wok hL K hK rev (walkV K hK rev d) far (GR P d) (GD P) hf
        (ys := if rev then xs.reverse else xs) (by cases rev <;> simpa using h2)
        (fun x hx c' fr hc' hfr => walk_ok hP rev d c' x fr hc' hfr (hmem x (hin x hx)).1
          (hfo.view_members (by rw [hvc]; exact hin x hx)))
        (fun x hx => (hmem x (hin x hx)).2) c hc
      rw [chainSet_seqAll rev _ hxs, chainSet_seqAll rev _ hxs, nodeD_walk, hmk] at key
      rw [e, gr_chain P hv, gd_of_chain P hvc]
      exact key
    | meet xs =>
      have hvm := forget_meet hv
      obtain ⟨h2, hmem, hs, hmk⟩ := hn.view_meet hvm
      have mem : ∀ c' : Near R, IsBound D c'.bound → ∀ x ∈ xs,
          WOk rev c'.bound x far (GR P d x) (GD P x) (walkV K hK rev d c' x far) :=
        fun c' hc' x hx => walk_ok hP rev d c' x far hc' hf (hmem x hx).1
          (hfo.view_members (by rw [hvm]; exact hx))
      rw [gr_meet P hv, gd_of_meet P hvm]
      cases hp : c.isPushed with
      | false =>
        have e : walkV (P := P) K hK rev (d + 1) c n far =
            andV K hK true true (fun x => walkV K hK rev d c x far) far .start xs := by
          simp only [walkV, hv, hp, Bool.false_eq_true, ite_false]
        rw [e]
        have := meet_wok_plain hL K hK rev h2 (fun x hx => (hmem x hx).2) hs (GR P d) (GD P)
          _ (mem c hc)
        rwa [hmk] at this
      | true =>
        have e : walkV (P := P) K hK rev (d + 1) c n far =
            andV K hK true false (fun x => walkV K hK rev d c x far) far .start xs ++
              andV K hK false true (fun x => walkV K hK rev d c.own x far) far .start xs := by
          simp only [walkV, hv, hp, ite_true]
        have ho : c.own.bound = none := by
          have h := hp
          simp only [Near.isPushed, Bool.and_eq_true] at h
          simp [Near.own, h.1]
        rw [e]
        have := meet_wok_pushed hL K hK rev hc h2 (fun x hx => (hmem x hx).2) hs (GR P d) (GD P)
          _ _ (mem c hc) (fun x hx => by
            have h := mem c.own (by rw [ho]; exact isBound_none D) x hx
            rwa [ho] at h)
        rwa [hmk] at this

/-! ## The race -/

theorem mem_keepNew {acc : List (Ans D P)} {x b : Ans D P} (h : b ∈ keepNew acc x) :
    b ∈ acc ∨ b = x := by
  unfold keepNew at h
  split at h
  · exact .inl h
  · simpa using h

theorem keepNew_sub {acc : List (Ans D P)} {x a : Ans D P} (h : a ∈ acc) : a ∈ keepNew acc x := by
  unfold keepNew
  split <;> simp [h]

theorem keepNew_has (acc : List (Ans D P)) (x : Ans D P) :
    ∃ y ∈ keepNew acc x, y.span = x.span := by
  by_cases hany : acc.any (fun y => decide (y.span = x.span)) = true
  · obtain ⟨y, hy, e⟩ := List.any_eq_true.1 hany
    exact ⟨y, keepNew_sub hy, of_decide_eq_true e⟩
  · exact ⟨x, by simp [keepNew, hany], rfl⟩

theorem keepItem_spec : ∀ (is : List (It D P)) (acc : List (Ans D P)),
    (∀ b ∈ is.foldl keepItem acc, b ∈ acc ∨ Item.closed b ∈ is) ∧
      ∀ a, a ∈ acc ∨ Item.closed a ∈ is → ∃ b ∈ is.foldl keepItem acc, b.span = a.span
  | [], acc => ⟨fun b hb => .inl hb, fun a ha => ⟨a, by simpa using ha, rfl⟩⟩
  | it :: is, acc => by
    simp only [List.foldl_cons]
    obtain ⟨h₁, h₂⟩ := keepItem_spec is (keepItem acc it)
    cases it with
    | opn t =>
      refine ⟨fun b hb => ?_, fun a ha => ?_⟩
      · rcases h₁ b hb with h | h
        · exact .inl h
        · exact .inr (List.mem_cons_of_mem _ h)
      · rcases ha with ha | ha
        · exact h₂ a (.inl ha)
        · exact h₂ a (.inr (by simpa using ha))
    | closed x =>
      refine ⟨fun b hb => ?_, fun a ha => ?_⟩
      · rcases h₁ b hb with h | h
        · rcases mem_keepNew h with h | rfl
          · exact .inl h
          · exact .inr (by simp)
        · exact .inr (List.mem_cons_of_mem _ h)
      · rcases ha with ha | ha
        · exact h₂ a (.inl (keepNew_sub ha))
        · rcases List.mem_cons.1 ha with h | h
          · obtain rfl : a = x := by simpa using h
            obtain ⟨y, hy, hys⟩ := keepNew_has acc a
            obtain ⟨b, hb, hbs⟩ := h₂ y (.inl hy)
            exact ⟨b, hb, hbs.trans hys⟩
          · exact h₂ a (.inr h)

omit [DecidableEq R] in
theorem any_itOpn {is : List (It D P)} : is.any itOpn = true ↔ ∃ t, Item.opn t ∈ is := by
  rw [List.any_eq_true]
  constructor
  · rintro ⟨it, hit, h⟩
    cases it with
    | closed a => cases h
    | opn t => exact ⟨t, hit⟩
  · rintro ⟨t, h⟩
    exact ⟨_, h, rfl⟩

include hL in
/-- A walk that stops at the first open product answers the unfolding race,
in either direction. -/
theorem walkRace_ok (hP : ProgFO P) (rev : Bool) :
    UOk D P (walkRace (K := DerivationKernel.over D K hK P) rev) := by
  have ok : ∀ (d : Nat) (g : GoalOf R Rel), GoalOk D g →
      WOk rev (if rev then g.rb else g.lb) g.node (if rev then g.lb else g.rb) (GR P d g.node)
        (GD P g.node) (walkV K hK rev d ⟨if rev then g.rb else g.lb, false⟩ g.node
          (if rev then g.lb else g.rb)) := fun d g hg =>
    walk_ok hL K hK hP rev d ⟨if rev then g.rb else g.lb, false⟩ g.node
      (if rev then g.lb else g.rb) (by cases rev <;> first | exact hg.lb | exact hg.rb)
      (by cases rev <;> first | exact hg.lb | exact hg.rb) hg.normal hg.fo
  have hgoal : ∀ g : GoalOf R Rel,
      goalD rev (if rev then g.rb else g.lb) g.node (if rev then g.lb else g.rb) = toGoal g :=
    fun g => by cases rev <;> rfl
  have hwrap : ∀ (g : GoalOf R Rel) (G : GRel),
      wrapD P.sorts.interp rev (if rev then g.rb else g.lb) (G.at P.sorts.interp)
        (if rev then g.lb else g.rb) = pairsOf P g G := fun g G => by cases rev <;> rfl
  refine ⟨fun d g hg a ha => ?_, fun d g hg hfin k G hG hne => ?_⟩
  · by_cases hop : (walkV (P := P) K hK rev d ⟨if rev then g.rb else g.lb, false⟩ g.node
        (if rev then g.lb else g.rb)).any itOpn = true
    · rw [walkRace_val] at ha
      simp only [hop, reduceIte] at ha
      cases ha
    · rw [walkRace_val] at ha
      simp only [hop] at ha
      rw [← hgoal g]
      exact (ok d g hg).goal a (((keepItem_spec _ []).1 a ha).resolve_left (by simp))
  · by_cases hop : (walkV (P := P) K hK rev d ⟨if rev then g.rb else g.lb, false⟩ g.node
        (if rev then g.lb else g.rb)).any itOpn = true
    · rw [walkRace_val] at hfin
      simp only [hop, reduceIte] at hfin
      cases hfin
    · rw [walkRace_val]
      simp only [hop]
      rw [← hwrap g G] at hne ⊢
      by_cases hc : G ∈ GR P d g.node
      · obtain ⟨a, ha, hX⟩ := (ok d g hg).closed G hc hne
        obtain ⟨b, hb, hbs⟩ := (keepItem_spec _ []).2 a (.inr ha)
        exact ⟨b, hb, by rw [hbs]; exact hX⟩
      · obtain ⟨t, ht, -⟩ := (ok d g hg).opn G (gdn_sub_gd k _ hG) hc hne
        exact absurd (any_itOpn.2 ⟨t, ht⟩) hop

end Unfold

end Tabled

end RwLog
