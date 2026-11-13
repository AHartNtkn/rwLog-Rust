/-
# Products that are a single span

A product of a normal form that contains no call is a single span
(`open_calls`). So when no product of an unfolding contains a call, the spans
it derives are those spans (`closed_eq_derivs`): the unfolders read them off
the products, and nothing is composed to get them.
-/
import RwLog.Rungs.R002.Unfold
import RwLog.Rungs.R000.Properties
import RwLog.Rungs.R000.Products

namespace RwLog

namespace R002

@[simp] theorem single_span (s : Span) : single [.span s] = some s := rfl

@[simp] theorem single_and (a b : Rel) : single [.and a b] = none := rfl

theorem single_eq_some {p : List Rel} {s : Span} : single p = some s ↔ p = [.span s] := by
  constructor
  · intro h
    unfold single at h
    split at h
    · cases h; rfl
    · cases h
  · rintro rfl; rfl

theorem mem_closed {N : List (List Rel)} {s : Span} : s ∈ closed N ↔ [.span s] ∈ N := by
  simp only [closed, List.mem_filterMap, single_eq_some]
  constructor
  · rintro ⟨p, hp, rfl⟩; exact hp
  · intro h; exact ⟨_, h, rfl⟩

theorem closed_append (N N' : List (List Rel)) : closed (N ++ N') = closed N ++ closed N' :=
  List.filterMap_append

theorem joinSeq_singles (x y : Span) :
    R000.joinSeq [.span x] [.span y] = (x.compose y).map fun c => [.span c] :=
  rfl

theorem mkAnd_cases (p q : List Rel) :
    (∃ a b, p = [.span a] ∧ q = [.span b] ∧
        R000.mkAnd p q = (a.meet b).map fun c => [.span c]) ∨
      ((single p = none ∨ single q = none) ∧
        R000.mkAnd p q = some [.and (toRel p) (toRel q)]) := by
  cases hsp : single p with
  | some a =>
    cases hsq : single q with
    | some b =>
      obtain rfl := single_eq_some.mp hsp
      obtain rfl := single_eq_some.mp hsq
      exact .inl ⟨a, b, rfl, rfl, rfl⟩
    | none =>
      refine .inr ⟨.inr rfl, ?_⟩
      unfold R000.mkAnd
      split
      · cases hsq
      · rfl
  | none =>
    refine .inr ⟨.inl rfl, ?_⟩
    unfold R000.mkAnd
    split
    · cases hsp
    · rfl

/-- A product of a normal form that is not a single span contains a call. -/
theorem open_calls : ∀ (e : Rel) (neg : Bool), ∀ p ∈ R000.norm neg e, single p = none →
    ∃ x ∈ p, x.calls ≠ [] := by
  intro e
  induction e with
  | zero => intro neg p hp; simp [R000.norm] at hp
  | span s =>
    intro neg p hp hs
    simp only [R000.norm, List.mem_singleton] at hp
    subst hp
    cases hs
  | or a b iha ihb =>
    intro neg p hp
    simp only [R000.norm, List.mem_append] at hp
    exact hp.elim (iha neg p) (ihb neg p)
  | and a b iha ihb =>
    intro neg r hr hsr
    simp only [R000.norm, List.mem_flatMap, List.mem_filterMap] at hr
    obtain ⟨p, hp, q, hq, hj⟩ := hr
    rcases mkAnd_cases p q with ⟨x, y, rfl, rfl, h⟩ | ⟨hs, h⟩
    · rw [h] at hj
      obtain ⟨c, -, rfl⟩ := Option.map_eq_some_iff.mp hj
      cases hsr
    · rw [h] at hj
      cases hj
      refine ⟨_, List.mem_singleton_self _, ?_⟩
      simp only [Rel.calls, ne_eq, List.append_eq_nil_iff, not_and_or]
      rcases hs with hs | hs
      · obtain ⟨x, hx, hc⟩ := iha neg p hp hs
        exact .inl fun h0 => hc ((R000.calls_toRel p).mp h0 x hx)
      · obtain ⟨x, hx, hc⟩ := ihb neg q hq hs
        exact .inr fun h0 => hc ((R000.calls_toRel q).mp h0 x hx)
  | seq a b iha ihb =>
    have key : ∀ (Na Nb : List (List Rel)), (∀ p ∈ Na, p ≠ []) → (∀ q ∈ Nb, q ≠ []) →
        (∀ p ∈ Na, single p = none → ∃ x ∈ p, x.calls ≠ []) →
        (∀ q ∈ Nb, single q = none → ∃ x ∈ q, x.calls ≠ []) →
        ∀ r ∈ Na.flatMap fun p => Nb.filterMap (R000.joinSeq p), single r = none →
          ∃ x ∈ r, x.calls ≠ [] := by
      intro Na Nb ha hb iha ihb r hr hsr
      obtain ⟨p, hp, hr⟩ := List.mem_flatMap.mp hr
      obtain ⟨q, hq, hj⟩ := List.mem_filterMap.mp hr
      have hpq : single p = none ∨ single q = none := by
        cases hsp : single p with
        | none => exact .inl rfl
        | some x =>
          cases hsq : single q with
          | none => exact .inr rfl
          | some y =>
            obtain rfl := single_eq_some.mp hsp
            obtain rfl := single_eq_some.mp hsq
            rw [joinSeq_singles] at hj
            obtain ⟨c, -, rfl⟩ := Option.map_eq_some_iff.mp hj
            cases hsr
      have hin : ∃ x, (x ∈ p ∨ x ∈ q) ∧ x.calls ≠ [] := by
        rcases hpq with hs | hs
        · obtain ⟨x, hx, hc⟩ := iha p hp hs
          exact ⟨x, .inl hx, hc⟩
        · obtain ⟨x, hx, hc⟩ := ihb q hq hs
          exact ⟨x, .inr hx, hc⟩
      obtain ⟨x, hx, hc⟩ := hin
      refine ⟨x, ?_, hc⟩
      rcases R000.joinSeq_cases hj with ⟨a', b', q', c, hl, rfl, -, rfl⟩ | rfl
      · have hpe : p.dropLast ++ [.span a'] = p := List.dropLast_append_getLast? _ hl
        rcases hx with hx | hx
        · rw [← hpe, List.mem_append, List.mem_singleton] at hx
          rcases hx with hx | rfl
          · exact List.mem_append_left _ hx
          · exact (hc rfl).elim
        · rcases List.mem_cons.mp hx with rfl | hx
          · exact (hc rfl).elim
          · exact List.mem_append_right _ (List.mem_cons_of_mem _ hx)
      · exact List.mem_append.mpr hx
    intro neg r hr
    cases neg
    · exact key _ _ (R000.norm_ne_nil a false) (R000.norm_ne_nil b false) (iha false) (ihb false)
        r (by simpa only [R000.norm] using hr)
    · exact key _ _ (R000.norm_ne_nil b true) (R000.norm_ne_nil a true) (ihb true) (iha true)
        r (by simpa only [R000.norm] using hr)
  | conv a iha => intro neg p hp; exact iha (!neg) p hp
  | call n =>
    intro neg p hp _
    simp only [R000.norm, List.mem_singleton] at hp
    subst hp
    exact ⟨_, List.mem_singleton_self _, by cases neg <;> simp [Rel.calls]⟩

/-- When every product is a single span, the spans derived by the products
are those spans. -/
theorem derivs_of_closed : ∀ N : List (List Rel), (∀ p ∈ N, single p ≠ none) →
    (N.flatMap fun p => R000.derivs (toRel p)) = closed N
  | [], _ => rfl
  | p :: N, h => by
    have ih := derivs_of_closed N fun p hp => h p (List.mem_cons_of_mem _ hp)
    cases hs : single p with
    | none => exact (h p List.mem_cons_self hs).elim
    | some s =>
      obtain rfl := single_eq_some.mp hs
      rw [List.flatMap_cons, ih]
      rfl

/-- When no product of a normal form contains a call, the spans its products
derive are its single spans. -/
theorem closed_eq_derivs (e : Rel) (neg : Bool)
    (h : ((R000.norm neg e).all fun p => (toRel p).calls.isEmpty) = true) :
    closed (R000.norm neg e) = (R000.norm neg e).flatMap fun p => R000.derivs (toRel p) := by
  rw [List.all_eq_true] at h
  refine (derivs_of_closed _ fun p hp hs => ?_).symm
  obtain ⟨x, hx, hc⟩ := open_calls e neg p hp hs
  exact hc ((R000.calls_toRel p).mp (List.isEmpty_iff.mp (h p hp)) x hx)

end R002

end RwLog
