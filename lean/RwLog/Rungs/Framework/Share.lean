/-
# Sharing ticks: the one who has had least is served first

A part of an engine, with its own law. Something that spends ticks on
several things, the members of a union or the tables a join reads, keeps for
each of them what it has spent on it, and serves them by `Share.offer`: the
things are offered ticks in a given order, and the first that takes any ends
the offer. A thing that takes nothing, because it is finished or has been
served already, passes the offer on.

The law of the part is `Share.offer_spec`. After an offer, each thing either
wanted nothing when it was reached, or it was not reached because a thing no
later in the order took ticks. When the order is the order of what has been
spent, that is: nothing that still wants ticks is passed over for a thing
that has had more. Whoever uses the part gets the law by saying what "wanted
nothing" and "took ticks" are for its things; nothing in the proof looks
inside a thing.

Fair OR is this law at a union: the things are the members, so a member is
served unless a member that has had no more is served. The same law at a
join is what makes a table read through a union share that table's ticks
with the other members and with nothing else.
-/
import RwLog.Rungs.Framework.TraverseStd

namespace RwLog

namespace Share

section

variable {M : Type → Type} [Monad M] {σ ι : Type}

/-- The things of `l` are offered ticks in order, each by `spend`, which
returns what it took. The first that takes anything ends the offer, and is
returned. -/
def offer (spend : ι → σ → M (σ × Nat)) : σ → List ι → M (σ × Option ι)
  | s, [] => pure (s, none)
  | s, x :: rest => do
    let r ← spend x s
    if 0 < r.2 then pure (r.1, some x) else offer spend r.1 rest

end

variable {σ ι : Type}

/-- What every spending keeps, an offer keeps. -/
theorem offer_inv (spend : ι → σ → Cost (σ × Nat)) (J : σ → Prop)
    (hJ : ∀ x s, J s → J (spend x s).val.1) :
    ∀ (l : List ι) (s : σ), J s → J (offer spend s l).val.1
  | [], s, h => by
    simp only [offer, Cost.pure_val]
    exact h
  | x :: rest, s, h => by
    have ih := offer_inv spend J hJ rest (spend x s).val.1 (hJ x s h)
    simp only [offer, Cost.bind_val]
    by_cases hc : 0 < (spend x s).val.2
    · simp only [hc, ↓reduceIte, Cost.pure_val]
      exact hJ x s h
    · simp only [hc, ↓reduceIte]
      exact ih

/-- **The law of sharing.** `I` is what every state has, and `R` relates a
state to every later one. `Passed x s` says that `x` wanted nothing in the
state `s`, and stays true later; `Took x s s'` says that `x` took ticks
between `s` and `s'`, and stays true from an earlier `s` and to a later `s'`.

After an offer: the state has `I` and is later than the first; and the list
is the things that were reached and wanted nothing, then, if any took ticks,
that thing, then the things not reached. -/
theorem offer_spec (spend : ι → σ → Cost (σ × Nat)) (I : σ → Prop) (R : σ → σ → Prop)
    (Passed : ι → σ → Prop) (Took : ι → σ → σ → Prop)
    (refl : ∀ s, R s s) (trans : ∀ {a b c}, R a b → R b c → R a c)
    (hI : ∀ x s, I s → I (spend x s).val.1) (hR : ∀ x s, I s → R s (spend x s).val.1)
    (hpass : ∀ x s, I s → (spend x s).val.2 = 0 → Passed x (spend x s).val.1)
    (htook : ∀ x s, I s → 0 < (spend x s).val.2 → Took x s (spend x s).val.1)
    (passed_mono : ∀ {x a b}, R a b → Passed x a → Passed x b)
    (took_start : ∀ {x a b c}, R a b → Took x b c → Took x a c) :
    ∀ (l : List ι) (s : σ), I s →
      I (offer spend s l).val.1 ∧ R s (offer spend s l).val.1 ∧
      (((offer spend s l).val.2 = none ∧ ∀ x ∈ l, Passed x (offer spend s l).val.1) ∨
        ∃ l1 y l2, l = l1 ++ y :: l2 ∧ (offer spend s l).val.2 = some y ∧
          (∀ x ∈ l1, Passed x (offer spend s l).val.1) ∧ Took y s (offer spend s l).val.1)
  | [], s, h => by
    simp only [offer, Cost.pure_val]
    exact ⟨h, refl s, .inl ⟨trivial, fun _ hx => absurd hx List.not_mem_nil⟩⟩
  | x :: rest, s, h => by
    have ih := offer_spec spend I R Passed Took refl trans hI hR hpass htook passed_mono
      took_start rest (spend x s).val.1 (hI x s h)
    simp only [offer, Cost.bind_val]
    by_cases hc : 0 < (spend x s).val.2
    · simp only [hc, ↓reduceIte, Cost.pure_val]
      exact ⟨hI x s h, hR x s h, .inr ⟨[], x, rest, rfl, rfl,
        fun _ hx => absurd hx List.not_mem_nil, htook x s h hc⟩⟩
    · simp only [hc, ↓reduceIte]
      obtain ⟨i1, i2, i3⟩ := ih
      have hx := hpass x s h (Nat.eq_zero_of_not_pos hc)
      refine ⟨i1, trans (hR x s h) i2, ?_⟩
      rcases i3 with ⟨e, hp⟩ | ⟨l1, y, l2, e, ey, hp, ht⟩
      · refine .inl ⟨e, fun z hz => ?_⟩
        rcases List.mem_cons.1 hz with rfl | hz
        · exact passed_mono i2 hx
        · exact hp z hz
      · refine .inr ⟨x :: l1, y, l2, by rw [e]; rfl, ey, fun z hz => ?_,
          took_start (hR x s h) ht⟩
        rcases List.mem_cons.1 hz with rfl | hz
        · exact passed_mono i2 hx
        · exact hp z hz

/-- **Nothing that still wants ticks is passed over for a thing that has had
more.** Where the things are offered in the order of a key, what has been
spent on each: after the offer every thing wanted nothing, or a thing whose
key was no greater took ticks. -/
theorem offer_least (spend : ι → σ → Cost (σ × Nat)) (I : σ → Prop) (R : σ → σ → Prop)
    (Passed : ι → σ → Prop) (Took : ι → σ → σ → Prop)
    (refl : ∀ s, R s s) (trans : ∀ {a b c}, R a b → R b c → R a c)
    (hI : ∀ x s, I s → I (spend x s).val.1) (hR : ∀ x s, I s → R s (spend x s).val.1)
    (hpass : ∀ x s, I s → (spend x s).val.2 = 0 → Passed x (spend x s).val.1)
    (htook : ∀ x s, I s → 0 < (spend x s).val.2 → Took x s (spend x s).val.1)
    (passed_mono : ∀ {x a b}, R a b → Passed x a → Passed x b)
    (took_start : ∀ {x a b c}, R a b → Took x b c → Took x a c)
    (key : ι → Nat) (l : List ι) (hsort : l.Pairwise fun a b => key a ≤ key b) (s : σ)
    (h : I s) :
    I (offer spend s l).val.1 ∧ R s (offer spend s l).val.1 ∧
      ∀ x ∈ l, (Passed x (offer spend s l).val.1 ∨
        ∃ y ∈ l, key y ≤ key x ∧ Took y s (offer spend s l).val.1) := by
  obtain ⟨h1, h2, h3⟩ := offer_spec spend I R Passed Took refl trans hI hR hpass htook
    passed_mono took_start l s h
  refine ⟨h1, h2, fun x hx => ?_⟩
  rcases h3 with ⟨-, hp⟩ | ⟨l1, y, l2, e, -, hp, ht⟩
  · exact .inl (hp x hx)
  · subst e
    rcases List.mem_append.1 hx with hx | hx
    · exact .inl (hp x hx)
    · refine .inr ⟨y, List.mem_append_right _ List.mem_cons_self, ?_, ht⟩
      rcases List.mem_cons.1 hx with rfl | hx
      · exact Nat.le_refl _
      · exact (List.pairwise_cons.1 (List.pairwise_append.1 hsort).2.1).1 x hx

end Share

end RwLog
