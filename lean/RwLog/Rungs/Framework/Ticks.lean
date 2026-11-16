/-
# Runs in ticks, and what a part owes of them

The laws that are about cost, fair OR first of them, compare runs by what
each goal has had spent on it. This file has the record such laws are stated
of, with no engine in it, in the manner of `Saturation.lean`, which has the
record completeness is stated of.

A run is described by three things for each goal `g` at each time `t`:
`spent t g`, the ticks spent on `g` so far, by whatever reads it; `has t g`,
what `g` covers; and `done t g`, that `g` takes no more ticks.

* `Cov A g x N`: `g` covers `x` at a time when no more than `N` ticks have
  been spent on it.
* `By A g x N`: `g` covers `x` at every time when `N` ticks have been spent
  on it, and at every time when it takes no more.
* `Dom A g B g' c`: whatever `g'` covers in the run `B` with `N` ticks spent
  on it, `g` covers in the run `A` by `c * N`.

`Cov` is how a run is read when it is the one compared with, and `By` how it
is read when it is the one bounded: `By` asks nothing of a goal no ticks
reach, so a bound on a goal is a promise about the ticks it is given and
never a promise that it is given any.

A part's contract in ticks is a statement in these words about the part and
what it reads. Those of the parts that only pass answers on are here:

* `Passes A g ms σ`: `g` reads the goals `ms` and covers what any of them
  covers, when it has had as many ticks as they are many times what that one
  needed and `σ` more for each (a union);
* `Passes A g [b] σ` is a call of the body `b`.

`Dom.pass` is the step of the composition they give: a goal that passes on
what `m` covers is delayed, against any goal `m` is compared with, by the
number of goals it reads and no more.
-/
import Mathlib.Data.Set.Basic

namespace RwLog

namespace Ticks

/-- A run, by what has been spent on each goal: the ticks spent on it at
each time, what it covers at each time, and whether it takes no more. -/
structure Run (ι X : Type) where
  spent : Nat → ι → Nat
  has : Nat → ι → Set X
  done : Nat → ι → Prop

variable {ι κ X : Type}

/-- The goal covers `x` at a time when no more than `N` ticks have been spent
on it. -/
def Cov (A : Run ι X) (g : ι) (x : X) (N : Nat) : Prop :=
  ∃ t, x ∈ A.has t g ∧ A.spent t g ≤ N

/-- The goal covers `x` at every time when `N` ticks have been spent on it,
and at every time when it takes no more. -/
def By (A : Run ι X) (g : ι) (x : X) (N : Nat) : Prop :=
  ∀ t, (N ≤ A.spent t g ∨ A.done t g) → x ∈ A.has t g

theorem By.mono {A : Run ι X} {g : ι} {x : X} {N M : Nat} (h : By A g x N) (hNM : N ≤ M) :
    By A g x M := fun t ht => h t (ht.imp (Nat.le_trans hNM) id)

theorem Cov.mono {A : Run ι X} {g : ι} {x : X} {N M : Nat} (h : Cov A g x N) (hNM : N ≤ M) :
    Cov A g x M := by
  obtain ⟨t, hx, ht⟩ := h
  exact ⟨t, hx, Nat.le_trans ht hNM⟩

/-- A goal that covers `x` by `N` covers it within `M`, if at some time
between `N` and `M` ticks have been spent on it. -/
theorem By.cov {A : Run ι X} {g : ι} {x : X} {N M : Nat} (h : By A g x N) {t : Nat}
    (h1 : N ≤ A.spent t g) (h2 : A.spent t g ≤ M) : Cov A g x M :=
  ⟨t, h t (.inl h1), h2⟩

/-- Whatever `g'` covers in the run `B` with `N` ticks spent on it, `g`
covers in the run `A` by `c * N + s`. -/
def Dom (A : Run ι X) (g : ι) (B : Run κ X) (g' : κ) (c s : Nat) : Prop :=
  ∀ x N, Cov B g' x N → By A g x (c * N + s)

/-- **The contract in ticks of a part that passes answers on.** The goal `g`
reads the goals `ms`; what one of them covers by `N` ticks of its own, `g`
covers by as many times `N + σ` as it reads goals. -/
def Passes (A : Run ι X) (g : ι) (ms : List ι) (σ : Nat) : Prop :=
  ∀ m ∈ ms, ∀ x N, By A m x N → By A g x (ms.length * (N + σ))

/-- **A goal that passes answers on is delayed by the number of goals it
reads.** -/
theorem Dom.pass {A : Run ι X} {B : Run κ X} {g m : ι} {ms : List ι} {g' : κ} {c s σ : Nat}
    (hP : Passes A g ms σ) (hm : m ∈ ms) (h : Dom A m B g' c s) :
    Dom A g B g' (ms.length * c) (ms.length * (s + σ)) := fun x N hx =>
  (hP m hm x _ (h x N hx)).mono (by
    rw [Nat.mul_add, Nat.mul_add, Nat.mul_add, Nat.mul_assoc]
    omega)

/-- A goal compared with itself in one run. -/
theorem Dom.of_by {A : Run ι X} {B : Run κ X} {g : ι} {g' : κ} {c s : Nat}
    (h : ∀ x N, Cov B g' x N → By A g x (c * N + s)) : Dom A g B g' c s := h

/-- A bound holds with a greater factor and more to spare. -/
theorem Dom.mono {A : Run ι X} {B : Run κ X} {g : ι} {g' : κ} {c s c' s' : Nat}
    (h : Dom A g B g' c s) (hc : c ≤ c') (hs : s ≤ s') : Dom A g B g' c' s' := fun x N hx =>
  (h x N hx).mono (Nat.add_le_add (Nat.mul_le_mul_right N hc) hs)

end Ticks

end RwLog
