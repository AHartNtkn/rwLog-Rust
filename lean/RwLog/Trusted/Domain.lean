/-
# The constraint domain

An engine never sees a sort or a disequality. It sees *representatives*: the
values of a type `R` that stand for spans with their stores, and it handles
them only through the operations of a constraint domain. This file says what
a domain is and what it must satisfy, whatever is behind it. The domain of
the language is sorts with the built-in disequality
(`Trusted/Semantics.lean`); its instance is not in the trusted files.

## Representatives

`R` is an answer type (`Answer R`, `Trusted/Runtime.lean`): a representative
denotes a relation between ground terms in every interpretation, and has a
converse of its own, `Answer.swap`, that denotes the converse relation. The
converse is not `Span.swap`. A representative is canonical up to the names
of its variables, and no canonical span in one name space commutes with
exchanging its sides: `(f $v $w) -> (f $w $v)` with its sides exchanged is
itself renamed, so a canonical form gives both the same value `L -> R`, and
exchanging sides would force `L = R`. A domain therefore keeps an orientation
with the canonical span, and the converse changes the orientation.

## Operations

* `rep s`: the representative of a span as it is written, with its store in
  canonical form; nothing if the span relates no pair. A domain need not
  represent a span that is not first-order (`Span.firstOrder`: a variable
  applied to an argument, or a constraint that is a variable), and may return
  nothing for it. The spans of a well-formed program are first-order.
* `compose a b`, `meet a b`: sequential composition and conjunction, with the
  stores combined and brought to canonical form; nothing if the result
  relates no pair. There is no separate simplification: every operation
  returns a representative.
* `rightBound a`: the right interface of `a` as a boundary, a representative
  that relates a term only to itself and relates to itself every right end
  of a pair of `a`. Nothing stands for the identity, the boundary that does
  not restrict. `leftBound a` is the right interface of the converse.
* `isBound b`: `b` relates a term only to itself, so it may be a boundary.
* `covers a b`: `a` relates every pair `b` relates.

## Laws

`Domain.Lawful D M` is what the operations satisfy in the interpretation `M`
of a program's sorts. Every law is unconditional.

* A representative is never empty (`live`): the test for an empty store is
  exact, so an operation returns nothing exactly when the result relates no
  pair (`rep_none` for a first-order span, `compose_none`, `meet_none`).
* Two representatives that relate the same pairs are the same value
  (`canon`). Stores have a canonical form, and two stores are equivalent
  exactly when their canonical forms are equal.
* Each operation returns the representative of what it names (`rep_some`,
  `compose_some`, `meet_some`, `covers_iff`).

Together these give every algebraic law as an equation between
representatives, with no relation "up to" anything: the converse is an
involution and commutes with every operation, composition is associative,
conjunction is associative, commutative and idempotent, a boundary is its own
converse, and the left interface of a span is the right interface of its
converse (`Kernel/DomainLaws.lean`). Nothing is stated up to the coverage of
spans as written (`Span.Equiv`), which composition does not respect once
stores are brought to canonical form.
-/
import RwLog.Trusted.Runtime

namespace RwLog

/-- The operations of a constraint domain on its type `R` of
representatives. -/
structure Domain (R : Type) where
  /-- The representative of a span as written. -/
  rep : Span → Option R
  /-- Sequential composition. -/
  compose : R → R → Option R
  /-- Conjunction. -/
  meet : R → R → Option R
  /-- The right interface, as a boundary; `none` is the identity. -/
  rightBound : R → Option R
  /-- The representative relates a term only to itself. -/
  isBound : R → Bool
  /-- Does the first representative cover the second? -/
  covers : R → R → Bool

namespace Domain

variable {R : Type} [Answer R]

/-- The left interface, as a boundary: the right interface of the
converse. -/
def leftBound (D : Domain R) (a : R) : Option R := D.rightBound (Answer.swap a)

/-- A chain of representatives composed from the left; `none` when some
composition relates no pair, and for the empty chain, which has no
representative. -/
def chain (D : Domain R) : List R → Option R
  | [] => none
  | s :: rest => rest.foldl (fun acc t => acc.bind (D.compose · t)) (some s)

/-- Does the chain compose? The empty chain does. -/
def composable (D : Domain R) (xs : List R) : Bool := xs.isEmpty || (D.chain xs).isSome

/-- The laws of a constraint domain in the interpretation `M`. -/
structure Lawful (D : Domain R) (M : Interp) : Prop where
  /-- No representative relates nothing. -/
  live : ∀ r : R, (Answer.den M r).Nonempty
  /-- Representatives that relate the same pairs are equal. -/
  canon : ∀ a b : R, Answer.den M a = Answer.den M b → a = b
  /-- The representative of a span relates the pairs the span relates. -/
  rep_some : ∀ (s : Span) (r : R), D.rep s = some r → Answer.den M r = s.denAt M
  /-- A first-order span has no representative only if it relates nothing. -/
  rep_none : ∀ s : Span, s.firstOrder = true → D.rep s = none → s.denAt M = ∅
  compose_some : ∀ a b c : R, D.compose a b = some c →
    Answer.den M c = (Answer.den M a).comp (Answer.den M b)
  compose_none : ∀ a b : R, D.compose a b = none →
    (Answer.den M a).comp (Answer.den M b) = ∅
  meet_some : ∀ a b c : R, D.meet a b = some c → Answer.den M c = Answer.den M a ∩ Answer.den M b
  meet_none : ∀ a b : R, D.meet a b = none → Answer.den M a ∩ Answer.den M b = ∅
  /-- What passes as a boundary relates a term only to itself. -/
  isBound_sub : ∀ b : R, D.isBound b = true → ∀ p ∈ Answer.den M b, p.2 = p.1
  /-- An interface is a boundary. -/
  rightBound_isBound : ∀ a b : R, D.rightBound a = some b → D.isBound b = true
  /-- The right interface relates to itself every right end of a pair. -/
  rightBound_mem : ∀ a b : R, D.rightBound a = some b →
    ∀ x y, (x, y) ∈ Answer.den M a → (y, y) ∈ Answer.den M b
  /-- Coverage is decided. -/
  covers_iff : ∀ a b : R, D.covers a b = true ↔ Answer.den M b ⊆ Answer.den M a

end Domain

end RwLog
