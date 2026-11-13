/-
# The kernel an engine is written against

An engine does not get to say what its work costs, and it does not get to say
what an answer is. It is written for arbitrary types `S` of representatives,
`N` of nodes and `A` of answers and an arbitrary monad `M`, and all it is
given is a `DerivationKernel S N A M`. It cannot look inside a
representative, a node or an answer, build one, or compare two, except by
calling an operation of the kernel, and it cannot touch the ticks at all,
except by spending more (`tick`) and by reading what a computation spent
(`metered`).

## Representatives

`Kernel S M` has the operations of a constraint domain (`Trusted/Domain.lean`)
on its representatives, each returning in `M`, and the comparison of two
representatives. `Kernel.Refines D K` says that a kernel `K` in the monad of
charged computations returns what the domain `D` returns: its converse is
the converse of the representatives, and the value of each operation is the
value of the same operation of `D`. Nothing is said about what it charges.

There is no operation that reads the size of a representative. On a store
that shares equal subterms, the size of a term as a tree is not a number the
machine holds: it can be exponential in the number of nodes. An engine that
wants to know what something costs runs it under `metered`. There is no
identity either: an absent boundary is the identity, and a chain has at
least two members. There is no simplification: every operation of a domain
returns a representative, with its store in canonical form.

`Domain.written` is the domain of spans as they are written: a span is its
own representative and no constraint is looked at. `Kernel.std` is its kernel
at the charges of `Trusted/Charged.lean`. It is what the kernels derived on a
machine refine today (`Trusted/KernelRung.lean`). It is lawful only where no
store matters; the kernel of the domain of sorts replaces it as the kernel
engines are judged at when that domain is derived (roadmap L39).

## Nodes

The program and the query are brought to their normal form before an engine
starts (`Kernel/NormalForm.lean`), and the engine is handed the root node. A
node is an identifier (`eqNode`). `view` reads its kind and members; a span
node reads as a span with nothing in it, and its representative is had by
`leaf`. `interval` and `without` name a stretch of a chain and a meet without
one member, `body` the body of a call, `convNode` the converse.

## Answers

An answer is an answer of a goal `lb ; node ; rb`, and an engine can make one
only by the rules of the derivation kernel (`Kernel/Derivation.lean`):

* `leaf`: the representative of a span node, composed with the boundaries;
* `join`: two answers of adjacent stretches of a chain, composed. The answer
  is for the chain of the members of both, however the stretches were split:
  this is the rule that builds in associativity;
* `meetA`: two answers of two parts of a meet, conjoined;
* `inj`: an answer of a member of a union, as an answer of the union;
* `unfold`: an answer of the body of a call, as an answer of the call;
* `swapA`: the converse of an answer, for the converse node. It is the
  converse of the representative.

`span` reads the representative of an answer. There is no other way to an
answer, so what an engine emits is sound, and no less general than a
derivation, whatever the engine does (`Rungs/Framework/Derivation.lean`).

`DerivationKernel.over D K hK P` is the derivation kernel of the program `P`
on the representatives of a kernel `K` that returns what the domain `D`
returns: its answers carry the proof that they are valid, each rule spends
what `K` charges for the operations it performs, and the operations on nodes
are charged as in `Trusted/Charged.lean`. The side conditions of `join` and
`meetA` compare a boundary with an interface as representatives, by
equality.

Walking over a list or a table of its own is free for an engine: only what is
done to representatives, nodes and answers is charged. An engine may still
charge itself for it.
-/
import RwLog.Trusted.Charged
import RwLog.Trusted.Domain
import RwLog.Kernel.Derivation

namespace RwLog

/-- The operations on representatives, for a type `S` of representatives, in
a monad `M`. -/
class Kernel (S : Type) (M : outParam (Type → Type)) extends Monad M where
  /-- Spend ticks. -/
  tick : Nat → M Unit
  /-- Run two computations side by side until one finishes (`Cost.race`). -/
  race : {α : Type} → M α → M α → M α
  /-- Run a computation and return what it spent (`Cost.metered`). -/
  metered : {α : Type} → M α → M (α × Nat)
  /-- The converse. -/
  swap : S → S
  /-- The representative of a span of the program. -/
  rep : Span → M (Option S)
  compose : S → S → M (Option S)
  meet : S → S → M (Option S)
  /-- Does the chain compose? -/
  composable : List S → M Bool
  /-- Does the first representative cover the second? -/
  covers : S → S → M Bool
  /-- Are the two representatives the same? -/
  eq : S → S → M Bool
  /-- The right interface, as a boundary. -/
  rightBound : S → M (Option S)
  /-- The left interface, as a boundary. -/
  leftBound : S → M (Option S)

/-- The domain of spans as they are written: a span is its own
representative, and no constraint is looked at. -/
def Domain.written : Domain Span where
  rep s := some s
  compose := Span.compose
  meet := Span.meet
  rightBound s := bound s.rightIface
  isBound s := decide (s.l = s.r)
  covers := Span.covers?

/-- The kernel of spans as they are written: every operation at its trusted
charge. -/
instance Kernel.std : Kernel Span Cost where
  tick := Cost.tick
  race := Cost.race
  metered := Cost.metered
  swap := Span.swap
  rep := Charged.rep
  compose := Charged.compose
  meet := Charged.meet
  composable := Charged.composable
  covers := Charged.covers
  eq := Charged.eq
  rightBound := Charged.rightBound
  leftBound := Charged.leftBound

/-- The kernel returns what the domain returns: it has the monad of charged
computations with its `tick`, `race` and `metered`, its converse is the
converse of the representatives, and the value of every operation is the
value of the same operation of the domain. Nothing is said about what it
charges. -/
structure Kernel.Refines {S : Type} [Answer S] [DecidableEq S] (D : Domain S)
    (K : Kernel S Cost) : Prop where
  monad : K.toMonad = Kernel.std.toMonad
  tick : K.tick = Cost.tick
  race : ∀ (α : Type) (a b : Cost α), K.race a b = Cost.race a b
  metered : ∀ (α : Type) (a : Cost α), K.metered a = Cost.metered a
  swap : K.swap = Answer.swap
  rep : ∀ s, (K.rep s).val = D.rep s
  compose : ∀ x y, (K.compose x y).val = D.compose x y
  meet : ∀ x y, (K.meet x y).val = D.meet x y
  composable : ∀ xs, (K.composable xs).val = D.composable xs
  covers : ∀ a s, (K.covers a s).val = D.covers a s
  eq : ∀ x y, (K.eq x y).val = decide (x = y)
  rightBound : ∀ s, (K.rightBound s).val = D.rightBound s
  leftBound : ∀ s, (K.leftBound s).val = D.leftBound s

theorem Domain.written_composable (xs : List Span) :
    Domain.written.composable xs = (Span.chain xs).isSome := by
  cases xs <;> rfl

/-- The kernel of spans as they are written returns what their domain
returns. -/
theorem Kernel.std_refines : Kernel.Refines Domain.written Kernel.std where
  monad := rfl
  tick := rfl
  race _ _ _ := rfl
  metered _ _ := rfl
  swap := rfl
  rep _ := rfl
  compose _ _ := rfl
  meet _ _ := rfl
  composable xs := (Domain.written_composable xs).symm
  covers _ _ := rfl
  eq _ _ := rfl
  rightBound _ := rfl
  leftBound _ := rfl

/-- A view with the span of a span node left out. -/
def NodeView.forget {S N : Type} : NodeView S N → NodeView Unit N
  | .span _ => .span ()
  | .call n f => .call n f
  | .chain xs => .chain xs
  | .meet xs => .meet xs
  | .union xs => .union xs

/-- The operations on representatives, on the nodes of the normal form and on
answers, for types `S` of representatives, `N` of nodes and `A` of answers,
in a monad `M`. -/
class DerivationKernel (S N A : Type) (M : outParam (Type → Type)) extends Kernel S M where
  /-- Read a node: its kind and its members. -/
  view : N → M (NodeView Unit N)
  /-- The stretch `[i, j)` of a chain, as a node. -/
  interval : N → Nat → Nat → M (Option N)
  /-- A meet without its `i`-th member, as a node. -/
  without : N → Nat → M (Option N)
  /-- The body a call node reads. -/
  body : N → M (Option N)
  /-- The converse of a node. -/
  convNode : N → M N
  /-- Are the two nodes the same node? -/
  eqNode : N → N → M Bool
  /-- The representative of an answer. -/
  span : A → S
  /-- The answer of the goal `lb ; n ; rb` on a span node `n`, if the span has
  a representative that composes with the boundaries. -/
  leaf : Option S → N → Option S → M (Option A)
  /-- Compose an answer of `lb ; x ; rb₁` with an answer of `lb₂ ; y ; rb`
  into an answer of `lb ; (x ; y) ; rb`, where `x ; y` is the chain of the
  members of both. `rb₁` is absent and `lb₂` is absent or the right interface
  of the first answer, or `lb₂` is absent and `rb₁` is the left interface of
  the second answer. -/
  join : A → A → M (Option A)
  /-- Conjoin an answer of `lb ; x ; rb` with an answer of `lb' ; y ; rb'`
  into an answer of `lb ; (x & y) ; rb`, where `x & y` is the meet of the
  members of both. `lb'` and `rb'` are `lb` and `rb`, or the interfaces of
  the first answer. -/
  meetA : A → A → M (Option A)
  /-- An answer of the `i`-th member of the union `u`, as an answer of `u`. -/
  inj : A → N → Nat → M (Option A)
  /-- An answer of the body of the call node `c`, as an answer of `c`. -/
  unfold : A → N → M (Option A)
  /-- The converse of an answer: an answer of the converse node between the
  exchanged boundaries. -/
  swapA : A → M A

/-- An answer of the derivation kernel of the program `P` on the domain `D`:
a goal, a representative, and the proof that the representative is an answer
of the goal. -/
structure Ans {R : Type} [Answer R] (D : Domain R) (P : Program) where
  goal : Goal R
  span : R
  valid : Valid D P goal span

namespace Ans

variable {R : Type} [Answer R] [DecidableEq R] {D : Domain R} {P : Program}

/-- Turn the result of an operation on representatives into an answer. -/
def ofCost (r : Cost (Option R)) (f : ∀ c, r.val = some c → Ans D P) : Cost (Option (Ans D P)) :=
  ⟨match h : r.val with
    | some c => some (f c h)
    | none => none, r.ticks, r.peak, r.held, r.held_le⟩

/-- Read a span and compose its representative with the boundaries of a goal,
at the charge of `K`. -/
def spanBothK (K : Kernel R Cost) (lb : Option R) (s : Span) (rb : Option R) :
    Cost (Option R) := do
  let r ← K.rep s
  match r with
  | none => pure none
  | some r =>
    let l ← (match lb with
      | none => pure (some r)
      | some l => K.compose l r : Cost (Option R))
    match l with
    | none => pure none
    | some s' => match rb with
      | none => pure (some s')
      | some t => K.compose s' t

theorem spanBothK_val {K : Kernel R Cost} (hK : K.Refines D) (lb : Option R) (s : Span)
    (rb : Option R) : (spanBothK K lb s rb).val = spanBoth D lb s rb := by
  unfold spanBothK spanBoth
  simp only [Cost.bind_val, hK.rep]
  cases D.rep s with
  | none => rfl
  | some r =>
    cases lb with
    | none => cases rb <;> simp [hK.compose]
    | some l =>
      simp only [Cost.bind_val, hK.compose, Option.bind_some]
      cases D.compose l r with
      | none => rfl
      | some s' => cases rb <;> simp [hK.compose]

variable (D) (P) (K : Kernel R Cost) (hK : K.Refines D)

/-- `leaf`: two tests that the boundaries are boundaries, reading the span,
and the compositions. -/
def leaf (lb : Option R) (n : Rel) (rb : Option R) : Cost (Option (Ans D P)) := do
  Cost.tick 2
  match n with
  | .span s =>
    if h : IsBound D lb ∧ IsBound D rb then
      ofCost (spanBothK K lb s rb) fun c hc =>
        ⟨⟨lb, .span s, rb⟩, c, Valid.leaf h.1 h.2 ((spanBothK_val hK lb s rb).symm.trans hc)⟩
    else pure none
  | _ => pure none

/-- What checking the side condition of a rule costs: the interface of the
answer that a boundary is compared with, at the charge of `K`, and one tick
for each comparison of identifiers. -/
def check (b : Option R) (iface : Cost (Option R)) : Cost Unit :=
  match b with
  | none => Cost.tick 1
  | some _ => do let _ ← iface; Cost.tick 1

/-- `join`: the side condition, the composition, and interning the chain of
the members of both nodes. -/
def join (a b : Ans D P) : Cost (Option (Ans D P)) := do
  check b.goal.lb (K.rightBound a.span)
  check a.goal.rb (K.leftBound b.span)
  let n := mkSeq (seqParts a.goal.node ++ seqParts b.goal.node)
  let _ ← Charged.op () (1 + (seqParts a.goal.node ++ seqParts b.goal.node).length)
    (seqParts a.goal.node ++ seqParts b.goal.node).length
  if h : JoinOk D a.span a.goal.rb b.goal.lb b.span then
    ofCost (K.compose a.span b.span) fun c hc =>
      ⟨⟨a.goal.lb, n, b.goal.rb⟩, c,
        Valid.join a.valid b.valid h ((hK.compose _ _).symm.trans hc)⟩
  else pure none

/-- `meetA`: the side condition, the meet, and interning the meet of the
members of both nodes, merged in order. -/
def meetA (a b : Ans D P) : Cost (Option (Ans D P)) := do
  check b.goal.lb (K.leftBound a.span)
  check b.goal.rb (K.rightBound a.span)
  let n := mkAnd (sortedParts (andParts a.goal.node ++ andParts b.goal.node))
  let _ ← Charged.op () (1 + (andParts a.goal.node ++ andParts b.goal.node).length)
    (andParts a.goal.node ++ andParts b.goal.node).length
  if h : MeetOk D a.span a.goal.lb a.goal.rb b.goal.lb b.goal.rb then
    ofCost (K.meet a.span b.span) fun c hc =>
      ⟨⟨a.goal.lb, n, a.goal.rb⟩, c,
        Valid.meet (x := a.goal.node) (y := b.goal.node) a.valid b.valid h
          ((hK.meet _ _).symm.trans hc)⟩
  else pure none

omit [DecidableEq R] in
/-- `inj`: read the member and compare. -/
def inj (a : Ans D P) (u : Rel) (i : Nat) : Cost (Option (Ans D P)) := do
  Cost.tick 2
  pure (if h : u.unionParts[i]? = some a.goal.node then
    some ⟨⟨a.goal.lb, u, a.goal.rb⟩, a.span, a.valid.inj (List.mem_of_getElem? h)⟩
  else none)

omit [DecidableEq R] in
/-- `unfold`: read the body of the call and compare. -/
def unfold (a : Ans D P) (c : Rel) : Cost (Option (Ans D P)) := do
  Cost.tick 2
  pure (match c with
    | .call n =>
      if h : a.goal.node = (P.body n).norm then
        some ⟨⟨a.goal.lb, .call n, a.goal.rb⟩, a.span, Valid.unfold (h ▸ a.valid)⟩
      else none
    | .conv (.call n) =>
      if h : a.goal.node = (P.body n).normConv then
        some ⟨⟨a.goal.lb, .conv (.call n), a.goal.rb⟩, a.span, Valid.unfoldConv (h ▸ a.valid)⟩
      else none
    | _ => none)

omit [DecidableEq R] in
/-- `swapA`: read the converse of the node. The representative is
conversed. -/
def swapA (a : Ans D P) : Cost (Ans D P) := do
  Cost.tick 1
  pure ⟨⟨a.goal.rb, a.goal.node.normConv, a.goal.lb⟩, Answer.swap a.span, a.valid.swap⟩

end Ans

/-- Read a node, with the span of a span node left out. -/
def Charged.viewNode (n : Rel) : Cost (NodeView Unit Rel) :=
  Charged.op n.view.forget (1 + Charged.members n.view) 0

/-- The derivation kernel of the program `P` on the representatives of a
kernel `K` that returns what the domain `D` returns. -/
@[reducible] def DerivationKernel.over {R : Type} [Answer R] [DecidableEq R] (D : Domain R)
    (K : Kernel R Cost) (hK : K.Refines D) (P : Program) :
    DerivationKernel R Rel (Ans D P) Cost :=
  { K with
    view := Charged.viewNode
    interval := Charged.interval
    without := Charged.without
    body := Charged.body P
    convNode := Charged.convNode
    eqNode := Charged.eqNode
    span := Ans.span
    leaf := Ans.leaf D P K hK
    join := Ans.join D P K hK
    meetA := Ans.meetA D P K hK
    inj := Ans.inj D P
    unfold := Ans.unfold D P
    swapA := Ans.swapA D P }

/-- The derivation kernel of the program `P` on spans as they are written. -/
@[reducible] def DerivationKernel.std (P : Program) :
    DerivationKernel Span Rel (Ans Domain.written P) Cost :=
  DerivationKernel.over Domain.written Kernel.std Kernel.std_refines P

end RwLog
