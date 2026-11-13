/-
# The unfolding race

Every incomplete table of the tabled machine (`Rungs/Tabled/Machine.lean`)
asks once a round whether its goal's *unfolding* to the depth of the round is
final, and for the goal's answers if it is. This file has the three ways the
question is answered and the races between them. All are written against the
derivation kernel, so their answers are answers of the goal made by its
rules.

## The unfolding of a goal

Reading a node costs one level of depth: a node read at depth `d + 1` has its
members, and the body of a call, read at depth `d`, and a node at depth `0`
is not read. The depth therefore bounds how far below the goal's node
anything is looked at, through members and through calls alike. (An engine
cannot recurse on a node: it is an identifier, and the kernel gives no
measure of what is below it.)

The unfolding is a list of *products*: one for every way of choosing a member
at each union read. A node that was not read is *opaque*. A product with no
opaque node is *closed*: it is an answer of the goal, made by `leaf`, `join`,
`meetA`, `inj` and `unfold`. A product with an opaque node is *open*. Its
spans form stretches between the opaque nodes, and it is kept while every
stretch composes; the first stretch has the left boundary of the goal in it
and the last one the right boundary. A meet with an open member is itself
opaque, once each of its members has a product between the boundaries the
meet stands between.

The unfolding is *final* when it has no open product, and then its closed
products are every answer of the goal.

## Three evaluations

* `eager` builds the whole list, member by member. It is the definition.
* `walk` goes through the products one at a time, from one end of every
  chain to the other, and stops at the first open product that reaches the
  top. The interface of what it has composed so far is pushed into what
  follows as a boundary, so a span that cannot follow is dropped where it
  stands. `walk false` goes from left to right and `walk true` from right to
  left.
* `shared` goes from left to right and computes, for a node and the interface
  to its left, the closed products and the interfaces the open ones leave,
  once: a node reached from two derivations that leave the same interface is
  looked up the second time.

A pushed boundary does not enter a meet when the question is whether the meet
is opaque: that is decided between the boundaries the meet stands between in
the goal, so that it does not depend on the direction of the evaluation.

`walk` can stop long before `shared` has finished, and `shared` can be
exponentially cheaper than `walk`, and each direction of `walk` than the
other. The tabled machine is run with them raced (`Kernel.race`):
`walkShared` is the left-to-right walk beside `shared`, and `raced` is that
beside the right-to-left walk.
-/
import RwLog.Rungs.Tabled.Machine

namespace RwLog

namespace Tabled

namespace Unfold

open Traverse

/-- A product of an unfolding: an answer, or an open product with its first
and its last stretch (absent when the product starts or ends with an opaque
node and there is no boundary). -/
inductive Prod (S A : Type) where
  | closed (a : A)
  | opn (l r : Option S)

def Prod.isOpn {S A : Type} : Prod S A → Bool
  | .closed _ => false
  | .opn _ _ => true

/-- The answers among the products. -/
def closedOf {S A : Type} (ps : List (Prod S A)) : List A :=
  ps.filterMap fun
    | .closed a => some a
    | .opn _ _ => none

/-- Go through a list, threading what is carried, until told to stop. -/
def untilL {M : Type → Type} [Monad M] {α β : Type} (f : β → α → M (Bool × α)) : List β → α → M (Bool × α)
  | [], acc => pure (false, acc)
  | x :: xs, acc => do
    let r ← f x acc
    if r.1 then pure r else untilL f xs r.2

section

variable {S N A : Type} {M : Type → Type} [K : DerivationKernel S N A M]

/-- Add an answer unless one with the same representative is there. -/
def addAns (xs : List A) (x : A) : M (List A) := do
  let b ← anyL (fun y => K.eq (K.span y) (K.span x)) xs
  pure (if b then xs else xs ++ [x])

/-! ## The whole unfolding -/

/-- Two stretches that meet, composed: nothing if they do not compose. An
absent stretch leaves the other as it is. -/
def glue : Option S → Option S → M (Option (Option S))
  | none, y => pure (some y)
  | some x, none => pure (some (some x))
  | some x, some y => do
    let z ← K.compose x y
    pure (z.map some)

/-- A product followed by a product of the next member of a chain. -/
def seqProd : Prod S A → Prod S A → M (Option (Prod S A))
  | .closed a, .closed b => do
    let c ← K.join a b
    pure (c.map .closed)
  | .closed a, .opn l r => do
    let l' ← glue (K := K) (some (K.span a)) l
    pure (l'.map fun l' => .opn l' r)
  | .opn l r, .closed b => do
    let r' ← glue (K := K) r (some (K.span b))
    pure (r'.map fun r' => .opn l r')
  | .opn l r, .opn l' r' => do
    let m ← glue (K := K) r l'
    pure (m.map fun _ => .opn l r')

/-- Apply a rule to the answers among the products. -/
def liftL (f : A → M (Option A)) (ps : List (Prod S A)) : M (List (Prod S A)) :=
  filterMapL (fun p => match p with
    | .closed a => do
      let b ← f a
      pure (b.map .closed)
    | .opn l r => pure (some (.opn l r))) ps

/-- The products of a chain from the products of its members. -/
def seqAll : List (List (Prod S A)) → M (List (Prod S A))
  | [] => pure []
  | ps :: rest => foldL (fun acc qs => flatMapL (fun p => filterMapL (seqProd (K := K) p) qs) acc)
      ps rest

/-- The closed products of a meet from the answers of its members. -/
def meetAll : List (List A) → M (List A)
  | [] => pure []
  | as :: rest => foldL (fun acc bs => flatMapL (fun a => filterMapL (K.meetA a) bs) acc) as rest

/-- The unfolding of the goal `lb ; n ; rb` to depth `d`. -/
def eager : Nat → Option S → N → Option S → M (List (Prod S A))
  | 0, lb, _, rb => pure [.opn lb rb]
  | d + 1, lb, n, rb => do
    K.tick 1
    let v ← K.view n
    match v with
    | .span _ => do
      let a ← K.leaf lb n rb
      pure (a.toList.map .closed)
    | .call _ _ => do
      let b ← K.body n
      match b with
      | none => pure []
      | some b => do
        let ps ← eager d lb b rb
        liftL (K := K) (fun a => K.unfold a n) ps
    | .union xs => flatMapL (fun p => do
        let ps ← eager d lb p.1 rb
        liftL (K := K) (fun a => K.inj a n p.2) ps) xs.zipIdx
    | .chain xs => do
      let pss ← mapL (fun p =>
        eager d (if p.2 = 0 then lb else none) p.1 (if p.2 + 1 = xs.length then rb else none))
        xs.zipIdx
      seqAll (K := K) pss
    | .meet xs => do
      let pss ← mapL (fun x => eager d lb x rb) xs
      let cs ← meetAll (K := K) (pss.map closedOf)
      let opq := pss.all (fun ps => !ps.isEmpty) && pss.any (fun ps => ps.any Prod.isOpn)
      pure (cs.map .closed ++ if opq then [.opn lb rb] else [])

/-- The unfolding race answered by building the whole unfolding. -/
def eagerRace : GOracle S N A M := fun d g => do
  let ps ← eager (K := K) d g.lb g.node g.rb
  if ps.any Prod.isOpn then pure (false, [])
  else do
    let as ← foldL (addAns (K := K)) [] (closedOf ps)
    pure (true, as)

/-! ## One product at a time -/

/-- What a walk hands on: an answer, or an open product with the stretch at
its far end (absent when it ends with an opaque node and no boundary). -/
inductive Item (S A : Type) where
  | closed (a : A)
  | opn (t : Option S)

/-- The boundary on the side a walk comes from, and whether it was pushed
there by the walk (and is not a boundary of the goal). -/
structure Near (S : Type) where
  bound : Option S
  pushed : Bool

/-- The boundary a meet stands between on the near side. -/
def Near.own {S : Type} (c : Near S) : Near S := if c.pushed then ⟨none, false⟩ else c

/-- Is anything pushed here that the goal does not have? -/
def Near.isPushed {S : Type} (c : Near S) : Bool := c.pushed && c.bound.isSome

/-- The rule `leaf` between the near and the far boundary. With `rev` the
near side is the right. -/
def leafAt (rev : Bool) (near : Option S) (n : N) (far : Option S) : M (Option A) :=
  if rev then K.leaf far n near else K.leaf near n far

/-- The interface of a representative on the far side. -/
def farBound (rev : Bool) (s : S) : M (Option S) :=
  if rev then K.leftBound s else K.rightBound s

/-- The rule `join` of what was walked first and what was walked after it. -/
def joinAt (rev : Bool) (a b : A) : M (Option A) := if rev then K.join b a else K.join a b

/-- What is pushed into the next member of a chain after an item. -/
def nearAfter (rev : Bool) : Item S A → M (Near S)
  | .closed a => do
    let c ← farBound (K := K) rev (K.span a)
    pure ⟨c, true⟩
  | .opn none => pure ⟨none, false⟩
  | .opn (some t) => do
    let c ← farBound (K := K) rev t
    pure ⟨c, true⟩

/-- An item of what was walked so far, followed by an item of the next member
walked under what the first pushes. An answer after an answer is their join.
After an open product, or when the next item is open, the product is open,
and its far stretch is that of the next item. -/
def extend (rev : Bool) : Option (Item S A) → Item S A → M (Option (Item S A))
  | none, it => pure (some it)
  | some (.closed a), .closed b => do
    let c ← joinAt (K := K) rev a b
    pure (c.map .closed)
  | some (.closed _), .opn t => pure (some (.opn t))
  | some (.opn _), .closed b => pure (some (.opn (some (K.span b))))
  | some (.opn _), .opn t => pure (some (.opn t))

/-- Apply a rule to an item that is an answer. -/
def liftItem (f : A → M (Option A)) : Item S A → M (Option (Item S A))
  | .closed a => do
    let b ← f a
    pure (b.map .closed)
  | .opn t => pure (some (.opn t))

variable {α : Type}

/-- The walker of one node: its near context, the node, its far boundary,
what to do with each item, and what is carried. -/
abbrev Walker (S N A : Type) (M : Type → Type) (α : Type) :=
  Near S → N → Option S → (Item S A → α → M (Bool × α)) → α → M (Bool × α)

/-- Walk the members of a chain in the order given, each under what the items
before it push, handing every product of the chain on. `far` is the far
boundary of the chain, which only its last member sees. -/
def seqW (rev : Bool) (w : Walker S N A M α) (far : Option S) :
    Option (Item S A) → Near S → List N → (Item S A → α → M (Bool × α)) → α → M (Bool × α)
  | pre, _, [], k, acc =>
    match pre with
    | some it => k it acc
    | none => pure (false, acc)
  | pre, c, x :: xs, k, acc =>
    w c x (if xs.isEmpty then far else none) (fun it acc => do
      let r ← extend (K := K) rev pre it
      match r with
      | none => pure (false, acc)
      | some it' => do
        let c' ← nearAfter (K := K) rev it'
        seqW rev w far (some it') c' xs k acc) acc

/-- Walk the members of a meet, all between the same boundaries. With
`closed` the answers of the meet are handed on, each the `meetA` of one
answer of every member. With `opq` the meet is handed on as an open
product once for every choice of products of the members, not all of them
answers. -/
def andW (closed opq : Bool) (w : N → (Item S A → α → M (Bool × α)) → α → M (Bool × α))
    (far : Option S) :
    Option (Item S A) → List N → (Item S A → α → M (Bool × α)) → α → M (Bool × α)
  | pre, [], k, acc =>
    match pre with
    | some (.closed a) => if closed then k (.closed a) acc else pure (false, acc)
    | some (.opn _) => if opq then k (.opn far) acc else pure (false, acc)
    | none => pure (false, acc)
  | pre, x :: xs, k, acc =>
    match pre, opq with
    | some (.opn _), false => pure (false, acc)
    | _, _ =>
      w x (fun it acc =>
        match pre, it with
        | none, it => andW closed opq w far (some it) xs k acc
        | some (.closed a), .closed b => do
          let c ← K.meetA a b
          match c with
          | some c => andW closed opq w far (some (.closed c)) xs k acc
          | none => pure (false, acc)
        | some (.closed _), .opn t => andW closed opq w far (some (.opn t)) xs k acc
        | some (.opn t), _ => andW closed opq w far (some (.opn t)) xs k acc) acc

/-- Go through the products of the unfolding of a node to depth `d`, between
the near context `c` and the far boundary, handing each to `k` until `k` says
stop. One tick for each node read. With `rev` chains are walked from their
last member to their first. -/
def walk (rev : Bool) : Nat → Walker S N A M α
  | 0, _, _, far, k, acc => k (.opn far) acc
  | d + 1, c, n, far, k, acc => do
    K.tick 1
    let v ← K.view n
    match v with
    | .span _ => do
      let a ← leafAt (K := K) rev c.bound n far
      match a with
      | some a => k (.closed a) acc
      | none => pure (false, acc)
    | .call _ _ => do
      let b ← K.body n
      match b with
      | none => pure (false, acc)
      | some b => walk rev d c b far (fun it acc => do
          let r ← liftItem (K := K) (fun a => K.unfold a n) it
          match r with
          | some it' => k it' acc
          | none => pure (false, acc)) acc
    | .union xs => untilL (fun p acc => walk rev d c p.1 far (fun it acc => do
          let r ← liftItem (K := K) (fun a => K.inj a n p.2) it
          match r with
          | some it' => k it' acc
          | none => pure (false, acc)) acc) xs.zipIdx acc
    | .chain xs =>
      seqW (K := K) rev (walk rev d : Walker S N A M α) far none c (if rev then xs.reverse else xs) k acc
    | .meet xs =>
      if c.isPushed then do
        let r ← andW (K := K) true false (fun x => walk rev d c x far) far none xs k acc
        if r.1 then pure r
        else andW (K := K) false true (fun x => walk rev d c.own x far) far none xs k r.2
      else andW (K := K) true true (fun x => walk rev d c x far) far none xs k acc

/-- The unfolding race answered by a walk that stops at the first open
product: from the left boundary to the right one, or with `rev` from the
right one to the left. -/
def walkRace (rev : Bool) : GOracle S N A M := fun d g => do
  let r ← walk (K := K) rev d ⟨if rev then g.rb else g.lb, false⟩ g.node
    (if rev then g.lb else g.rb)
    (fun it acc => match it with
      | .closed a => do
        let acc' ← addAns (K := K) acc a
        pure (false, acc')
      | .opn _ => pure (true, acc)) []
  pure (if r.1 then (false, []) else (true, r.2))

/-! ## With shared work -/

/-- The products of a node after an interface: the answers, without repeats,
and the interface each open product leaves on its right (absent: no
restriction), without repeats. -/
structure Summary (S A : Type) where
  closed : List A
  opens : List (Option S)

/-- What a summary was computed for: a node, or the members of a chain from
the `idx`-th on when `idx` is positive; the depth; the context on the left;
the boundary on the right. -/
structure Key (S N : Type) where
  node : N
  idx : Nat
  d : Nat
  near : Near S
  far : Option S

abbrev Memo (S N A : Type) := List (Key S N × Summary S A)

/-- Compare two keys: one tick, then the nodes and the boundaries. -/
def sameKey (k k' : Key S N) : M Bool := do
  K.tick 1
  if k.idx = k'.idx ∧ k.d = k'.d ∧ k.near.pushed = k'.near.pushed then do
    let b ← K.eqNode k.node k'.node
    if b then do
      let l ← sameBound (K := K) k.near.bound k'.near.bound
      if l then sameBound (K := K) k.far k'.far else pure false
    else pure false
  else pure false

def lookup (m : Memo S N A) (k : Key S N) : M (Option (Summary S A)) := do
  let r ← findL (fun p => sameKey (K := K) p.1 k) m
  pure (r.map Prod.snd)

/-- Look the key up; compute and record the summary if it is not there. -/
def memo (k : Key S N) (m : Memo S N A) (body : Memo S N A → M (Summary S A × Memo S N A)) :
    M (Summary S A × Memo S N A) := do
  let hit ← lookup (K := K) m k
  match hit with
  | some s => pure (s, m)
  | none => do
    let r ← body m
    pure (r.1, (k, r.1) :: r.2)

/-- Add an interface unless it is already there. -/
def addOpen (xs : List (Option S)) (x : Option S) : M (List (Option S)) := do
  let b ← anyL (fun y => sameBound (K := K) y x) xs
  pure (if b then xs else xs ++ [x])

/-- Add the products of one summary to another. -/
def addSummary (s : Summary S A) (closed : List A) (opens : List (Option S)) :
    M (Summary S A) := do
  let cs ← foldL (addAns (K := K)) s.closed closed
  let os ← foldL (addOpen (K := K)) s.opens opens
  pure ⟨cs, os⟩

/-- The evaluation of one node: its left context, the node, its right
boundary, and the memo. -/
abbrev Evaluator (S N A : Type) (M : Type → Type) :=
  Near S → N → Option S → Memo S N A → M (Summary S A × Memo S N A)

/-- The summary of the members `xs` of the chain `n`, which start at its
`i`-th member, after the context `c`. Each product of the first member is
followed by the summary of the rest after the interface it leaves. -/
def sufS (w : Evaluator S N A M) (n : N) (d : Nat) (far : Option S) :
    Nat → List N → Near S → Memo S N A → M (Summary S A × Memo S N A)
  | _, [], _, m => pure (⟨[], []⟩, m)
  | _, [x], c, m => w c x far m
  | i, x :: y :: xs, c, m =>
    (if i = 0 then fun body => body m else memo (K := K) ⟨n, i, d, c, far⟩ m) fun m => do
      let s ← w c x none m
      let r ← foldL (fun (acc : Summary S A × Memo S N A) a => do
        let c' ← K.rightBound (K.span a)
        let t ← sufS w n d far (i + 1) (y :: xs) ⟨c', true⟩ acc.2
        let zs ← filterMapL (fun b => K.join a b) t.1.closed
        let s' ← addSummary (K := K) acc.1 zs t.1.opens
        pure (s', t.2)) (⟨[], []⟩, s.2) s.1.closed
      foldL (fun (acc : Summary S A × Memo S N A) o => do
        let t ← sufS w n d far (i + 1) (y :: xs) ⟨o, o.isSome⟩ acc.2
        let os ← mapL (fun b => K.rightBound (K.span b)) t.1.closed
        let s' ← addSummary (K := K) acc.1 [] (os ++ t.1.opens)
        pure (s', t.2)) r s.1.opens

/-- The summaries of the members of a meet, all in the same context. -/
def membersS (w : N → Memo S N A → M (Summary S A × Memo S N A)) :
    List N → Memo S N A → M (List (Summary S A) × Memo S N A)
  | [], m => pure ([], m)
  | x :: xs, m => do
    let s ← w x m
    let r ← membersS w xs s.2
    pure (s.1 :: r.1, r.2)

/-- Is a meet opaque, given the summaries of its members between the
boundaries it stands between? Every member has a product and one of them an
open one. -/
def opaqueS (ss : List (Summary S A)) : Bool :=
  ss.all (fun s => !s.closed.isEmpty || !s.opens.isEmpty) && ss.any (fun s => !s.opens.isEmpty)

/-- The summary of a node unfolded to depth `d` after the context `c`. One
tick for each node evaluated. -/
def evalS : Nat → Evaluator S N A M
  | 0, _, _, far, m => pure (⟨[], [far]⟩, m)
  | d + 1, c, n, far, m => memo (K := K) ⟨n, 0, d + 1, c, far⟩ m fun m => do
    K.tick 1
    let v ← K.view n
    match v with
    | .span _ => do
      let a ← K.leaf c.bound n far
      pure (⟨a.toList, []⟩, m)
    | .call _ _ => do
      let b ← K.body n
      match b with
      | none => pure (⟨[], []⟩, m)
      | some b => do
        let r ← evalS d c b far m
        let cs ← filterMapL (fun a => K.unfold a n) r.1.closed
        pure (⟨cs, r.1.opens⟩, r.2)
    | .union xs => foldL (fun (acc : Summary S A × Memo S N A) p => do
        let r ← evalS d c p.1 far acc.2
        let cs ← filterMapL (fun a => K.inj a n p.2) r.1.closed
        let s' ← addSummary (K := K) acc.1 cs r.1.opens
        pure (s', r.2)) (⟨[], []⟩, m) xs.zipIdx
    | .chain xs => sufS (K := K) (evalS d) n d far 0 xs c m
    | .meet xs => do
      let r ← membersS (fun x m => evalS d c x far m) xs m
      let cs ← meetAll (K := K) (r.1.map (·.closed))
      let cs' ← foldL (addAns (K := K)) [] cs
      let o ← if c.isPushed then membersS (fun x m => evalS d c.own x far m) xs r.2
        else pure r
      pure (⟨cs', if opaqueS o.1 then [far] else []⟩, o.2)

/-- The unfolding race answered with shared work. -/
def sharedRace : GOracle S N A M := fun d g => do
  let r ← evalS (K := K) d ⟨g.lb, false⟩ g.node g.rb []
  pure (if r.1.opens.isEmpty then (true, r.1.closed) else (false, []))

/-! ## The races -/

/-- The left-to-right walk and the shared evaluation, side by side. -/
def walkShared : GOracle S N A M := fun d g =>
  K.race (walkRace (K := K) false d g) (sharedRace (K := K) d g)

/-- The left-to-right walk, the shared evaluation and the right-to-left walk,
side by side. -/
def raced : GOracle S N A M := fun d g =>
  K.race (walkShared (K := K) d g) (walkRace (K := K) true d g)

end

end Unfold

end Tabled

end RwLog
