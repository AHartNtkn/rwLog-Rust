/-
# The operations on terms as programs on the base machine

Every program here is written for an arbitrary machine (`Base`,
`Trusted/Base.lean`), so it spends exactly the reads, allocations, comparisons
and table accesses it performs. `Prog.kernelProg` collects them; that they
return what the specification kernel returns is proved in the files next to
this one.

## How terms are handled

*Interning.* An operation works on terms it has brought into one table
(`Intern`): the table maps a node to the pointer of the one copy of it, so two
pointers from the table stand for the same term only if they are the same
pointer. Equality of terms is then one comparison of pointers, and a term that
occurs many times is one node. The table is local to one operation.

*Rebuilding.* `rebuild` copies a term through the table, replacing its
variables as a `leaf` function says, and remembers what each node became
(`memo`), so a shared node is rebuilt once. Renumbering a span's variables,
interning it, and substituting for a variable are all instances.

*Solving.* `msolve` solves equations between interned terms exactly as
`solve` (`Kernel/Solve.lean`) does, in the same order, so it finds the same
substitution, except that a pair of equal pointers is skipped at once. A
variable is eliminated by rebuilding the equations that are left.
-/
import RwLog.Trusted.KernelRung

namespace RwLog

namespace Prog

/-- The tables of a machine with pointers `P`. -/
abbrev Tb (P : Type) {V F : Type} {M : Type → Type} [Base P V F M] (α : Type) : Type :=
  Base.Tbl (P := P) α

/-- The interning table: for a variable or a symbol, the pointer of its node;
for an application, by its first part and then its second. -/
structure Intern (P : Type) {V F : Type} {M : Type → Type} [Base P V F M] where
  leaf : Tb P P
  app : Tb P (Tb P P)

variable {P V F : Type} {M : Type → Type} [Base P V F M]

def Intern.empty : Intern P := ⟨Base.empty, Base.empty⟩

/-- The pointer of the one copy of a node, added if it is new. -/
def mk (I : Intern P) : Node P V F → M (P × Intern P)
  | .var v => do
    let o ← Base.get I.leaf (.word v)
    match o with
    | some p => pure (p, I)
    | none => do
      let p ← Base.alloc (.var v)
      let l ← Base.set I.leaf (.word v) p
      pure (p, { I with leaf := l })
  | .sym f => do
    let o ← Base.get I.leaf (.name f)
    match o with
    | some p => pure (p, I)
    | none => do
      let p ← Base.alloc (.sym f)
      let l ← Base.set I.leaf (.name f) p
      pure (p, { I with leaf := l })
  | .app a b => do
    let o ← Base.get I.app (.ptr a)
    let row := o.getD Base.empty
    let o' ← Base.get row (.ptr b)
    match o' with
    | some p => pure (p, I)
    | none => do
      let p ← Base.alloc (.app a b)
      let row' ← Base.set row (.ptr b) p
      let t ← Base.set I.app (.ptr a) row'
      pure (p, { I with app := t })

/-- Copy the term at `p` through the table, with each variable `v` (at the
pointer `q`) replaced by `leaf I q v`. `memo` holds what each node already
visited became. -/
def rebuild (leaf : Intern P → P → V → M (P × Intern P)) (I : Intern P) (memo : Tb P P) (p : P) :
    M (P × Intern P × Tb P P) := do
  let o ← Base.get memo (.ptr p)
  match o with
  | some r => pure (r, I, memo)
  | none => do
    let n ← Base.read p
    match n with
    | .var v => do
      let r ← leaf I p v
      let memo' ← Base.set memo (.ptr p) r.1
      pure (r.1, r.2, memo')
    | .sym f => do
      let r ← mk I (.sym f)
      let memo' ← Base.set memo (.ptr p) r.1
      pure (r.1, r.2, memo')
    | .app a b => do
      let ra ← rebuild leaf I memo a
      let rb ← rebuild leaf ra.2.1 ra.2.2 b
      let r ← mk rb.2.1 (.app ra.1 rb.1)
      let memo' ← Base.set rb.2.2 (.ptr p) r.1
      pure (r.1, r.2, memo')
partial_fixpoint

/-- `rebuild` on each member of a list. -/
def rebuildAll (leaf : Intern P → P → V → M (P × Intern P)) :
    Intern P → Tb P P → List P → M (List P × Intern P × Tb P P)
  | I, memo, [] => pure ([], I, memo)
  | I, memo, p :: ps => do
    let r ← rebuild leaf I memo p
    let rs ← rebuildAll leaf r.2.1 r.2.2 ps
    pure (r.1 :: rs.1, rs.2)

/-- `rebuild` on the terms of a span, with one memo. -/
def rebuildSpan (leaf : Intern P → P → V → M (P × Intern P)) (I : Intern P) (s : MSpan P) :
    M (MSpan P × Intern P) := do
  let l ← rebuild leaf I Base.empty s.l
  let r ← rebuild leaf l.2.1 l.2.2 s.r
  let c ← rebuildAll leaf r.2.1 r.2.2 s.c
  pure (⟨l.1, r.1, c.1⟩, c.2.1)

/-- Renumber a variable into the left half. -/
def leafL (I : Intern P) (_ : P) (v : V) : M (P × Intern P) := do
  let w ← Base.inl P v
  mk I (.var w)

/-- Renumber a variable into the right half. -/
def leafR (I : Intern P) (_ : P) (v : V) : M (P × Intern P) := do
  let w ← Base.inr P v
  mk I (.var w)

/-- Keep a variable. -/
def leafKeep (I : Intern P) (_ : P) (v : V) : M (P × Intern P) := mk I (.var v)

/-- Replace the variable `x` by the term at `u`; another variable stays the
node it is. For terms that are already in the table. -/
def leafSub (x : V) (u : P) (I : Intern P) (p : P) (v : V) : M (P × Intern P) := do
  let e ← Base.eqV P v x
  pure (if e then u else p, I)

/-- Does the variable `x` occur in the term at `p`? `seen` holds the answer
for each node already visited. -/
def occurs (x : V) (seen : Tb P Bool) (p : P) : M (Bool × Tb P Bool) := do
  let o ← Base.get seen (.ptr p)
  match o with
  | some b => pure (b, seen)
  | none => do
    let n ← Base.read p
    match n with
    | .var v => do
      let e ← Base.eqV P v x
      let seen' ← Base.set seen (.ptr p) e
      pure (e, seen')
    | .sym _ => do
      let seen' ← Base.set seen (.ptr p) false
      pure (false, seen')
    | .app a b => do
      let ra ← occurs x seen a
      let rb ← occurs x ra.2 b
      let seen' ← Base.set rb.2 (.ptr p) (ra.1 || rb.1)
      pure (ra.1 || rb.1, seen')
partial_fixpoint

/-- What `solve` does with the first equation. -/
inductive Act (P V : Type) where
  /-- The two sides are the same term. -/
  | skip
  /-- No substitution makes them equal. -/
  | fail
  /-- Two applications: equate their parts. -/
  | split (a c b d : P)
  /-- Replace the variable `x` by the term at `u`. -/
  | elim (x : V) (u : P)

/-- Decide what to do with the equation between the terms at `p` and `q`. -/
def act (p q : P) : M (Act P V) := do
  let s ← Base.same p q
  if s then pure .skip else do
    let n ← Base.read p
    let m ← Base.read q
    match n, m with
    | .var x, .var y => do
      let e ← Base.eqV P x y
      pure (if e then .skip else .elim x q)
    | .var x, .sym _ => pure (.elim x q)
    | .var x, .app _ _ => do
      let o ← occurs x Base.empty q
      pure (if o.1 then .fail else .elim x q)
    | .sym _, .var y => pure (.elim y p)
    | .app _ _, .var y => do
      let o ← occurs y Base.empty p
      pure (if o.1 then .fail else .elim y p)
    | .sym f, .sym g => do
      let e ← Base.eqF P f g
      pure (if e then .skip else .fail)
    | .app a b, .app c d => pure (.split a c b d)
    | .sym _, .app _ _ => pure .fail
    | .app _ _, .sym _ => pure .fail

/-- Replace `x` by the term at `u` in every equation, with one memo. -/
def substPairs (x : V) (u : P) :
    Intern P → Tb P P → List (P × P) → M (List (P × P) × Intern P × Tb P P)
  | I, memo, [] => pure ([], I, memo)
  | I, memo, e :: E => do
    let l ← rebuild (leafSub x u) I memo e.1
    let r ← rebuild (leafSub x u) l.2.1 l.2.2 e.2
    let rs ← substPairs x u r.2.1 r.2.2 E
    pure ((l.1, r.1) :: rs.1, rs.2)

/-- Solve the equations, as `solve` does: the variables eliminated and what
each was replaced by, in order, or `none` when there is no solution. -/
def msolve (I : Intern P) (E : List (P × P)) : M (Option (List (V × P)) × Intern P) := do
  match E with
  | [] => pure (some [], I)
  | e :: E => do
    let a ← act e.1 e.2
    match a with
    | .skip => msolve I E
    | .fail => pure (none, I)
    | .split a c b d => msolve I ((a, c) :: (b, d) :: E)
    | .elim x u => do
      let s ← substPairs x u I Base.empty E
      let r ← msolve s.2.1 s.1
      pure (r.1.map ((x, u) :: ·), r.2)
partial_fixpoint

/-- Apply the eliminations, in order, to a span. -/
def applyAll : List (V × P) → Intern P → MSpan P → M (MSpan P × Intern P)
  | [], I, s => pure (s, I)
  | b :: bs, I, s => do
    let r ← rebuildSpan (leafSub b.1 b.2) I s
    applyAll bs r.2 r.1

/-- Solve `E` and apply the solution to `out`. -/
def solveInto (I : Intern P) (E : List (P × P)) (out : MSpan P) : M (Option (MSpan P)) := do
  let r ← msolve I E
  match r.1 with
  | none => pure none
  | some bs => do
    let s ← applyAll bs r.2 out
    pure (some s.1)

/-- Sequential composition: match the right of `x` against the left of `y`. -/
def compose (x y : MSpan P) : M (Option (MSpan P)) := do
  let a ← rebuildSpan leafL Intern.empty x
  let b ← rebuildSpan leafR a.2 y
  solveInto b.2 [(a.1.r, b.1.l)] ⟨a.1.l, b.1.r, a.1.c ++ b.1.c⟩

/-- Conjunction: match both sides. -/
def meet (x y : MSpan P) : M (Option (MSpan P)) := do
  let a ← rebuildSpan leafL Intern.empty x
  let b ← rebuildSpan leafR a.2 y
  solveInto b.2 [(a.1.l, b.1.l), (a.1.r, b.1.r)] ⟨a.1.l, a.1.r, a.1.c ++ b.1.c⟩

/-- Does `acc` compose with the chain? -/
def chainFrom : MSpan P → List (MSpan P) → M Bool
  | _, [] => pure true
  | acc, t :: rest => do
    let r ← compose acc t
    match r with
    | none => pure false
    | some s => chainFrom s rest

/-- Does the chain compose? -/
def composable : List (MSpan P) → M Bool
  | [] => pure true
  | s :: rest => chainFrom s rest

/-- Are the two lists the same pointers, in order? -/
def sameAll : List P → List P → M Bool
  | [], [] => pure true
  | p :: ps, q :: qs => do
    let s ← Base.same p q
    if s then sameAll ps qs else pure false
  | [], _ :: _ => pure false
  | _ :: _, [] => pure false

/-- Bring two spans into one table. -/
def internBoth (x y : MSpan P) : M (MSpan P × MSpan P) := do
  let a ← rebuildSpan leafKeep Intern.empty x
  let b ← rebuildSpan leafKeep a.2 y
  pure (a.1, b.1)

/-- Are the two spans the same, as written? -/
def eq (x y : MSpan P) : M Bool := do
  let r ← internBoth x y
  sameAll (r.1.l :: r.1.r :: r.1.c) (r.2.l :: r.2.r :: r.2.c)

/-- Are the two expressions the same, as written? -/
def eqRel : RelOf (MSpan P) → RelOf (MSpan P) → M Bool
  | .zero, .zero => pure true
  | .span s, .span t => eq s t
  | .or a b, .or c d => do
    let x ← eqRel a c
    if x then eqRel b d else pure false
  | .and a b, .and c d => do
    let x ← eqRel a c
    if x then eqRel b d else pure false
  | .seq a b, .seq c d => do
    let x ← eqRel a c
    if x then eqRel b d else pure false
  | .conv a, .conv b => eqRel a b
  | .call m, .call n => pure (decide (m = n))
  | _, _ => pure false

/-- `patCmp` on two terms of one table. -/
def pcmp (p q : P) : M Ordering := do
  let s ← Base.same p q
  if s then pure .eq else do
    let n ← Base.read p
    let m ← Base.read q
    match n, m with
    | .var a, .var b => Base.cmpV P a b
    | .var _, .sym _ => pure .lt
    | .var _, .app _ _ => pure .lt
    | .sym _, .var _ => pure .gt
    | .app _ _, .var _ => pure .gt
    | .sym f, .sym g => Base.cmpF P f g
    | .sym _, .app _ _ => pure .lt
    | .app _ _, .sym _ => pure .gt
    | .app a b, .app c d => do
      let o ← pcmp a c
      match o with
      | .eq => pcmp b d
      | .lt => pure .lt
      | .gt => pure .gt
partial_fixpoint

/-- `listCmp patCmp` on terms of one table. -/
def pcmpAll : List P → List P → M Ordering
  | [], [] => pure .eq
  | [], _ :: _ => pure .lt
  | _ :: _, [] => pure .gt
  | p :: ps, q :: qs => do
    let o ← pcmp p q
    match o with
    | .eq => pcmpAll ps qs
    | .lt => pure .lt
    | .gt => pure .gt

/-- `spanCmp`. -/
def spanCmp (x y : MSpan P) : M Ordering := do
  let r ← internBoth x y
  pcmpAll (r.1.l :: r.1.r :: r.1.c) (r.2.l :: r.2.r :: r.2.c)

/-- `relCmp`. -/
def relCmp : RelOf (MSpan P) → RelOf (MSpan P) → M Ordering
  | .zero, .zero => pure .eq
  | .zero, .span _ => pure .lt
  | .zero, .or _ _ => pure .lt
  | .zero, .and _ _ => pure .lt
  | .zero, .seq _ _ => pure .lt
  | .zero, .conv _ => pure .lt
  | .zero, .call _ => pure .lt
  | .span _, .zero => pure .gt
  | .span a, .span b => spanCmp a b
  | .span _, .or _ _ => pure .lt
  | .span _, .and _ _ => pure .lt
  | .span _, .seq _ _ => pure .lt
  | .span _, .conv _ => pure .lt
  | .span _, .call _ => pure .lt
  | .or _ _, .zero => pure .gt
  | .or _ _, .span _ => pure .gt
  | .or a b, .or c d => do
    let o ← relCmp a c
    match o with
    | .eq => relCmp b d
    | .lt => pure .lt
    | .gt => pure .gt
  | .or _ _, .and _ _ => pure .lt
  | .or _ _, .seq _ _ => pure .lt
  | .or _ _, .conv _ => pure .lt
  | .or _ _, .call _ => pure .lt
  | .and _ _, .zero => pure .gt
  | .and _ _, .span _ => pure .gt
  | .and _ _, .or _ _ => pure .gt
  | .and a b, .and c d => do
    let o ← relCmp a c
    match o with
    | .eq => relCmp b d
    | .lt => pure .lt
    | .gt => pure .gt
  | .and _ _, .seq _ _ => pure .lt
  | .and _ _, .conv _ => pure .lt
  | .and _ _, .call _ => pure .lt
  | .seq _ _, .zero => pure .gt
  | .seq _ _, .span _ => pure .gt
  | .seq _ _, .or _ _ => pure .gt
  | .seq _ _, .and _ _ => pure .gt
  | .seq a b, .seq c d => do
    let o ← relCmp a c
    match o with
    | .eq => relCmp b d
    | .lt => pure .lt
    | .gt => pure .gt
  | .seq _ _, .conv _ => pure .lt
  | .seq _ _, .call _ => pure .lt
  | .conv _, .zero => pure .gt
  | .conv _, .span _ => pure .gt
  | .conv _, .or _ _ => pure .gt
  | .conv _, .and _ _ => pure .gt
  | .conv _, .seq _ _ => pure .gt
  | .conv a, .conv b => relCmp a b
  | .conv _, .call _ => pure .lt
  | .call _, .zero => pure .gt
  | .call _, .span _ => pure .gt
  | .call _, .or _ _ => pure .gt
  | .call _, .and _ _ => pure .gt
  | .call _, .seq _ _ => pure .gt
  | .call _, .conv _ => pure .gt
  | .call m, .call n => pure (compare m n)

/-- Put `e` before the first member that is not below it. -/
def insertRel (e : RelOf (MSpan P)) : List (RelOf (MSpan P)) → M (List (RelOf (MSpan P)))
  | [] => pure [e]
  | b :: l => do
    let o ← relCmp e b
    match o with
    | .gt => do
      let l' ← insertRel e l
      pure (b :: l')
    | _ => pure (e :: b :: l)

/-- Sort by `relCmp`. -/
def sortRel : List (RelOf (MSpan P)) → M (List (RelOf (MSpan P)))
  | [] => pure []
  | e :: es => do
    let s ← sortRel es
    insertRel e s

/-- Is `e` one of the list, as written? -/
def memRel (e : RelOf (MSpan P)) : List (RelOf (MSpan P)) → M Bool
  | [] => pure false
  | b :: l => do
    let x ← eqRel e b
    if x then pure true else memRel e l

/-- The members in the order of their first occurrence. -/
def firstsRel : List (RelOf (MSpan P)) → List (RelOf (MSpan P)) → M (List (RelOf (MSpan P)))
  | acc, [] => pure acc
  | acc, e :: es => do
    let x ← memRel e acc
    if x then firstsRel acc es else firstsRel (acc ++ [e]) es

/-- Is the expression not `0`? -/
def notZero : RelOf (MSpan P) → Bool
  | .zero => false
  | _ => true

/-- `sortedBranches`. -/
def sortedBranches (es : List (RelOf (MSpan P))) : M (List (RelOf (MSpan P))) := do
  let s ← sortRel (es.filter notZero)
  firstsRel [] s

/-- The canonical form of an expression. -/
def canon : RelOf (MSpan P) → M (RelOf (MSpan P))
  | .zero => pure .zero
  | .span s => pure (.span s)
  | .or a b => do
    let a' ← canon a
    let b' ← canon b
    let bs ← sortedBranches (orBranches a' ++ orBranches b')
    pure (mkOr bs)
  | .and a b => do
    let a' ← canon a
    let b' ← canon b
    pure (.and a' b')
  | .seq a b => do
    let a' ← canon a
    let b' ← canon b
    pure (.seq a' b')
  | .conv a => do
    let a' ← canon a
    pure (.conv a')
  | .call n => pure (.call n)

/-- Mark every variable of the term at `p` in `marks`. `seen` holds the nodes
already visited. -/
def markVars (marks : Tb P Unit) (seen : Tb P Unit) (p : P) : M (Tb P Unit × Tb P Unit) := do
  let o ← Base.get seen (.ptr p)
  match o with
  | some _ => pure (marks, seen)
  | none => do
    let seen' ← Base.set seen (.ptr p) ()
    let n ← Base.read p
    match n with
    | .var v => do
      let marks' ← Base.set marks (.word v) ()
      pure (marks', seen')
    | .sym _ => pure (marks, seen')
    | .app a b => do
      let ra ← markVars marks seen' a
      markVars ra.1 ra.2 b
partial_fixpoint

/-- Is every variable of the term at `p` marked? `seen` holds the answer for
each node already visited. -/
def allMarked (marks : Tb P Unit) (seen : Tb P Bool) (p : P) : M (Bool × Tb P Bool) := do
  let o ← Base.get seen (.ptr p)
  match o with
  | some b => pure (b, seen)
  | none => do
    let n ← Base.read p
    match n with
    | .var v => do
      let m ← Base.get marks (.word v)
      let seen' ← Base.set seen (.ptr p) m.isSome
      pure (m.isSome, seen')
    | .sym _ => do
      let seen' ← Base.set seen (.ptr p) true
      pure (true, seen')
    | .app a b => do
      let ra ← allMarked marks seen a
      let rb ← allMarked marks ra.2 b
      let seen' ← Base.set rb.2 (.ptr p) (ra.1 && rb.1)
      pure (ra.1 && rb.1, seen')
partial_fixpoint

/-- The members whose variables are all marked. -/
def keepMarked (marks : Tb P Unit) : Tb P Bool → List P → M (List P)
  | _, [] => pure []
  | seen, p :: ps => do
    let r ← allMarked marks seen p
    let rest ← keepMarked marks r.2 ps
    pure (if r.1 then p :: rest else rest)

/-- The interface at the term `p` of a span with store `c`, as a boundary:
`p {c|p} -> p`, or nothing when that is `$x -> $x`. -/
def ifaceBound (p : P) (c : List P) : M (Option (MSpan P)) := do
  let m ← markVars Base.empty Base.empty p
  let c' ← keepMarked m.1 Base.empty c
  let n ← Base.read p
  match n, c' with
  | .var _, [] => pure none
  | _, _ => pure (some ⟨p, p, c'⟩)

def rightBound (s : MSpan P) : M (Option (MSpan P)) := ifaceBound s.r s.c

def leftBound (s : MSpan P) : M (Option (MSpan P)) := ifaceBound s.l s.c

/-- One-way matching of the term at `p` onto the term at `t`, both of one
table. `θ` holds what each variable of the pattern is bound to, and `memo`
what each node of the pattern already matched. -/
def mmatch (p t : P) (θ : Tb P P) (memo : Tb P P) : M (Option (Tb P P × Tb P P)) := do
  let o ← Base.get memo (.ptr p)
  match o with
  | some t' => do
    let s ← Base.same t' t
    pure (if s then some (θ, memo) else none)
  | none => do
    let n ← Base.read p
    match n with
    | .var v => do
      let b ← Base.get θ (.word v)
      match b with
      | some u => do
        let s ← Base.same u t
        if s then do
          let memo' ← Base.set memo (.ptr p) t
          pure (some (θ, memo'))
        else pure none
      | none => do
        let θ' ← Base.set θ (.word v) t
        let memo' ← Base.set memo (.ptr p) t
        pure (some (θ', memo'))
    | .sym f => do
      let m ← Base.read t
      match m with
      | .sym g => do
        let e ← Base.eqF P f g
        if e then do
          let memo' ← Base.set memo (.ptr p) t
          pure (some (θ, memo'))
        else pure none
      | _ => pure none
    | .app p₁ p₂ => do
      let m ← Base.read t
      match m with
      | .app t₁ t₂ => do
        let r₁ ← mmatch p₁ t₁ θ memo
        match r₁ with
        | none => pure none
        | some s₁ => do
          let r₂ ← mmatch p₂ t₂ s₁.1 s₁.2
          match r₂ with
          | none => pure none
          | some s₂ => do
            let memo' ← Base.set s₂.2 (.ptr p) t
            pure (some (s₂.1, memo'))
      | _ => pure none
partial_fixpoint

/-- Does `a`, which has no constraints, cover `s`? -/
def coversPlain (a s : MSpan P) : M Bool := do
  let r ← internBoth a s
  let m₁ ← mmatch r.1.l r.2.l Base.empty Base.empty
  match m₁ with
  | none => pure false
  | some s₁ => do
    let m₂ ← mmatch r.1.r r.2.r s₁.1 s₁.2
    pure m₂.isSome

end Prog

/-- The operations on terms, for every machine. -/
def Prog.kernelProg : KernelProg where
  ops := {
    compose := Prog.compose
    meet := Prog.meet
    composable := Prog.composable
    coversPlain := Prog.coversPlain
    eq := Prog.eq
    eqRel := Prog.eqRel
    canon := Prog.canon
    rightBound := Prog.rightBound
    leftBound := Prog.leftBound }

end RwLog
