/-
# The operations on terms as programs on the base machine

Every program here is written for an arbitrary machine (`Base`,
`Trusted/Base.lean`), so it spends exactly the reads, allocations, comparisons
and table accesses it performs. `Prog.kernelProg` collects them; that they
return what the specification kernel returns is proved in the files next to
this one.

## How terms are handled

The store keeps one copy of each node, so two pointers stand for the same term
only if they are the same pointer. Equality of terms is one comparison of
pointers, and a term that occurs many times is one node.

*Rebuilding.* `rebuild` copies a term with its variables replaced as a `leaf`
function says, and remembers what each node became (`memo`), so a shared node
is rebuilt once and a node that does not change is not copied at all.
Renumbering a span's variables and substituting for a variable are instances.

*Solving.* `msolve` solves equations between terms exactly as `solve`
(`Kernel/Solve.lean`) does, in the same order, so it finds the same
substitution, except that a pair of equal pointers is skipped at once. A
variable is eliminated by rebuilding the equations that are left.
-/
import RwLog.Trusted.KernelRung

namespace RwLog

namespace Prog

/-- The tables of a machine with pointers `P`. -/
abbrev Tb (P : Type) {V F : Type} {M : Type → Type} [Base P V F M] (α : Type) : Type :=
  Base.Tbl (P := P) α

variable {P V F : Type} {M : Type → Type} [Base P V F M]

/-- Copy the term at `p`, with each variable `v` (at the pointer `q`)
replaced by `leaf q v`. `memo` holds what each node already visited became. -/
def rebuild (leaf : P → V → M P) (memo : Tb P P) (p : P) : M (P × Tb P P) := do
  let o ← Base.get memo (.ptr p)
  match o with
  | some r => pure (r, memo)
  | none => do
    let n ← Base.read p
    match n with
    | .var v => do
      let r ← leaf p v
      let memo' ← Base.set memo (.ptr p) r
      pure (r, memo')
    | .sym _ => do
      let memo' ← Base.set memo (.ptr p) p
      pure (p, memo')
    | .app a b => do
      let ra ← rebuild leaf memo a
      let rb ← rebuild leaf ra.2 b
      let r ← Base.alloc (.app ra.1 rb.1)
      let memo' ← Base.set rb.2 (.ptr p) r
      pure (r, memo')
partial_fixpoint

/-- `rebuild` on each member of a list. -/
def rebuildAll (leaf : P → V → M P) : Tb P P → List P → M (List P × Tb P P)
  | memo, [] => pure ([], memo)
  | memo, p :: ps => do
    let r ← rebuild leaf memo p
    let rs ← rebuildAll leaf r.2 ps
    pure (r.1 :: rs.1, rs.2)

/-- `rebuild` on the terms of a span, with one memo. -/
def rebuildSpan (leaf : P → V → M P) (s : MSpan P) : M (MSpan P) := do
  let l ← rebuild leaf Base.empty s.l
  let r ← rebuild leaf l.2 s.r
  let c ← rebuildAll leaf r.2 s.c
  pure ⟨l.1, r.1, c.1⟩

/-- Renumber a variable into the left half. -/
def leafL (_ : P) (v : V) : M P := do
  let w ← Base.inl P v
  Base.alloc (.var w)

/-- Renumber a variable into the right half. -/
def leafR (_ : P) (v : V) : M P := do
  let w ← Base.inr P v
  Base.alloc (.var w)

/-- Replace the variable `x` by the term at `u`; another variable stays the
node it is. -/
def leafSub (x : V) (u : P) (p : P) (v : V) : M P := do
  let e ← Base.eqV P v x
  pure (if e then u else p)

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
def substPairs (x : V) (u : P) : Tb P P → List (P × P) → M (List (P × P) × Tb P P)
  | memo, [] => pure ([], memo)
  | memo, e :: E => do
    let l ← rebuild (leafSub x u) memo e.1
    let r ← rebuild (leafSub x u) l.2 e.2
    let rs ← substPairs x u r.2 E
    pure ((l.1, r.1) :: rs.1, rs.2)

/-- Solve the equations, as `solve` does: the variables eliminated and what
each was replaced by, in order, or `none` when there is no solution. -/
def msolve (E : List (P × P)) : M (Option (List (V × P))) := do
  match E with
  | [] => pure (some [])
  | e :: E => do
    let a ← act e.1 e.2
    match a with
    | .skip => msolve E
    | .fail => pure none
    | .split a c b d => msolve ((a, c) :: (b, d) :: E)
    | .elim x u => do
      let s ← substPairs x u Base.empty E
      let r ← msolve s.1
      pure (r.map ((x, u) :: ·))
partial_fixpoint

/-- Apply the eliminations, in order, to a span. -/
def applyAll : List (V × P) → MSpan P → M (MSpan P)
  | [], s => pure s
  | b :: bs, s => do
    let r ← rebuildSpan (leafSub b.1 b.2) s
    applyAll bs r

/-- Solve `E` and apply the solution to `out`. -/
def solveInto (E : List (P × P)) (out : MSpan P) : M (Option (MSpan P)) := do
  let r ← msolve E
  match r with
  | none => pure none
  | some bs => do
    let s ← applyAll bs out
    pure (some s)

/-- Sequential composition: match the right of `x` against the left of `y`. -/
def compose (x y : MSpan P) : M (Option (MSpan P)) := do
  let a ← rebuildSpan leafL x
  let b ← rebuildSpan leafR y
  solveInto [(a.r, b.l)] ⟨a.l, b.r, a.c ++ b.c⟩

/-- Conjunction: match both sides. -/
def meet (x y : MSpan P) : M (Option (MSpan P)) := do
  let a ← rebuildSpan leafL x
  let b ← rebuildSpan leafR y
  solveInto [(a.l, b.l), (a.r, b.r)] ⟨a.l, a.r, a.c ++ b.c⟩

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

/-- Are the two spans the same, as written? -/
def eq (x y : MSpan P) : M Bool := sameAll (x.l :: x.r :: x.c) (y.l :: y.r :: y.c)

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

/-- `patCmp`. -/
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

/-- `listCmp patCmp`. -/
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
def spanCmp (x y : MSpan P) : M Ordering :=
  pcmpAll (x.l :: x.r :: x.c) (y.l :: y.r :: y.c)

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

/-- One-way matching of the term at `p` onto the term at `t`. `θ` holds what each variable of the pattern is bound to, and `memo`
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
  let m₁ ← mmatch a.l s.l Base.empty Base.empty
  match m₁ with
  | none => pure false
  | some s₁ => do
    let m₂ ← mmatch a.r s.r s₁.1 s₁.2
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
