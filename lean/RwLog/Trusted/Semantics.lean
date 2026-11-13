/-
# Ground semantics (the specification)

## Constraints

An *interpretation* `M` is a set of ground constraints: the ones taken to
hold. The sorts of a program fix one interpretation, `Sorts.interp`:

* `(s t)` holds exactly when the ground term `t` belongs to the sort `s`
  (`Sorts.Mem`, read off the declaration of `s`; a name with no declaration
  is the empty sort);
* `(!= t u)` holds exactly when `t` and `u` are different terms;
* no other constraint holds.

The sorts of a well-formed program are such that finitely many of them have
no term in common, or one, or infinitely many (`Sorts.WellFormed`).

The spans of a well-formed program are first-order (`Span.firstOrder`): no
variable is applied to an argument, and no constraint is a variable. The
surface syntax writes no other span. The meaning below is given for every
span; a constraint domain is held to spans that are first-order
(`Trusted/Domain.lean`).

There are no rules and no models: the sorts of a program are sets of ground
terms, and nothing else is said about constraints.

## Relations

In an interpretation, an expression denotes a set of pairs of ground terms.
A span `l {c} -> r` relates `lσ` to `rσ` when every constraint of `cσ` holds:
one substitution produces both sides and satisfies the sorts and the
disequalities of the store. Union, intersection, composition and converse
are the usual ones, and recursion is the least fixpoint. The meaning of an
expression in a program (`ProgramOf.pairs`) is its denotation in the
interpretation of the program's sorts.

The denotation is stated for any interpretation because an answer of a
machine need not be a span (`Trusted/Runtime.lean`): what an answer relates
is asked given which constraints hold.
-/
import RwLog.Trusted.Syntax
import Mathlib.Order.FixedPoints
import Mathlib.Data.Set.Finite.Basic

namespace RwLog

/-! ## Interpretations and sorts -/

/-- An interpretation: the ground constraints that hold. -/
abbrev Interp := Set GTerm

/-- The case of a sort that reads a term with head `f` and `n` arguments: the
sorts named for the arguments. -/
def SortDef.caseOf (d : SortDef) (f : Sym) (n : Nat) : Option (List (Option Name)) :=
  (d.cases.find? fun c => c.1 = f ∧ c.2.length = n).map Prod.snd

/-- The ground term belongs to the sort of that name. -/
inductive Sorts.Mem (S : Sorts) : Name → GTerm → Prop
  /-- A case reads the term, and each argument belongs to the sort named for
  it. -/
  | case {n : Name} {d : SortDef} {t : GTerm} {f : Sym} {ts : List GTerm}
      {as : List (Option Name)} :
      S.lookup n = some d → t.spine = some (f, ts) → d.caseOf f ts.length = some as →
      (∀ (i : Nat) (m : Name) (u : GTerm), as[i]? = some (some m) → ts[i]? = some u → Mem S m u) →
      Mem S n t
  /-- No case reads the term, the sort has every other term but the listed
  ones, and each argument belongs to the sort named for the arguments. -/
  | rest {n : Name} {d : SortDef} {t : GTerm} {f : Sym} {ts : List GTerm} {ex : List (Sym × Nat)}
      {a : Option Name} :
      S.lookup n = some d → t.spine = some (f, ts) → d.caseOf f ts.length = none →
      d.rest = some (ex, a) → (f, ts.length) ∉ ex →
      (∀ (m : Name) (u : GTerm), a = some m → u ∈ ts → Mem S m u) → Mem S n t

/-- The ground constraint holds under the sorts. -/
def Sorts.Holds (S : Sorts) : GTerm → Prop
  | .app (.sym s) t => S.Mem s t
  | .app (.app (.sym f) t) u => f = neSym ∧ t ≠ u
  | _ => False

/-- The interpretation the sorts fix: the constraints that hold. -/
def Sorts.interp (S : Sorts) : Interp := {a | S.Holds a}

/-- The sorts are well formed: the terms that belong to all of finitely many
sorts are none, one, or infinitely many. A finite choice is written as a
union of relations and not as a sort, so a variable of a store that is not
bound has infinitely many values. -/
def Sorts.WellFormed (S : Sorts) : Prop :=
  ∀ ns : List Name, {t : GTerm | ∀ n ∈ ns, S.Mem n t} = ∅ ∨
    (∃ t, {t : GTerm | ∀ n ∈ ns, S.Mem n t} = {t}) ∨ {t : GTerm | ∀ n ∈ ns, S.Mem n t}.Infinite

/-! ## Relations in one interpretation -/

/-- A relation between ground terms. -/
abbrev PRel := Set (GTerm × GTerm)

namespace PRel

def comp (R S : PRel) : PRel := {p | ∃ m, (p.1, m) ∈ R ∧ (m, p.2) ∈ S}

def inv (R : PRel) : PRel := {p | (p.2, p.1) ∈ R}

end PRel

/-- The pairs a span relates in `M`. -/
def Span.denAt (M : Interp) (s : Span) : PRel :=
  {p | ∃ σ : Nat → GTerm, p.1 = s.l.bind σ ∧ p.2 = s.r.bind σ ∧ ∀ c ∈ s.c, c.bind σ ∈ M}

/-- Denotation of an expression in `M`, given the meaning `ρ` of each name. -/
def denoteAt (M : Interp) (ρ : Name → PRel) : Rel → PRel
  | .zero => ∅
  | .span s => s.denAt M
  | .or a b => denoteAt M ρ a ∪ denoteAt M ρ b
  | .and a b => denoteAt M ρ a ∩ denoteAt M ρ b
  | .seq a b => (denoteAt M ρ a).comp (denoteAt M ρ b)
  | .conv a => (denoteAt M ρ a).inv
  | .call n => ρ n

theorem denoteAt_mono (M : Interp) {ρ ρ' : Name → PRel} (h : ρ ≤ ρ') :
    ∀ e, denoteAt M ρ e ⊆ denoteAt M ρ' e
  | .zero => le_rfl
  | .span _ => le_rfl
  | .or a b => Set.union_subset_union (denoteAt_mono M h a) (denoteAt_mono M h b)
  | .and a b => Set.inter_subset_inter (denoteAt_mono M h a) (denoteAt_mono M h b)
  | .seq a b => fun _ ⟨m, h1, h2⟩ => ⟨m, denoteAt_mono M h a h1, denoteAt_mono M h b h2⟩
  | .conv a => fun _ hp => denoteAt_mono M h a hp
  | .call n => h n

/-- One unfolding of every definition of the program, in `M`. -/
def ProgramOf.stepAt (P : Program) (M : Interp) : (Name → PRel) →o (Name → PRel) where
  toFun ρ n := denoteAt M ρ (P.body n)
  monotone' _ _ h n := denoteAt_mono M h (P.body n)

/-- The meaning of every name in `M`: the least fixpoint. -/
def ProgramOf.meaningAt (P : Program) (M : Interp) : Name → PRel := OrderHom.lfp (P.stepAt M)

/-- The meaning of an expression in a program, in `M`. -/
def ProgramOf.semAt (P : Program) (M : Interp) (e : Rel) : PRel := denoteAt M (P.meaningAt M) e

theorem ProgramOf.meaningAt_eq (P : Program) (M : Interp) (n : Name) :
    P.meaningAt M n = denoteAt M (P.meaningAt M) (P.body n) := by
  have := OrderHom.map_lfp (P.stepAt M)
  exact (congrFun this n).symm

/-- A program is well formed when its names are distinct, every called name,
in a body or in the query, is defined, its sorts are well formed, and every
span, in a body or in the query, is first-order. -/
def ProgramOf.WellFormed (P : Program) (q : Rel) : Prop :=
  (P.defs.map Prod.fst).Nodup ∧
  (∀ n ∈ q.calls ++ (P.defs.flatMap fun d => d.2.calls), n ∈ P.defs.map Prod.fst) ∧
  P.sorts.WellFormed ∧
  ∀ s ∈ q.spans ++ (P.defs.flatMap fun d => d.2.spans), s.firstOrder = true

/-- The meaning of an expression in a program: its pairs in the
interpretation of the program's sorts. -/
def ProgramOf.pairs (P : Program) (e : Rel) : PRel := P.semAt P.sorts.interp e

end RwLog
