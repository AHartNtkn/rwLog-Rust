/-
# rwLog core syntax

Terms are finite trees over an open, infinite signature (`Sym := String`).
A surface term `(f t₁ … tₙ)` is represented in curried form
`app (… (app (sym f) t₁) …) tₙ`; an atom `f` is the same term as `(f)`.
`Term.mk` is that encoding, and `Term.mk_inj` shows it is faithful: a symbol
together with its argument list is recovered uniquely, so `(f a)` and
`(f a b)` remain different constructors.

Variables are a type parameter. Patterns use `Nat` variables; ground terms use
`Empty`, so groundness is enforced by the type.
-/
import Mathlib.Data.List.Basic

namespace RwLog

abbrev Sym := String
abbrev Name := String

inductive Term (V : Type) where
  | var : V → Term V
  | sym : Sym → Term V
  | app : Term V → Term V → Term V
  deriving DecidableEq, Repr

abbrev Pat := Term Nat
abbrev GTerm := Term Empty

namespace Term

variable {V W U : Type}

/-- The surface term `(f t₁ … tₙ)`. -/
def mk (f : Sym) (args : List (Term V)) : Term V :=
  args.foldl app (sym f)

/-- Head symbol and arguments of a term whose spine ends in a symbol. -/
def spine : Term V → Option (Sym × List (Term V))
  | var _ => none
  | sym f => some (f, [])
  | app t u => (spine t).map fun p => (p.1, p.2 ++ [u])

theorem spine_foldl (acc : Term V) (args : List (Term V)) :
    spine (args.foldl app acc) = (spine acc).map fun p => (p.1, p.2 ++ args) := by
  induction args generalizing acc with
  | nil => simp
  | cons x xs ih => simp [ih, spine, Option.map_map, Function.comp_def]

theorem spine_mk (f : Sym) (args : List (Term V)) :
    spine (mk f args) = some (f, args) := by
  simp [mk, spine_foldl, spine]

/-- The term is first-order: no variable is applied to an argument, so every
application is a symbol with its arguments. The surface syntax writes no
other term. -/
def firstOrder : Term V → Bool
  | var _ => true
  | sym _ => true
  | app (var _) _ => false
  | app t u => firstOrder t && firstOrder u

/-- The term can be a constraint: it is first-order and is not a variable. -/
def isAtom : Term V → Bool
  | var _ => false
  | t => firstOrder t

/-- The curried encoding of surface terms is faithful. -/
theorem mk_inj {f g : Sym} {xs ys : List (Term V)} (h : mk f xs = mk g ys) :
    f = g ∧ xs = ys := by
  have := congrArg spine h
  simp [spine_mk] at this
  exact this

/-- Parallel substitution. -/
def bind (σ : V → Term W) : Term V → Term W
  | var v => σ v
  | sym f => sym f
  | app t u => app (bind σ t) (bind σ u)

/-- Variable renaming. -/
def rename (f : V → W) : Term V → Term W := bind (fun v => var (f v))

@[simp] theorem bind_var (σ : V → Term W) (v : V) : bind σ (var v) = σ v := rfl
@[simp] theorem bind_sym (σ : V → Term W) (f : Sym) : bind σ (sym f) = sym f := rfl
@[simp] theorem bind_app (σ : V → Term W) (t u : Term V) :
    bind σ (app t u) = app (bind σ t) (bind σ u) := rfl

@[simp] theorem bind_bind (σ : V → Term W) (τ : W → Term U) (t : Term V) :
    bind τ (bind σ t) = bind (fun v => bind τ (σ v)) t := by
  induction t with
  | var v => rfl
  | sym f => rfl
  | app t u iht ihu => simp [iht, ihu]

@[simp] theorem bind_var_id (t : Term V) : bind var t = t := by
  induction t with
  | var v => rfl
  | sym f => rfl
  | app t u iht ihu => simp [iht, ihu]

/-- Variables occurring in a term. -/
def vars : Term V → List V
  | var v => [v]
  | sym _ => []
  | app t u => vars t ++ vars u

theorem bind_congr {σ τ : V → Term W} {t : Term V} (h : ∀ v ∈ vars t, σ v = τ v) :
    bind σ t = bind τ t := by
  induction t with
  | var v => exact h v (by simp [vars])
  | sym f => rfl
  | app t u iht ihu =>
    simp only [bind_app]
    rw [iht (fun v hv => h v (by simp [vars, hv])),
        ihu (fun v hv => h v (by simp [vars, hv]))]

/-- Symbols occurring in a term. -/
def syms : Term V → List Sym
  | var _ => []
  | sym f => [f]
  | app t u => syms t ++ syms u

/-- Rename symbols. -/
def mapSym (π : Sym → Sym) : Term V → Term V
  | var v => var v
  | sym f => sym (π f)
  | app t u => app (mapSym π t) (mapSym π u)

def size : Term V → Nat
  | var _ => 1
  | sym _ => 1
  | app t u => size t + size u + 1

end Term

/-! ## Constraints

A constraint is a term, and a store is a list of constraints. Two shapes of
constraint have a meaning (`Trusted/Semantics.lean`): `(s t)`, which says
that `t` belongs to the sort `s`, and `(!= t u)`, which says that `t` and `u`
are different terms. -/

abbrev Store := List Pat

/-- The symbol of the built-in disequality `(!= t u)`. -/
def neSym : Sym := "!="

/-! ## Sorts

A sort is a set of ground terms, declared by a grammar that is decided by
the head symbol of a term and the number of its arguments.

`cases` lists shapes `(f s₁ … sₙ)`: a term with head `f` and `n` arguments
belongs to the sort when each argument belongs to the sort named for it, and
`none` in place of a name allows any term. The first case with the head and
the number of arguments of the term is the one that is read. A term that no
case reads belongs to the sort only if `rest` is `some (ex, a)`, its head
with its number of arguments is not in `ex`, and each of its arguments
belongs to the sort `a` names (`none` allows any term). So

* `prog = l | (b prog) | (f prog prog)` is the cases `l`, `(b prog)` and
  `(f prog prog)` with `rest := none`;
* `name`, every term that is not `(app _ _)` or `(lam _ _)`, is no case with
  `rest := some ([(app, 2), (lam, 2)], none)`;
* `neut = name | (app neut norm)` is the case `(app neut norm)` with
  `rest := some ([(lam, 2)], none)`;
* `no_c`, every term in which `(c _)` occurs nowhere, is no case with
  `rest := some ([(c, 1)], some no_c)`. -/

structure SortDef where
  cases : List (Sym × List (Option Name))
  rest : Option (List (Sym × Nat) × Option Name)
  deriving DecidableEq, Repr

/-- The sorts a program declares. -/
abbrev Sorts := List (Name × SortDef)

/-! ## Spans

A span `l {c} -> r` carries one constraint store. Stores are not attached to
"rules" or "queries": composing or conjoining two spans combines their
stores. -/

structure Span where
  l : Pat
  r : Pat
  c : Store
  deriving DecidableEq, Repr

namespace Span

/-- The converse span. -/
def swap (s : Span) : Span := ⟨s.r, s.l, s.c⟩

@[simp] theorem swap_swap (s : Span) : s.swap.swap = s := rfl

/-- The span is first-order: its sides are, and each constraint of its store
is first-order and is not a variable. -/
def firstOrder (s : Span) : Bool :=
  s.l.firstOrder && s.r.firstOrder && s.c.all Term.isAtom

end Span

/-! ## Relations

The syntax of expressions does not depend on what a span is, so it is given
for any type of spans. The language is the instance at `Span`; an engine is
written for an arbitrary type of spans, which it can only handle through the
operations of the kernel (`Trusted/Kernel.lean`). -/

inductive RelOf (S : Type) where
  | zero
  | span (s : S)
  | or (a b : RelOf S)
  | and (a b : RelOf S)
  | seq (a b : RelOf S)
  | conv (a : RelOf S)
  | call (n : Name)
  deriving DecidableEq, Repr

/-- The expressions of the language. -/
abbrev Rel := RelOf Span

/-- The spans of an expression. -/
def RelOf.spans {S : Type} : RelOf S → List S
  | .zero => []
  | .span s => [s]
  | .or a b => spans a ++ spans b
  | .and a b => spans a ++ spans b
  | .seq a b => spans a ++ spans b
  | .conv a => spans a
  | .call _ => []

/-- Names called by an expression. -/
def RelOf.calls {S : Type} : RelOf S → List Name
  | .zero => []
  | .span _ => []
  | .or a b => calls a ++ calls b
  | .and a b => calls a ++ calls b
  | .seq a b => calls a ++ calls b
  | .conv a => calls a
  | .call n => [n]

namespace RelOf

/-- The span `l {c} -> r`. -/
def rw (l r : Pat) (c : Store := []) : Rel := .span ⟨l, r, c⟩

/-- `@t`, the identity at `t`. -/
def at_ (t : Pat) : Rel := rw t t

def CallFree (e : Rel) : Prop := e.calls = []

/-- The mirror image of an expression: every span is swapped and every
sequence is reversed. It denotes the converse (`denote_dual`), with calls
read in the mirrored program `ProgramOf.dual`. -/
def dual : Rel → Rel
  | .zero => .zero
  | .span s => .span s.swap
  | .or a b => .or a.dual b.dual
  | .and a b => .and a.dual b.dual
  | .seq a b => .seq b.dual a.dual
  | .conv a => .conv a.dual
  | .call n => .call n

instance (e : Rel) : Decidable e.CallFree := inferInstanceAs (Decidable (_ = _))

end RelOf

/-! ## Programs -/

structure ProgramOf (S : Type) where
  defs : List (Name × RelOf S)
  sorts : Sorts

/-- The programs of the language. -/
abbrev Program := ProgramOf Span

/-- The body of a definition. Well-formed programs never call an undefined
name, so the default is never observed by them. -/
def ProgramOf.body {S : Type} (P : ProgramOf S) (n : Name) : RelOf S :=
  ((P.defs.lookup n)).getD .zero

namespace ProgramOf

/-- The mirrored program: every body is mirrored, and the sorts are
unchanged. -/
def dual (P : Program) : Program :=
  { P with defs := P.defs.map fun d => (d.1, d.2.dual) }

end ProgramOf

end RwLog
