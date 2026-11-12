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

A constraint is a term (its head symbol names the constraint). A store is a
finite set of constraints; in syntax it is written as a list, and its meaning
only depends on which constraints occur in it. -/

abbrev Store := List Pat

/-- A rule body: `fail`, or equations together with a (possibly empty)
conjunction of constraints. The body with neither is the drop body `.`.
Equations are not constraints and never enter a store: on a ground store an
equation is a test, and on a non-ground span it instantiates the span. -/
inductive Body where
  | fail
  | conj (eqs : List (Pat × Pat)) (cs : List Pat)
  deriving DecidableEq, Repr

/-- A refutation rule `h₁, …, hₙ <=> body`. Rules fire by matching their heads
against distinct constraints of the store. -/
structure TRule where
  heads : List Pat
  body : Body
  deriving DecidableEq, Repr

abbrev Theory := List TRule

/-! ### Terminating theories

The semantics requires every theory to terminate. A rule is well formed
only if it passes the following decidable check, which guarantees
termination of rule firing on every store, ground or not.

`Pat.smaller u t` is the substitution-stable strict order: `u` is smaller than
`t` and no variable occurs more often in `u` than in `t`, so `uθ` is smaller
than `tθ` for every substitution `θ`. A rule is decreasing when its body is
smaller than its heads in the multiset extension of that order
(Dershowitz–Manna): after cancelling atoms that occur in both, some head is
left, and every remaining body atom is smaller than some remaining head. -/

def Pat.smaller (u t : Pat) : Bool :=
  decide (u.size < t.size) && u.vars.all fun v => decide (u.vars.count v ≤ t.vars.count v)

def TRule.Decreasing (ρ : TRule) : Bool :=
  match ρ.body with
  | .fail => true
  | .conj _ cs =>
    let B := cs.diff ρ.heads
    let H := ρ.heads.diff cs
    !H.isEmpty && B.all fun b => H.any fun h => Pat.smaller b h


/-- The constraints a body adds. -/
def Body.atoms : Body → List Pat
  | .fail => []
  | .conj _ cs => cs

/-- The equations of a body. -/
def Body.eqs : Body → List (Pat × Pat)
  | .fail => []
  | .conj eqs _ => eqs

/-- A rule is well formed when it has a head, every variable of its body
(constraints and equations) occurs in its heads, and it is decreasing. A rule fires by matching its
heads, so a body variable not bound by them would have no value; reading it
existentially would let a rule refute through a value it chose itself, which
is not what the rule says. Decreasing rules make rule firing terminate. -/
def TRule.WellFormed (ρ : TRule) : Prop :=
  ρ.heads ≠ [] ∧ (∀ c ∈ ρ.body.atoms, ∀ v ∈ c.vars, ∃ h ∈ ρ.heads, v ∈ h.vars) ∧
    (∀ e ∈ ρ.body.eqs, ∀ v ∈ e.1.vars ++ e.2.vars, ∃ h ∈ ρ.heads, v ∈ h.vars) ∧
    ρ.Decreasing = true

instance (ρ : TRule) : Decidable ρ.WellFormed := by
  unfold TRule.WellFormed; infer_instance

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

end Span

/-! ## Relations -/

inductive Rel where
  | zero
  | span (s : Span)
  | or (a b : Rel)
  | and (a b : Rel)
  | seq (a b : Rel)
  | conv (a : Rel)
  | call (n : Name)
  deriving DecidableEq, Repr

namespace Rel

/-- The span `l {c} -> r`. -/
def rw (l r : Pat) (c : Store := []) : Rel := span ⟨l, r, c⟩

/-- `@t`, the identity at `t`. -/
def at_ (t : Pat) : Rel := rw t t

/-- Names called by an expression. -/
def calls : Rel → List Name
  | zero => []
  | span _ => []
  | or a b => calls a ++ calls b
  | and a b => calls a ++ calls b
  | seq a b => calls a ++ calls b
  | conv a => calls a
  | call n => [n]

def CallFree (e : Rel) : Prop := e.calls = []

/-- The mirror image of an expression: every span is swapped and every
sequence is reversed. It denotes the converse (`denote_dual`), with calls
read in the mirrored program `Program.dual`. -/
def dual : Rel → Rel
  | zero => zero
  | span s => span s.swap
  | or a b => or a.dual b.dual
  | and a b => and a.dual b.dual
  | seq a b => seq b.dual a.dual
  | conv a => conv a.dual
  | call n => call n

instance (e : Rel) : Decidable e.CallFree := inferInstanceAs (Decidable (_ = _))

end Rel

/-! ## Programs -/

structure Program where
  defs : List (Name × Rel)
  theory : Theory

namespace Program

/-- The body of a definition. Well-formed programs never call an undefined
name, so the default is never observed by them. -/
def body (P : Program) (n : Name) : Rel := ((P.defs.lookup n)).getD .zero

/-- A program is well formed when its names are distinct, every called
name, in a body or in the query, is defined, and every rule of its theory is
well formed. -/
def WellFormed (P : Program) (q : Rel) : Prop :=
  (P.defs.map Prod.fst).Nodup ∧
  (∀ n ∈ q.calls ++ (P.defs.flatMap fun d => d.2.calls), n ∈ P.defs.map Prod.fst) ∧
  ∀ ρ ∈ P.theory, ρ.WellFormed

instance (P : Program) (q : Rel) : Decidable (P.WellFormed q) := by
  unfold WellFormed; infer_instance

/-- The mirrored program: every body is mirrored, and the theory is
unchanged. -/
def dual (P : Program) : Program :=
  { P with defs := P.defs.map fun d => (d.1, d.2.dual) }

end Program

end RwLog
