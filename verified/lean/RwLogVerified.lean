/-
# Rust code of the engine, translated by Aeneas and proved against the specification

* `RwlogCore` (generated, not edited): `verified/rust/src` as Lean functions.
* `RwLogVerified.Digits`, `RwLogVerified.TrieModel`: the keys of nodes and the
  trie that finds a node by its key, as a list.
* `RwLogVerified.Store`: the invariant of the Rust store; each primitive
  keeps it, does what it says, and costs one tick.
* `RwLogVerified.Repr`: an identifier stands for a specification term.
* `RwLogVerified.Walk`: what the frames on the stack of a loop over a term
  stand for.
* `RwLogVerified.Rebuild`, `Occurs`: applying a binding to a term and the
  occurs check, each once per distinct subterm.
* `RwLogVerified.SolveCost`, `Solve`: the unifier `solve_into` returns what
  `RwLog.Eqns.solveOn` returns, within the number of variables times the distinct subterms and equations.
* `RwLogVerified.SpanSpec`, `Compose`: `compose` and `meet` of spans.
* `RwLogVerified.Chain`: the test that a chain of spans composes.
* `RwLogVerified.MatchSpec`, `Cover`: one-way matching, coverage when the
  covering span has no constraints, and equality of spans.
* `RwLogVerified.Iface`: the interfaces of a span as boundaries.
* `RwLogVerified.Sorts`: the declarations of sorts as lists of the store, one
  step of a sort on a term, and membership of a ground term.
* `RwLogVerified.Conj`: conjunctions of sorts as lists of the store, one
  identifier for one set, and one step of a conjunction.
* `RwLogVerified.Names`: the list of every name of the declarations.
* `RwLogVerified.Live`: whether a conjunction of sorts has a member, by
  going through the conjunctions it reaches.
* `RwLogVerified.Count`: how many members a conjunction of sorts has, with
  the member when there is one.
* `RwLogVerified.Incl`: whether every member of a conjunction of sorts is in
  a sort, by going through the keys the pair of the two reaches.
* `RwLogVerified.But`, `RwLogVerified.ButLoop`, `RwLogVerified.ButLink`:
  whether every member of a conjunction of sorts, but for finitely many
  ground terms, is in a sort: the functions, the loop of asks, and the link
  to the specification with the bound of the charge.
* `RwLogVerified.Push`: the sorts the variables of a pattern must be in for
  an instance of it to be in a sort.
* `RwLogVerified.Sole`: the one root of the members of a conjunction of sorts
  that are not among finitely many ground terms.
* `RwLogVerified.Gone`: the ground terms the exclusions of a store exclude a
  variable from.
* `RwLogVerified.Open`: the variable after a variable; replacing the variables
  whose sorts have one member by that member; replacing a variable by a
  symbol applied to new variables.
* `RwLogVerified.Tighten`: whether an exclusion always holds, of one and of
  a list; the first variable whose values have one root.
* `RwLogVerified.TightRun`: the rounds of tightening as a function of the
  pattern, the exclusions and the entries; that they end, and that what they
  come to is reached by replacements of the specification.
* `RwLogVerified.Tight`: tightening a store, within the charge of its rounds.
* `RwLogVerified.Number`: the variables of a pattern in the order they
  first occur; the sorts that hold of all values of a variable; a store with
  its variables numbered in that order.
* `RwLogVerified.Solved`: the normal form of an exclusion: the variables of
  a numbered store; aliases turned to their first variable; the sorts of
  the variables pushed onto their values; the free variables left with one
  value bound to it.
* `RwLogVerified.Assemble`: the exclusions of a normal store: whether one
  solved exclusion is an instance of another; the solved forms of a list;
  the ones that are instances of no other.
* `RwLogVerified.Prune`: a store without its hidden variables: the solved
  form of an exclusion, the exclusions whose solved forms are over the
  variables of the pattern, and the entries of these variables.
* `RwLogVerified.Normal`: the normal store of a problem: the store a problem
  starts from (equations solved, variables numbered, sorts pushed down to
  the variables), and the whole function: the variables with one value
  replaced, the hidden ones dropped, the rest tightened and numbered.
* `RwLogVerified.Dom`: the operations of the sorts domain on normal stores:
  the representative of a pair of patterns over the solutions of one,
  composition, conjunction, the right bound, the converse, whether a
  representative relates each term to itself only, and whether one covers
  another.
* `RwLogVerified.SpanRep`: the representative of a span as written:
  whether a term is first-order, what each constraint says, and the normal
  store of the two sides under the sorts and the disequalities.
* `RwLogVerified.Kernel`: the kernel rung whose charges are those bounds.
* `RwLogVerified.KernelRuns`: its charges on a worked composition.

Every theorem says the Rust function does not panic, returns the
specification's result, and advances the store's tick counter by at most a
stated amount.
-/
import RwLogVerified.Digits
import RwLogVerified.TrieModel
import RwLogVerified.Store
import RwLogVerified.Repr
import RwLogVerified.Walk
import RwLogVerified.Rebuild
import RwLogVerified.Occurs
import RwLogVerified.SolveCost
import RwLogVerified.Solve
import RwLogVerified.SpanSpec
import RwLogVerified.Compose
import RwLogVerified.Chain
import RwLogVerified.MatchSpec
import RwLogVerified.Cover
import RwLogVerified.Iface
import RwLogVerified.Sorts
import RwLogVerified.Conj
import RwLogVerified.Names
import RwLogVerified.Live
import RwLogVerified.Count
import RwLogVerified.Incl
import RwLogVerified.But
import RwLogVerified.ButLoop
import RwLogVerified.ButLink
import RwLogVerified.Push
import RwLogVerified.Sole
import RwLogVerified.Gone
import RwLogVerified.Open
import RwLogVerified.Tighten
import RwLogVerified.TightRun
import RwLogVerified.Tight
import RwLogVerified.Number
import RwLogVerified.Solved
import RwLogVerified.Assemble
import RwLogVerified.Prune
import RwLogVerified.Normal
import RwLogVerified.Dom
import RwLogVerified.SpanRep
import RwLogVerified.Kernel
import RwLogVerified.KernelRuns
