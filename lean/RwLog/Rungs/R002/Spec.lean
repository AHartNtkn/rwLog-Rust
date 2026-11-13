/-
# Rung R002: what must be proved

As for R001, every property is stated here as a `Prop` in the
`R002.Obligation` namespace and nothing in this file is proved: an obligation
is discharged by a theorem `R002.<name> : Obligation.<name>` in another file,
and `AxiomAudit.lean` lists the discharged ones.

R002 is judged against R001 by cost (`Trusted/Cost.lean`): it must keep every
property of R001, never cost more than a fixed polynomial of what R001 costs,
and cost exponentially less on a family of inputs.

* **Same machine.** The cost given to R001 is the cost of R001
  (`baseline_exact`), both unfolders compute R001's unfolding race exactly
  (`eager_exact`, `onDemand_exact`), and so R002's runtime *is* R001's
  (`runtime_eq`): the same states, the same steps, the same trace. Every
  theorem about `R001.runtime` is then a theorem about `R002.runtime` by
  rewriting, which is how R002 keeps R001's properties; the three every rung
  must state are stated (`sound`, `complete`, `honest_exhaustion`).
* **Never much worse.** One call of the on-demand unfolder costs at most a
  cubic polynomial of what the eager one costs on the same goal
  (`onDemand_dominated`), and so R002 simulates R001 within an explicit cubic
  polynomial (`simulates`).
* **Exponentially better on a family.** While its root table is open, each
  round of R001 costs at least the number of nodes of the root goal's
  unfolding to the round before (`baseline_lower`), for every program and
  query. On the family `sepFam`, R002 halts within a quartic polynomial of `k`
  while R001 pays at least `2 ^ k` (`separates`). The quartic is the tabled
  machine's own cost on a chain of `k` open tables (the completion check peels
  one table per pass and looks each one up by position); the unfolding race
  no longer contributes more than that.
-/
import RwLog.Rungs.R002.Engine

namespace RwLog

namespace R002

/-- The number of nodes of an expression. -/
def nodes : Rel → Nat
  | .zero => 1
  | .span _ => 1
  | .or a b => 1 + nodes a + nodes b
  | .and a b => 1 + nodes a + nodes b
  | .seq a b => 1 + nodes a + nodes b
  | .conv a => 1 + nodes a
  | .call _ => 1

/-! ### The separating family

`rel w { w | w }` has no answers and its unfolding doubles with every level.
`c0` is `@z` and each `c(i+1)` calls `c(i)`, so the query `c(k) | w` needs
about `k` rounds for the answer `z -> z` to travel up the chain of tables. For
all those rounds the root is open, and R001 rebuilds its unfolding each
round. R002 stops its walk at the first call it meets. -/

def chainName (i : Nat) : Name := "c" ++ toString i

def sepDefs (k : Nat) : List (Name × Rel) :=
  [("w", .or (.call "w") (.call "w")), (chainName 0, .at_ (.sym "z"))] ++
    (List.range k).map fun i => (chainName (i + 1), .call (chainName i))

def sepFam (k : Nat) : Program × Rel :=
  (⟨sepDefs k, []⟩, .or (.call (chainName k)) (.call "w"))

namespace Obligation

/-! ### Same machine -/

/-- The eager unfolder computes R001's unfolding race. -/
def eager_exact : Prop :=
  ∀ P d g, (eager P d g).val = (R001.unfoldFinal P d g, R001.unfoldAnswers P d g)

/-- The on-demand unfolder computes R001's unfolding race: the same verdict
and the same list of the same spans. -/
def onDemand_exact : Prop :=
  ∀ P d g, (onDemand P d g).val = (R001.unfoldFinal P d g, R001.unfoldAnswers P d g)

/-- The costed baseline is R001: forgetting its ticks gives R001's runtime. -/
def baseline_exact : Prop := baseline.runtime = R001.runtime

/-- R002's runtime is R001's. -/
def runtime_eq : Prop := runtime = R001.runtime

/-- P0.1 to P0.3 for R002. -/
def sound : Prop := runtime.Sound
def complete : Prop := runtime.Complete
def honest_exhaustion : Prop := runtime.HonestExhaustion

/-! ### Never much worse -/

/-- One call of the on-demand unfolder costs at most a cubic polynomial of
what the eager one costs on the same goal at the same depth, and of the sizes
of the program and the goal. -/
def onDemand_dominated : Prop :=
  ∀ P d g, (onDemand P d g).ticks ≤ 4 * ((eager P d g).ticks + P.size + goalSize g + 1) ^ 3

/-- R002 simulates R001 within `5 c³ (n + 2)³`, where `c` is what R001 has
paid and `n` the size of the program and the query. -/
def simulates : Prop := Simulates baseline costed fun c n => 5 * c ^ 3 * (n + 2) ^ 3

/-! ### Exponentially better on a family -/

/-- While the root table is open, a round of R001 costs at least the number
of nodes of the root goal's unfolding to any earlier depth. -/
def baseline_lower : Prop :=
  ∀ (st : R001.State) (t : R001.Table), st.tables.head? = some t → t.done = false →
    ∀ i, i < st.depth → nodes (R000.unfoldN st.P i t.goal.rel) ≤ (baseline.step st).ticks

/-- On `sepFam k`, R002 halts within `500 (k + 1)⁴` ticks, and R001 has paid
at least `2 ^ k` whenever it has halted. -/
def separates : Prop := Separates baseline costed sepFam (fun k => 2 ^ k) fun k => 500 * (k + 1) ^ 4

end Obligation

end R002

end RwLog
