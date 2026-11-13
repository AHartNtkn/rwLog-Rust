# Files out of the build

The kernel and the cost monad were restated on 2026-11-13 (roadmap L30 first
part, L31, L44): an engine is now written against a `DerivationKernel`, its
states are over spans, nodes of the normal form and answers, and `Cost` has a
space component. The files below were written against the kernel as it stood
before (`Kernel S M` with `size`, `idSpan`, `eqRel` and `canon`, engines over
expressions, answers that are bare spans). They are not imported by
`RwLog.lean`, are not built, and are not repaired. They are kept as the text
the port of R005 starts from (roadmap M3 part B and M4). At the tag `epoch-1`
all of them build.

| Files | What they are |
|---|---|
| `RwLog/Rungs/Tabled/` `Gen`, `Reading`, `Exact`, `Repeats`, `Direction`, `Machine` | the tabled machine against the old kernel and in the old cost monad |
| `RwLog/Rungs/R005/` (all) | the top rung of epoch 1 and the unfolders it races |
| `RwLog/Rungs/Mirror/` (all) | the mirrored machine |
| `RwLog/Rungs/Directed/` (all) | goal-directed tables |
| `RwLog/Rungs/Hedge/` (all) | two machines side by side |
| `RwLog/Rungs/Framework/` `Race`, `RaceWinner` | what `Cost.race` returns and spends, in ticks only; to be restated with the space component when the port needs them |
| `Tests/` `R005Runs`, `DirectedRuns`, `MiddleRuns`, `SimulationRuns` | runs and measurements of the above (`SimulationRuns` was added while parked; it checks at `326b608`, and holds what R005 pays on the inputs of `SYMMETRIC_ENGINE_SIMULATION.md`) |

The runtime and its kept properties were restated on the same day (roadmap
L28, L35, L38, L40): a runtime has its own type of answers with a denotation,
a step has a third output (a progress certificate), and a machine that is
done gives a final report. The files below define or reason about a machine
with the two-output step and no final report. They are out of the build for
the same reason and on the same terms.

| Files | What they are |
|---|---|
| `RwLog/Rungs/Naive/` `Engine`, `Correct`, `Properties` | the naive machine (R000 of epoch 1) as a `Runtime`, and its theorems |
| `RwLog/Rungs/Tabled/Base/` (all: `Engine`, `Spec`, `Proofs/`) | the tabled machine (R001 of epoch 1) as a `Runtime`, and its theorems |
| `Tests/` `NaiveRuns`, `TabledRuns` | runs of the two on the conformance cases |

Still built: the specification, `Kernel/`, `SpanLayer/`, `Lib/`,
`Rungs/Naive/` `Chain`, `Normalize`, `NormalizeCorrect` and `Unfold`
(normalisation and unfolding, which mention no machine), and the rest of
`Rungs/Framework/`. No machine is in the build until R005 is ported.

The trusted statements were restated on 2026-11-13 for sorts (roadmap L48,
L51): rules, theories and models are gone, an engine handles representatives
of a constraint domain, and the kernel has no simplification. `Theory/`,
`Conformance/`, and `Kernel/` `Refute`, `RefuteCorrect`, `SimplifyMono`,
`Live` and `ExactCover` are deleted from master and exist at the tag. The
parked files above use them, so the port restates what it needs against
`Trusted/Domain.lean`.

A file leaves this list when it is ported and imported again, or is deleted
because the port did not need it. The list must be empty when M4 is declared
done (roadmap L46).
