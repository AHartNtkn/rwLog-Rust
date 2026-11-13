# Files out of the build

The kernel and the cost monad were restated on 2026-11-13 (roadmap L30 first
part, L31, L44): an engine is now written against a `DerivationKernel`, its
states are over spans, nodes of the normal form and answers, and `Cost` has a
space component. The files below were written against the kernel as it stood
before (`Kernel S M` with `size`, `idSpan`, `eqRel` and `canon`, engines over
expressions, answers that are bare spans). They are not imported by
`RwLog.lean`, are not built, and are not repaired. They are kept as the text
the proofs of the port of R005 start from (roadmap M3 part B and M4). At the tag `epoch-1`
all of them build.

| Files | What they are |
|---|---|
| `RwLog/Rungs/Tabled/` `Exact`, `Repeats`, `Direction` | theorems of epoch 1 about the tabled machine in the old cost monad |
| `RwLog/Rungs/Mirror/` `Direction`, `Bounds`, `Keeps`, `Trace` | theorems of epoch 1 about the mirrored machine |

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

R005's machine was ported on 2026-11-13 (roadmap L04): `Rungs/Tabled/`
`Machine` and `Unfold`, `Rungs/Mirror/Machine`, `Rungs/R005/Engine`,
`Framework/` `Race` and `RaceWinner`, and `Tests/R005Runs` are rewritten
against the derivation kernel and are built. The files the rewrite replaced
(`Gen` and `Reading` of both machines, the rest of `Rungs/R005/`,
`Rungs/Directed/`, `Rungs/Hedge/`, and their tests) are deleted and exist at
the tag. The files listed above are proofs; each is deleted when the property
it proves is re-established for the new text or found not to be needed.

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
