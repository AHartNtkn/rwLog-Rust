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
| `Tests/` `R005Runs`, `DirectedRuns`, `MiddleRuns` | runs and measurements of the above |

Still built: the specification, `Kernel/`, `SpanLayer/`, `Lib/`,
`Rungs/Naive/`, `Rungs/Tabled/Base/` (the tabled machine as a plain
`Runtime`), and the rest of `Rungs/Framework/`.

A file leaves this list when it is ported and imported again, or is deleted
because the port did not need it. The list must be empty when M4 is declared
done (roadmap L46).
