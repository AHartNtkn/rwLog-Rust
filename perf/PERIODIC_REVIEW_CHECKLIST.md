# Periodic Corpus Review Checklist

Run this review monthly, and before major optimization pushes.

## Coverage Health

- [ ] Each workload category still has representative quick and stress cases.
- [ ] Realistic workloads are present where required by policy.
- [ ] New feature areas are covered by at least one corpus case.

## Signal Quality

- [ ] Cases with high variance are identified.
- [ ] Noisy cases are tuned, replaced, or moved out of quick gate.
- [ ] Gate thresholds still separate normal variance from regressions.

## Runtime Cost

- [ ] Quick tier runtime remains practical for CI.
- [ ] Stress tier runtime remains suitable for nightly runs.
- [ ] Case count growth is intentional and justified.

## Tooling Integrity

- [ ] `perf_corpus_sanity --lint` passes with no policy drift.
- [ ] `perf_corpus_gate` still gates all quick cases.
- [ ] Baseline refresh cadence was followed.

## Outcome

- [ ] Record review date, reviewer, and actions taken.
- [ ] Open follow-up issues for deferred cleanup work.
