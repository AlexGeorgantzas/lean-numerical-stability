# `NonrandomRounding` profile and split decision

## Baseline

The pre-split module was profiled on 2026-07-22 with the repository's pinned
Lean toolchain:

```console
lake env lean --profile NumStability/Analysis/NonrandomRounding.lean
```

The profiled run took 181.676 seconds wall-clock time. Profiling itself adds
substantial overhead, so this number must not be compared directly with the
cached Lake timing in the older repository report. The cumulative profile is
still useful for identifying the kind of work responsible for the outlier:

| Profile category | Cumulative time |
| --- | ---: |
| tactic interpretation | 164 s |
| `norm_num` | 113 s |
| typeclass inference | 80.1 s |
| tactic execution | 38.3 s |
| linting | 37.3 s |
| metavariable instantiation | 30.7 s |
| expression sharing | 17.2 s |
| `ring` | 13.7 s |
| type checking | 8.02 s |
| imports | 7.36 s |

Individual concrete trace declarations accounted for blocks of up to 20
seconds in metavariable instantiation and 24.9 seconds in linting. The module
contains 377 `norm_num` invocations and 151 `linarith` invocations. Its cost is
therefore dominated by large exact-arithmetic certificates, not by its eight
direct imports or its roughly four thousand source lines.

The complete raw profiler output is deliberately left under the ignored
`benchmark-results/` directory. It is machine- and profiler-dependent and is
not a stable versioned artifact.

## Decision

The initial performance split established a one-way chain of five compiled
layers. The subsequent architecture review classified the complete family as
source correspondence for Higham Section 1.17, not reusable analysis. Its
canonical ownership is therefore:

1. `HornerEvaluation` — rational/Horner definitions and abstract local-error
   traces.
2. `SourceInterval` — finite-normal and interval-propagation results.
3. `GridVariation` — the exact reference curve and variation bounds.
4. `StoredGrid` — concrete IEEE-double numerator and denominator certificates.
5. `ErrorSpread` — the final error-spread and nonrandomness endpoints.

The dependency chain remains one-way, so narrower imports continue to isolate
expensive edits. No leaf is classified reusable merely because some of its
lemmas are abstract: every declaration in this batch supports the particular
Kahan example and its Higham source correspondence. Any later extraction of
generic interval-propagation theory requires a separate API review and profile.

## Implemented result

The two canonical aggregates are declaration-free and complete. All six old
paths remain exact import-only compatibility wrappers:

| Historical path | Canonical path |
| --- | --- |
| `NumStability.Analysis.NonrandomRounding` | `NumStability.Source.Higham.Chapter01.Section17` |
| `NumStability.Analysis.NonrandomRounding.Core` | `NumStability.Source.Higham.Chapter01.Section17.HornerEvaluation` |
| `NumStability.Analysis.NonrandomRounding.SourceInterval` | `NumStability.Source.Higham.Chapter01.Section17.SourceInterval` |
| `NumStability.Analysis.NonrandomRounding.GridVariation` | `NumStability.Source.Higham.Chapter01.Section17.GridVariation` |
| `NumStability.Analysis.NonrandomRounding.StoredGrid` | `NumStability.Source.Higham.Chapter01.Section17.StoredGrid` |
| `NumStability.Analysis.NonrandomRounding.Conclusions` | `NumStability.Source.Higham.Chapter01.Section17.ErrorSpread` |

The original isolated first-build observations were 18 seconds for `Core`,
328 seconds for `SourceInterval`, 33 seconds for `GridVariation`, 37 seconds
for `StoredGrid`, and 24 seconds for `Conclusions`. They were collected while a
disjoint clean-cache Chapter 9 build was also running, so they are validation
evidence rather than a controlled before/after benchmark. They nevertheless
localize the dominant cost in the interval-propagation proofs: the concrete
stored-grid certificate is not the principal bottleneck. The next performance
pilot should target reusable interval-propagation proof techniques, not further
pathname splitting.
