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

Split the file by mathematical role while retaining
`NumStability.Analysis.NonrandomRounding` as a compatibility umbrella:

1. `Core` — rational/Horner definitions and abstract local-error traces.
2. `SourceInterval` — finite-normal and interval propagation results.
3. `GridVariation` — the exact reference curve and variation bounds.
4. `StoredGrid` — concrete IEEE-double numerator and denominator certificates.
5. `Conclusions` — the final error-spread and nonrandomness endpoints.

The reusable analytic layers must not import the concrete stored-grid
certificate. This improves import precision and isolates expensive edits. A
split alone is not expected to reduce the sum of clean elaboration times: the
large exact certificates and four long interval proofs remain genuine work.
Further proof refactoring should extract reusable interval-propagation lemmas
and should be accepted only after a second profile shows a reduction.

## Implemented result

The compatibility module now re-exports five compiled layers:

| Layer | Lines | Initial build result |
| --- | ---: | ---: |
| `Core` | 526 | pass (18 s) |
| `SourceInterval` | 972 | pass (328 s) |
| `GridVariation` | 622 | pass (33 s) |
| `StoredGrid` | 1,755 | pass (37 s) |
| `Conclusions` | 115 | pass (24 s) |

These first-build times were observed while a disjoint clean-cache Chapter 9
build was also running, so they are validation evidence rather than a controlled
before/after benchmark. They nevertheless localize the dominant cost in the
four interval-propagation proofs: the concrete stored-grid certificate is not
the principal bottleneck once the layers are measured separately. The next
proof-engineering pilot should therefore target reusable interval propagation,
not further pathname splitting.
