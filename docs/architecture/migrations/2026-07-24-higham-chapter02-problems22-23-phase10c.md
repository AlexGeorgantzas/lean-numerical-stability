# Phase 10C: Higham Chapter 2 Problems 22 and 23

Date: 2026-07-24

Execution base: `db1711c5587f2b15d8a1344911f233b2f20b7233`

This record is the authoritative pre-edit ownership map for the first
Chapter 2 batch in Stage 1. All Git blobs, physical line counts, imports,
declaration populations, consumers, and structural ceilings refer to the
immutable execution base above. The implementation may change module
ownership, imports, documentation, manifests, and tests only. Public
declaration names, namespaces, types, bodies, visibility, and source order
must remain unchanged.

## Scope and numbering correction

The historical files after Problem 2.19 use a one-place offset from the
second-edition printed numbering. Two adjacent APIs therefore need to be
separated by role and assigned to the correct printed locators:

1. historical `Analysis.Problem2_21` formalizes printed Problem 2.22, the
   naive IEEE maximum branch in the presence of NaN; and
2. the current canonical `Source.Higham.Chapter02.Problem22`, reached through
   historical `Analysis.Problem2_22` and `Higham.Chapter02.Problem22`,
   formalizes printed Problem 2.23, Kahan's Heron formula.

The current canonical Problem 22 name is therefore incorrect. This batch
frees that locator for the actual Problem 2.22 API, moves the Heron theorem
surface to canonical Problem 23, and preserves all three historical import
paths.

The IEEE maximum definitions and theorems are source-neutral and belong in a
reusable floating-point API. Canonical `Source.Higham.Chapter02.Problem22`
will be an import-only source locator for that API. The two Heron declarations
are explicitly problem-numbered and remain source material.

The slice is complete only when:

1. every compiled declaration has exactly one canonical owner recorded below;
2. `Analysis.Problem2_21`, `Analysis.Problem2_22`, and
   `Higham.Chapter02.Problem22` are exact one-import wrappers;
3. no production module imports any of those historical paths;
4. the new IEEE and Chapter 2 aggregates are documented, sorted,
   declaration-free complete aggregates;
5. canonical-leaf, source-locator, aggregate-only, and old-only import tests
   pass independently;
6. source and compiled ownership audits preserve both declaration populations
   after normalizing only the changed owner paths and generated private
   prefixes; and
7. the full architecture, compatibility, provenance, test, build,
   LibraryLookup, baseline, and clean-checkout gates pass.

## Immutable source inventory

| Base owner | Git blob | Lines | Explicit declarations | Compiled ownership |
| --- | --- | ---: | ---: | ---: |
| `Analysis.Problem2_21` | `8cb6bf87c3fd510d75e1c967ffa75c5d9350cb5b` | 147 | 1 public definition + 14 public theorems | 15 public + 1 generated internal constant |
| `Source.Higham.Chapter02.Problem22` | `bad9ab8521b1d619dea358ed2346c6e1c6020b8e` | 61 | 2 public theorems | 2 public theorems |
| `Analysis.Problem2_22` | `601aa082b9f488bf4a9c966645a080a9a289d2de` | 7 | 0 | 0; compatibility wrapper |
| `Higham.Chapter02.Problem22` | `fbe426eb8fa29f71db821317f691260154817466` | 8 | 0 | 0; compatibility wrapper |

The two ownership populations total 18 compiled constants: 17 public
constants and one generated internal equation theorem. There are no explicit
private declarations.

### Reusable IEEE maximum population

- `NumStability.ieeeNaiveMax`
- `NumStability.ieeeNaiveMax.eq_1` (generated internal equation theorem)
- `NumStability.ieeeNaiveMax_concrete_nan_counterexample`
- `NumStability.ieeeNaiveMax_eq_left_of_ieeeGt`
- `NumStability.ieeeNaiveMax_eq_right_of_not_ieeeGt`
- `NumStability.ieeeNaiveMax_finite_correct_but_not_nan_propagating`
- `NumStability.ieeeNaiveMax_finite_finite_eq_max`
- `NumStability.ieeeNaiveMax_finite_finite_left_of_lt`
- `NumStability.ieeeNaiveMax_finite_finite_right_of_le`
- `NumStability.ieeeNaiveMax_finite_nan`
- `NumStability.ieeeNaiveMax_left_nan`
- `NumStability.ieeeNaiveMax_left_nan_finite_result_not_nan`
- `NumStability.ieeeNaiveMax_nan_finite`
- `NumStability.ieeeNaiveMax_nan_finite_ne_finite_nan`
- `NumStability.ieeeNaiveMax_not_nan_propagating`
- `NumStability.ieeeNaiveMax_right_nan`

The base owner directly imports `Analysis.FloatingPointArithmetic`. No
external production declaration consumes this population. Its only direct
production importer is the broad historical `Analysis` aggregate.

### Heron Problem 2.23 population

- `NumStability.problem2_22_guard_digit_a_sub_b_exact`
- `NumStability.problem2_22_kahanHeronArea_relError_le_gamma9_unitRoundoff`

The declaration names retain their historical `problem2_22` spelling for API
compatibility; only their canonical module locator is corrected. The base
owner directly imports `Analysis.Heron`. No external production declaration
consumes this population. Its direct production importers are the canonical
Chapter 2 aggregate and the two historical import wrappers.

## Exact ownership and forwarding map

| Base or historical module | Canonical module after this batch | Role after this batch |
| --- | --- | --- |
| `Analysis.Problem2_21` | `FloatingPoint.IEEE.NaiveMaximum` | compatibility wrapper to the Problem 22 source locator |
| `Source.Higham.Chapter02.Problem22` | `FloatingPoint.IEEE.NaiveMaximum` | import-only source locator for printed Problem 2.22 |
| `Source.Higham.Chapter02.Problem22` declaration population | `Source.Higham.Chapter02.Problem23` | source owner for printed Problem 2.23 |
| `Analysis.Problem2_22` | `Source.Higham.Chapter02.Problem23` | compatibility wrapper |
| `Higham.Chapter02.Problem22` | `Source.Higham.Chapter02.Problem23` | compatibility wrapper |

The new declaration-free aggregate is `FloatingPoint.IEEE`, importing
`FloatingPoint.IEEE.NaiveMaximum`. Existing `FloatingPoint` gains the IEEE
aggregate. Existing `Source.Higham.Chapter02` imports both printed Problem 22
and Problem 23 locators.

The historical `Analysis.Problem2_21` wrapper imports
`Source.Higham.Chapter02.Problem22`, not the reusable leaf directly. This
keeps the old numbered path attached to its source locator while the locator
itself re-exports the reusable implementation. The other two historical
wrappers import `Source.Higham.Chapter02.Problem23` directly.

## Dependency and consumer retargeting

The reusable `FloatingPoint.IEEE.NaiveMaximum` leaf retains the mathematical
dependency on `Analysis.FloatingPointArithmetic`. The Problem 22 source
locator imports only that reusable leaf. The Problem 23 source leaf retains
the dependency on `Analysis.Heron`.

The immutable direct production imports are retargeted as follows:

- `Analysis` drops historical `Analysis.Problem2_21`; the reusable API is
  reached through the complete `FloatingPoint` entry point and source
  correspondence through `Source`;
- `Source.Higham.Chapter02` retains Problem 22 and adds Problem 23;
- `Analysis.Problem2_21` becomes a one-import Problem 22 wrapper;
- `Analysis.Problem2_22` becomes a one-import Problem 23 wrapper; and
- `Higham.Chapter02.Problem22` becomes a one-import Problem 23 wrapper.

No production declaration-level consumer requires another retargeting.

## Preservation audit

Each canonical implementation declaration region must compare byte-for-byte
with its base owner after UTF-8/BOM and line-ending normalization. Header
comments, module documentation, imports, and path-specific prose may change;
declarations and namespace scaffolding may not.

The compiled comparison normalizes:

- `NumStability.Analysis.Problem2_21` to
  `NumStability.FloatingPoint.IEEE.NaiveMaximum`; and
- `NumStability.Source.Higham.Chapter02.Problem22` to
  `NumStability.Source.Higham.Chapter02.Problem23`.

It also normalizes a matching generated private/equation prefix if Lean
changes it with the module owner. The result must preserve exactly 16 IEEE
maximum constants and 2 Heron constants, with no additions, removals,
duplicates, visibility changes, type changes, or body/proof changes. The
global compiled declaration and dependency populations are expected to remain
unchanged.

## Entry points, tests, and manifests

The implementation adds seven isolated tests:

1. reusable leaf `FloatingPoint.IEEE.NaiveMaximum`;
2. new aggregate `FloatingPoint.IEEE`;
3. canonical source locator `Source.Higham.Chapter02.Problem22`;
4. canonical source leaf `Source.Higham.Chapter02.Problem23`;
5. old-only `Analysis.Problem2_21`;
6. old-only `Analysis.Problem2_22`; and
7. old-only `Higham.Chapter02.Problem22`.

The three existing Problem 22 tests may be repurposed where their import path
already matches an item above; each remains an isolated one-module import.
The `FloatingPoint`, Chapter 2, Source, endpoint, compatibility, all-library,
and root smokes are updated wherever their public surface is in scope.

The tier manifest records:

- `FloatingPoint.IEEE` as `aggregate`;
- `FloatingPoint.IEEE.NaiveMaximum` as `reusable`;
- `Source.Higham.Chapter02.Problem22` and `Problem23` as `source`; and
- all three historical modules as `compatibility`.

`FloatingPoint.IEEE` becomes a reusable public entry point. The compatibility
table gains the `Analysis.Problem2_21` map and corrects the two historical
Problem 22 targets to canonical Problem 23. The layout manifest removes
`Analysis.Problem2_21` from unclassified and noncanonical debt and adds the
complete-aggregate contract for `FloatingPoint.IEEE`.

Relative to the Phase 10B base, the expected pre-measurement structural
ratchet is:

| Measure | Phase 10B | Expected Phase 10C |
| --- | ---: | ---: |
| Production modules | 964 | 967 |
| Classified modules | 345 | 349 |
| Unclassified modules | 619 | 618 |
| Aggregate modules | 66 | 67 |
| Compatibility modules | 93 | 94 |
| Reusable modules | 50 | 51 |
| Source modules | 129 | 130 |
| Noncanonical legacy modules | 412 | 411 |

Exact source lines, import edges, docstring counts, compatibility target
counts, and classification percentage are deliberately deferred to the
generated post-edit baseline.

## Required gates

The candidate worktree must pass, in order:

1. source-region ownership and wrapper-shape audits;
2. isolated canonical, aggregate, and old-only Lean tests;
3. `python tools/architecture/check_layout.py`;
4. `python tools/architecture/check_compatibility.py`;
5. `python tools/architecture/check_provenance.py`;
6. `lake test`;
7. `lake build NumStability NumStabilityTest`;
8. `lake env lean examples/LibraryLookup.lean`;
9. compiled declaration/dependency extraction and normalized ownership audit;
10. architecture baseline generation and strict ratchet comparison; and
11. the same relevant gates from a clean checkout of the committed revision.

This map is immutable after its pre-edit commit. Any implementation departure
must be recorded in the later build-evidence document rather than rewriting
this execution record.
