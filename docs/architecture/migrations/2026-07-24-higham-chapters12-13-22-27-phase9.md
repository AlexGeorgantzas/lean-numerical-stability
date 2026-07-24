# Phase 9: Higham Chapters 12, 13, 22, and 27

Date: 2026-07-24

Execution base: `943289eaa350f4430292e177f5d7ef876afb08af`

This record is the authoritative pre-edit ownership map for Phase 9. All line
numbers and Git blobs refer to the immutable execution base. The migration is
a path-and-import reorganization: declaration names, namespaces, types,
bodies, visibility, and source order remain unchanged.

## Scope and completion rule

This phase moves eleven misplaced source owners into four semantic Higham
chapter families:

- iterative refinement in Chapter 12;
- Demmel's sharp block-multiplier result in Chapter 13;
- Vandermonde systems and refinement in Chapter 22; and
- floating-point software specifications in Chapter 27.

The phase is complete only when:

1. every declaration is owned by exactly one canonical `Source.Higham` leaf;
2. the Chapter 12, Chapter 22, Chapter 22 Section 3, and Chapter 27 entry
   points are documented, sorted, declaration-free aggregates;
3. all eleven historical paths are exact import-only compatibility wrappers;
4. no production module imports one of the eleven historical implementation
   paths;
5. every old direct-import surface remains available from the corresponding
   wrapper and all broad historical entry points retain their public surface;
6. source and compiled old-versus-new ownership audits pass after normalizing
   only the changed owner and `_private` module prefixes; and
7. isolated canonical, aggregate, and old-only tests plus every repository
   architecture gate pass.

## Immutable source inventory

The eleven owners contain 835 explicit declarations: 822 public and 13
private. Their compiled environments contain 2,217 owned constants: 1,043
public, 1,093 internal, and 81 private.

| Historical owner | Git blob | Lines | Explicit declarations | Compiled ownership | First declaration | Last declaration |
| --- | --- | ---: | ---: | ---: | --- | --- |
| `Algorithms.HighamChapter12` | `e288b17cd1dc6343b7f6de05bede34f023bdd93d` | 732 | 28 public | 28 public + 8 internal | `higham12_1_SolverWBound` | `higham12_22_infNorm_skew_apply` |
| `Algorithms.HighamChapter12OmegaDiscontinuity` | `aaf08e1f11e87fb82a4b70a773d6ac3f47cd67ee` | 178 | 9 public | 9 public + 4 internal | `higham12ResidualComponent` | `higham12_exists_arbitrarily_small_component_perturb_with_omega_ge_one` |
| `Algorithms.HighamChapter12Problem12_2` | `e677db30eaebc597cc2c147b31cf915de13d464b` | 262 | 5 public | 5 public + 8 internal | `higham12_problem12_2_two_step_recurrence` | `higham12_problem12_2_from_solver_exists_forward_error_multiple_cond_u` |
| `Algorithms.LU.Higham13DemmelSharpMultiplier` | `e6b0ec6b31519a091141a5da85b46cc8208be89c` | 742 | 14 public + 12 private | 14 public + 19 internal + 20 private | private `higham13_rectOpNorm2_le_of_rectOpNorm2Le`; first public `higham13DemmelLeadingBlock` | `higham13_notes_demmel_sharp_multiplier_attained` |
| `Algorithms.Vandermonde.Higham22` | `4d63ef110f50ba72f64330e85bdd908d747b55a9` | 8,285 | 502 public | 582 public + 707 internal + 45 private | `higham22Vandermonde` | `higham22_corollary22_7_monomial_residual` |
| `Algorithms.Vandermonde.Higham22MonomialClosure` | `3122dfe74e460e54bfc803edceb994cb555b91c1` | 819 | 30 public | 37 public + 95 internal | `higham22ClosureComplexUpperBidiag` | `higham22_corollary22_7_monomial_residual_closed` |
| `Algorithms.Vandermonde.Higham22Problem22_7` | `c59b73e472776debf28a09aaec703e9a4b4d4c58` | 1,490 | 74 public | 74 public + 50 internal | `higham22_problem22_7_sum_succ_sub` | `higham22_problem22_7_extrema_kappa2_le_two` |
| `Algorithms.Vandermonde.Higham22Ch12RefinementBridge` | `0c5ae74133d6b9373ea3fd34c34cd64bb0d07e30` | 468 | 18 public + 1 private | 18 public + 29 internal + 4 private | `ch22bHornerResidual` | `ch22b_refinement_converges_via_ch12` |
| `Algorithms.Vandermonde.Higham22ComplexConfluentRefinementBridge` | `83f7a8fba8e7c545321e2f26b37ac1f1df9dfe28` | 815 | 40 public | 40 public + 43 internal + 6 private | `ch22b_iter_deriv_add` | `ch22bComplexConfluent_theorem12_3_exact_q_bound` |
| `Algorithms.SoftwareIssues.Higham27` | `c1988819758eaa273f88e577434df2ae448022d7` | 1,215 | 92 public | 226 public + 106 internal + 6 private | `FPException` | `higham27_smith_complex_division_symmetric` |
| `Algorithms.SoftwareIssues.Higham27Pythag` | `3db1c0c888324ed616b0a6c915314d9082a10730` | 195 | 10 public | 10 public + 24 internal | `higham27PythagHalleyStep` | `higham27_problem27_6_cubic_error_bound` |

The family totals are:

| Family | Explicit declarations | Compiled ownership |
| --- | ---: | ---: |
| Chapter 12 | 42 public | 42 public + 20 internal |
| Chapter 13 | 14 public + 12 private | 14 public + 19 internal + 20 private |
| Chapter 22 | 664 public + 1 private | 751 public + 924 internal + 55 private |
| Chapter 27 | 102 public | 236 public + 130 internal + 6 private |

The twelve explicit Chapter 13 private anchors occur at base lines 30, 58,
108, 524, 528, 531, 534, 542, 556, 633, 636, and 658. The sole explicit
Chapter 22 private declaration is `ch22b_polyDesc_append` at line 268 of the
real refinement bridge. The remaining compiled-private constants are generated
match splitters and equation theorems.

## Exact old-to-new ownership map

| Historical owner | Canonical owner |
| --- | --- |
| `Algorithms.HighamChapter12` | `Source.Higham.Chapter12.IterativeRefinement` |
| `Algorithms.HighamChapter12OmegaDiscontinuity` | `Source.Higham.Chapter12.OmegaDiscontinuity` |
| `Algorithms.HighamChapter12Problem12_2` | `Source.Higham.Chapter12.Problem02` |
| `Algorithms.LU.Higham13DemmelSharpMultiplier` | `Source.Higham.Chapter13.DemmelSharpMultiplier` |
| `Algorithms.Vandermonde.Higham22` | `Source.Higham.Chapter22.VandermondeSystems` |
| `Algorithms.Vandermonde.Higham22MonomialClosure` | `Source.Higham.Chapter22.MonomialResidual` |
| `Algorithms.Vandermonde.Higham22Problem22_7` | `Source.Higham.Chapter22.Problem07` |
| `Algorithms.Vandermonde.Higham22Ch12RefinementBridge` | `Source.Higham.Chapter22.Section03.RealRefinement` |
| `Algorithms.Vandermonde.Higham22ComplexConfluentRefinementBridge` | `Source.Higham.Chapter22.Section03.ComplexConfluentRefinement` |
| `Algorithms.SoftwareIssues.Higham27` | `Source.Higham.Chapter27.SoftwareEnvironment` |
| `Algorithms.SoftwareIssues.Higham27Pythag` | `Source.Higham.Chapter27.Problem06` |

The new declaration-free aggregates are:

- `Source.Higham.Chapter12`;
- `Source.Higham.Chapter22`;
- `Source.Higham.Chapter22.Section03`; and
- `Source.Higham.Chapter27`.

The Chapter 22 Section 3 boundary is substantive rather than cosmetic. Its
two implementation leaves both formalize the printed Section 22.3 refinement
claim, share the public `NumStability.Ch22B` namespace, and preserve the
existing real-to-complex import surface. Public namespace renaming is outside
this compatibility-preserving phase.

The 8,285-line Vandermonde owner is intentionally moved one-to-one. Splitting
its 502 source declarations now would change file-boundary-dependent helpers
and obscure the path migration audit. A later evidence-backed internal split
may refine that owner after the semantic hierarchy is stable.

## Canonical dependency graph

Within Chapter 12, both `OmegaDiscontinuity` and `Problem02` import
`IterativeRefinement`. The Chapter 13 sharp-multiplier leaf retains its direct
dependency on the historical BlockLU source-closure implementation; that
dependency belongs to the later BlockLU migration.

Within Chapter 22, `Problem07`, `MonomialResidual`, and
`ComplexConfluentRefinement` import `VandermondeSystems`.
`RealRefinement` imports both `VandermondeSystems` and
`ComplexConfluentRefinement`, preserving its historical transitive surface.
Both refinement leaves import the canonical Chapter 12
`IterativeRefinement` leaf. `Problem06` in Chapter 27 imports
`SoftwareEnvironment`.

`Source.Higham` gains the Chapter 12, Chapter 22, and Chapter 27 aggregates.
`Algorithms` replaces ten old direct imports with the Chapter 12, Chapter 22,
and Chapter 27 aggregates plus the canonical Chapter 13 leaf. This preserves
the historical broad surface while reducing six direct imports.

Other production consumers of the old Chapter 12 core are rewritten directly
to `Source.Higham.Chapter12.IterativeRefinement`:

- `Algorithms.LeastSquares.Higham20Equations`;
- both Chapter 22 refinement leaves; and
- `Source.Higham.CrossChapter.LUSolverWeights.Doolittle` and
  `Source.Higham.CrossChapter.LUSolverWeights.Factorization`.

The two existing Chapter 9-to-12 bridge wrappers and the two existing Chapter
13 Table 13.1 wrappers are already canonical compatibility modules and remain
unchanged.

## Preservation audit

Canonical files may change only headers, direct imports, module documentation,
and path-specific comments. Declaration blocks and namespace scaffolds are the
preservation target. All 835 explicit declaration blocks, including the 13
source-private blocks, must compare byte-for-byte after UTF-8/BOM and LF
normalization.

Moving a file changes generated names beginning with
`_private.<historical-owner>.0`. The compiled comparison may normalize only
the eleven owner paths and their corresponding `_private` prefixes in names,
types, and bodies. It must then compare unique ownership, normalized names,
kinds, visibility, type structural hashes, and body/proof structural hashes.

Because every declaration owner moves one-to-one, the expected result is the
same 2,217 constants with no helper delta. Any added, removed, or mismatched
constant requires an explicit investigation and record update.

## Isolated import coverage

The phase adds 26 isolated tests:

- fifteen canonical-only tests for eleven leaves and four aggregates, with
  the Chapter 22 Section 3 aggregate counted once within the Chapter 22 set;
- eleven old-only compatibility tests, one per historical implementation
  path.

Each old-only test imports exactly one old module. Representative checks cover
all four Chapter 12 surfaces, the Chapter 13 bound and attainment theorem, all
five Chapter 22 implementation leaves, and both Chapter 27 owners. Shared
`Algorithms`, `Source`, `Source.Higham`, `Higham`, `All`, root,
`SourceCanonical`, and `SourceMigration` smokes exercise the changed broad
entry points.

## Architecture and documentation ratchet

Before incidental source-line changes, the expected structure is:

| Measure | Phase 8 | Expected Phase 9 |
| --- | ---: | ---: |
| Production modules | 938 | 953 |
| Classified modules | 301 | 327 |
| Unclassified modules | 637 | 626 |
| Aggregate modules | 58 | 62 |
| Compatibility modules | 75 | 86 |
| Source modules | 112 | 123 |
| Missing module docs | 224 | 222 |
| Legacy naming exceptions | 430 | 419 |
| Mixed modules | 0 | 0 |
| Declaration-bearing umbrellas | 0 | 0 |
| Unsorted aggregates | 0 | 0 |

The `Algorithms` direct-import ceiling is expected to move from 453 to 447;
its direct `Source` imports move from five to nine, and its direct `Analysis`
imports remain 44. Compatibility inventory grows from 75 to 86 wrappers and
from 173 to 184 direct canonical targets.

Current source ledgers must be corrected where they still call Chapter 12
Problem 12.2 or Chapter 27 Problem 27.6 unformalized. The exact Problem 27.6
real-arithmetic recurrence is proved; only its machine-dependent MATLAB
stopping-test claim remains deferred. Historical generated baselines remain
immutable.

Validation requires targeted leaf/wrapper builds, all registered import tests,
`lake test`, `lake build NumStability NumStabilityTest`, the library lookup
example, layout/compatibility/provenance/source-boundary checks, aggregate
ordering, baseline generation and clean reproduction, JSON validation,
`git diff --check`, and a final clean-checkout rerun.
