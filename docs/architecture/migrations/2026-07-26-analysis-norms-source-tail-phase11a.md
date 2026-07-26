# Analysis norms source-tail extraction, phase 11A (2026-07-26)

This is the immutable pre-edit ownership record for organization Phase 11A.
It was written on branch `codex/organization-phase-11-analysis-norms` at base
revision `41fd9fa61336d33f0a197f6620975f5b9b3de714`, after Phase 10F was
pushed to `main`. No production, test, manifest, compatibility-table, or live
architecture-document edit for Phase 11A precedes this record.

Phase 11A follows the ordering recorded in
`docs/architecture/reviews/OUTLIERS.md`: extract the literal ambient-radius
Higham Theorem 6.4 layer first, preserve the historical import surface, and
only then split the high-fan-in reusable norm core. The exact physical tree for
this bounded step is:

    NumStability/Analysis/
      Norms.lean                         compatibility facade
      Norms/
        Core.lean                       transitional core implementation
    NumStability/Source/Higham/
      Chapter06.lean                    complete aggregate
      Chapter06/
        Theorem04.lean                  source implementation

`NumStability.Analysis.Norms` becomes an import-only compatibility module over
both new owners. Every production importer of the old path retargets to
`NumStability.Analysis.Norms.Core`; none consumes an ambient-radius declaration.
The Analysis aggregate additionally imports the source leaf to preserve its
historical public surface (as it already does for earlier source extractions),
while reusable Analysis leaves remain source-free. The Source Higham entry
point gains Chapter 6.

This phase preserves every declaration name, namespace, type, proof, and
visibility. It does not yet split the reusable core, rename public APIs,
minimize the core's Mathlib imports, or package the other numbered Chapter 6
problem families. Those operations belong to Phase 11B after this owner change
has passed an exact compiled-graph comparison.

## Frozen baseline

The authoritative compiled input is
`benchmark-results/architecture/phase10f-clean-declarations.tsv`, whose
SHA-256 is
`958CB3FFB9A7814A80B33E31B1A162E7F2E4E630FE025A48EA6330EC8438BF93`.
It captures the production source tree with normalized SHA-256
`1d9e1f241fe7dac8113f16c6230e92df39f02f28e8a2e5e764d6ae4005f76381`.

The historical `NumStability.Analysis.Norms` source has Git blob
`9638d5b5a54e402ec27e2d6b37fa264cefb9ea70` and file SHA-256
`5F7CA006038781DBE378D12169846CDAA00E1A1439283CBF1F689B88E4781470`.
It has 24,042 physical lines, 22,811 nonblank lines, and 33 direct imports:
32 Mathlib modules and `NumStability.Analysis.MatrixAlgebra`.

The owner contains exactly 1,804 compiled constants: 1,398 public, 402
generated/internal, and four private. The global frozen graph contains 81,950
declarations, 305,425 signature edges, 439,195 body/proof edges, and 491,557
union edges.

## Exact seam and ownership

The split is the existing section boundary at historical physical line 23622,
the module comment `## Ambient-radius normalization for Higham Theorem 6.4`.
The namespace opener, scoped opens, all imports, and historical lines 45--23620
move to `Analysis.Norms.Core`, followed by `end NumStability`. The section
comment and historical lines 23629--24040 move to
`Source.Higham.Chapter06.Theorem04`, which imports only
`Analysis.Norms.Core`, opens the same namespace/scopes, and closes the
namespace itself.

### Transitional core owner

`Analysis.Norms.Core` receives exactly 1,783 compiled constants: 1,385 public,
394 generated/internal, and four private. It retains all 33 frozen direct
imports. No declaration in this owner references the new source owner.

The move is deliberately mechanical in Phase 11A. In Phase 11B this owner is
partitioned into source-free vector norms, matrix norms, singular-value
infrastructure, attainment, conditioning, and inverse-perturbation leaves.
Until that split, it still contains generic mathematics interleaved with
source-shaped `HighamProblem6*` declarations. It is therefore explicitly left
unclassified in Phase 11A rather than being mislabeled reusable or increasing
the reviewed `mixed` tier from zero. This is a bounded, named transitional debt
item removed by Phase 11B, not a claim that `Core` is already source-pure.

### Source owner

`Source.Higham.Chapter06.Theorem04` receives exactly these 13 explicit
declarations, in their existing order:

1. `MixedInverseAmbientRelativeAmplificationRadiusSet`;
2. `mixedInverseAmbientRelativeAmplificationRadiusSup`;
3. `IsSupMixedInverseAmbientRelativeAmplificationRadius`;
4. `mixedInverseAmbientRelativeAmplificationRadius_mem`;
5. `mixedInverseAmbientRelativeAmplificationRadius_value_le`;
6. `mixedInverseAmbientRelativeAmplificationRadius_sup_le`;
7. `exists_mixedInverseAmbientRelativeAmplificationRadius_lower_bound`;
8. `mixedInverseAmbientRelativeAmplificationRadius_sup_lower_le_of_linearized`;
9. `mixedInverseAmbientRelativeAmplificationRadius_sup_tendsto_condition_of_linearized_witnesses`;
10. `mixedInverseAmbientRelativeAmplificationRadius_nonempty_of_selfNormalized`;
11. `mixedInverseAmbientRelativeAmplificationRadius_bddAbove_of_small`;
12. `isSup_mixedInverseAmbientRelativeAmplificationRadiusSup`; and
13. `mixedInverseAmbientRelativeAmplificationRadiusSup_tendsto_conditionNumberProduct_of_positive_radii`.

Together with seven generated `_simp_1_*` theorems under the lower-bound
theorem and the generated
`mixedInverseAmbientRelativeAmplificationRadiusSup.eq_1`, this is exactly 21
compiled constants: 13 public and eight internal, with no private declaration.
They have 81 outgoing signature edges and 126 outgoing body/proof edges. Every
project target is either another declaration in this source owner or a
declaration remaining in `Analysis.Norms.Core`. There are no incoming
signature or body/proof edges from any declaration outside these 21 constants.
Consequently no declaration consumer needs a source import, and the only new
cross-owner declaration edges run in the permitted Source-to-Analysis
direction.

## Production import contract

The 23 textual production importers of the historical path all replace it
one-for-one with `NumStability.Analysis.Norms.Core`:

- `Algorithms.Chapter06Lemma66`;
- `Algorithms.LeastSquares.LSPerturbation`;
- `Algorithms.LeastSquares.LSQRSolve`;
- `Algorithms.MatrixPowersComplex`;
- `Algorithms.MatrixPowersLp`;
- `Algorithms.MatrixPowersLpJordan`;
- `Algorithms.PNormPowerMethodGeneralP`;
- `Algorithms.QR.Higham19Problem19_9`;
- `Algorithms.QR.Higham19TurnbullAitken`;
- `Algorithms.TestMatrices.Higham28Moments`;
- `Analysis`;
- `Analysis.Higham6Asides`;
- `Analysis.Higham6BlockAntidiag`;
- `Analysis.HighamChapter6Duality`;
- `Analysis.HighamChapter7`;
- `Analysis.MatrixPowersBaiDemmelGuDistance`;
- `Analysis.MatrixPowersLp185Primary`;
- `Analysis.SingularValues.WeylMirsky`;
- `Source.Higham.Chapter14.Problem15`;
- `Source.Higham.Chapter22.VandermondeSystems`;
- `Source.Higham.Chapter23.BilinearAlgorithm`;
- `Source.Higham.Chapter23.ThreeM`; and
- `Source.Higham.Chapter27.SoftwareEnvironment`.

Twenty-two of these modules have compiled declaration edges into the old
owner. `Source.Higham.Chapter23.BilinearAlgorithm` has no such edge; its Core
retarget is a deliberately deferred stale-import cleanup because minimizing
that leaf's upstream Mathlib surface is outside this ownership-only subphase.
Phase 11B must either remove or replace that import after isolated compilation.

After migration, no production module imports the compatibility facade.
`Source.Higham.Chapter06.Theorem04` imports the transitional core directly;
`Source.Higham.Chapter06` imports only the theorem leaf; and
`Source.Higham` adds the Chapter 6 aggregate in sorted order. Child modules do
not import their parent aggregates. Both the Chapter 6 aggregate and the old
facade are declaration-free, with sorted, unique imports.

The Chapter 6 aggregate is complete over its current physical descendants,
not a claim of complete Higham Chapter 6 coverage. In particular,
`Algorithms.Chapter06Lemma66`, `Analysis.Higham6Asides`,
`Analysis.Higham6BlockAntidiag`, and `Analysis.HighamChapter6Duality` remain
mislocated until their bounded Phase 11B source moves.

Because `Analysis.lean` documents a compatibility-preserving aggregate rather
than a reusable-tier boundary, its one-for-one retarget to `Analysis.Norms.Core`
is accompanied by a direct import of `Source.Higham.Chapter06.Theorem04`.
This mirrors its existing direct source imports and preserves every declaration
formerly reachable from `import NumStability.Analysis` without making any
reusable leaf depend on Source.

The compatibility table records the historical path as a two-target wrapper:

- `NumStability.Analysis.Norms` ->
  `NumStability.Analysis.Norms.Core` and
  `NumStability.Source.Higham.Chapter06.Theorem04`.

This is required because the old import exposed both the reusable declarations
and the literal Higham theorem. Keeping the old path reusable would either
break that public surface or introduce an Analysis-to-Source tier violation.

## Tests and manifests

Four isolated one-import tests are required and registered in sorted order in
`NumStabilityTest.lean`:

- `Import/Analysis/Norms/Core`;
- `Import/Compatibility/Analysis/Norms` (old-only, importing exactly the
  historical facade);
- `Import/Source/Chapter06`; and
- `Import/Source/Chapter06/Theorem04`.

The canonical core test checks representative vector, matrix, singular-value,
attainment, conditioning, and inverse-perturbation declarations. The theorem
leaf and Chapter 6 aggregate tests check the ambient feasible set, supremum,
upper/lower bridge, and final positive-radius limit theorem. The old-only test
checks representatives from both owners and must not import any canonical path
directly.

The affected `Analysis`, `SourceCanonical`, `SourceMigration`, `Source`,
`Higham`, `All`, and root smoke surfaces gain representative checks. Analysis,
Source, and root surfaces check both a reusable representative and the final
ambient theorem, preserving the former aggregate surface. `SourceMigration`
checks both the canonical leaf and the old facade.

The tier manifest records:

- `Source.Higham.Chapter06.Theorem04` as source;
- `Source.Higham.Chapter06` as aggregate; and
- `Analysis.Norms` as compatibility.

`Analysis.Norms.Core` remains explicitly unclassified for the bounded reason
recorded above. Phase 11B must classify every semantic descendant and remove
the Core exception before the Norms split is considered complete.

The layout manifest adds the Chapter 6 complete-aggregate contract, removes
`Analysis.Norms` from unclassified debt, and records no new exception. The
compatibility inventory gains one wrapper and two direct targets. Every new or
rewritten module receives a module docstring; the existing documentation and
naming debt totals therefore remain unchanged.

## Live documentation contract

The implementation updates the current (non-dated) navigation and policy
documents that describe this surface: `README.md`, `ARCHITECTURE.md`,
`docs/architecture/TIERS.md`, `docs/architecture/COMPATIBILITY.md`,
`docs/architecture/reviews/ENDPOINTS.md`,
`docs/architecture/reviews/OUTLIERS.md`,
`docs/source_coverage/higham_ch06.md`, and `docs/LIBRARY_LOOKUP.md`.
Current Chapter 21 and Chapter 27 formalization reports or source ledgers that
cite the old Norms implementation path are updated to distinguish Core from
the compatibility facade. Dated baselines, earlier migration maps, and
historical audit reports remain immutable evidence and are not rewritten.

The exact Phase 10F-to-11A structural forecast is:

| Measure | Phase 10F | Phase 11A forecast |
| --- | ---: | ---: |
| Lean modules | 990 | 993 |
| Direct imports | 4,063 | 4,069 |
| Internal direct imports | 2,694 | 2,700 |
| External direct imports | 1,369 | 1,369 |
| Classified modules | 381 | 384 |
| Classification coverage | 38.485% | 38.671% |
| Unclassified modules | 609 | 609 |
| Aggregate modules | 76 | 77 |
| Compatibility modules | 103 | 104 |
| Reusable modules | 58 | 58 |
| Source modules | 137 | 138 |
| Internal modules | 2 | 2 |
| Upstream modules | 5 | 5 |
| Mixed modules | 0 | 0 |
| Compatibility wrappers | 103 | 104 |
| Compatibility direct targets | 202 | 204 |
| Missing module docs | 217 | 217 |
| Legacy naming exceptions | 403 | 403 |

The generated baseline, not this forecast, is authoritative. Any difference
must be explained in the final evidence instead of being hidden by unrelated
debt cleanup.

## Exact graph preservation

The normalized Phase 10F/11A declaration comparison must be empty in both
directions. The owner field for the 1,783 constants in
`Analysis.Norms.Core` and the 21 constants in
`Source.Higham.Chapter06.Theorem04` normalizes to historical owner
`NumStability.Analysis.Norms`. Public and internal names require no rewrite.
In declaration records and in both the source and target endpoint of every
signature/body edge, the four private names normalize the prefix
`_private.NumStability.Analysis.Norms.Core.0.` to
`_private.NumStability.Analysis.Norms.0.`. The source owner has no private
constant. No other name, owner, kind, visibility, signature edge, or body/proof
edge rewrite is permitted.

## Validation gates

Phase 11A is complete only after all of the following pass:

1. focused builds of the transitional core, source leaf, Chapter 6 aggregate,
   historical facade, all 23 former direct importers, and the Source/Analysis
   entry points;
2. all four isolated canonical-only and old-only import tests;
3. affected Analysis, Source.Higham, Higham, SourceCanonical,
   SourceMigration, Source, All, and root smokes;
4. layout, compatibility, provenance, source-boundary, aggregate-ordering,
   placeholder, and exact legacy-debt contracts;
5. `lake build NumStability`, `lake test`, and
   `lake build NumStability NumStabilityTest`;
6. `lake env lean examples/LibraryLookup.lean`;
7. a fresh declaration/dependency extraction with the exact normalized graph
   comparison above;
8. a strict-source architecture baseline and reproducibility check;
9. independent production, documentation, and full-diff review; and
10. repetition of the full gates from a clean implementation commit before
    baseline and evidence commits.

Representative `#print axioms` checks must not exceed the established
`[propext, Classical.choice, Quot.sound]` ceiling. No `sorry`, `admit`, or new
top-level `axiom`/`constant` command is allowed.

## Deferred Phase 11B

Once this subphase is green, `Analysis.Norms.Core` will be split according to
the frozen declaration graph into semantic vector-norm, matrix-norm,
singular-value, attainment, conditioning, and inverse-perturbation owners.
Numbered Higham Problem 6.x declarations will move to bounded Chapter 6 source
leaves. `Analysis.Norms.Core` will then become an import-only reusable
aggregate or compatibility surface, and the historical `Analysis.Norms`
facade will continue forwarding to the complete reusable and source surfaces.
That second map must be committed before any Phase 11B production edit.
