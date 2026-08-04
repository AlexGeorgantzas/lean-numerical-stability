# W09 private-declaration and retention closure

P0010 contains **165** private declarations across **31** of the 72 historical owners. Lean mangles a private name to `_private.<defining module>.<n>.<name>`, so the defining module is part of the name: relocating one renames it and every incident edge is reported missing against the frozen graph. **No private declaration is moved or renamed.**

## Reproduction

Derived from the hash-pinned P0010 graph and the W09 selector exactly as B0009 specifies: select declarations whose owner is in `W09.tsv`; seed with every selected private; retain only selected-to-selected `signature` and `body` edges; build reverse adjacency `target -> source`; breadth-first traverse to a fixed point; ordinal-sort; serialize UTF-8 without BOM, LF, final newline.

| payload | expected | measured | reproduced |
| --- | ---: | ---: | :---: |
| signature closure | 186 (165 private + 21 public) | 186 (165 + 21) | yes |
| body closure | 423 (165 private + 258 public) | 423 (165 + 258) | yes |
| union closure | 423 (165 private + 258 public) | 423 (165 + 258) | yes |
| union payload sha256 | `07D43B378AB6CC169B19A8A0897F5149...` | reproduced by `closure.py` | yes |

The union closure is the retention **floor**: 423 declarations. W09 retains **570**, because two further classes cannot move either.

## Why retention exceeds the floor

* **28 file-scoped `local` ambient declarations** across 16 owners. A `local instance` is not exported, so any declaration using it must stay in the same module. Lean also names an anonymous one by counting homonyms already in scope -- this wave holds `instMeasurableSpaceRSqMat` and `_1`..`_5` across six owners -- so relocating one silently renames it and breaks the frozen count.
* **120 declarations that consume retained material**, closed upward so no destination has to import a compatibility facade.

## Per-owner closure

| historical owner | private | in union closure | retained |
| --- | ---: | ---: | ---: |
| `Higham28` | 0 | 0 | 0 |
| `Higham28Asymptotics` | 0 | 0 | 0 |
| `Higham28Cauchy` | 0 | 0 | 0 |
| `Higham28Companion` | 3 | 7 | 7 |
| `Higham28CompanionSpectral` | 28 | 46 | 46 |
| `Higham28Contracts` | 7 | 15 | 16 |
| `Higham28Exact` | 0 | 0 | 0 |
| `Higham28GaussianDirection` | 0 | 0 | 0 |
| `Higham28GaussianOrthogonal` | 0 | 0 | 0 |
| `Higham28GaussianQRHaar` | 4 | 18 | 18 |
| `Higham28Ginibre` | 1 | 7 | 10 |
| `Higham28GinibreAbsoluteDetRecurrence` | 8 | 11 | 11 |
| `Higham28GinibreAtlas` | 0 | 0 | 0 |
| `Higham28GinibreCharacteristicProduct` | 2 | 25 | 25 |
| `Higham28GinibreComplexPairs` | 2 | 8 | 9 |
| `Higham28GinibreCorollary31Factor` | 0 | 1 | 1 |
| `Higham28GinibreDeterminantIntegral` | 0 | 1 | 1 |
| `Higham28GinibreDeterminantMoment` | 0 | 0 | 7 |
| `Higham28GinibreDimensionTwo` | 0 | 1 | 7 |
| `Higham28GinibreExpectationGlue` | 0 | 1 | 1 |
| `Higham28GinibreFiniteFormula` | 0 | 16 | 19 |
| `Higham28GinibreGaussianBridge` | 4 | 6 | 8 |
| `Higham28GinibreIncidence` | 0 | 3 | 11 |
| `Higham28GinibreIntegral` | 0 | 4 | 6 |
| `Higham28GinibreJointDensity` | 1 | 2 | 2 |
| `Higham28GinibreMeasure` | 0 | 0 | 8 |
| `Higham28GinibreMultiplicity` | 0 | 1 | 1 |
| `Higham28GinibreOrthogonalFiber` | 14 | 25 | 25 |
| `Higham28GinibreParity` | 8 | 16 | 16 |
| `Higham28GinibrePlaneChart` | 1 | 9 | 13 |
| `Higham28GinibrePlaneIncidence` | 0 | 0 | 0 |
| `Higham28GinibrePlaneSylvester` | 1 | 2 | 10 |
| `Higham28GinibreProjectiveIntegral` | 10 | 13 | 13 |
| `Higham28GinibreRecurrence` | 4 | 10 | 12 |
| `Higham28GinibreRoots` | 1 | 2 | 23 |
| `Higham28GinibreSignedConclusion` | 0 | 6 | 6 |
| `Higham28GinibreSignedExpectation` | 1 | 12 | 14 |
| `Higham28GinibreSignedGaussian` | 0 | 0 | 0 |
| `Higham28GinibreSignedIncidence` | 7 | 16 | 22 |
| `Higham28GinibreSignedIncidenceAlgebra` | 0 | 0 | 0 |
| `Higham28GinibreSignedKernel` | 0 | 0 | 0 |
| `Higham28GinibreSignedRank` | 4 | 9 | 9 |
| `Higham28GinibreSignedRankTransfer` | 0 | 6 | 8 |
| `Higham28GinibreSignedScalar` | 0 | 1 | 1 |
| `Higham28GinibreTraceDensity` | 5 | 18 | 19 |
| `Higham28GinibreTruncatedIncidence` | 4 | 7 | 7 |
| `Higham28HilbertAsymptotic` | 3 | 5 | 5 |
| `Higham28HilbertCondition` | 5 | 13 | 13 |
| `Higham28Moments` | 8 | 14 | 14 |
| `Higham28OrthogonalCoordinates` | 0 | 0 | 0 |
| `Higham28OrthogonalFibers` | 0 | 0 | 8 |
| `Higham28OrthogonalHaar` | 0 | 0 | 0 |
| `Higham28OrthogonalSphere` | 0 | 0 | 0 |
| `Higham28Pascal` | 3 | 6 | 6 |
| `Higham28PascalCondition` | 0 | 1 | 1 |
| `Higham28PascalDualFlag` | 0 | 0 | 0 |
| `Higham28PascalOscillation` | 0 | 1 | 5 |
| `Higham28PascalOscillationCore` | 0 | 4 | 7 |
| `Higham28PascalOscillationExact` | 0 | 2 | 2 |
| `Higham28PascalSpectral` | 2 | 6 | 6 |
| `Higham28PascalTotalPositivity` | 2 | 4 | 4 |
| `Higham28Probability` | 0 | 0 | 15 |
| `Higham28RandsvdNorm` | 0 | 0 | 0 |
| `Higham28ReciprocalSPD` | 1 | 3 | 3 |
| `Higham28ShiftedHilbert` | 0 | 0 | 0 |
| `Higham28Stewart` | 3 | 5 | 19 |
| `Higham28StewartHaar` | 0 | 0 | 0 |
| `Higham28StewartRawFiber` | 0 | 0 | 8 |
| `Higham28StewartRecursion` | 0 | 0 | 8 |
| `Higham28ToeplitzCondition` | 0 | 5 | 5 |
| `Higham28ToeplitzGeneral` | 0 | 6 | 6 |
| `Higham28ToeplitzSpectrum` | 18 | 23 | 23 |
