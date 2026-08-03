# W03 integrator requests

W03 touches no forbidden or shared path, so every item below is recorded rather than
applied. Each names the exact file, the intended change, and the rationale, so a
hash-pinned request can be produced without re-deriving anything.

## 1. `check_layout.py` errors that only an integrator can clear

A direct run in the worker tree exits 1 with 12 errors. None is worker-fixable:
each resolves only through a path B0004 forbids to W03 or places outside its scope.

| error | file that must change | why W03 cannot do it |
| --- | --- | --- |
| `new unclassified modules` (the new canonical leaves) | `docs/architecture/tiers.json` | forbidden (exact). The reusable leaves under `NumStability.Algorithms.LinearSystems.*` and `NumStability.Analysis.MatrixNorms.*` are reusable tier; the `NumStability.Source.Higham.*` leaves are source correspondence |
| `stale missing module docstrings baseline` | `docs/architecture/layout-exceptions.json` | forbidden (exact). This is an *improvement*: the compatibility modules now carry module docstrings, so the ratchet baseline needs `--write-baseline` |
| `new declaration bearing umbrellas`: `Source.Higham.Chapter06.Lemma06`, `Source.Higham.Chapter10.Theorem07`, `Source.Higham.Chapter11.Theorem07` | those three umbrella `.lean` files | unavoidable by construction: B0004 authorizes destination prefixes *beneath* these umbrellas while the umbrella files themselves hold declarations and are forbidden or out of scope. Either relocate their declarations or record the exception |
| `NumStability.Source` / `Source.Higham` / `Chapter06` / `Chapter10` / `Chapter14` miss canonical descendants | `NumStability/Source.lean`, `NumStability/Source/Higham.lean`, and the chapter aggregates | forbidden (exact) or outside B0004's destination prefixes |
| `NumStability.Analysis` / `Analysis.MatrixNorms` / `LinearSystems.LU` miss canonical descendants | `NumStability/Analysis.lean`, `NumStability/Analysis/MatrixNorms.lean`, `NumStability/Algorithms/LinearSystems/LU.lean` | forbidden (exact) |

The exact module lists are reproduced verbatim below so the wiring can be generated
mechanically.

```text
error: NumStabilityTest does not reach 87 test module(s): NumStabilityTest.Reorganization.W03.Canonical.Algorithms.LinearSystems.Cholesky.ErrorAnalysis.Certificates, NumStabilityTest.Reorganization.W03.Canonical.Algorithms.LinearSystems.Cholesky.ErrorAnalysis.Demmel, NumStabilityTest.Reorganization.W03.Canonical.Algorithms.LinearSystems.Cholesky.Factorization.Spec, NumStabilityTest.Reorganization.W03.Canonical.Algorithms.LinearSystems.Cholesky.Perturbation.Basic, NumStabilityTest.Reorganization.W03.Canonical.Algorithms.LinearSystems.Cholesky.PositiveSemidefinite.Basic, NumStabilityTest.Reorganization.W03.Canonical.Algorithms.LinearSystems.Cholesky.PositiveSemidefinite.KahanMatrix, NumStabilityTest.Reorganization.W03.Canonical.Algorithms.LinearSystems.Cholesky.PositiveSemidefinite.ScaledStage, NumStabilityTest.Reorganization.W03.Canonical.Algorithms.LinearSystems.Cholesky.RoundedFactorization.Basic, NumStabilityTest.Reorganization.W03.Canonical.Algorithms.LinearSystems.Cholesky.Solve.Basic, NumStabilityTest.Reorganization.W03.Canonical.Algorithms.LinearSystems.LU.NonsymmetricPositiveDefinite.Basic, NumStabilityTest.Reorganization.W03.Canonical.Algorithms.LinearSystems.SymmetricIndefinite.ErrorAnalysis.BlockLDLT, Num StabilityTest.Reorganization.W03.Canonical.Algorithms.LinearSystems.SymmetricIndefinite.ErrorAnalysis.BlockLDLTStep, NumStabilityTest.Reorganization.W03.Canonical.Algorithms.LinearSystems.SymmetricIndefinite.ErrorAnalysis.Predicates, Nu mStabilityTest.Reorganization.W03.C
error: new unclassified modules: NumStability.Algorithms.LinearSystems.Cholesky.ErrorAnalysis.Certificates, NumStability.Algorithms.LinearSystems.Cholesky.ErrorAnalysis.Demmel, NumStability.Algorithms.LinearSystems.Cholesky.Factorization.Spec, NumStability.Algorithms.LinearSystems.Cholesky.Perturbation.Basic, NumStability.Algorithms.LinearSystems.Cholesky.PositiveSemidefinite.Basic, NumStability.Algorithms.LinearSystems.Cholesky.PositiveSemidefinite.KahanMatrix, NumStability.Algorithms.LinearSystems.Cholesky.PositiveSemidefinite.ScaledStage, NumStability.Algorithms.LinearSystems.Cholesky.RoundedFactorization.Basic, NumStability.Algorithms.LinearSystems.Cholesky.Solve.Basic, NumStability.Algorithms.LinearSystems.LU.NonsymmetricPositiveDefinite.Basic, NumStability.Algorithms.LinearSystems.SymmetricIndefinite.ErrorAnalysis.BlockLDLT, NumStability.Algorithms.LinearSystems.SymmetricIndefinite.ErrorAnalysis.BlockLDLTStep, NumStability.Algorithms.LinearSystems.SymmetricIndefinite.ErrorAnalysis.Predicates, NumStability.Algorithms.LinearSystems.SymmetricIndefinite.ErrorAnalysis.SkewSymmetric, NumStability.Algorithms.LinearSystems.SymmetricIndefinite.Pivoting.Basic, NumStability.Algorithms.LinearSystems.SymmetricIndefinite.Pivoting.Tridiagonal, NumStability.Analysis.MatrixNorms.EntrywiseAbsolute.Basic, NumStability.Analysis.MatrixNorms.SpectralExtrema.Basic
error: stale missing module docstrings baseline; review the improvement and run --write-baseline: NumStability.Algorithms.Ch10Theorem107FailureVacuity, NumStability.Algorithms.Cholesky.CholeskyDemmel, NumStability.Algorithms.Cholesky.CholeskyFl, NumStability.Algorithms.Cholesky.CholeskyIndefinite, NumStability.Algorithms.Cholesky.CholeskyNonsym, NumStability.Algorithms.Cholesky.CholeskyPSD, NumStability.Algorithms.Cholesky.CholeskyPerturbation, NumStability.Algorithms.Cholesky.CholeskySolve, NumStability.Algorithms.Cholesky.CholeskySpec, NumStability.Algorithms.Cholesky.Higham10Problem10_3
error: new declaration bearing umbrellas: NumStability.Source.Higham.Chapter06.Lemma06, NumStability.Source.Higham.Chapter10.Theorem07, NumStability.Source.Higham.Chapter11.Theorem07
error: NumStability.Algorithms.LinearSystems.LU misses 1 canonical descendant(s): NumStability.Algorithms.LinearSystems.LU.NonsymmetricPositiveDefinite.Basic
error: NumStability.Analysis misses 2 canonical descendant(s): NumStability.Analysis.MatrixNorms.EntrywiseAbsolute.Basic, NumStability.Analysis.MatrixNorms.SpectralExtrema.Basic
error: NumStability.Analysis.MatrixNorms misses 2 canonical descendant(s): NumStability.Analysis.MatrixNorms.EntrywiseAbsolute.Basic, NumStability.Analysis.MatrixNorms.SpectralExtrema.Basic
error: NumStability.Source misses 19 canonical descendant(s): NumStability.Source.Higham.Chapter06.Lemma06.OperatorTwoNormBound.Bridge, NumStability.Source.Higham.Chapter10.Equation07.AbsoluteFactorNorm.Bridge, NumStability.Source.Higham.Chapter10.Equation29.Mathias.FirstBreakdown, NumStability.Source.Higham.Chapter10.Equation29.Mathias.SourceIngredients, NumStability.Source.Higham.Chapter10.Equation30.ComplexPositiveDefinite.SourceClosure, NumStability.Source.Higham.Chapter10.Lemma11.PivotSequenceStability.SourceClosure, NumStability.Source.Higham.Chapter10.Lemma13.KahanSharpness.GramFamily, NumStability.Source.Higham.Chapter10.Lemma13.KahanSharpness.Limit, NumStability.Source.Higham.Chapter10.Problem03.ArbitraryEvaluationOrder.Basic, NumStability.Source.Higham.Chapter10.Section04.PositiveDefiniteSymmetricPart.Equation29, NumStability.Source.Higham.Chapter10.Theorem06.RoundedCholesky.ActualClosure, NumStability.Source.Higham.Chapter10.Theorem07.FailureVacuity.Vacuity, NumStability.Source.Higham.Chapter10.Theorem08.ComponentwisePerturbation.Resolvent, NumStability.Source.Higham.Chapter10.Theorem08.NormwiseDiscrepancy.LiteralSource, NumStability.Source.Higham.Chapter10.Theorem14.CompletePivotedPSD.ActualRun, NumStability.Source.Higham.Chapter10.Theorem14.CompletePivotedPSD.Equation22, NumStability.Source.Higham.Chapter10.Theorem14.CompletePivotedPSD.SourceError, NumStability.Source.Higham.Chapter10.Theorem14.CompletePivotedPSD.SourceSuccess, NumStability.Source.Higham.Chapter14.Secti
error: NumStability.Source.Higham misses 19 canonical descendant(s): NumStability.Source.Higham.Chapter06.Lemma06.OperatorTwoNormBound.Bridge, NumStability.Source.Higham.Chapter10.Equation07.AbsoluteFactorNorm.Bridge, NumStability.Source.Higham.Chapter10.Equation29.Mathias.FirstBreakdown, NumStability.Source.Higham.Chapter10.Equation29.Mathias.SourceIngredients, NumStability.Source.Higham.Chapter10.Equation30.ComplexPositiveDefinite.SourceClosure, NumStability.Source.Higham.Chapter10.Lemma11.PivotSequenceStability.SourceClosure, NumStability.Source.Higham.Chapter10.Lemma13.KahanSharpness.GramFamily, NumStability.Source.Higham.Chapter10.Lemma13.KahanSharpness.Limit, NumStability.Source.Higham.Chapter10.Problem03.ArbitraryEvaluationOrder.Basic, NumStability.Source.Higham.Chapter10.Section04.PositiveDefiniteSymmetricPart.Equation29, NumStability.Source.Higham.Chapter10.Theorem06.RoundedCholesky.ActualClosure, NumStability.Source.Higham.Chapter10.Theorem07.FailureVacuity.Vacuity, NumStability.Source.Higham.Chapter10.Theorem08.ComponentwisePerturbation.Resolvent, NumStability.Source.Higham.Chapter10.Theorem08.NormwiseDiscrepancy.LiteralSource, NumStability.Source.Higham.Chapter10.Theorem14.CompletePivotedPSD.ActualRun, NumStability.Source.Higham.Chapter10.Theorem14.CompletePivotedPSD.Equation22, NumStability.Source.Higham.Chapter10.Theorem14.CompletePivotedPSD.SourceError, NumStability.Source.Higham.Chapter10.Theorem14.CompletePivotedPSD.SourceSuccess, NumStability.Source.Higham.Chapter1
error: NumStability.Source.Higham.Chapter06 misses 1 canonical descendant(s): NumStability.Source.Higham.Chapter06.Lemma06.OperatorTwoNormBound.Bridge
error: NumStability.Source.Higham.Chapter10 misses 17 canonical descendant(s): NumStability.Source.Higham.Chapter10.Equation07.AbsoluteFactorNorm.Bridge, NumStability.Source.Higham.Chapter10.Equation29.Mathias.FirstBreakdown, NumStability.Source.Higham.Chapter10.Equation29.Mathias.SourceIngredients, NumStability.Source.Higham.Chapter10.Equation30.ComplexPositiveDefinite.SourceClosure, NumStability.Source.Higham.Chapter10.Lemma11.PivotSequenceStability.SourceClosure, NumStability.Source.Higham.Chapter10.Lemma13.KahanSharpness.GramFamily, NumStability.Source.Higham.Chapter10.Lemma13.KahanSharpness.Limit, NumStability.Source.Higham.Chapter10.Problem03.ArbitraryEvaluationOrder.Basic, NumStability.Source.Higham.Chapter10.Section04.PositiveDefiniteSymmetricPart.Equation29, NumStability.Source.Higham.Chapter10.Theorem06.RoundedCholesky.ActualClosure, NumStability.Source.Higham.Chapter10.Theorem07.FailureVacuity.Vacuity, NumStability.Source.Higham.Chapter10.Theorem08.ComponentwisePerturbation.Resolvent, NumStability.Source.Higham.Chapter10.Theorem08.NormwiseDiscrepancy.LiteralSource, NumStability.Source.Higham.Chapter10.Theorem14.CompletePivotedPSD.ActualRun, NumStability.Source.Higham.Chapter10.Theorem14.CompletePivotedPSD.Equation22, NumStability.Source.Higham.Chapter10.Theorem14.CompletePivotedPSD.SourceError, NumStability.Source.Higham.Chapter10.Theorem14.CompletePivotedPSD.SourceSuccess
error: NumStability.Source.Higham.Chapter14 misses 1 canonical descendant(s): NumStability.Source.Higham.Chapter14.Section03.ResidualOperatorTwoNorm.Bridge Lean modules: 1730 unclassified modules: 337 mixed modules: 9 modules missing module docs: 180 legacy naming exceptions: 265 declaration-bearing umbrellas: 17 unsorted aggregate imports: 0
```

## 2. Retarget the 34 non-owner C0004 consumers

`B0004-overlap-review.md` assigns this to integration: "Retarget the 34 non-owner
C0004 files that directly import W03 historical owners only during integration,
after reviewing which canonical leaf each consumer needs." W03 leaves all of them
untouched and all historical paths compiling. The direct importers measured in the
worker tree are:

- `NumStability.Algorithms`
- `NumStability.Algorithms.Ch14Cor147SourceDomainConstructor`
- `NumStability.Algorithms.Ch14GaussJordanSPDCorollary`
- `NumStability.Algorithms.Ch15DixonClosure`
- `NumStability.Algorithms.HighamChapters1To9SourceClosure`
- `NumStability.Algorithms.LeastSquares.Higham20Remaining`
- `NumStability.Algorithms.LeastSquares.LSNormalEquations`
- `NumStability.Algorithms.Underdetermined.UnderdeterminedSolve`
- `NumStability.Analysis.Perturbation.LeastSquares.NormalEquations`
- `NumStability.Source.Higham.Chapter04.Algorithm03.SourceClosure.Basic`
- `NumStability.Source.Higham.Chapter07.Corollary06.Equilibration.Basic`
- `NumStability.Source.Higham.Chapter07.Equation25.SourceEndpoint.Basic`
- `NumStability.Source.Higham.Chapter07.Equation26.ComponentwiseDistance.Basic`
- `NumStability.Source.Higham.Chapter07.Equation26.RumpCycle.Basic`
- `NumStability.Source.Higham.Chapter08.Equation10.ColumnPivotedQR.Basic`
- `NumStability.Source.Higham.Chapter08.Equation14.FanInProduct.Basic`
- `NumStability.Source.Higham.Chapter08.Section03.BidiagonalComparison.Basic`
- `NumStability.Source.Higham.Chapter08.Section04.FanInAsymptotics.Basic`
- `NumStability.Source.Higham.Chapter09.Theorem15.Barrlund.Basic`
- `NumStability.Source.Higham.Chapter09.Theorem15.Sun.Basic`
- `NumStability.Source.Higham.Chapter10.Theorem07`
- `NumStability.Source.Higham.Chapter11.Problems`
- `NumStability.Source.Higham.Chapter11.Section01.Basic`
- `NumStability.Source.Higham.Chapter11.Section01.CompletePivoting`
- `NumStability.Source.Higham.Chapter11.Section01.PartialPivoting`
- `NumStability.Source.Higham.Chapter11.Section01.RookPivoting`
- `NumStability.Source.Higham.Chapter11.Section01.Tridiagonal`
- `NumStability.Source.Higham.Chapter11.Section02.Aasen`
- `NumStability.Source.Higham.Chapter11.Section03.SkewSymmetric`
- `NumStability.Source.Higham.Chapter13.Lemma09`
- `NumStability.Source.Higham.Chapter19.Sensitivity`
- `NumStability.Source.Higham.Chapter20.Equations`
- `NumStability.Source.Higham.Chapter20.NormalEquations`
- `NumStability.Source.Higham.Chapter20.Remaining`
- `NumStabilityTest.Import.Compatibility.Algorithms.LeastSquares.CanonicalDependencies`
- `examples.LibraryLookup`

## 3. Two consumers that transitively reach W03 owners

Two owners import third-party modules whose closure reaches nine W03 owners:

| owner | import | reaches |
| --- | --- | --- |
| `Algorithms.Ch10Theorem107FailureVacuity` | `NumStability.Algorithms.HighamChapters1To9SourceClosure` | 9 W03 owners |
| `Algorithms.Cholesky.Higham1014SourceSuccess` | `NumStability.Source.Higham.Chapter10.Theorem07` | 9 W03 owners |

Neither closes a build cycle, because neither reaches its own owner, and the full
build confirms it. But both mean a canonical destination transitively depends on a
compatibility facade. Both third-party modules are on B0004's forbidden list, so
only the integrator can retarget them.

## 4. Umbrella and aggregate creation

Per the overlap review, family, chapter, source, global and test umbrellas are
created or updated only in the integration worktree. W03 created none. The 61 new
canonical modules and 87 new test modules need wiring:

- the 61 canonical leaves into their family and chapter aggregates;
- the 87 focused tests into `NumStabilityTest.lean`.
