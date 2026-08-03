# B0006 C0005 activation and W06/W08 overlap review

Branch base checkpoint: `C0005`

Branch base commit: `240c0d041781385a647fbec461d6863537e562cb`

Wave: `W06`

This review is pinned to C0005 inventory SHA-256
`1210D2D774406964AF0359ADF6DEA9296B5EF95B3E0F8F1A582D6AFB2D3FE940`
and combined-baseline SHA-256
`D961829AA197564A94193B9909695E6DA077D02B64F07EFC6FC531BB291EF190`.
The raw format-2 TSV has SHA-256
`1DA19910927D41F4B45266ABA3F5E1A1F165637F7E984F8A19E15DA4FBB4A8D0`.
The immutable W06 selector contains 67 production owners and has SHA-256
`5D482CF32C656C77AF3AABA674C3FE39AA5AEBD0FED6BC0C3E569DCDB328E484`.
P0007 has SHA-256
`E1C2787CC0D0D8A08E016932CEBC1831FAD6929BF22FA757D12BFC49F8ADCF39`
and freezes 3,512 declarations, 15,044 signature edges, 16,341 body/proof
edges, and 22,079 union edges. The projection checker has SHA-256
`29691CD63DB83A156247EA2C627407F4E90D127128A945B5AF97D014E11AB443`.

## Reviewed destinations

The declaration audit authorizes exactly these 49 production child prefixes:

```text
NumStability/Algorithms/MatrixEquations/Sylvester/Conditioning/AttainedMinima/
NumStability/Algorithms/MatrixEquations/Sylvester/Conditioning/AutomaticBounds/
NumStability/Algorithms/MatrixEquations/Sylvester/Conditioning/PracticalEstimator/
NumStability/Algorithms/MatrixEquations/Sylvester/Conditioning/SigmaMinBounds/
NumStability/Algorithms/MatrixEquations/Sylvester/Equation/VectorizationIdentities/
NumStability/Algorithms/MatrixEquations/Sylvester/Solvers/ComplexSchur/
NumStability/Algorithms/MatrixEquations/Sylvester/Solvers/HessenbergSchur/
NumStability/Algorithms/MatrixEquations/Sylvester/Solvers/PivotedSmallBlocks/
NumStability/Algorithms/MatrixEquations/Sylvester/Solvers/QuasiTriangularBartelsStewart/
NumStability/Algorithms/MatrixEquations/Sylvester/Solvers/TriangularBartelsStewart/
NumStability/Algorithms/MatrixPowers/ComputedIteration/
NumStability/Algorithms/NormEstimation/OneNorm/
NumStability/Analysis/CStarMatrices/Basic/
NumStability/Analysis/CStarMatrices/Expectation/
NumStability/Analysis/CStarMatrices/Trace/
NumStability/Analysis/FunctionalCalculus/OperatorLog/
NumStability/Analysis/FunctionalCalculus/Resolvent/
NumStability/Analysis/LinearOperators/Jordan/NormalForm/
NumStability/Analysis/LinearOperators/MatrixPowers/BaiDemmelGu/
NumStability/Analysis/LinearOperators/MatrixPowers/ExactNormBounds/
NumStability/Analysis/LinearOperators/MatrixPowers/Gautschi/
NumStability/Analysis/LinearOperators/MatrixPowers/Henrici/
NumStability/Analysis/LinearOperators/MatrixPowers/JordanScaling/
NumStability/Analysis/LinearOperators/MatrixPowers/Kreiss/
NumStability/Analysis/LinearOperators/MatrixPowers/Laszlo/
NumStability/Analysis/LinearOperators/MatrixPowers/LpBounds/
NumStability/Analysis/LinearOperators/MatrixPowers/Spijker/
NumStability/Analysis/LinearOperators/NumericalRadius/Berger/
NumStability/Analysis/LinearOperators/NumericalRadius/Core/
NumStability/Analysis/LinearOperators/Pseudospectra/Perturbation/
NumStability/Analysis/LinearOperators/Pseudospectra/PowerBounds/
NumStability/Analysis/LinearOperators/Pseudospectra/Resolvent/
NumStability/Analysis/LinearOperators/Schur/Real/Triangularization/
NumStability/Analysis/MatrixInequalities/LiebTrace/
NumStability/Source/Higham/Chapter16/Problem02/LyapunovIntegral/
NumStability/Source/Higham/Chapter16/Section01/SylvesterEquation/ComplexSolvability/
NumStability/Source/Higham/Chapter16/Section01/SylvesterEquation/VectorizationNotes/
NumStability/Source/Higham/Chapter16/Section02/BartelsStewart/Equation09/
NumStability/Source/Higham/Chapter16/Section02/BartelsStewart/Equations04To08/
NumStability/Source/Higham/Chapter16/Section02/SylvesterAndLyapunovBackwardError/AttainedMinima/
NumStability/Source/Higham/Chapter16/Section03/PerturbationAndConditioning/AttainedSeparation/
NumStability/Source/Higham/Chapter16/Section03/PerturbationAndConditioning/AutomaticBounds/
NumStability/Source/Higham/Chapter16/Section03/PerturbationAndConditioning/SigmaMinCorollaries/
NumStability/Source/Higham/Chapter16/Section04/PracticalErrorBounds/Equation29Extensions/
NumStability/Source/Higham/Chapter16/Section04/PracticalErrorBounds/NormEstimator/
NumStability/Source/Higham/Chapter18/Section01/MatrixPowerBounds/Equations04And05/
NumStability/Source/Higham/Chapter18/Section01/MatrixPowerBounds/NamedBounds/
NumStability/Source/Higham/Chapter18/Section02/FinitePrecisionPowers/Equations08To14/
NumStability/Source/Higham/Chapter18/Section02/FinitePrecisionPowers/Theorems01And02/
```

The vacancy proof is deterministic. From the C0005 code tree, enumerate
`git ls-tree -r --name-only 240c0d041781385a647fbec461d6863537e562cb`,
normalize `\` to `/`, case-fold with Unicode `casefold`, and, for each prefix
above, count names for which `name.casefold().startswith(prefix.casefold())`.
Repeat the same predicate over the `path` column of the immutable `scope.tsv`
at main commit `39e5c200685c1cc3bd0e823658eddbd958737901`. Both vectors contain 49
zeroes. A pairwise test of `a.startswith(b) or b.startswith(a)` after
case-folding finds zero equal or ancestor/descendant pairs. Finally, comparing
against `phase.json.shared_paths` with the same exact/prefix semantics finds
zero intersections. Thus all 49 implementation children are vacant, unique,
pairwise non-ancestral, outside every historical owner, and outside current
shared state. Their corresponding `.lean` umbrellas, all intermediate family
umbrellas, roots, manifests, test roots, and phase controls remain
integrator-owned and are forbidden to the worker.

## Semantic routing

The Chapter 16 owners split at mathematical boundaries. Generic sigma-minimum,
attained-minimum, automatic-bound, practical-estimator, vectorization, Schur,
Bartels--Stewart, quasi-triangular, Hessenberg--Schur, and pivoted-small-block
APIs use the reusable children above. Numbered equations 1--9, 15, 21, 23--29,
printed minimizers, norm-estimator endpoints, and Problem 16.2 use the exact
Chapter 16 children. Direct Chapter 9 or Chapter 19 source dependencies remain
on the source side.

The Chapter 18 owners similarly split generic computed powers, Jordan and
`Lp` bounds, exact norm bounds, pseudospectra, resolvents, functional calculus,
Jordan form, numerical radius, Berger, C-star matrix, Lieb, Bai--Demmel--Gu,
Henrici, Kreiss, Laszlo, Spijker, and Gautschi APIs from exact equations 4--14,
Theorems 18.1--18.2, and named printed endpoints. No reviewed reusable route
requires a Source import.

### Per-owner declaration routing

Every child below is an exact reviewed module name beneath one of the frozen
prefixes. A semicolon separates command groups that must be audited
independently. `Historical (N)` means the graph retention floor contains `N`
declarations owned by that historical module; it is not permission to move
the other commands without the required command-span and ambient-context
audit.

| Historical owner | Reusable child module(s) | Source child module(s) | Retained boundary |
| --- | --- | --- | ---: |
| `NumStability.Algorithms.MatrixPowers` | `NumStability.Algorithms.MatrixPowers.ComputedIteration.Model`; `NumStability.Analysis.LinearOperators.MatrixPowers.ExactNormBounds.Real`; `NumStability.Analysis.LinearOperators.MatrixPowers.JordanScaling.RealDiagonal` | `NumStability.Source.Higham.Chapter18.Section01.MatrixPowerBounds.Equations04And05.RealDiagonal`; `NumStability.Source.Higham.Chapter18.Section02.FinitePrecisionPowers.Equations08To14.ComputedIteration`; `NumStability.Source.Higham.Chapter18.Section02.FinitePrecisionPowers.Theorems01And02.RealCases` | `Historical (0)` |
| `NumStability.Algorithms.MatrixPowersComplex` | `NumStability.Analysis.LinearOperators.MatrixPowers.ExactNormBounds.Complex`; `NumStability.Analysis.LinearOperators.MatrixPowers.JordanScaling.Complex` | `NumStability.Source.Higham.Chapter18.Section02.FinitePrecisionPowers.Equations08To14.ComplexSimilarity`; `NumStability.Source.Higham.Chapter18.Section02.FinitePrecisionPowers.Theorems01And02.ComplexJordan` | `Historical (0)` |
| `NumStability.Algorithms.MatrixPowersJordan` | `NumStability.Analysis.LinearOperators.MatrixPowers.JordanScaling.RealJordan` | `NumStability.Source.Higham.Chapter18.Section01.MatrixPowerBounds.Equations04And05.RealJordan`; `NumStability.Source.Higham.Chapter18.Section02.FinitePrecisionPowers.Theorems01And02.RealJordan` | `Historical (0)` |
| `NumStability.Algorithms.MatrixPowersLp` | `NumStability.Analysis.LinearOperators.MatrixPowers.LpBounds.ComplexDiagonal` | `NumStability.Source.Higham.Chapter18.Section01.MatrixPowerBounds.Equations04And05.LpDiagonal` | `Historical (0)` |
| `NumStability.Algorithms.MatrixPowersLpJordan` | `NumStability.Analysis.LinearOperators.MatrixPowers.LpBounds.ComplexJordan` | `NumStability.Source.Higham.Chapter18.Section01.MatrixPowerBounds.Equations04And05.LpJordan` | `Historical (0)` |
| `NumStability.Algorithms.MatrixPowersPseudospectral` | `NumStability.Analysis.LinearOperators.Pseudospectra.Perturbation.Definitions` | `NumStability.Source.Higham.Chapter18.Section02.FinitePrecisionPowers.Equations08To14.PseudospectralRadius`; `NumStability.Source.Higham.Chapter18.Section02.FinitePrecisionPowers.Theorems01And02.PseudospectralPackaging` | `Historical (0)` |
| `NumStability.Algorithms.MatrixPowersPseudospectralCriterion` | `NumStability.Analysis.LinearOperators.Pseudospectra.Perturbation.ConvergenceCriterion` | `NumStability.Source.Higham.Chapter18.Section02.FinitePrecisionPowers.Theorems01And02.PseudospectralCriterion` | `Historical (0)` |
| `NumStability.Algorithms.MatrixPowersSpectral` | `NumStability.Analysis.LinearOperators.MatrixPowers.ExactNormBounds.SpectralRadius` | `NumStability.Source.Higham.Chapter18.Section02.FinitePrecisionPowers.Theorems01And02.SpectralCriterion` | `Historical (0)` |
| `NumStability.Algorithms.Sylvester.Higham16AutoCondition` | `NumStability.Algorithms.MatrixEquations.Sylvester.Conditioning.AutomaticBounds.GramPositivity` | `NumStability.Source.Higham.Chapter16.Section03.PerturbationAndConditioning.AutomaticBounds.Equations23To28` | `Historical (8)` |
| `NumStability.Algorithms.Sylvester.Higham16Eq9Assembly` | `NumStability.Algorithms.MatrixEquations.Sylvester.Solvers.TriangularBartelsStewart.ResidualAssembly` | `NumStability.Source.Higham.Chapter16.Section02.BartelsStewart.Equation09.Assembly` | `Historical (0)` |
| `NumStability.Algorithms.Sylvester.Higham16Eq9EndToEnd` | `NumStability.Algorithms.MatrixEquations.Sylvester.Solvers.TriangularBartelsStewart.EndToEnd` | `NumStability.Source.Higham.Chapter16.Section02.BartelsStewart.Equation09.EndToEnd` | `Historical (0)` |
| `NumStability.Algorithms.Sylvester.Higham16HessenbergRounded` | `NumStability.Algorithms.MatrixEquations.Sylvester.Solvers.HessenbergSchur.RoundedColumnSolve` | `NumStability.Source.Higham.Chapter16.Section02.BartelsStewart.Equations04To08.HessenbergRounded` | `Historical (2)` |
| `NumStability.Algorithms.Sylvester.Higham16HessenbergSchur` | `NumStability.Algorithms.MatrixEquations.Sylvester.Solvers.HessenbergSchur.ShiftedCoefficient` | `NumStability.Source.Higham.Chapter16.Section02.BartelsStewart.Equations04To08.HessenbergSchur` | `Historical (34)` |
| `NumStability.Algorithms.Sylvester.Higham16LyapunovSigmaMin` | `NumStability.Algorithms.MatrixEquations.Sylvester.Conditioning.SigmaMinBounds.Lyapunov` | `NumStability.Source.Higham.Chapter16.Section03.PerturbationAndConditioning.SigmaMinCorollaries.Lyapunov` | `Historical (0)` |
| `NumStability.Algorithms.Sylvester.Higham16Minimizers` | `NumStability.Algorithms.MatrixEquations.Sylvester.Conditioning.AttainedMinima.BackwardError`; `NumStability.Algorithms.MatrixEquations.Sylvester.Conditioning.AttainedMinima.Separation` | `NumStability.Source.Higham.Chapter16.Section02.SylvesterAndLyapunovBackwardError.AttainedMinima.Equations15And21`; `NumStability.Source.Higham.Chapter16.Section03.PerturbationAndConditioning.AttainedSeparation.Equation26`; `NumStability.Source.Higham.Chapter16.Section04.PracticalErrorBounds.Equation29Extensions.Minimizers` | `Historical (194)` |
| `NumStability.Algorithms.Sylvester.Higham16NormEstimator` | `NumStability.Algorithms.NormEstimation.OneNorm.GeneralIndex`; `NumStability.Algorithms.MatrixEquations.Sylvester.Conditioning.PracticalEstimator.OneNorm` | `NumStability.Source.Higham.Chapter16.Section04.PracticalErrorBounds.NormEstimator.Equation29` | `Historical (0)` |
| `NumStability.Algorithms.Sylvester.Higham16PerturbationSigmaMin` | `NumStability.Algorithms.MatrixEquations.Sylvester.Conditioning.SigmaMinBounds.SylvesterPerturbation` | `NumStability.Source.Higham.Chapter16.Section03.PerturbationAndConditioning.SigmaMinCorollaries.SylvesterPerturbation` | `Historical (0)` |
| `NumStability.Algorithms.Sylvester.Higham16PivotedSmallBlocks` | `NumStability.Algorithms.MatrixEquations.Sylvester.Solvers.PivotedSmallBlocks.CompletePivot` | `NumStability.Source.Higham.Chapter16.Section02.BartelsStewart.Equations04To08.PivotedSmallBlocks` | `Historical (0)` |
| `NumStability.Algorithms.Sylvester.Higham16Problem16_2` | — | `NumStability.Source.Higham.Chapter16.Problem02.LyapunovIntegral.Results` | `Historical (27)` |
| `NumStability.Algorithms.Sylvester.Higham16PsiSigmaMin` | `NumStability.Algorithms.MatrixEquations.Sylvester.Conditioning.SigmaMinBounds.StructuredSylvester` | `NumStability.Source.Higham.Chapter16.Section03.PerturbationAndConditioning.SigmaMinCorollaries.StructuredSylvester` | `Historical (0)` |
| `NumStability.Algorithms.Sylvester.Higham16QuasiQuasiRounded` | `NumStability.Algorithms.MatrixEquations.Sylvester.Solvers.QuasiTriangularBartelsStewart.SmallSystemRounding` | `NumStability.Source.Higham.Chapter16.Section02.BartelsStewart.Equations04To08.QuasiQuasiRounded` | `Historical (0)` |
| `NumStability.Algorithms.Sylvester.Higham16QuasiQuasiSylvester` | `NumStability.Algorithms.MatrixEquations.Sylvester.Solvers.QuasiTriangularBartelsStewart.QuasiQuasiSolve` | `NumStability.Source.Higham.Chapter16.Section02.BartelsStewart.Equations04To08.QuasiQuasiSylvester` | `Historical (0)` |
| `NumStability.Algorithms.Sylvester.Higham16QuasiRoundedSolve` | `NumStability.Algorithms.MatrixEquations.Sylvester.Solvers.QuasiTriangularBartelsStewart.QuasiTriangularSolve` | `NumStability.Source.Higham.Chapter16.Section02.BartelsStewart.Equations04To08.QuasiRoundedSolve` | `Historical (7)` |
| `NumStability.Algorithms.Sylvester.Higham16QuasiRoundedSylvester` | `NumStability.Algorithms.MatrixEquations.Sylvester.Solvers.QuasiTriangularBartelsStewart.QuasiTriangularSylvester` | `NumStability.Source.Higham.Chapter16.Section02.BartelsStewart.Equations04To08.QuasiRoundedSylvester` | `Historical (16)` |
| `NumStability.Algorithms.Sylvester.Higham16RoundedExecutor` | `NumStability.Algorithms.MatrixEquations.Sylvester.Solvers.QuasiTriangularBartelsStewart.Executor` | `NumStability.Source.Higham.Chapter16.Section02.BartelsStewart.Equations04To08.RoundedExecutor` | `Historical (0)` |
| `NumStability.Algorithms.Sylvester.Higham16RoundedTriangular` | `NumStability.Algorithms.MatrixEquations.Sylvester.Solvers.TriangularBartelsStewart.RoundedSolve` | `NumStability.Source.Higham.Chapter16.Section02.BartelsStewart.Equations04To08.RoundedTriangular` | `Historical (0)` |
| `NumStability.Algorithms.Sylvester.Higham16Spectrum` | `NumStability.Algorithms.MatrixEquations.Sylvester.Solvers.ComplexSchur.SpectralSolvability`; `NumStability.Algorithms.MatrixEquations.Sylvester.Solvers.QuasiTriangularBartelsStewart.BlockTraversal` | `NumStability.Source.Higham.Chapter16.Section01.SylvesterEquation.ComplexSolvability.SpectralCriterion`; `NumStability.Source.Higham.Chapter16.Section02.BartelsStewart.Equations04To08.Spectrum` | `Historical (305)` |
| `NumStability.Algorithms.Sylvester.Higham16SpectrumMinimizers` | `NumStability.Algorithms.MatrixEquations.Sylvester.Conditioning.AttainedMinima.SpectralPracticalBounds` | `NumStability.Source.Higham.Chapter16.Section04.PracticalErrorBounds.Equation29Extensions.SpectralMinimizers` | `Historical (16)` |
| `NumStability.Algorithms.Sylvester.Higham16VecNorm` | `NumStability.Algorithms.MatrixEquations.Sylvester.Conditioning.SigmaMinBounds.Vectorized`; `NumStability.Algorithms.MatrixEquations.Sylvester.Solvers.ComplexSchur.VectorizedSolvability` | `NumStability.Source.Higham.Chapter16.Section01.SylvesterEquation.ComplexSolvability.Vectorized`; `NumStability.Source.Higham.Chapter16.Section02.BartelsStewart.Equations04To08.Vectorized`; `NumStability.Source.Higham.Chapter16.Section03.PerturbationAndConditioning.SigmaMinCorollaries.Vectorized`; `NumStability.Source.Higham.Chapter16.Section04.PracticalErrorBounds.Equation29Extensions.Vectorized` | `Historical (48)` |
| `NumStability.Algorithms.Sylvester.Higham16VecPermutationNotes` | `NumStability.Algorithms.MatrixEquations.Sylvester.Equation.VectorizationIdentities.KroneckerPermutation` | `NumStability.Source.Higham.Chapter16.Section01.SylvesterEquation.VectorizationNotes.Notes` | `Historical (3)` |
| `NumStability.Analysis.BergerGeneral` | `NumStability.Analysis.LinearOperators.NumericalRadius.Berger.General` | `NumStability.Source.Higham.Chapter18.Section01.MatrixPowerBounds.NamedBounds.BergerGeneral` | `Historical (10)` |
| `NumStability.Analysis.BergerInequality` | `NumStability.Analysis.LinearOperators.NumericalRadius.Berger.Hermitian` | `NumStability.Source.Higham.Chapter18.Section01.MatrixPowerBounds.NamedBounds.BergerHermitian` | `Historical (1)` |
| `NumStability.Analysis.BergerResolvent` | `NumStability.Analysis.LinearOperators.NumericalRadius.Berger.PowerTwo` | `NumStability.Source.Higham.Chapter18.Section01.MatrixPowerBounds.NamedBounds.BergerResolvent` | `Historical (10)` |
| `NumStability.Analysis.CStarMatrixBridge` | `NumStability.Analysis.CStarMatrices.Basic.RealMatrixBridge` | — | `Historical (0)` |
| `NumStability.Analysis.CStarMatrixExpectation` | `NumStability.Analysis.CStarMatrices.Expectation.Finite` | — | `Historical (0)` |
| `NumStability.Analysis.CStarMatrixTrace` | `NumStability.Analysis.CStarMatrices.Trace.Basic` | — | `Historical (0)` |
| `NumStability.Analysis.DunfordResidue` | `NumStability.Analysis.FunctionalCalculus.Resolvent.DunfordResidue` | `NumStability.Source.Higham.Chapter18.Section02.FinitePrecisionPowers.Equations08To14.DunfordResidue` | `Historical (0)` |
| `NumStability.Analysis.HenriciExtremal` | `NumStability.Analysis.LinearOperators.MatrixPowers.Henrici.Extremal` | `NumStability.Source.Higham.Chapter18.Section01.MatrixPowerBounds.NamedBounds.HenriciExtremal` | `Historical (0)` |
| `NumStability.Analysis.HenriciSharpConstant` | `NumStability.Analysis.LinearOperators.MatrixPowers.Henrici.ImprovedConstant` | `NumStability.Source.Higham.Chapter18.Section01.MatrixPowerBounds.NamedBounds.HenriciImprovedConstant` | `Historical (0)` |
| `NumStability.Analysis.HenriciSharpConstantExact` | `NumStability.Analysis.LinearOperators.MatrixPowers.Henrici.SharpConstant` | `NumStability.Source.Higham.Chapter18.Section01.MatrixPowerBounds.NamedBounds.HenriciSharpConstant` | `Historical (0)` |
| `NumStability.Analysis.JordanNormalForm` | `NumStability.Analysis.LinearOperators.Jordan.NormalForm.PrimaryDecomposition` | — | `Historical (0)` |
| `NumStability.Analysis.LiebTrace` | `NumStability.Analysis.MatrixInequalities.LiebTrace.Concavity` | — | `Historical (0)` |
| `NumStability.Analysis.MatrixPowersBaiDemmelGu` | `NumStability.Analysis.LinearOperators.MatrixPowers.BaiDemmelGu.StabilityRadius` | `NumStability.Source.Higham.Chapter18.Section01.MatrixPowerBounds.NamedBounds.BaiDemmelGu` | `Historical (0)` |
| `NumStability.Analysis.MatrixPowersBaiDemmelGuDistance` | `NumStability.Analysis.LinearOperators.MatrixPowers.BaiDemmelGu.DistanceToInstability` | `NumStability.Source.Higham.Chapter18.Section01.MatrixPowerBounds.NamedBounds.BaiDemmelGuDistance` | `Historical (0)` |
| `NumStability.Analysis.MatrixPowersBinomialBound` | `NumStability.Analysis.LinearOperators.MatrixPowers.Henrici.BinomialPowerBound` | `NumStability.Source.Higham.Chapter18.Section01.MatrixPowerBounds.NamedBounds.HenriciBinomialBound` | `Historical (17)` |
| `NumStability.Analysis.MatrixPowersGautschi` | `NumStability.Analysis.LinearOperators.MatrixPowers.Gautschi.Bounds` | `NumStability.Source.Higham.Chapter18.Section01.MatrixPowerBounds.NamedBounds.Gautschi` | `Historical (0)` |
| `NumStability.Analysis.MatrixPowersHenrici` | `NumStability.Analysis.LinearOperators.MatrixPowers.Henrici.DepartureFromNormality` | `NumStability.Source.Higham.Chapter18.Section01.MatrixPowerBounds.NamedBounds.HenriciDeparture` | `Historical (0)` |
| `NumStability.Analysis.MatrixPowersHenriciNormal` | `NumStability.Analysis.LinearOperators.MatrixPowers.Henrici.NormalMatrices` | `NumStability.Source.Higham.Chapter18.Section01.MatrixPowerBounds.NamedBounds.HenriciNormal` | `Historical (2)` |
| `NumStability.Analysis.MatrixPowersKreiss` | `NumStability.Analysis.LinearOperators.MatrixPowers.Kreiss.ResolventBound` | `NumStability.Source.Higham.Chapter18.Section01.MatrixPowerBounds.NamedBounds.Kreiss` | `Historical (0)` |
| `NumStability.Analysis.MatrixPowersKreissSpijker` | `NumStability.Analysis.LinearOperators.MatrixPowers.Spijker.KreissBridge` | `NumStability.Source.Higham.Chapter18.Section01.MatrixPowerBounds.NamedBounds.SpijkerKreiss` | `Historical (0)` |
| `NumStability.Analysis.MatrixPowersLaszlo` | `NumStability.Analysis.LinearOperators.MatrixPowers.Laszlo.NearestNormal` | `NumStability.Source.Higham.Chapter18.Section01.MatrixPowerBounds.NamedBounds.Laszlo` | `Historical (0)` |
| `NumStability.Analysis.MatrixPowersLp185Primary` | `NumStability.Analysis.LinearOperators.MatrixPowers.LpBounds.PrimaryEquation05` | `NumStability.Source.Higham.Chapter18.Section01.MatrixPowerBounds.Equations04And05.Equation05Primary` | `Historical (0)` |
| `NumStability.Analysis.MatrixPowersSchur` | `NumStability.Analysis.LinearOperators.MatrixPowers.ExactNormBounds.Schur` | `NumStability.Source.Higham.Chapter18.Section01.MatrixPowerBounds.NamedBounds.NormalPowers` | `Historical (9)` |
| `NumStability.Analysis.MatrixPowersSpijkerClosure` | `NumStability.Analysis.LinearOperators.MatrixPowers.Spijker.Closure` | `NumStability.Source.Higham.Chapter18.Section01.MatrixPowerBounds.NamedBounds.SpijkerClosure` | `Historical (4)` |
| `NumStability.Analysis.MatrixPowersSpijkerPlanar` | `NumStability.Analysis.LinearOperators.MatrixPowers.Spijker.PlanarAlgebra` | `NumStability.Source.Higham.Chapter18.Section01.MatrixPowerBounds.NamedBounds.SpijkerPlanar` | `Historical (5)` |
| `NumStability.Analysis.MatrixPowersSpijkerPlanarAnalysis` | `NumStability.Analysis.LinearOperators.MatrixPowers.Spijker.PlanarAnalysis` | `NumStability.Source.Higham.Chapter18.Section01.MatrixPowerBounds.NamedBounds.SpijkerPlanarAnalysis` | `Historical (17)` |
| `NumStability.Analysis.MatrixPowersSpijkerRational` | `NumStability.Analysis.LinearOperators.MatrixPowers.Spijker.Rational` | `NumStability.Source.Higham.Chapter18.Section01.MatrixPowerBounds.NamedBounds.SpijkerRational` | `Historical (0)` |
| `NumStability.Analysis.NilpotentJordanChain` | `NumStability.Analysis.LinearOperators.Jordan.NormalForm.NilpotentChains` | — | `Historical (0)` |
| `NumStability.Analysis.NumericalRadius` | `NumStability.Analysis.LinearOperators.NumericalRadius.Core.Basic` | `NumStability.Source.Higham.Chapter18.Section01.MatrixPowerBounds.NamedBounds.NumericalRadius` | `Historical (1)` |
| `NumStability.Analysis.OperatorLog` | `NumStability.Analysis.FunctionalCalculus.OperatorLog.Monotonicity` | — | `Historical (0)` |
| `NumStability.Analysis.PseudospectralLowerBound` | `NumStability.Analysis.LinearOperators.Pseudospectra.Perturbation.LowerBounds` | `NumStability.Source.Higham.Chapter18.Section02.FinitePrecisionPowers.Equations08To14.PseudospectralLowerBound` | `Historical (0)` |
| `NumStability.Analysis.PseudospectralPowerBound` | `NumStability.Analysis.LinearOperators.Pseudospectra.PowerBounds.Contour` | `NumStability.Source.Higham.Chapter18.Section02.FinitePrecisionPowers.Equations08To14.PowerBound` | `Historical (0)` |
| `NumStability.Analysis.PseudospectralResolvent` | `NumStability.Analysis.LinearOperators.Pseudospectra.Resolvent.LowerBounds` | `NumStability.Source.Higham.Chapter18.Section02.FinitePrecisionPowers.Equations08To14.ResolventLowerBound` | `Historical (1)` |
| `NumStability.Analysis.RealSchurTriangulation` | `NumStability.Analysis.LinearOperators.Schur.Real.Triangularization.SplitCharpoly` | — | `Historical (0)` |
| `NumStability.Analysis.ResolventFunctionalCalculus` | `NumStability.Analysis.FunctionalCalculus.Resolvent.Analyticity` | `NumStability.Source.Higham.Chapter18.Section02.FinitePrecisionPowers.Equations08To14.ResolventCalculus` | `Historical (0)` |
| `NumStability.Analysis.SpijkerProjectionIntegral` | `NumStability.Analysis.LinearOperators.MatrixPowers.Spijker.ProjectionIntegral` | `NumStability.Source.Higham.Chapter18.Section01.MatrixPowerBounds.NamedBounds.SpijkerProjectionIntegral` | `Historical (0)` |
| `NumStability.Analysis.SylvesterSchurExistence` | `NumStability.Algorithms.MatrixEquations.Sylvester.Solvers.ComplexSchur.Existence` | `NumStability.Source.Higham.Chapter16.Section01.SylvesterEquation.ComplexSolvability.SchurFactors` | `Historical (31)` |

## Private retention boundary

P0007 contains exactly 94 private declarations. Their sorted UTF-8/LF payload
(one name per line with a final LF) has SHA-256
`338E72C78847070E2AF174A6A4FC57FEA8886464339F95027CE791FE7018113B`:

- `_private.NumStability.Algorithms.Sylvester.Higham16Minimizers.0.NumStability.abs_sub_add_add_le`
- `_private.NumStability.Algorithms.Sylvester.Higham16Minimizers.0.NumStability.continuous_lyapunovBackwardObjective`
- `_private.NumStability.Algorithms.Sylvester.Higham16Minimizers.0.NumStability.continuous_pairFst`
- `_private.NumStability.Algorithms.Sylvester.Higham16Minimizers.0.NumStability.continuous_pairFst_entry`
- `_private.NumStability.Algorithms.Sylvester.Higham16Minimizers.0.NumStability.continuous_pairSnd`
- `_private.NumStability.Algorithms.Sylvester.Higham16Minimizers.0.NumStability.continuous_pairSnd_entry`
- `_private.NumStability.Algorithms.Sylvester.Higham16Minimizers.0.NumStability.continuous_sylvesterBackwardObjective`
- `_private.NumStability.Algorithms.Sylvester.Higham16Minimizers.0.NumStability.continuous_tripleFst`
- `_private.NumStability.Algorithms.Sylvester.Higham16Minimizers.0.NumStability.continuous_tripleFst_entry`
- `_private.NumStability.Algorithms.Sylvester.Higham16Minimizers.0.NumStability.continuous_tripleSndFst`
- `_private.NumStability.Algorithms.Sylvester.Higham16Minimizers.0.NumStability.continuous_tripleSndFst_entry`
- `_private.NumStability.Algorithms.Sylvester.Higham16Minimizers.0.NumStability.continuous_tripleSndSnd`
- `_private.NumStability.Algorithms.Sylvester.Higham16Minimizers.0.NumStability.continuous_tripleSndSnd_entry`
- `_private.NumStability.Algorithms.Sylvester.Higham16Minimizers.0.NumStability.isBackwardError_sylvesterBackwardObjective`
- `_private.NumStability.Algorithms.Sylvester.Higham16Minimizers.0.NumStability.isClosed_lyapunovBackwardFeasibleSet`
- `_private.NumStability.Algorithms.Sylvester.Higham16Minimizers.0.NumStability.isClosed_sylvesterBackwardFeasibleSet`
- `_private.NumStability.Algorithms.Sylvester.Higham16Minimizers.0.NumStability.isLyapunovBackwardError_lyapunovBackwardObjective`
- `_private.NumStability.Algorithms.Sylvester.Higham16Minimizers.0.NumStability.lyapunovBackwardFeasibleSet`
- `_private.NumStability.Algorithms.Sylvester.Higham16Minimizers.0.NumStability.lyapunovBackwardObjective`
- `_private.NumStability.Algorithms.Sylvester.Higham16Minimizers.0.NumStability.lyapunovBackwardObjective_le`
- `_private.NumStability.Algorithms.Sylvester.Higham16Minimizers.0.NumStability.lyapunovBackwardObjective_nonneg`
- `_private.NumStability.Algorithms.Sylvester.Higham16Minimizers.0.NumStability.sq_le_sq_of_nonneg_of_le`
- `_private.NumStability.Algorithms.Sylvester.Higham16Minimizers.0.NumStability.sylvesterBackwardFeasibleSet`
- `_private.NumStability.Algorithms.Sylvester.Higham16Minimizers.0.NumStability.sylvesterBackwardObjective`
- `_private.NumStability.Algorithms.Sylvester.Higham16Minimizers.0.NumStability.sylvesterBackwardObjective_le`
- `_private.NumStability.Algorithms.Sylvester.Higham16Minimizers.0.NumStability.sylvesterBackwardObjective_nonneg`
- `_private.NumStability.Algorithms.Sylvester.Higham16Problem16_2.0.NumStability.higham16Problem16_2QuadraticCLM`
- `_private.NumStability.Algorithms.Sylvester.Higham16Problem16_2.0.NumStability.higham16Problem16_2QuadraticComplexLinear`
- `_private.NumStability.Algorithms.Sylvester.Higham16Problem16_2.0.NumStability.higham16_eventually_norm_pow_le_of_spectralRadius_lt`
- `_private.NumStability.Algorithms.Sylvester.Higham16Problem16_2.0.NumStability.higham16_exists_uniform_geometric_power_bound`
- `_private.NumStability.Algorithms.Sylvester.Higham16Problem16_2.0.NumStability.higham16_kernel_integrable_of_exp_decay`
- `_private.NumStability.Algorithms.Sylvester.Higham16Problem16_2.0.NumStability.higham16_neg_one_hurwitz`
- `_private.NumStability.Algorithms.Sylvester.Higham16Problem16_2.0.NumStability.higham16_normSq_add_real`
- `_private.NumStability.Algorithms.Sylvester.Higham16Problem16_2.0.NumStability.higham16_norm_exp_smul_le_of_uniform_power_bound`
- `_private.NumStability.Algorithms.Sylvester.Higham16Problem16_2.0.NumStability.higham16_problem16_2_integral_posDef_of_pointwise`
- `_private.NumStability.Algorithms.Sylvester.Higham16Problem16_2.0.NumStability.higham16_problem16_2_kernel_deriv_integrableOn`
- `_private.NumStability.Algorithms.Sylvester.Higham16Problem16_2.0.NumStability.higham16_problem16_2_quadraticCLM_apply`
- `_private.NumStability.Algorithms.Sylvester.Higham16Problem16_2.0.NumStability.higham16_problem16_2_quadraticComplexLinear_apply`
- `_private.NumStability.Algorithms.Sylvester.Higham16Problem16_2.0.NumStability.higham16_zero_posSemidef_not_posDef`
- `_private.NumStability.Algorithms.Sylvester.Higham16QuasiRoundedSolve.0.NumStability.Wave15.solve2x2_core`
- `_private.NumStability.Algorithms.Sylvester.Higham16Spectrum.0.NumStability.column_sum_split_of_zero_below`
- `_private.NumStability.Algorithms.Sylvester.Higham16Spectrum.0.NumStability.mulVec_injective_of_det_ne_zero`
- `_private.NumStability.Algorithms.Sylvester.Higham16Spectrum.0.NumStability.mulVec_surjective_of_det_ne_zero`
- `_private.NumStability.Algorithms.Sylvester.Higham16Spectrum.0.NumStability.rectMatMul_schur_coords_expand_for_triangular`
- `_private.NumStability.Algorithms.Sylvester.Higham16Spectrum.0.NumStability.triangular_column_sum_split`
- `_private.NumStability.Algorithms.Sylvester.Higham16Spectrum.0.NumStability.two_column_block_sum_split`
- `_private.NumStability.Algorithms.Sylvester.Higham16VecPermutationNotes.0.NumStability.higham16_sum_swap_indicator`
- `_private.NumStability.Analysis.BergerGeneral.0.NumStability.bergerGeneral_smul_pow`
- `_private.NumStability.Analysis.BergerGeneral.0.NumStability.bergerGeneral_sum_p`
- `_private.NumStability.Analysis.BergerGeneral.0.NumStability.bergerGeneral_telescoping`
- `_private.NumStability.Analysis.BergerGeneral.0.NumStability.bergerGeneral_unit_root`
- `_private.NumStability.Analysis.BergerGeneral.0.NumStability.term𝔼`
- `_private.NumStability.Analysis.BergerInequality.0.NumStability.term𝔼`
- `_private.NumStability.Analysis.BergerResolvent.0.NumStability.exists_unit_sq_mul`
- `_private.NumStability.Analysis.BergerResolvent.0.NumStability.inner_diag_diff`
- `_private.NumStability.Analysis.BergerResolvent.0.NumStability.term𝔼`
- `_private.NumStability.Analysis.MatrixPowersBinomialBound.0.NumStability.Ppiece`
- `_private.NumStability.Analysis.MatrixPowersBinomialBound.0.NumStability.Ppiece_apply_eq_zero`
- `_private.NumStability.Analysis.MatrixPowersBinomialBound.0.NumStability.Ppiece_eq_zero_of_ge`
- `_private.NumStability.Analysis.MatrixPowersBinomialBound.0.NumStability.Ppiece_eq_zero_of_lt`
- `_private.NumStability.Analysis.MatrixPowersBinomialBound.0.NumStability.Ppiece_succ_succ`
- `_private.NumStability.Analysis.MatrixPowersBinomialBound.0.NumStability.Ppiece_succ_zero`
- `_private.NumStability.Analysis.MatrixPowersBinomialBound.0.NumStability.Ppiece_zero_succ`
- `_private.NumStability.Analysis.MatrixPowersBinomialBound.0.NumStability.Ppiece_zero_zero`
- `_private.NumStability.Analysis.MatrixPowersBinomialBound.0.NumStability.norm_Ppiece_le`
- `_private.NumStability.Analysis.MatrixPowersBinomialBound.0.NumStability.opNorm_one`
- `_private.NumStability.Analysis.MatrixPowersBinomialBound.0.NumStability.opNorm_unitary`
- `_private.NumStability.Analysis.MatrixPowersBinomialBound.0.NumStability.opNorm_unitary_conj`
- `_private.NumStability.Analysis.MatrixPowersBinomialBound.0.NumStability.sum_Ppiece`
- `_private.NumStability.Analysis.MatrixPowersSchur.0.NumStability.conjTranspose_mul_diag`
- `_private.NumStability.Analysis.MatrixPowersSchur.0.NumStability.l2_opNorm_of_mem_unitaryGroup`
- `_private.NumStability.Analysis.MatrixPowersSchur.0.NumStability.l2_opNorm_one`
- `_private.NumStability.Analysis.MatrixPowersSchur.0.NumStability.l2_opNorm_unitary_conj`
- `_private.NumStability.Analysis.MatrixPowersSchur.0.NumStability.mul_conjTranspose_diag`
- `_private.NumStability.Analysis.MatrixPowersSchur.0.NumStability.pi_norm_pow`
- `_private.NumStability.Analysis.MatrixPowersSpijkerPlanar.0.NumStability.natDegree_C_mul_mul_le_two_mul`
- `_private.NumStability.Analysis.MatrixPowersSpijkerPlanarAnalysis.0.NumStability.exists_spijkerPartitionCrossing`
- `_private.NumStability.Analysis.MatrixPowersSpijkerPlanarAnalysis.0.NumStability.integral_abs_deriv_le_eVariationOn`
- `_private.NumStability.Analysis.MatrixPowersSpijkerPlanarAnalysis.0.NumStability.lintegral_spijkerPartitionLevelMultiplicity`
- `_private.NumStability.Analysis.MatrixPowersSpijkerPlanarAnalysis.0.NumStability.measurable_spijkerPartitionLevelMultiplicity`
- `_private.NumStability.Analysis.MatrixPowersSpijkerPlanarAnalysis.0.NumStability.spijkerActiveIncrements`
- `_private.NumStability.Analysis.MatrixPowersSpijkerPlanarAnalysis.0.NumStability.spijkerActiveIncrements_card_le_of_crossing_bound`
- `_private.NumStability.Analysis.MatrixPowersSpijkerPlanarAnalysis.0.NumStability.spijkerLevelInterval`
- `_private.NumStability.Analysis.MatrixPowersSpijkerPlanarAnalysis.0.NumStability.spijkerPartitionEndpointValues`
- `_private.NumStability.Analysis.MatrixPowersSpijkerPlanarAnalysis.0.NumStability.spijkerPartitionLevelMultiplicity`
- `_private.NumStability.Analysis.MatrixPowersSpijkerPlanarAnalysis.0.NumStability.spijkerPartitionLevelMultiplicity_eq_card`
- `_private.NumStability.Analysis.MatrixPowersSpijkerPlanarAnalysis.0.NumStability.spijkerPartitionLevelMultiplicity_le`
- `_private.NumStability.Analysis.MatrixPowersSpijkerPlanarAnalysis.0.NumStability.spijkerPartition_edist_sum_le`
- `_private.NumStability.Analysis.MatrixPowersSpijkerPlanarAnalysis.0.NumStability.spijker_eVariationOn_le`
- `_private.NumStability.Analysis.NumericalRadius.0.NumStability.term𝔼`
- `_private.NumStability.Analysis.PseudospectralResolvent.0.NumStability.«term↑ₐ»`
- `_private.NumStability.Analysis.SylvesterSchurExistence.0.NumStability.complexSylvesterVecCoeffDualIndexEquiv`
- `_private.NumStability.Analysis.SylvesterSchurExistence.0.NumStability.complex_mulVec_injective_of_det_ne_zero`
- `_private.NumStability.Analysis.SylvesterSchurExistence.0.NumStability.complex_mulVec_surjective_of_det_ne_zero`

The following case-sensitive derivation is the reproducible authority. The two
input hashes are checked before parsing; Python dictionaries and sets preserve
Lean's case-sensitive declaration identity. This distinction matters because
`spijkerPlanarAnalyticBridge` and `SpijkerPlanarAnalyticBridge` are different
declarations.

```powershell
$env:PYTHONIOENCODING='utf-8'
@'
import csv, hashlib
from collections import Counter, defaultdict, deque

selector = 'docs/architecture/phases/2026-08-repository-reorganization/selectors/W06.tsv'
graph = 'benchmark-results/C0005-combined.tsv'
expected = {
    selector: '5D482CF32C656C77AF3AABA674C3FE39AA5AEBD0FED6BC0C3E569DCDB328E484',
    graph: '1DA19910927D41F4B45266ABA3F5E1A1F165637F7E984F8A19E15DA4FBB4A8D0',
}
for path, digest in expected.items():
    assert hashlib.sha256(open(path, 'rb').read()).hexdigest().upper() == digest

with open(selector, encoding='utf-8', newline='') as f:
    modules = {row['module'] for row in csv.DictReader(f, delimiter='\t')}

selected, private, owner = set(), set(), {}
with open(graph, encoding='utf-8', newline='') as f:
    for row in csv.reader(f, delimiter='\t'):
        if row and row[0] == 'declaration' and row[2] in modules:
            selected.add(row[1]); owner[row[1]] = row[2]
            if row[4] == 'private': private.add(row[1])

reverse = {'signature': defaultdict(set), 'body': defaultdict(set),
           'union': defaultdict(set)}
with open(graph, encoding='utf-8', newline='') as f:
    for row in csv.reader(f, delimiter='\t'):
        if row and row[0] == 'edge' and row[2] in selected and row[3] in selected:
            reverse[row[1]][row[3]].add(row[2])
            reverse['union'][row[3]].add(row[2])

def closure(edges):
    result, queue = set(private), deque(private)
    while queue:
        for user in edges[queue.popleft()]:
            if user not in result:
                result.add(user); queue.append(user)
    return result

for kind in ('signature', 'body', 'union'):
    result = closure(reverse[kind])
    payload = ('\n'.join(sorted(result)) + '\n').encode()
    print(kind, len(result), hashlib.sha256(payload).hexdigest().upper())

result = closure(reverse['union'])
print('private', len(private), 'public', len(result - private))
for module, count in sorted(Counter(owner[name] for name in result).items()):
    print(module, count)
'@ | python -
```

The exact results are:

- signature closure: 96 declarations;
- body/proof closure: 768 declarations;
- union closure: 768 declarations;
- union visibility: 94 private and 674 public;
- sorted body and union closure payload SHA-256:
  `41383EF135DE610DB526922D2A0855193A8D44982F71554C4B2121E55B84A5DD`.

The union closure partitions by historical owner as follows:

| Historical owner | Retained graph floor |
| --- | ---: |
| `NumStability.Algorithms.Sylvester.Higham16AutoCondition` | 8 |
| `NumStability.Algorithms.Sylvester.Higham16HessenbergRounded` | 2 |
| `NumStability.Algorithms.Sylvester.Higham16HessenbergSchur` | 34 |
| `NumStability.Algorithms.Sylvester.Higham16Minimizers` | 194 |
| `NumStability.Algorithms.Sylvester.Higham16Problem16_2` | 27 |
| `NumStability.Algorithms.Sylvester.Higham16QuasiRoundedSolve` | 7 |
| `NumStability.Algorithms.Sylvester.Higham16QuasiRoundedSylvester` | 16 |
| `NumStability.Algorithms.Sylvester.Higham16Spectrum` | 305 |
| `NumStability.Algorithms.Sylvester.Higham16SpectrumMinimizers` | 16 |
| `NumStability.Algorithms.Sylvester.Higham16VecNorm` | 48 |
| `NumStability.Algorithms.Sylvester.Higham16VecPermutationNotes` | 3 |
| `NumStability.Analysis.BergerGeneral` | 10 |
| `NumStability.Analysis.BergerInequality` | 1 |
| `NumStability.Analysis.BergerResolvent` | 10 |
| `NumStability.Analysis.MatrixPowersBinomialBound` | 17 |
| `NumStability.Analysis.MatrixPowersHenriciNormal` | 2 |
| `NumStability.Analysis.MatrixPowersSchur` | 9 |
| `NumStability.Analysis.MatrixPowersSpijkerClosure` | 4 |
| `NumStability.Analysis.MatrixPowersSpijkerPlanar` | 5 |
| `NumStability.Analysis.MatrixPowersSpijkerPlanarAnalysis` | 17 |
| `NumStability.Analysis.NumericalRadius` | 1 |
| `NumStability.Analysis.PseudospectralResolvent` | 1 |
| `NumStability.Analysis.SylvesterSchurExistence` | 31 |
| **Total** | **768** |

This is a graph floor, not a byte-move authorization. Command roots,
mutual/generated families, section state, attributes, options, and ambient
imports may enlarge it. The worker must never move a private declaration and
must publish the final command-level closure.

## Cross-wave proof

W06 and W08 have zero exact owner overlap. Parsing C0005 source imports finds
zero W06-to-W08 imports and zero W08-to-W06 imports. Filtering the hash-pinned
C0005 graph finds zero signature and zero body/proof edges in either direction.
The reviewed production destinations have zero exact or ancestor/descendant
overlap. The sole common direct downstream importer is integrator-owned
`NumStability/Algorithms.lean`, which imports 38 W06 owners and all 42 W08
owners.

## Accepted and future boundaries

W06 has six direct imports of accepted W02 owners and thirteen direct imports
of accepted W05 owners. W05 froze 8,161 W06-to-W05 typed declaration edges;
its delivery evidence defines the exact canonical retargets and retained
`Higham16` imports. `Higham16NormEstimator` also has one W10 import and three
body edges into it; W10 is not worker-owned. W07, W09, and W11 consume the
historical `MatrixPowers`, `JordanNormalForm`, and `LiebTrace` surfaces.
Accepted and future consumer changes are integration requests, not W06 scope.

No W06 source migration is part of this activation record.
