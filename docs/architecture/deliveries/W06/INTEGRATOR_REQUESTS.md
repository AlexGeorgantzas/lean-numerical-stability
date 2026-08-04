# W06 integrator requests

These are the exact shared/forbidden changes required to accept W06. The worker
did not edit any path below. Every existing-file blob OID is the C0005 preimage
at `240c0d041781385a647fbec461d6863537e562cb`; a new file has null preimage.
The integrator should encode these instructions in a hash-pinned request based
independently on C0005.

`REVIEWED_ROUTE_STATUS.tsv` and the final Git tree are the mechanical authority
for generated children. In particular, do **not** import all 143 activation-
review suggestions blindly: W06 emits 112 declaration leaves, 15 honest Source
locators, and omits 17 projection-pinned suggestions. Parent umbrellas should
import the worker's 49 prefix `.All` modules, including the two reviewed empty
prefix entry points.

## 1. Exact prefix umbrellas and upward discovery wiring

For every one of B0006's 49 production `destination_prefixes`, create the null-
preimage shared umbrella at `<prefix-with-final-slash-removed>.lean`, containing
a module docstring and the single import
`<prefix-as-Lean-module>.All`. This rule identifies 49 exact paths without
authorizing any broad parent tree.

The exact sorted null-preimage paths are:

- `NumStability/Algorithms/MatrixEquations/Sylvester/Conditioning/AttainedMinima.lean`
- `NumStability/Algorithms/MatrixEquations/Sylvester/Conditioning/AutomaticBounds.lean`
- `NumStability/Algorithms/MatrixEquations/Sylvester/Conditioning/PracticalEstimator.lean`
- `NumStability/Algorithms/MatrixEquations/Sylvester/Conditioning/SigmaMinBounds.lean`
- `NumStability/Algorithms/MatrixEquations/Sylvester/Equation/VectorizationIdentities.lean`
- `NumStability/Algorithms/MatrixEquations/Sylvester/Solvers/ComplexSchur.lean`
- `NumStability/Algorithms/MatrixEquations/Sylvester/Solvers/HessenbergSchur.lean`
- `NumStability/Algorithms/MatrixEquations/Sylvester/Solvers/PivotedSmallBlocks.lean`
- `NumStability/Algorithms/MatrixEquations/Sylvester/Solvers/QuasiTriangularBartelsStewart.lean`
- `NumStability/Algorithms/MatrixEquations/Sylvester/Solvers/TriangularBartelsStewart.lean`
- `NumStability/Algorithms/MatrixPowers/ComputedIteration.lean`
- `NumStability/Algorithms/NormEstimation/OneNorm.lean`
- `NumStability/Analysis/CStarMatrices/Basic.lean`
- `NumStability/Analysis/CStarMatrices/Expectation.lean`
- `NumStability/Analysis/CStarMatrices/Trace.lean`
- `NumStability/Analysis/FunctionalCalculus/OperatorLog.lean`
- `NumStability/Analysis/FunctionalCalculus/Resolvent.lean`
- `NumStability/Analysis/LinearOperators/Jordan/NormalForm.lean`
- `NumStability/Analysis/LinearOperators/MatrixPowers/BaiDemmelGu.lean`
- `NumStability/Analysis/LinearOperators/MatrixPowers/ExactNormBounds.lean`
- `NumStability/Analysis/LinearOperators/MatrixPowers/Gautschi.lean`
- `NumStability/Analysis/LinearOperators/MatrixPowers/Henrici.lean`
- `NumStability/Analysis/LinearOperators/MatrixPowers/JordanScaling.lean`
- `NumStability/Analysis/LinearOperators/MatrixPowers/Kreiss.lean`
- `NumStability/Analysis/LinearOperators/MatrixPowers/Laszlo.lean`
- `NumStability/Analysis/LinearOperators/MatrixPowers/LpBounds.lean`
- `NumStability/Analysis/LinearOperators/MatrixPowers/Spijker.lean`
- `NumStability/Analysis/LinearOperators/NumericalRadius/Berger.lean`
- `NumStability/Analysis/LinearOperators/NumericalRadius/Core.lean`
- `NumStability/Analysis/LinearOperators/Pseudospectra/Perturbation.lean`
- `NumStability/Analysis/LinearOperators/Pseudospectra/PowerBounds.lean`
- `NumStability/Analysis/LinearOperators/Pseudospectra/Resolvent.lean`
- `NumStability/Analysis/LinearOperators/Schur/Real/Triangularization.lean`
- `NumStability/Analysis/MatrixInequalities/LiebTrace.lean`
- `NumStability/Source/Higham/Chapter16/Problem02/LyapunovIntegral.lean`
- `NumStability/Source/Higham/Chapter16/Section01/SylvesterEquation/ComplexSolvability.lean`
- `NumStability/Source/Higham/Chapter16/Section01/SylvesterEquation/VectorizationNotes.lean`
- `NumStability/Source/Higham/Chapter16/Section02/BartelsStewart/Equation09.lean`
- `NumStability/Source/Higham/Chapter16/Section02/BartelsStewart/Equations04To08.lean`
- `NumStability/Source/Higham/Chapter16/Section02/SylvesterAndLyapunovBackwardError/AttainedMinima.lean`
- `NumStability/Source/Higham/Chapter16/Section03/PerturbationAndConditioning/AttainedSeparation.lean`
- `NumStability/Source/Higham/Chapter16/Section03/PerturbationAndConditioning/AutomaticBounds.lean`
- `NumStability/Source/Higham/Chapter16/Section03/PerturbationAndConditioning/SigmaMinCorollaries.lean`
- `NumStability/Source/Higham/Chapter16/Section04/PracticalErrorBounds/Equation29Extensions.lean`
- `NumStability/Source/Higham/Chapter16/Section04/PracticalErrorBounds/NormEstimator.lean`
- `NumStability/Source/Higham/Chapter18/Section01/MatrixPowerBounds/Equations04And05.lean`
- `NumStability/Source/Higham/Chapter18/Section01/MatrixPowerBounds/NamedBounds.lean`
- `NumStability/Source/Higham/Chapter18/Section02/FinitePrecisionPowers/Equations08To14.lean`
- `NumStability/Source/Higham/Chapter18/Section02/FinitePrecisionPowers/Theorems01And02.lean`

Before validating the hash-pinned shared request, add these 49 paths and every
new higher umbrella below to `phase.json.shared_paths` as permanent
integrator-owned discovery state. A destination directory remains worker-owned;
only its sibling `.lean` umbrella becomes shared.

Wire those prefix umbrellas upward as follows. Retain every existing import and
sort/deduplicate the final import list.

### Algorithms

- `NumStability/Algorithms/MatrixEquations/Sylvester/Conditioning.lean`, preimage
  `a0242e269afd4dca042aeb97322c2d37da84b295`: retain `.All`; add
  `Conditioning.AttainedMinima`, `.AutomaticBounds`, `.PracticalEstimator`, and
  `.SigmaMinBounds`.
- `NumStability/Algorithms/MatrixEquations/Sylvester/Equation.lean`, preimage
  `e6c54ef206310a589b9864559659cc41404e8c31`: retain `.All`; add
  `Equation.VectorizationIdentities`.
- Create null-preimage `NumStability/Algorithms/MatrixEquations/Sylvester/Solvers.lean`
  importing the five prefix umbrellas `Solvers.ComplexSchur`, `.HessenbergSchur`,
  `.PivotedSmallBlocks`, `.QuasiTriangularBartelsStewart`, and
  `.TriangularBartelsStewart`.
- `NumStability/Algorithms/MatrixEquations/Sylvester.lean`, preimage
  `e82213ea84244881b612a363b000cd557da88e51`: add `...Sylvester.Solvers`.
- Create null-preimage `NumStability/Algorithms/NormEstimation.lean` importing
  `NumStability.Algorithms.NormEstimation.OneNorm`.
- `NumStability/Algorithms.lean`, preimage
  `3b36a704f4c398a4d3a919b26851b29d9321dcb3`: add
  `NumStability.Algorithms.NormEstimation`. Do not replace the B0006-owned
  historical `NumStability.Algorithms.MatrixPowers` facade with an aggregate.
- `NumStability/Algorithms/Sylvester.lean`, preimage
  `3ebd63ec7740be45ebb8452c604999ad35bb5833`: retain every import and append:

```lean
import NumStability.Algorithms.MatrixEquations.Sylvester.Conditioning.AttainedMinima
import NumStability.Algorithms.MatrixEquations.Sylvester.Conditioning.AutomaticBounds
import NumStability.Algorithms.MatrixEquations.Sylvester.Conditioning.PracticalEstimator
import NumStability.Algorithms.MatrixEquations.Sylvester.Conditioning.SigmaMinBounds
import NumStability.Algorithms.MatrixEquations.Sylvester.Equation.VectorizationIdentities
import NumStability.Algorithms.MatrixEquations.Sylvester.Solvers
import NumStability.Algorithms.NormEstimation.OneNorm
import NumStability.Source.Higham.Chapter16.Problem02
import NumStability.Source.Higham.Chapter16.Section01.SylvesterEquation
import NumStability.Source.Higham.Chapter16.Section02.BartelsStewart
import NumStability.Source.Higham.Chapter16.Section02.SylvesterAndLyapunovBackwardError
import NumStability.Source.Higham.Chapter16.Section03.PerturbationAndConditioning
import NumStability.Source.Higham.Chapter16.Section04.PracticalErrorBounds
```

### Analysis

Create these null-preimage higher umbrellas over the exact prefix umbrellas:

- `NumStability/Analysis/CStarMatrices.lean` imports `CStarMatrices.Basic`,
  `.Expectation`, and `.Trace`.
- `NumStability/Analysis/FunctionalCalculus.lean` imports
  `FunctionalCalculus.OperatorLog` and `.Resolvent`.
- `NumStability/Analysis/LinearOperators/Jordan.lean` imports
  `LinearOperators.Jordan.NormalForm`.
- `NumStability/Analysis/LinearOperators/MatrixPowers.lean` imports the nine
  subfamilies `BaiDemmelGu`, `ExactNormBounds`, `Gautschi`, `Henrici`,
  `JordanScaling`, `Kreiss`, `Laszlo`, `LpBounds`, and `Spijker`.
- `NumStability/Analysis/LinearOperators/NumericalRadius.lean` imports
  `NumericalRadius.Berger` and `.Core`.
- `NumStability/Analysis/LinearOperators/Pseudospectra.lean` imports
  `Pseudospectra.Perturbation`, `.PowerBounds`, and `.Resolvent`.
- `NumStability/Analysis/LinearOperators/Schur/Real.lean` imports
  `Schur.Real.Triangularization`.
- `NumStability/Analysis/MatrixInequalities.lean` imports
  `MatrixInequalities.LiebTrace`.

Update:

- `NumStability/Analysis/LinearOperators.lean`, preimage
  `b1208ce6e4790923cf2fb3f2e493b982a2f1f712`: add `Jordan`, `MatrixPowers`,
  `NumericalRadius`, and `Pseudospectra`; retain existing `Schur`.
- `NumStability/Analysis/LinearOperators/Schur.lean`, preimage
  `c53a2becf973d0918b9ef2bbcefbda8a3b66cba1`: retain `.All`; add `.Real`.
- `NumStability/Analysis.lean`, preimage
  `e092306d7af94df74e9d64b8a7a9d03599b63644`: retain existing imports and add
  `NumStability.Analysis.CStarMatrices`, `.FunctionalCalculus`, and
  `.MatrixInequalities`.

### Source hierarchy

Create these null-preimage higher umbrellas (the direct leaf umbrellas come
from the 49-prefix rule):

- `NumStability/Source/Higham/Chapter16/Problem02.lean` imports
  `NumStability.Source.Higham.Chapter16.Problem02.LyapunovIntegral`.
- `NumStability/Source/Higham/Chapter16/Section01/SylvesterEquation.lean`
  retains existing `.All` and adds
  `.ComplexSolvability` and `.VectorizationNotes`.
- `NumStability/Source/Higham/Chapter16/Section02/BartelsStewart.lean` imports
  `.Equation09` and
  `.Equations04To08`.
- `NumStability/Source/Higham/Chapter16/Section02/SylvesterAndLyapunovBackwardError.lean`
  retains existing `.All` and adds `.AttainedMinima`.
- `NumStability/Source/Higham/Chapter16/Section03/PerturbationAndConditioning.lean`
  retains existing `.All` and adds `.AttainedSeparation`, `.AutomaticBounds`,
  and `.SigmaMinCorollaries`.
- `NumStability/Source/Higham/Chapter16/Section04/PracticalErrorBounds.lean`
  retains existing `.All` and adds `.Equation29Extensions` and `.NormEstimator`.
- `NumStability/Source/Higham/Chapter18/Section01/MatrixPowerBounds.lean`
  imports `.Equations04And05` and `.NamedBounds`.
- `NumStability/Source/Higham/Chapter18/Section02/FinitePrecisionPowers.lean`
  imports `.Equations08To14` and `.Theorems01And02`; create
  `NumStability/Source/Higham/Chapter18/Section02.lean` importing it.

Update these exact existing files:

- `NumStability/Source/Higham/Chapter16.lean`, preimage
  `37a703ee33b6cce357eb39f759e47aaf4ad42a0d`: add `Chapter16.Problem02`.
- `NumStability/Source/Higham/Chapter16/Section01.lean`, preimage
  `5444684d5599b6ba3e47a1328dab75411cda7fd0`: replace
  `.SylvesterEquation.All` with `.SylvesterEquation`.
- `NumStability/Source/Higham/Chapter16/Section02.lean`, preimage
  `ffb5e6ae95d23993478b7d77bab36a847b37dfeb`: add `.BartelsStewart`; replace
  `.SylvesterAndLyapunovBackwardError.All` with its parent umbrella.
- `NumStability/Source/Higham/Chapter16/Section03.lean`, preimage
  `21f4e6df1e18de9c9be64fc9a4189a8b95f15ba2`: replace
  `.PerturbationAndConditioning.All` with its parent umbrella.
- `NumStability/Source/Higham/Chapter16/Section04.lean`, preimage
  `631f2a891c0b6240c616d5a4b270be76159ee057`: replace
  `.PracticalErrorBounds.All` with its parent umbrella.
- `NumStability/Source/Higham/Chapter18.lean`, preimage
  `c6119e493b20f92338bb236d6dfd69e1c6665d2e`:
  add `Chapter18.Section02`.
- `NumStability/Source/Higham/Chapter18/Section01.lean`, preimage
  `34f9f79666f34e929196db7ba637f4558fb29c1b`: retain the Schur import and add
  `Chapter18.Section01.MatrixPowerBounds`.

`NumStability/Source/Higham.lean`, `NumStability/Source.lean`,
`NumStability.lean`, and `NumStability/All.lean` already reach these parents and
need no W06 patch.

## 2. Test discovery

- Create null-preimage `NumStabilityTest/Reorganization/W06.lean`, importing
  the exact 257 sorted modules in
  `INTEGRATOR_MANIFEST.json:test_aggregate_imports`. That list is generated
  from and checked against final `TEST_MATRIX.tsv`.
- `NumStabilityTest.lean`, preimage
  `4dee2d8bf47c00957f51b2fb2dd06fd5b9dacea0`: add
  `import NumStabilityTest.Reorganization.W06`.

## 3. Exact accepted-consumer retargets

Apply these C0005-preimage-pinned patches. Do not edit them on the worker branch.

- `NumStability/Analysis/SemiconvergentExistenceGaps.lean`, blob
  `760ba924ec970291a113c037656dbc109470ca20`: replace
  `import NumStability.Algorithms.MatrixPowersJordan` with
  `import NumStability.Analysis.LinearOperators.MatrixPowers.JordanScaling.RealJordan`.
- `NumStability/Analysis/SemiconvergentLimitGeneral.lean`, blob
  `59ea98fa1820566e6a1aef6d2bbcbac1df688271`: replace
  `import NumStability.Algorithms.MatrixPowersSpectral` with sorted imports of
  `NumStability.Analysis.LinearOperators.MatrixPowers.ExactNormBounds.SpectralRadius`
  and
  `NumStability.Analysis.LinearOperators.MatrixPowers.JordanScaling.RealDiagonal`.
  The frozen evidence is five body edges to `SpectralRadius` and two to
  `RealDiagonal`.
- `NumStability/Analysis/SemiconvergentRealSpectrumComplete.lean`, blob
  `d580c8c50364b5d44b8263b5325522990858eef3`: replace
  `import NumStability.Analysis.RealSchurTriangulation` with
  `import NumStability.Analysis.LinearOperators.Schur.Real.Triangularization.SplitCharpoly`.
- `NumStability/Analysis/Error/RoundingProducts/Core.lean`, blob
  `040c8383c8bc4308bc30694440a00962325d9214`: replace
  `import NumStability.Analysis.LiebTrace` with
  `import NumStability.Analysis.MatrixInequalities.LiebTrace.Concavity`.
- `NumStability/Source/Higham/Chapter14/Section05/SpectralConvergence.lean`, blob
  `86a3492bad89d86f36889dd696d27c87e21fddc3`: replace its old
  `Algorithms.MatrixPowers` import with
  `NumStability.Analysis.LinearOperators.MatrixPowers.JordanScaling.RealDiagonal`
  (two body edges: `matPow_diagonal` and `matPow_similarity`).
- `NumStability/Source/Higham/Chapter17/Problem01.lean`, blob
  `0ffaca593d6ae73b75245ffb3ab8b37e340420af`: replace its old
  `Algorithms.MatrixPowersSpectral` import with
  `NumStability.Analysis.LinearOperators.MatrixPowers.ExactNormBounds.SpectralRadius`.
- `NumStability/Source/Higham/Chapter03/Problem02/ProductBounds/PositiveFactors.lean`,
  blob `9a6e33058e1aaa6624e122640071ac5fdf44ca56`: delete the typed-unused
  `import NumStability.Analysis.LiebTrace`; the needed theorem arrives through
  the retargeted rounding-products core.

Delete these five typed-unused imports from each of the next three files:
`NumStability.Analysis.CStarMatrixBridge`,
`NumStability.Analysis.CStarMatrixExpectation`,
`NumStability.Analysis.CStarMatrixTrace`, `NumStability.Analysis.LiebTrace`, and
`NumStability.Analysis.OperatorLog`.

- `NumStability/Source/Higham/Chapter01/FloatingPointArithmetic/CancellationOfRoundingErrors.lean`, blob
  `785ad0b3cdb2531eb27aa2dc93e55dc89c096f74`.
- `NumStability/Source/Higham/Chapter01/FloatingPointArithmetic/IncreasingPrecision.lean`, blob
  `c14ccc8c5f0f16483537a1967086e23ba5891ecb`.
- `NumStability/Source/Higham/Chapter01/FloatingPointArithmetic/InstabilityWithoutCancellation.lean`, blob
  `27c4fc74af8f342dd923d18b7fe9b3e295f7eca8`.

Keep the old `Higham16QuasiRoundedSolve` imports in these two Chapter 11 files;
their ten typed edges target retained declarations:

- `NumStability/Source/Higham/Chapter11/BunchTridiagonalActualSolve.lean`, blob
  `cb1b1b81d08bc235175b9e3b4655d701fd95bbb0`.
- `NumStability/Source/Higham/Chapter11/Higham11BunchKaufmanActualSelector.lean`, blob
  `f44bd770d884355d303eddbf9f435da9d3c167c8`.

## 4. Tier, layout, and compatibility manifests

- `docs/architecture/tiers.json`, preimage
  `be3753f00f4ced58118705241b91ef0fe6c6b58d`: classify the 67 reusable
  declaration leaves as `reusable`, 45 Source declaration leaves plus 15
  Source locators as `source`, and all 49 worker `.All` modules plus integration
  umbrellas as `aggregate`. Classify only the 44 pure historical shims as
  `compatibility`; never classify the 23 declaration-bearing facades that way.
  The exact sorted module arrays are in
  `INTEGRATOR_MANIFEST.json:classifications`; do not infer them from paths.
- `docs/architecture/layout-exceptions.json`, preimage
  `e1d0920050f6b59c0a681509c5dbda5ebc2e0bbc`: remove resolved docstring debt;
  remove pure shims from unclassified/noncanonical debt; retain narrow reviewed
  debt for the 23 declaration-bearing facades and only real shared umbrellas.
- `docs/architecture/COMPATIBILITY.md`, preimage
  `66168cb3dc3eff5db38cb2a900bceb5d84bd239b`: add only the exact 44 modules in
  `INTEGRATOR_MANIFEST.json:classifications.compatibility_pure_import_shims` to
  the forwarding table. Document the exact 23 declaration-bearing facades from
  the adjacent manifest array separately; they are not forwarding modules.
  Use `DECLARATION_ROUTES.tsv`, `RETENTION.tsv`, and
  `REVIEWED_ROUTE_STATUS.tsv` for declaration-level details.

## 5. Deferred future-wave surfaces (record, do not patch now)

- W10: `Higham16NormEstimator` retains
  `NumStability.Algorithms.CondEstimation`; three body edges target
  `lapackNormEstimator`/its lower bound.
- W07 keeps three historical `MatrixPowers` imports until its wave; their future
  exact target is
  `NumStability.Analysis.LinearOperators.MatrixPowers.JordanScaling.RealDiagonal`
  (four body rows total):
  `NumStability/Algorithms/StationaryIteration.lean` blob
  `251bbb2dcd74492e076c7776e675a896be4cfa4e`,
  `NumStability/Algorithms/StationaryIterationDrazin.lean` blob
  `f1a3be1f6f625fa32d751d52b37e477a1303c80b`, and
  `NumStability/Algorithms/StationaryIterationSemiconvergent.lean` blob
  `0239b2e47b0a590cc8e7c685e7957a6015b9341e`.
- W09 keeps `Analysis.JordanNormalForm` in
  `NumStability/Algorithms/TestMatrices/Higham28Companion.lean`, blob
  `07d24d9292039f9aba360c047e6b4a1495f4a8b5`; future target is
  `NumStability.Analysis.LinearOperators.Jordan.NormalForm.PrimaryDecomposition`.
- W11 keeps `Analysis.LiebTrace` in the three trace-MGF consumers:
  `NumStability/Algorithms/RandNLA/ElementwiseTraceMGF.lean` blob
  `18acf114e273b6a85251c879611487b0735f714f`,
  `NumStability/Algorithms/RandNLA/RowSamplingTraceMGF.lean` blob
  `caae9619b0c0a1e891e567c82ba56cc23e69f1a5`, and
  `NumStability/Algorithms/RandNLA/UniformRowSamplingMGF.lean` blob
  `dce1fefe4d1b68e75e1aea84652d2b810dc5a099`. Their 70 signature and 180
  body rows (181 union pairs) require exactly these five future imports:
  `NumStability.Analysis.CStarMatrices.Basic.RealMatrixBridge`,
  `NumStability.Analysis.CStarMatrices.Expectation.Finite`,
  `NumStability.Analysis.CStarMatrices.Trace.Basic`,
  `NumStability.Analysis.FunctionalCalculus.OperatorLog.Monotonicity`, and
  `NumStability.Analysis.MatrixInequalities.LiebTrace.Concavity`.

## Dependency evidence

The frozen boundary is preserved exactly and will be re-proved by P0007:

- W06 to W05: 13 direct imports; 4,943 signature plus 3,218 body/proof rows,
  8,161 typed rows total and 5,777 union pairs.
- W06 to W02: 6 direct imports; 309 signature plus 217 body/proof rows, 526
  typed rows total and 343 union pairs.
- W06 to W10: one direct import and three body/proof rows.
- Downstream compatibility imports: W07 = 3, W09 = 1, W11 = 3.

## Delivery-time strict-source boundary

The worker ran the repository-wide source audit against the final W06 tree with
the exact command below while holding `Local\lean-reorganization-2026-08`:

```text
python tools/architecture/generate_baseline.py --skip-declarations --strict-source \
  --output-dir benchmark-results/W06-strict-source --name W06-strict-source
```

The scan found 2,035 modules, zero unresolved project imports, zero import
cycles, and zero reusable-to-mixed pairs.  It exited 2 solely because the
integrator-owned tier/import graph still has 31 reusable-to-Source reachable
pairs.  All 31 start at one of these accepted reusable consumers:

- `NumStability.Analysis.SemiconvergentBlockFormExists`
- `NumStability.Analysis.SemiconvergentExistenceComplete`
- `NumStability.Analysis.SemiconvergentExistenceFull`
- `NumStability.Analysis.SemiconvergentExistenceGaps`
- `NumStability.Analysis.SemiconvergentLimitGeneral`
- `NumStability.Analysis.SemiconvergentRealSpectrumComplete`

They end at six new Chapter 18 source leaves and pass through the historical
`MatrixPowers`, `MatrixPowersJordan`, or `MatrixPowersSpectral` facades.  Twelve
of the paths also pass through the deliberately deferred W07 owner
`NumStability.Algorithms.StationaryIterationSemiconvergent`.  Section 3's
accepted-consumer retargets remove the direct W02 bridges; section 5 records the
remaining W07 retargets that the active contract explicitly defers to W07.

The W06-owned canonical audit is independently green: all 176 canonical
modules have zero direct or transitive Source reachability, zero direct or
transitive dependency on a W06 historical facade, zero cycles, and zero
unresolved imports.  No B0006-authorized edit can remove the 31 global pairs.
Do not weaken the checker, misclassify a declaration-bearing facade as
compatibility, or edit a future-wave owner to conceal them.  Preserve this
delivery-time exit as integration evidence and rerun the global strict-source
gate after the exact accepted-consumer and later W07 retargets are applied.
