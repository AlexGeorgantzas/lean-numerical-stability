# W11 changed paths

This report is generated from the exact Git inventory
`a32095e6e50189f7dcc39312bb4c6a36f421fab5..DELIVERY_HEAD`. Before the delivery commit, untracked
worker files are classified as additions; the committed-tip replay must
produce the same path/status inventory.

| Category | Count |
| --- | ---: |
| Modified historical owners | 18 |
| Added reusable RandNLA modules | 19 |
| Added reviewed source modules | 18 |
| Added canonical-only tests | 37 |
| Added old-path-only tests | 18 |
| Added focused tests | 21 |
| Added delivery evidence | 15 |
| **Total** | **146** |

B0010 scope result: **0 unowned paths; 0 forbidden paths**.

All 18 exact historical owners appear as `M`. Every `A` path is below
one of B0010's reviewed destination, W11-test, or delivery-evidence prefixes.

## Modified historical owners (18)

- `M` `NumStability/Algorithms/RandNLA.lean`
- `M` `NumStability/Algorithms/RandNLA/ElementwiseSampling.lean`
- `M` `NumStability/Algorithms/RandNLA/ElementwiseSpectral.lean`
- `M` `NumStability/Algorithms/RandNLA/ElementwiseTraceMGF.lean`
- `M` `NumStability/Algorithms/RandNLA/HitCountConcentration.lean`
- `M` `NumStability/Algorithms/RandNLA/LeastSquaresSketch.lean`
- `M` `NumStability/Algorithms/RandNLA/LowRankApprox.lean`
- `M` `NumStability/Algorithms/RandNLA/Preconditioning.lean`
- `M` `NumStability/Algorithms/RandNLA/RowSampling.lean`
- `M` `NumStability/Algorithms/RandNLA/RowSamplingGram.lean`
- `M` `NumStability/Algorithms/RandNLA/RowSamplingLeverage.lean`
- `M` `NumStability/Algorithms/RandNLA/RowSamplingLeverageComputedBasis.lean`
- `M` `NumStability/Algorithms/RandNLA/RowSamplingLeverageMGF.lean`
- `M` `NumStability/Algorithms/RandNLA/RowSamplingTraceMGF.lean`
- `M` `NumStability/Algorithms/RandNLA/UniformRowSampling.lean`
- `M` `NumStability/Algorithms/RandNLA/UniformRowSamplingComposition.lean`
- `M` `NumStability/Algorithms/RandNLA/UniformRowSamplingFP.lean`
- `M` `NumStability/Algorithms/RandNLA/UniformRowSamplingMGF.lean`

## Added reusable RandNLA modules (19)

- `A` `NumStability/Algorithms/RandomizedLinearAlgebra/Concentration/HitCounts/Bounds.lean`
- `A` `NumStability/Algorithms/RandomizedLinearAlgebra/Concentration/SpectralTransfer/Elementwise.lean`
- `A` `NumStability/Algorithms/RandomizedLinearAlgebra/Concentration/TraceMGF/Elementwise.lean`
- `A` `NumStability/Algorithms/RandomizedLinearAlgebra/Concentration/TraceMGF/LeverageScore.lean`
- `A` `NumStability/Algorithms/RandomizedLinearAlgebra/Concentration/TraceMGF/RowNorm.lean`
- `A` `NumStability/Algorithms/RandomizedLinearAlgebra/Concentration/TraceMGF/UniformRows.lean`
- `A` `NumStability/Algorithms/RandomizedLinearAlgebra/LeastSquaresSketching/Objectives/Core.lean`
- `A` `NumStability/Algorithms/RandomizedLinearAlgebra/LeastSquaresSketching/RowSampling/Core.lean`
- `A` `NumStability/Algorithms/RandomizedLinearAlgebra/LowRankApproximation/ColumnSketches/Core.lean`
- `A` `NumStability/Algorithms/RandomizedLinearAlgebra/LowRankApproximation/RankFactorizations/Core.lean`
- `A` `NumStability/Algorithms/RandomizedLinearAlgebra/Preconditioning/ExactTransforms/Core.lean`
- `A` `NumStability/Algorithms/RandomizedLinearAlgebra/Preconditioning/ExactTransforms/UniformRowComposition.lean`
- `A` `NumStability/Algorithms/RandomizedLinearAlgebra/Sampling/Elementwise/Core.lean`
- `A` `NumStability/Algorithms/RandomizedLinearAlgebra/Sampling/LeverageScore/ComputedBasis.lean`
- `A` `NumStability/Algorithms/RandomizedLinearAlgebra/Sampling/LeverageScore/Core.lean`
- `A` `NumStability/Algorithms/RandomizedLinearAlgebra/Sampling/RowNorm/Core.lean`
- `A` `NumStability/Algorithms/RandomizedLinearAlgebra/Sampling/RowNorm/Gram.lean`
- `A` `NumStability/Algorithms/RandomizedLinearAlgebra/Sampling/UniformRows/Core.lean`
- `A` `NumStability/Algorithms/RandomizedLinearAlgebra/Sampling/UniformRows/FloatingPoint.lean`

## Added reviewed source modules (18)

- `A` `NumStability/Source/DrineasMahoney/RandNLA2016/Algorithm01/ElementwiseSampling/HitCountConcentration.lean`
- `A` `NumStability/Source/DrineasMahoney/RandNLA2016/Algorithm01/ElementwiseSampling/Sampling.lean`
- `A` `NumStability/Source/DrineasMahoney/RandNLA2016/Algorithm01/ElementwiseSampling/TraceMGF.lean`
- `A` `NumStability/Source/DrineasMahoney/RandNLA2016/Algorithm02/RowSampling/Endpoints.lean`
- `A` `NumStability/Source/DrineasMahoney/RandNLA2016/Algorithm03/RandomProjectionPreconditioning/FloatingPoint.lean`
- `A` `NumStability/Source/DrineasMahoney/RandNLA2016/Algorithm03/RandomProjectionPreconditioning/Preconditioning.lean`
- `A` `NumStability/Source/DrineasMahoney/RandNLA2016/Algorithm03/RandomProjectionPreconditioning/UniformRowComposition.lean`
- `A` `NumStability/Source/DrineasMahoney/RandNLA2016/Algorithm03/RandomProjectionPreconditioning/UniformRows.lean`
- `A` `NumStability/Source/DrineasMahoney/RandNLA2016/Equation02/SpectralApproximation/ElementwiseSpectral.lean`
- `A` `NumStability/Source/DrineasMahoney/RandNLA2016/Equation04/RowSamplingProbability/Normalization.lean`
- `A` `NumStability/Source/DrineasMahoney/RandNLA2016/Equation05/GramApproximation/Bounds.lean`
- `A` `NumStability/Source/DrineasMahoney/RandNLA2016/Equation06/LeverageProbability/Normalization.lean`
- `A` `NumStability/Source/DrineasMahoney/RandNLA2016/Equation07/SubspaceEmbedding/ComputedBasis.lean`
- `A` `NumStability/Source/DrineasMahoney/RandNLA2016/Equation07/SubspaceEmbedding/Leverage.lean`
- `A` `NumStability/Source/DrineasMahoney/RandNLA2016/Equation07/SubspaceEmbedding/LeverageTraceMGF.lean`
- `A` `NumStability/Source/DrineasMahoney/RandNLA2016/Equation07/SubspaceEmbedding/RowNormTraceMGF.lean`
- `A` `NumStability/Source/DrineasMahoney/RandNLA2016/Equation08/LeastSquaresSketch/Endpoints.lean`
- `A` `NumStability/Source/DrineasMahoney/RandNLA2016/Equation09/LowRankApproximation/Endpoints.lean`

## Added canonical-only tests (37)

- `A` `NumStabilityTest/Reorganization/W11/Canonical/C001.lean`
- `A` `NumStabilityTest/Reorganization/W11/Canonical/C002.lean`
- `A` `NumStabilityTest/Reorganization/W11/Canonical/C003.lean`
- `A` `NumStabilityTest/Reorganization/W11/Canonical/C004.lean`
- `A` `NumStabilityTest/Reorganization/W11/Canonical/C005.lean`
- `A` `NumStabilityTest/Reorganization/W11/Canonical/C006.lean`
- `A` `NumStabilityTest/Reorganization/W11/Canonical/C007.lean`
- `A` `NumStabilityTest/Reorganization/W11/Canonical/C008.lean`
- `A` `NumStabilityTest/Reorganization/W11/Canonical/C009.lean`
- `A` `NumStabilityTest/Reorganization/W11/Canonical/C010.lean`
- `A` `NumStabilityTest/Reorganization/W11/Canonical/C011.lean`
- `A` `NumStabilityTest/Reorganization/W11/Canonical/C012.lean`
- `A` `NumStabilityTest/Reorganization/W11/Canonical/C013.lean`
- `A` `NumStabilityTest/Reorganization/W11/Canonical/C014.lean`
- `A` `NumStabilityTest/Reorganization/W11/Canonical/C015.lean`
- `A` `NumStabilityTest/Reorganization/W11/Canonical/C016.lean`
- `A` `NumStabilityTest/Reorganization/W11/Canonical/C017.lean`
- `A` `NumStabilityTest/Reorganization/W11/Canonical/C018.lean`
- `A` `NumStabilityTest/Reorganization/W11/Canonical/C019.lean`
- `A` `NumStabilityTest/Reorganization/W11/Canonical/C020.lean`
- `A` `NumStabilityTest/Reorganization/W11/Canonical/C021.lean`
- `A` `NumStabilityTest/Reorganization/W11/Canonical/C022.lean`
- `A` `NumStabilityTest/Reorganization/W11/Canonical/C023.lean`
- `A` `NumStabilityTest/Reorganization/W11/Canonical/C024.lean`
- `A` `NumStabilityTest/Reorganization/W11/Canonical/C025.lean`
- `A` `NumStabilityTest/Reorganization/W11/Canonical/C026.lean`
- `A` `NumStabilityTest/Reorganization/W11/Canonical/C027.lean`
- `A` `NumStabilityTest/Reorganization/W11/Canonical/C028.lean`
- `A` `NumStabilityTest/Reorganization/W11/Canonical/C029.lean`
- `A` `NumStabilityTest/Reorganization/W11/Canonical/C030.lean`
- `A` `NumStabilityTest/Reorganization/W11/Canonical/C031.lean`
- `A` `NumStabilityTest/Reorganization/W11/Canonical/C032.lean`
- `A` `NumStabilityTest/Reorganization/W11/Canonical/C033.lean`
- `A` `NumStabilityTest/Reorganization/W11/Canonical/C034.lean`
- `A` `NumStabilityTest/Reorganization/W11/Canonical/C035.lean`
- `A` `NumStabilityTest/Reorganization/W11/Canonical/C036.lean`
- `A` `NumStabilityTest/Reorganization/W11/Canonical/C037.lean`

## Added old-path-only tests (18)

- `A` `NumStabilityTest/Reorganization/W11/OldPath/ElementwiseSampling.lean`
- `A` `NumStabilityTest/Reorganization/W11/OldPath/ElementwiseSpectral.lean`
- `A` `NumStabilityTest/Reorganization/W11/OldPath/ElementwiseTraceMGF.lean`
- `A` `NumStabilityTest/Reorganization/W11/OldPath/HitCountConcentration.lean`
- `A` `NumStabilityTest/Reorganization/W11/OldPath/LeastSquaresSketch.lean`
- `A` `NumStabilityTest/Reorganization/W11/OldPath/LowRankApprox.lean`
- `A` `NumStabilityTest/Reorganization/W11/OldPath/Preconditioning.lean`
- `A` `NumStabilityTest/Reorganization/W11/OldPath/RandNLA.lean`
- `A` `NumStabilityTest/Reorganization/W11/OldPath/RowSampling.lean`
- `A` `NumStabilityTest/Reorganization/W11/OldPath/RowSamplingGram.lean`
- `A` `NumStabilityTest/Reorganization/W11/OldPath/RowSamplingLeverage.lean`
- `A` `NumStabilityTest/Reorganization/W11/OldPath/RowSamplingLeverageComputedBasis.lean`
- `A` `NumStabilityTest/Reorganization/W11/OldPath/RowSamplingLeverageMGF.lean`
- `A` `NumStabilityTest/Reorganization/W11/OldPath/RowSamplingTraceMGF.lean`
- `A` `NumStabilityTest/Reorganization/W11/OldPath/UniformRowSampling.lean`
- `A` `NumStabilityTest/Reorganization/W11/OldPath/UniformRowSamplingComposition.lean`
- `A` `NumStabilityTest/Reorganization/W11/OldPath/UniformRowSamplingFP.lean`
- `A` `NumStabilityTest/Reorganization/W11/OldPath/UniformRowSamplingMGF.lean`

## Added focused tests (21)

- `A` `NumStabilityTest/Reorganization/W11/Focused/ElementwiseSampling.lean`
- `A` `NumStabilityTest/Reorganization/W11/Focused/ElementwiseSpectralEquation02.lean`
- `A` `NumStabilityTest/Reorganization/W11/Focused/ElementwiseSpectralReusable.lean`
- `A` `NumStabilityTest/Reorganization/W11/Focused/LeastSquaresChapter20Closure.lean`
- `A` `NumStabilityTest/Reorganization/W11/Focused/LeastSquaresReusable.lean`
- `A` `NumStabilityTest/Reorganization/W11/Focused/LowRankEquation09.lean`
- `A` `NumStabilityTest/Reorganization/W11/Focused/LowRankMatrixInversionRetarget.lean`
- `A` `NumStabilityTest/Reorganization/W11/Focused/LowRankReusable.lean`
- `A` `NumStabilityTest/Reorganization/W11/Focused/Preconditioning.lean`
- `A` `NumStabilityTest/Reorganization/W11/Focused/PrivateHitCountClosure.lean`
- `A` `NumStabilityTest/Reorganization/W11/Focused/PrivateRowGramClosure.lean`
- `A` `NumStabilityTest/Reorganization/W11/Focused/PrivateUniformClosure.lean`
- `A` `NumStabilityTest/Reorganization/W11/Focused/ProtectedChapter20.lean`
- `A` `NumStabilityTest/Reorganization/W11/Focused/ProtectedMatrixInversionAPIs.lean`
- `A` `NumStabilityTest/Reorganization/W11/Focused/ProtectedW02Doolittle.lean`
- `A` `NumStabilityTest/Reorganization/W11/Focused/ProtectedW02ProbabilitySpectral.lean`
- `A` `NumStabilityTest/Reorganization/W11/Focused/ProtectedW06TraceMGF.lean`
- `A` `NumStabilityTest/Reorganization/W11/Focused/RowAndLeverageSampling.lean`
- `A` `NumStabilityTest/Reorganization/W11/Focused/SharedConsumerRetargetTarget.lean`
- `A` `NumStabilityTest/Reorganization/W11/Focused/TraceMGFConcentration.lean`
- `A` `NumStabilityTest/Reorganization/W11/Focused/UniformRowSampling.lean`

## Added delivery evidence (15)

- `A` `docs/architecture/deliveries/W11/CHANGED_PATHS.md`
- `A` `docs/architecture/deliveries/W11/CHECK_PROJECTION.py`
- `A` `docs/architecture/deliveries/W11/CHECK_SCOPE.py`
- `A` `docs/architecture/deliveries/W11/CHECK_STATIC.py`
- `A` `docs/architecture/deliveries/W11/DECLARATION_ROUTES.tsv`
- `A` `docs/architecture/deliveries/W11/DELIVERY.md`
- `A` `docs/architecture/deliveries/W11/GENERATE_MIGRATION.py`
- `A` `docs/architecture/deliveries/W11/INTEGRATOR_REQUESTS.md`
- `A` `docs/architecture/deliveries/W11/PRIVATE_CLOSURE.md`
- `A` `docs/architecture/deliveries/W11/PRIVATE_CLOSURE.tsv`
- `A` `docs/architecture/deliveries/W11/PROJECTION.md`
- `A` `docs/architecture/deliveries/W11/RETENTION.tsv`
- `A` `docs/architecture/deliveries/W11/ROUTE_SUMMARY.json`
- `A` `docs/architecture/deliveries/W11/ROUTING.md`
- `A` `docs/architecture/deliveries/W11/TEST_MATRIX.tsv`
