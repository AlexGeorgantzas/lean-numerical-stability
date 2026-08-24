# R10 changed paths

Base code: `fda296b2079acae3bf1d3565b2dc6e45dc8f6ef5`

Closed delivery set: **80 paths** (9 modified, 71 added).

Production: 26; tests: 38; delivery evidence: 16; outside scope: 0.

| Status | Path |
|---|---|
| A | `docs/architecture/deliveries/R10/auditors/generate_evidence.py` |
| A | `docs/architecture/deliveries/R10/auditors/materialize_worker.py` |
| A | `docs/architecture/deliveries/R10/CHANGED_PATHS.md` |
| A | `docs/architecture/deliveries/R10/DECLARATION_ROUTES.tsv` |
| A | `docs/architecture/deliveries/R10/DELIVERY.md` |
| A | `docs/architecture/deliveries/R10/GATE_RESULTS.tsv` |
| A | `docs/architecture/deliveries/R10/INTEGRATOR_REQUESTS.md` |
| A | `docs/architecture/deliveries/R10/MATERIALIZATION.json` |
| A | `docs/architecture/deliveries/R10/PRIVATE_CLOSURE.md` |
| A | `docs/architecture/deliveries/R10/PRIVATE_CLOSURE.tsv` |
| A | `docs/architecture/deliveries/R10/PRIVATE_NORMALIZATION.tsv` |
| A | `docs/architecture/deliveries/R10/PROJECTION.md` |
| A | `docs/architecture/deliveries/R10/REALIZED_IMPORTS.tsv` |
| A | `docs/architecture/deliveries/R10/RETENTION.tsv` |
| A | `docs/architecture/deliveries/R10/ROUTING.md` |
| A | `docs/architecture/deliveries/R10/TEST_MATRIX.tsv` |
| M | `NumStability/Algorithms/RandNLA/ElementwiseSpectral.lean` |
| M | `NumStability/Algorithms/RandNLA/HitCountConcentration.lean` |
| M | `NumStability/Algorithms/RandNLA/LeastSquaresSketch.lean` |
| M | `NumStability/Algorithms/RandNLA/Preconditioning.lean` |
| M | `NumStability/Algorithms/RandNLA/RowSamplingGram.lean` |
| M | `NumStability/Algorithms/RandNLA/RowSamplingLeverage.lean` |
| M | `NumStability/Algorithms/RandNLA/UniformRowSampling.lean` |
| M | `NumStability/Algorithms/RandNLA/UniformRowSamplingComposition.lean` |
| M | `NumStability/Algorithms/RandNLA/UniformRowSamplingFP.lean` |
| A | `NumStability/Algorithms/RandomizedLinearAlgebra/Preconditioning/CountSketch/HashCollisionProbabilities.lean` |
| A | `NumStability/Algorithms/RandomizedLinearAlgebra/Preconditioning/CountSketch/SketchedGramLoewnerCovers.lean` |
| A | `NumStability/Algorithms/RandomizedLinearAlgebra/Preconditioning/CountSketch/SketchedGramMoments.lean` |
| A | `NumStability/Algorithms/RandomizedLinearAlgebra/Preconditioning/CountSketch/SketchInjectivityBounds.lean` |
| A | `NumStability/Algorithms/RandomizedLinearAlgebra/Preconditioning/ExactTransforms/UniformRowEmbedding.lean` |
| A | `NumStability/Algorithms/RandomizedLinearAlgebra/Sampling/UniformRows/GramDotFloatingPoint.lean` |
| A | `NumStability/Algorithms/RandomizedLinearAlgebra/Sampling/UniformRows/GramMoments.lean` |
| A | `NumStability/Source/DrineasMahoney/RandNLA2016/Algorithm01/ElementwiseSampling/HitPairEvents.lean` |
| A | `NumStability/Source/DrineasMahoney/RandNLA2016/Algorithm03/RandomProjectionPreconditioning/SparsePreconditionedEmbeddings.lean` |
| A | `NumStability/Source/DrineasMahoney/RandNLA2016/Algorithm03/RandomProjectionPreconditioning/SparsePreconditionedGramBounds.lean` |
| A | `NumStability/Source/DrineasMahoney/RandNLA2016/Algorithm03/RandomProjectionPreconditioning/SparsePreconditionedGramGrids.lean` |
| A | `NumStability/Source/DrineasMahoney/RandNLA2016/Equation02/SpectralApproximation/ResidualMomentBounds.lean` |
| A | `NumStability/Source/DrineasMahoney/RandNLA2016/Equation02/SpectralApproximation/SpectralEventEndpoints.lean` |
| A | `NumStability/Source/DrineasMahoney/RandNLA2016/Equation05/GramApproximation/SampledGramEndpoints.lean` |
| A | `NumStability/Source/DrineasMahoney/RandNLA2016/Equation07/SubspaceEmbedding/SampledGramOperatorNorm.lean` |
| A | `NumStability/Source/DrineasMahoney/RandNLA2016/Equation08/LeastSquaresSketch/FloatingPointObjectiveBounds.lean` |
| A | `NumStability/Source/DrineasMahoney/RandNLA2016/Equation08/LeastSquaresSketch/SketchedObjectiveBounds.lean` |
| A | `NumStabilityTest/Reorganization/R10/All.lean` |
| A | `NumStabilityTest/Reorganization/R10/CanonicalOnly/Algorithms_RandomizedLinearAlgebra_Preconditioning_CountSketch_HashCollisionProbabilities.lean` |
| A | `NumStabilityTest/Reorganization/R10/CanonicalOnly/Algorithms_RandomizedLinearAlgebra_Preconditioning_CountSketch_SketchedGramLoewnerCovers.lean` |
| A | `NumStabilityTest/Reorganization/R10/CanonicalOnly/Algorithms_RandomizedLinearAlgebra_Preconditioning_CountSketch_SketchedGramMoments.lean` |
| A | `NumStabilityTest/Reorganization/R10/CanonicalOnly/Algorithms_RandomizedLinearAlgebra_Preconditioning_CountSketch_SketchInjectivityBounds.lean` |
| A | `NumStabilityTest/Reorganization/R10/CanonicalOnly/Algorithms_RandomizedLinearAlgebra_Preconditioning_ExactTransforms_UniformRowEmbedding.lean` |
| A | `NumStabilityTest/Reorganization/R10/CanonicalOnly/Algorithms_RandomizedLinearAlgebra_Sampling_UniformRows_GramDotFloatingPoint.lean` |
| A | `NumStabilityTest/Reorganization/R10/CanonicalOnly/Algorithms_RandomizedLinearAlgebra_Sampling_UniformRows_GramMoments.lean` |
| A | `NumStabilityTest/Reorganization/R10/CanonicalOnly/Source_DrineasMahoney_RandNLA2016_Algorithm01_ElementwiseSampling_HitPairEvents.lean` |
| A | `NumStabilityTest/Reorganization/R10/CanonicalOnly/Source_DrineasMahoney_RandNLA2016_Algorithm03_RandomProjectionPreconditioning_SparsePreconditionedEmbeddings.lean` |
| A | `NumStabilityTest/Reorganization/R10/CanonicalOnly/Source_DrineasMahoney_RandNLA2016_Algorithm03_RandomProjectionPreconditioning_SparsePreconditionedGramBounds.lean` |
| A | `NumStabilityTest/Reorganization/R10/CanonicalOnly/Source_DrineasMahoney_RandNLA2016_Algorithm03_RandomProjectionPreconditioning_SparsePreconditionedGramGrids.lean` |
| A | `NumStabilityTest/Reorganization/R10/CanonicalOnly/Source_DrineasMahoney_RandNLA2016_Equation02_SpectralApproximation_ResidualMomentBounds.lean` |
| A | `NumStabilityTest/Reorganization/R10/CanonicalOnly/Source_DrineasMahoney_RandNLA2016_Equation02_SpectralApproximation_SpectralEventEndpoints.lean` |
| A | `NumStabilityTest/Reorganization/R10/CanonicalOnly/Source_DrineasMahoney_RandNLA2016_Equation05_GramApproximation_SampledGramEndpoints.lean` |
| A | `NumStabilityTest/Reorganization/R10/CanonicalOnly/Source_DrineasMahoney_RandNLA2016_Equation07_SubspaceEmbedding_SampledGramOperatorNorm.lean` |
| A | `NumStabilityTest/Reorganization/R10/CanonicalOnly/Source_DrineasMahoney_RandNLA2016_Equation08_LeastSquaresSketch_FloatingPointObjectiveBounds.lean` |
| A | `NumStabilityTest/Reorganization/R10/CanonicalOnly/Source_DrineasMahoney_RandNLA2016_Equation08_LeastSquaresSketch_SketchedObjectiveBounds.lean` |
| A | `NumStabilityTest/Reorganization/R10/Focused/ProtectedCanonicalTargets.lean` |
| A | `NumStabilityTest/Reorganization/R10/OldOnly/NumStability_Algorithms_RandNLA.lean` |
| A | `NumStabilityTest/Reorganization/R10/OldOnly/NumStability_Algorithms_RandNLA_ElementwiseSampling.lean` |
| A | `NumStabilityTest/Reorganization/R10/OldOnly/NumStability_Algorithms_RandNLA_ElementwiseSpectral.lean` |
| A | `NumStabilityTest/Reorganization/R10/OldOnly/NumStability_Algorithms_RandNLA_ElementwiseTraceMGF.lean` |
| A | `NumStabilityTest/Reorganization/R10/OldOnly/NumStability_Algorithms_RandNLA_HitCountConcentration.lean` |
| A | `NumStabilityTest/Reorganization/R10/OldOnly/NumStability_Algorithms_RandNLA_LeastSquaresSketch.lean` |
| A | `NumStabilityTest/Reorganization/R10/OldOnly/NumStability_Algorithms_RandNLA_LowRankApprox.lean` |
| A | `NumStabilityTest/Reorganization/R10/OldOnly/NumStability_Algorithms_RandNLA_Preconditioning.lean` |
| A | `NumStabilityTest/Reorganization/R10/OldOnly/NumStability_Algorithms_RandNLA_RowSampling.lean` |
| A | `NumStabilityTest/Reorganization/R10/OldOnly/NumStability_Algorithms_RandNLA_RowSamplingGram.lean` |
| A | `NumStabilityTest/Reorganization/R10/OldOnly/NumStability_Algorithms_RandNLA_RowSamplingLeverage.lean` |
| A | `NumStabilityTest/Reorganization/R10/OldOnly/NumStability_Algorithms_RandNLA_RowSamplingLeverageComputedBasis.lean` |
| A | `NumStabilityTest/Reorganization/R10/OldOnly/NumStability_Algorithms_RandNLA_RowSamplingLeverageMGF.lean` |
| A | `NumStabilityTest/Reorganization/R10/OldOnly/NumStability_Algorithms_RandNLA_RowSamplingTraceMGF.lean` |
| A | `NumStabilityTest/Reorganization/R10/OldOnly/NumStability_Algorithms_RandNLA_UniformRowSampling.lean` |
| A | `NumStabilityTest/Reorganization/R10/OldOnly/NumStability_Algorithms_RandNLA_UniformRowSamplingComposition.lean` |
| A | `NumStabilityTest/Reorganization/R10/OldOnly/NumStability_Algorithms_RandNLA_UniformRowSamplingFP.lean` |
| A | `NumStabilityTest/Reorganization/R10/OldOnly/NumStability_Algorithms_RandNLA_UniformRowSamplingMGF.lean` |
| A | `NumStabilityTest/Reorganization/R10/PrivateNormalization.lean` |
