# R05 changed paths

Exact status-aware ledger of the R05 worker diff against C0003 `e20de2f931caa12221e708c341e9cb4f64d29b25`.
No path is deleted and none is Git-renamed.

| group | modified | added | total |
| --- | ---: | ---: | ---: |
| production | 28 | 28 | 56 |
| tests | 0 | 98 | 98 |
| delivery | 0 | 9 | 9 |
| **total** | **28** | **135** | **163** |

## production

| status | path |
| --- | --- |
| A | `NumStability/Algorithms/LinearSystems/Underdetermined/MinimumNorm/Solvers/Executor/Core.lean` |
| A | `NumStability/Algorithms/LinearSystems/Underdetermined/Perturbation/Bounds/Core.lean` |
| A | `NumStability/Algorithms/LinearSystems/Underdetermined/Perturbation/Radius/Core.lean` |
| A | `NumStability/Algorithms/LinearSystems/Underdetermined/QR/Givens/EndToEnd/Core.lean` |
| A | `NumStability/Algorithms/LinearSystems/Underdetermined/QR/Givens/Rounded/Core.lean` |
| M | `NumStability/Algorithms/LinearSystems/Underdetermined/QR/Givens/StoredReplay/Closure.lean` |
| A | `NumStability/Algorithms/LinearSystems/Underdetermined/QR/Givens/StoredReplay/EndToEnd/Core.lean` |
| A | `NumStability/Algorithms/LinearSystems/Underdetermined/QR/ModifiedGramSchmidt/Rounded/Core.lean` |
| A | `NumStability/Algorithms/LinearSystems/Underdetermined/SeminormalEquations/ConditionTransfer/Core.lean` |
| A | `NumStability/Algorithms/LinearSystems/Underdetermined/SeminormalEquations/EndToEnd/Core.lean` |
| M | `NumStability/Algorithms/LinearSystems/Underdetermined/SeminormalEquations/ForwardError/ActualOutput.lean` |
| A | `NumStability/Algorithms/LinearSystems/Underdetermined/SeminormalEquations/ForwardError/ComputedOutput/Core.lean` |
| A | `NumStability/Algorithms/LinearSystems/Underdetermined/SeminormalEquations/Householder/EndToEnd.lean` |
| A | `NumStability/Algorithms/LinearSystems/Underdetermined/SeminormalEquations/Householder/Uniform.lean` |
| M | `NumStability/Algorithms/LinearSystems/Underdetermined/SeminormalEquations/HouseholderClosure/Closure.lean` |
| M | `NumStability/Algorithms/LinearSystems/Underdetermined/SeminormalEquations/HouseholderClosure/Uniform.lean` |
| A | `NumStability/Algorithms/LinearSystems/Underdetermined/SeminormalEquations/Uniform/Core.lean` |
| M | `NumStability/Algorithms/Underdetermined/Higham21Attainability.lean` |
| M | `NumStability/Algorithms/Underdetermined/Higham21Eq21_11Uniform.lean` |
| M | `NumStability/Algorithms/Underdetermined/Higham21Eq21_8.lean` |
| M | `NumStability/Algorithms/Underdetermined/Higham21Eq21_9.lean` |
| M | `NumStability/Algorithms/Underdetermined/Higham21Equation21_11.lean` |
| M | `NumStability/Algorithms/Underdetermined/Higham21Equation21_11Scalar.lean` |
| M | `NumStability/Algorithms/Underdetermined/Higham21GivensClosure.lean` |
| M | `NumStability/Algorithms/Underdetermined/Higham21GivensRounded.lean` |
| M | `NumStability/Algorithms/Underdetermined/Higham21MGSRounded.lean` |
| M | `NumStability/Algorithms/Underdetermined/Higham21Perturbation.lean` |
| M | `NumStability/Algorithms/Underdetermined/Higham21PerturbationRadius.lean` |
| M | `NumStability/Algorithms/Underdetermined/Higham21SNEClosure.lean` |
| M | `NumStability/Algorithms/Underdetermined/Higham21SNEConditionTransfer.lean` |
| M | `NumStability/Algorithms/Underdetermined/Higham21SNEUniform.lean` |
| M | `NumStability/Algorithms/Underdetermined/Higham21Theorem214SourceClosure.lean` |
| M | `NumStability/Algorithms/Underdetermined/UnderdeterminedSolve.lean` |
| M | `NumStability/Source/Higham/Chapter20/Equations.lean` |
| A | `NumStability/Source/Higham/Chapter20/Equations/Core/Results.lean` |
| M | `NumStability/Source/Higham/Chapter20/Lemma11.lean` |
| A | `NumStability/Source/Higham/Chapter20/Lemma11/Core/Results.lean` |
| M | `NumStability/Source/Higham/Chapter20/Prose.lean` |
| A | `NumStability/Source/Higham/Chapter20/Prose/Core/Results.lean` |
| M | `NumStability/Source/Higham/Chapter20/Theorem03.lean` |
| A | `NumStability/Source/Higham/Chapter20/Theorem03/Core/Results.lean` |
| M | `NumStability/Source/Higham/Chapter20/Theorem04.lean` |
| A | `NumStability/Source/Higham/Chapter20/Theorem04/Core/Results.lean` |
| M | `NumStability/Source/Higham/Chapter20/Theorem07.lean` |
| A | `NumStability/Source/Higham/Chapter20/Theorem07/Core/Results.lean` |
| M | `NumStability/Source/Higham/Chapter20/Theorem08.lean` |
| A | `NumStability/Source/Higham/Chapter20/Theorem08/Core/Results.lean` |
| A | `NumStability/Source/Higham/Chapter21/Attainability/Results.lean` |
| A | `NumStability/Source/Higham/Chapter21/Corrections/CorrectedMGS/RoundedReplay.lean` |
| M | `NumStability/Source/Higham/Chapter21/Corrections/Problem19_12/RoundedReplay.lean` |
| A | `NumStability/Source/Higham/Chapter21/Equation08/Results/Core.lean` |
| A | `NumStability/Source/Higham/Chapter21/Equation09/Results/Core.lean` |
| A | `NumStability/Source/Higham/Chapter21/Equation11/Results/Core.lean` |
| A | `NumStability/Source/Higham/Chapter21/Equation11/ScalarCase/Core.lean` |
| A | `NumStability/Source/Higham/Chapter21/Equation11/UniformEnvelope/Core.lean` |
| A | `NumStability/Source/Higham/Chapter21/Theorem04/SourceClosure/Supplement/Core.lean` |

## tests

| status | path |
| --- | --- |
| A | `NumStabilityTest/Reorganization/R05/Aggregate/NumStability.lean` |
| A | `NumStabilityTest/Reorganization/R05/All.lean` |
| A | `NumStabilityTest/Reorganization/R05/Canonical/NumStability_Algorithms_LinearSystems_Underdetermined_MinimumNorm_Solvers_Executor_Core.lean` |
| A | `NumStabilityTest/Reorganization/R05/Canonical/NumStability_Algorithms_LinearSystems_Underdetermined_Perturbation_Bounds_Core.lean` |
| A | `NumStabilityTest/Reorganization/R05/Canonical/NumStability_Algorithms_LinearSystems_Underdetermined_Perturbation_Radius_Core.lean` |
| A | `NumStabilityTest/Reorganization/R05/Canonical/NumStability_Algorithms_LinearSystems_Underdetermined_QR_Givens_EndToEnd_Core.lean` |
| A | `NumStabilityTest/Reorganization/R05/Canonical/NumStability_Algorithms_LinearSystems_Underdetermined_QR_Givens_Rounded_Core.lean` |
| A | `NumStabilityTest/Reorganization/R05/Canonical/NumStability_Algorithms_LinearSystems_Underdetermined_QR_Givens_StoredReplay_EndToEnd_Core.lean` |
| A | `NumStabilityTest/Reorganization/R05/Canonical/NumStability_Algorithms_LinearSystems_Underdetermined_QR_ModifiedGramSchmidt_Rounded_Core.lean` |
| A | `NumStabilityTest/Reorganization/R05/Canonical/NumStability_Algorithms_LinearSystems_Underdetermined_SeminormalEquations_ConditionTransfer_Core.lean` |
| A | `NumStabilityTest/Reorganization/R05/Canonical/NumStability_Algorithms_LinearSystems_Underdetermined_SeminormalEquations_EndToEnd_Core.lean` |
| A | `NumStabilityTest/Reorganization/R05/Canonical/NumStability_Algorithms_LinearSystems_Underdetermined_SeminormalEquations_ForwardError_ComputedOutput_Core.lean` |
| A | `NumStabilityTest/Reorganization/R05/Canonical/NumStability_Algorithms_LinearSystems_Underdetermined_SeminormalEquations_Householder_EndToEnd.lean` |
| A | `NumStabilityTest/Reorganization/R05/Canonical/NumStability_Algorithms_LinearSystems_Underdetermined_SeminormalEquations_Householder_Uniform.lean` |
| A | `NumStabilityTest/Reorganization/R05/Canonical/NumStability_Algorithms_LinearSystems_Underdetermined_SeminormalEquations_Uniform_Core.lean` |
| A | `NumStabilityTest/Reorganization/R05/Canonical/NumStability_Source_Higham_Chapter20_Equations_Core_Results.lean` |
| A | `NumStabilityTest/Reorganization/R05/Canonical/NumStability_Source_Higham_Chapter20_Lemma11_Core_Results.lean` |
| A | `NumStabilityTest/Reorganization/R05/Canonical/NumStability_Source_Higham_Chapter20_Prose_Core_Results.lean` |
| A | `NumStabilityTest/Reorganization/R05/Canonical/NumStability_Source_Higham_Chapter20_Theorem03_Core_Results.lean` |
| A | `NumStabilityTest/Reorganization/R05/Canonical/NumStability_Source_Higham_Chapter20_Theorem04_Core_Results.lean` |
| A | `NumStabilityTest/Reorganization/R05/Canonical/NumStability_Source_Higham_Chapter20_Theorem07_Core_Results.lean` |
| A | `NumStabilityTest/Reorganization/R05/Canonical/NumStability_Source_Higham_Chapter20_Theorem08_Core_Results.lean` |
| A | `NumStabilityTest/Reorganization/R05/Canonical/NumStability_Source_Higham_Chapter21_Attainability_Results.lean` |
| A | `NumStabilityTest/Reorganization/R05/Canonical/NumStability_Source_Higham_Chapter21_Corrections_CorrectedMGS_RoundedReplay.lean` |
| A | `NumStabilityTest/Reorganization/R05/Canonical/NumStability_Source_Higham_Chapter21_Equation08_Results_Core.lean` |
| A | `NumStabilityTest/Reorganization/R05/Canonical/NumStability_Source_Higham_Chapter21_Equation09_Results_Core.lean` |
| A | `NumStabilityTest/Reorganization/R05/Canonical/NumStability_Source_Higham_Chapter21_Equation11_Results_Core.lean` |
| A | `NumStabilityTest/Reorganization/R05/Canonical/NumStability_Source_Higham_Chapter21_Equation11_ScalarCase_Core.lean` |
| A | `NumStabilityTest/Reorganization/R05/Canonical/NumStability_Source_Higham_Chapter21_Equation11_UniformEnvelope_Core.lean` |
| A | `NumStabilityTest/Reorganization/R05/Canonical/NumStability_Source_Higham_Chapter21_Theorem04_SourceClosure_Supplement_Core.lean` |
| A | `NumStabilityTest/Reorganization/R05/Consumer/NumStability_Algorithms.lean` |
| A | `NumStabilityTest/Reorganization/R05/Consumer/NumStability_Algorithms_LeastSquares_Higham20ZeroDeltaB.lean` |
| A | `NumStabilityTest/Reorganization/R05/Consumer/NumStability_Algorithms_LinearSystems.lean` |
| A | `NumStabilityTest/Reorganization/R05/Consumer/NumStability_Algorithms_LinearSystems_Underdetermined_SeminormalEquations_QRTransfer_EnvelopeTransfer.lean` |
| A | `NumStabilityTest/Reorganization/R05/Consumer/NumStability_Source_Higham_Chapter20_Theorem03_ZeroDeltaB.lean` |
| A | `NumStabilityTest/Reorganization/R05/Consumer/NumStability_Source_Higham_Chapter21.lean` |
| A | `NumStabilityTest/Reorganization/R05/Consumer/NumStability_Source_Higham_Chapter21_Equation10_Closure.lean` |
| A | `NumStabilityTest/Reorganization/R05/Consumer/NumStability_Source_Higham_Chapter21_Equation11_ActualOutput.lean` |
| A | `NumStabilityTest/Reorganization/R05/Consumer/NumStability_Source_Higham_Chapter21_Equation11_Closure.lean` |
| A | `NumStabilityTest/Reorganization/R05/Consumer/NumStability_Source_Higham_Chapter21_RowScalingInvariance.lean` |
| A | `NumStabilityTest/Reorganization/R05/Consumer/NumStability_Source_Higham_Chapter21_Theorem03_Attainment.lean` |
| A | `NumStabilityTest/Reorganization/R05/Consumer/NumStability_Source_Higham_Chapter21_Theorem04_GivensQMethod_Closure.lean` |
| A | `NumStabilityTest/Reorganization/R05/Consumer/NumStability_Source_Higham_Chapter21_Theorem04_ModifiedGramSchmidtQMethod_RoundedReplay.lean` |
| A | `NumStabilityTest/Reorganization/R05/Consumer/NumStability_Source_Higham_Chapter21_Theorem04_RowwiseBackwardError.lean` |
| A | `NumStabilityTest/Reorganization/R05/Consumer/NumStability_Source_Higham_Chapter21_Theorem04_SeminormalEquations_ActualOutput.lean` |
| A | `NumStabilityTest/Reorganization/R05/Consumer/NumStability_Source_Higham_Chapter21_Theorem04_SeminormalEquations_Closure.lean` |
| A | `NumStabilityTest/Reorganization/R05/Consumer/NumStability_Source_Higham_Chapter21_Theorem04_SeminormalEquations_EnvelopeTransfer.lean` |
| A | `NumStabilityTest/Reorganization/R05/Consumer/NumStability_Source_Higham_Chapter21_Theorem04_SeminormalEquations_Uniform.lean` |
| A | `NumStabilityTest/Reorganization/R05/Consumer/NumStability_Source_Higham_Chapter21_Theorem04_SourceClosure_SourceClosure.lean` |
| A | `NumStabilityTest/Reorganization/R05/OldOnly/NumStability_Algorithms_LinearSystems_LeastSquares_Equality_Basic.lean` |
| A | `NumStabilityTest/Reorganization/R05/OldOnly/NumStability_Algorithms_LinearSystems_Underdetermined_QR_Givens_StoredReplay_Closure.lean` |
| A | `NumStabilityTest/Reorganization/R05/OldOnly/NumStability_Algorithms_LinearSystems_Underdetermined_SeminormalEquations_ForwardError_ActualOutput.lean` |
| A | `NumStabilityTest/Reorganization/R05/OldOnly/NumStability_Algorithms_LinearSystems_Underdetermined_SeminormalEquations_HouseholderClosure_Closure.lean` |
| A | `NumStabilityTest/Reorganization/R05/OldOnly/NumStability_Algorithms_LinearSystems_Underdetermined_SeminormalEquations_HouseholderClosure_Uniform.lean` |
| A | `NumStabilityTest/Reorganization/R05/OldOnly/NumStability_Algorithms_Underdetermined_Higham21.lean` |
| A | `NumStabilityTest/Reorganization/R05/OldOnly/NumStability_Algorithms_Underdetermined_Higham21Attainability.lean` |
| A | `NumStabilityTest/Reorganization/R05/OldOnly/NumStability_Algorithms_Underdetermined_Higham21Eq21_11Uniform.lean` |
| A | `NumStabilityTest/Reorganization/R05/OldOnly/NumStability_Algorithms_Underdetermined_Higham21Eq21_8.lean` |
| A | `NumStabilityTest/Reorganization/R05/OldOnly/NumStability_Algorithms_Underdetermined_Higham21Eq21_9.lean` |
| A | `NumStabilityTest/Reorganization/R05/OldOnly/NumStability_Algorithms_Underdetermined_Higham21Equation21_11.lean` |
| A | `NumStabilityTest/Reorganization/R05/OldOnly/NumStability_Algorithms_Underdetermined_Higham21Equation21_11Scalar.lean` |
| A | `NumStabilityTest/Reorganization/R05/OldOnly/NumStability_Algorithms_Underdetermined_Higham21Givens.lean` |
| A | `NumStabilityTest/Reorganization/R05/OldOnly/NumStability_Algorithms_Underdetermined_Higham21GivensClosure.lean` |
| A | `NumStabilityTest/Reorganization/R05/OldOnly/NumStability_Algorithms_Underdetermined_Higham21GivensRounded.lean` |
| A | `NumStabilityTest/Reorganization/R05/OldOnly/NumStability_Algorithms_Underdetermined_Higham21MGS.lean` |
| A | `NumStabilityTest/Reorganization/R05/OldOnly/NumStability_Algorithms_Underdetermined_Higham21MGSRounded.lean` |
| A | `NumStabilityTest/Reorganization/R05/OldOnly/NumStability_Algorithms_Underdetermined_Higham21Perturbation.lean` |
| A | `NumStabilityTest/Reorganization/R05/OldOnly/NumStability_Algorithms_Underdetermined_Higham21PerturbationRadius.lean` |
| A | `NumStabilityTest/Reorganization/R05/OldOnly/NumStability_Algorithms_Underdetermined_Higham21ProjectorNorm.lean` |
| A | `NumStabilityTest/Reorganization/R05/OldOnly/NumStability_Algorithms_Underdetermined_Higham21QRFoundations.lean` |
| A | `NumStabilityTest/Reorganization/R05/OldOnly/NumStability_Algorithms_Underdetermined_Higham21RankStability.lean` |
| A | `NumStabilityTest/Reorganization/R05/OldOnly/NumStability_Algorithms_Underdetermined_Higham21SNEActualOutput.lean` |
| A | `NumStabilityTest/Reorganization/R05/OldOnly/NumStability_Algorithms_Underdetermined_Higham21SNEClosure.lean` |
| A | `NumStabilityTest/Reorganization/R05/OldOnly/NumStability_Algorithms_Underdetermined_Higham21SNEConditionTransfer.lean` |
| A | `NumStabilityTest/Reorganization/R05/OldOnly/NumStability_Algorithms_Underdetermined_Higham21SNEEnvelopeTransfer.lean` |
| A | `NumStabilityTest/Reorganization/R05/OldOnly/NumStability_Algorithms_Underdetermined_Higham21SNEForward.lean` |
| A | `NumStabilityTest/Reorganization/R05/OldOnly/NumStability_Algorithms_Underdetermined_Higham21SNEQRMajorant.lean` |
| A | `NumStabilityTest/Reorganization/R05/OldOnly/NumStability_Algorithms_Underdetermined_Higham21SNERemainderBounds.lean` |
| A | `NumStabilityTest/Reorganization/R05/OldOnly/NumStability_Algorithms_Underdetermined_Higham21SNESigned.lean` |
| A | `NumStabilityTest/Reorganization/R05/OldOnly/NumStability_Algorithms_Underdetermined_Higham21SNEUniform.lean` |
| A | `NumStabilityTest/Reorganization/R05/OldOnly/NumStability_Algorithms_Underdetermined_Higham21Theorem214SourceClosure.lean` |
| A | `NumStabilityTest/Reorganization/R05/OldOnly/NumStability_Algorithms_Underdetermined_UnderdeterminedSolve.lean` |
| A | `NumStabilityTest/Reorganization/R05/OldOnly/NumStability_Algorithms_Underdetermined_UnderdeterminedSpec.lean` |
| A | `NumStabilityTest/Reorganization/R05/OldOnly/NumStability_Analysis_Perturbation_LeastSquares_BackwardError.lean` |
| A | `NumStabilityTest/Reorganization/R05/OldOnly/NumStability_Analysis_Perturbation_LeastSquares_Basic.lean` |
| A | `NumStabilityTest/Reorganization/R05/OldOnly/NumStability_Analysis_Perturbation_LeastSquares_Equality_MixedStability.lean` |
| A | `NumStabilityTest/Reorganization/R05/OldOnly/NumStability_Analysis_Perturbation_LeastSquares_Equality_Perturbation.lean` |
| A | `NumStabilityTest/Reorganization/R05/OldOnly/NumStability_Analysis_Perturbation_LeastSquares_Equality_RowwiseBackwardError.lean` |
| A | `NumStabilityTest/Reorganization/R05/OldOnly/NumStability_Source_Higham_Chapter20_Equations.lean` |
| A | `NumStabilityTest/Reorganization/R05/OldOnly/NumStability_Source_Higham_Chapter20_Lemma11.lean` |
| A | `NumStabilityTest/Reorganization/R05/OldOnly/NumStability_Source_Higham_Chapter20_Prose.lean` |
| A | `NumStabilityTest/Reorganization/R05/OldOnly/NumStability_Source_Higham_Chapter20_Theorem03.lean` |
| A | `NumStabilityTest/Reorganization/R05/OldOnly/NumStability_Source_Higham_Chapter20_Theorem03_QRSolve.lean` |
| A | `NumStabilityTest/Reorganization/R05/OldOnly/NumStability_Source_Higham_Chapter20_Theorem04.lean` |
| A | `NumStabilityTest/Reorganization/R05/OldOnly/NumStability_Source_Higham_Chapter20_Theorem07.lean` |
| A | `NumStabilityTest/Reorganization/R05/OldOnly/NumStability_Source_Higham_Chapter20_Theorem08.lean` |
| A | `NumStabilityTest/Reorganization/R05/OldOnly/NumStability_Source_Higham_Chapter21_Corrections_Problem19_12_RoundedReplay.lean` |
| A | `NumStabilityTest/Reorganization/R05/PrivateNormalization.lean` |

## delivery

| status | path |
| --- | --- |
| A | `docs/architecture/deliveries/R05/CHANGED_PATHS.md` |
| A | `docs/architecture/deliveries/R05/DECLARATION_ROUTES.tsv` |
| A | `docs/architecture/deliveries/R05/DELIVERY.md` |
| A | `docs/architecture/deliveries/R05/GATE_RESULTS.tsv` |
| A | `docs/architecture/deliveries/R05/PRIVATE_CLOSURE.tsv` |
| A | `docs/architecture/deliveries/R05/PRIVATE_NORMALIZATION.tsv` |
| A | `docs/architecture/deliveries/R05/PROJECTION.md` |
| A | `docs/architecture/deliveries/R05/RETENTION.tsv` |
| A | `docs/architecture/deliveries/R05/TEST_MATRIX.tsv` |
