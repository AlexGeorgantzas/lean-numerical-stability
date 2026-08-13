# R11 changed paths

Exact status-aware ledger of the R11 worker diff against C0001 `117aa2bb7e61f41e1531a78452f9f7f6cd5b0771`.

Statuses are `M` for a retained historical path that was modified in place and
`A` for a newly added path. No path is deleted and none is Git-renamed, so every
historical import keeps resolving.

| group | modified | added | total |
| --- | ---: | ---: | ---: |
| production | 64 | 5 | 69 |
| tests | 0 | 205 | 205 |
| delivery | 0 | 16 | 16 |
| **total** | **64** | **226** | **290** |

## Production

The five relocated owners become documented import-only wrappers; the reviewed
`Chapter19.Core` outlier is absent from this list because it is preserved
byte-for-byte. Three `Algorithms.QR.Householder*Support` wrappers retarget their
single support import as the frozen route directs; the other 56 keep their exact
existing imports and gain module documentation only.

| status | path |
| --- | --- |
| A | `NumStability/Algorithms/LinearSystems/QR/Householder/PanelApplication.lean` |
| A | `NumStability/Algorithms/LinearSystems/QR/Householder/StoredQR.lean` |
| A | `NumStability/Algorithms/LinearSystems/QR/Householder/TrailingPanels.lean` |
| M | `NumStability/Algorithms/LinearSystems/QR/HouseholderApplySupport.lean` |
| M | `NumStability/Algorithms/LinearSystems/QR/HouseholderQRSupport.lean` |
| M | `NumStability/Algorithms/LinearSystems/QR/HouseholderSpecSupport.lean` |
| M | `NumStability/Algorithms/QR/GivensMatrixStep.lean` |
| M | `NumStability/Algorithms/QR/GivensQR.lean` |
| M | `NumStability/Algorithms/QR/GivensSpec.lean` |
| M | `NumStability/Algorithms/QR/GramSchmidt.lean` |
| M | `NumStability/Algorithms/QR/GramSchmidtPolar.lean` |
| M | `NumStability/Algorithms/QR/Higham19.lean` |
| M | `NumStability/Algorithms/QR/Higham19Alg11CGSRounded.lean` |
| M | `NumStability/Algorithms/QR/Higham19Alg12MGSClosure.lean` |
| M | `NumStability/Algorithms/QR/Higham19Alg12MGSNonbreakdown.lean` |
| M | `NumStability/Algorithms/QR/Higham19Alg12MGSPaddedClosure.lean` |
| M | `NumStability/Algorithms/QR/Higham19Alg12MGSRepair.lean` |
| M | `NumStability/Algorithms/QR/Higham19Alg12MGSRounded.lean` |
| M | `NumStability/Algorithms/QR/Higham19Alg12MGSSourceRate.lean` |
| M | `NumStability/Algorithms/QR/Higham19FormedQ.lean` |
| M | `NumStability/Algorithms/QR/Higham19Labels.lean` |
| M | `NumStability/Algorithms/QR/Higham19Lemma3ActualSequence.lean` |
| M | `NumStability/Algorithms/QR/Higham19Lemma7Gamma4.lean` |
| M | `NumStability/Algorithms/QR/Higham19Lemma9DisjointSweep.lean` |
| M | `NumStability/Algorithms/QR/Higham19PolarNearest.lean` |
| M | `NumStability/Algorithms/QR/Higham19Problem19_10.lean` |
| M | `NumStability/Algorithms/QR/Higham19Problem19_9.lean` |
| M | `NumStability/Algorithms/QR/Higham19Problem6ActualStep.lean` |
| M | `NumStability/Algorithms/QR/Higham19Sensitivity.lean` |
| M | `NumStability/Algorithms/QR/Higham19SensitivityClosure.lean` |
| M | `NumStability/Algorithms/QR/Higham19StoredLoop.lean` |
| M | `NumStability/Algorithms/QR/Higham19StoredLoopAllPivots.lean` |
| M | `NumStability/Algorithms/QR/Higham19StoredLoopStrongModel.lean` |
| M | `NumStability/Algorithms/QR/Higham19SunBischof.lean` |
| M | `NumStability/Algorithms/QR/Higham19Theorem10ActualMatrix.lean` |
| M | `NumStability/Algorithms/QR/Higham19Theorem5Nonbreakdown.lean` |
| M | `NumStability/Algorithms/QR/Higham19Theorem5SourceClosure.lean` |
| M | `NumStability/Algorithms/QR/Higham19Theorem6ActualSource.lean` |
| M | `NumStability/Algorithms/QR/Higham19Thm6ColPivot.lean` |
| M | `NumStability/Algorithms/QR/Higham19Thm6ColPivotFull.lean` |
| M | `NumStability/Algorithms/QR/Higham19Thm6CoxHigham.lean` |
| M | `NumStability/Algorithms/QR/Higham19Thm6CoxHighamAssembly.lean` |
| M | `NumStability/Algorithms/QR/Higham19Thm6CoxHighamConcrete.lean` |
| M | `NumStability/Algorithms/QR/Higham19Thm6CoxHighamFull.lean` |
| M | `NumStability/Algorithms/QR/Higham19Thm6Elementwise.lean` |
| M | `NumStability/Algorithms/QR/Higham19Thm6ElementwiseEntry.lean` |
| M | `NumStability/Algorithms/QR/Higham19Thm6ElementwisePackaged.lean` |
| M | `NumStability/Algorithms/QR/Higham19Thm6Final.lean` |
| M | `NumStability/Algorithms/QR/Higham19Thm6Pivoted.lean` |
| M | `NumStability/Algorithms/QR/Higham19Thm6RowSpecific.lean` |
| M | `NumStability/Algorithms/QR/Higham19Thm6StrongModel.lean` |
| M | `NumStability/Algorithms/QR/Higham19TurnbullAitken.lean` |
| M | `NumStability/Algorithms/QR/Higham19WYApplicationClosure.lean` |
| M | `NumStability/Algorithms/QR/HouseholderApply.lean` |
| M | `NumStability/Algorithms/QR/HouseholderApplySupport.lean` |
| M | `NumStability/Algorithms/QR/HouseholderConstruction2.lean` |
| M | `NumStability/Algorithms/QR/HouseholderMatrixStep.lean` |
| M | `NumStability/Algorithms/QR/HouseholderOneStep.lean` |
| M | `NumStability/Algorithms/QR/HouseholderQApply.lean` |
| M | `NumStability/Algorithms/QR/HouseholderQR.lean` |
| M | `NumStability/Algorithms/QR/HouseholderQRSupport.lean` |
| M | `NumStability/Algorithms/QR/HouseholderReflector.lean` |
| M | `NumStability/Algorithms/QR/HouseholderSpec.lean` |
| M | `NumStability/Algorithms/QR/HouseholderSpecSupport.lean` |
| M | `NumStability/Algorithms/QR/QRSolve.lean` |
| M | `NumStability/Source/Higham/Chapter19/Sensitivity.lean` |
| A | `NumStability/Source/Higham/Chapter19/Sensitivity/Bounds/Results.lean` |
| M | `NumStability/Source/Higham/Chapter19/StoredLoop.lean` |
| A | `NumStability/Source/Higham/Chapter19/StoredLoop/Perturbation/Bridge.lean` |

## Tests

205 added paths: the 204 isolated targets of the frozen
B0003 test plan plus the declaration-free aggregate at
`NumStabilityTest/Reorganization/R11/All.lean`, which is the module the
already-frozen R0003 postimage of `NumStabilityTest.lean` imports.

| status | path |
| --- | --- |
| A | `NumStabilityTest/Reorganization/R11/All.lean` |
| A | `NumStabilityTest/Reorganization/R11/Canonical/NumStability_Algorithms_LinearSystems_QR_Householder_PanelApplication.lean` |
| A | `NumStabilityTest/Reorganization/R11/Canonical/NumStability_Algorithms_LinearSystems_QR_Householder_StoredQR.lean` |
| A | `NumStabilityTest/Reorganization/R11/Canonical/NumStability_Algorithms_LinearSystems_QR_Householder_TrailingPanels.lean` |
| A | `NumStabilityTest/Reorganization/R11/Canonical/NumStability_Source_Higham_Chapter19_Sensitivity_Bounds_Results.lean` |
| A | `NumStabilityTest/Reorganization/R11/Canonical/NumStability_Source_Higham_Chapter19_StoredLoop_Perturbation_Bridge.lean` |
| A | `NumStabilityTest/Reorganization/R11/Consumer/NumStability_Algorithms_LeastSquares_Higham20Theorem20_7.lean` |
| A | `NumStabilityTest/Reorganization/R11/Consumer/NumStability_Algorithms_LeastSquares_LSQRSolve.lean` |
| A | `NumStabilityTest/Reorganization/R11/Consumer/NumStability_Algorithms_LinearSystems_LeastSquares_Basic.lean` |
| A | `NumStabilityTest/Reorganization/R11/Consumer/NumStability_Algorithms_LinearSystems_LeastSquares_Equality_Basic.lean` |
| A | `NumStabilityTest/Reorganization/R11/Consumer/NumStability_Algorithms_LinearSystems_LeastSquares_QRSolve.lean` |
| A | `NumStabilityTest/Reorganization/R11/Consumer/NumStability_Algorithms_LinearSystems_LeastSquares_RowSorting.lean` |
| A | `NumStabilityTest/Reorganization/R11/Consumer/NumStability_Algorithms_LinearSystems_LeastSquares_StoredQR.lean` |
| A | `NumStabilityTest/Reorganization/R11/Consumer/NumStability_Algorithms_LinearSystems_LeastSquares_TraceKernel.lean` |
| A | `NumStabilityTest/Reorganization/R11/Consumer/NumStability_Algorithms_LinearSystems_QR.lean` |
| A | `NumStabilityTest/Reorganization/R11/Consumer/NumStability_Algorithms_LinearSystems_Underdetermined_BackwardError_Normwise_UnderdeterminedSolve.lean` |
| A | `NumStabilityTest/Reorganization/R11/Consumer/NumStability_Algorithms_LinearSystems_Underdetermined_BackwardError_Rowwise_UnderdeterminedSolve.lean` |
| A | `NumStabilityTest/Reorganization/R11/Consumer/NumStability_Algorithms_LinearSystems_Underdetermined_Conditioning_Componentwise_Radius.lean` |
| A | `NumStabilityTest/Reorganization/R11/Consumer/NumStability_Algorithms_LinearSystems_Underdetermined_Conditioning_Componentwise_UnderdeterminedSolve.lean` |
| A | `NumStabilityTest/Reorganization/R11/Consumer/NumStability_Algorithms_LinearSystems_Underdetermined_MinimumNorm_Solvers_UnderdeterminedSolve.lean` |
| A | `NumStabilityTest/Reorganization/R11/Consumer/NumStability_Algorithms_LinearSystems_Underdetermined_MinimumNorm_Specifications_UnderdeterminedSolve.lean` |
| A | `NumStabilityTest/Reorganization/R11/Consumer/NumStability_Algorithms_LinearSystems_Underdetermined_Perturbation_Componentwise_Radius.lean` |
| A | `NumStabilityTest/Reorganization/R11/Consumer/NumStability_Algorithms_LinearSystems_Underdetermined_Perturbation_Componentwise_UnderdeterminedSolve.lean` |
| A | `NumStabilityTest/Reorganization/R11/Consumer/NumStability_Algorithms_LinearSystems_Underdetermined_Perturbation_FixedRadius_Radius.lean` |
| A | `NumStabilityTest/Reorganization/R11/Consumer/NumStability_Algorithms_LinearSystems_Underdetermined_Projectors_ComplementNorm_ProjectorNorm.lean` |
| A | `NumStabilityTest/Reorganization/R11/Consumer/NumStability_Algorithms_LinearSystems_Underdetermined_QR_Foundations_UnderdeterminedSolve.lean` |
| A | `NumStabilityTest/Reorganization/R11/Consumer/NumStability_Algorithms_LinearSystems_Underdetermined_QR_Givens_BackwardError_Core.lean` |
| A | `NumStabilityTest/Reorganization/R11/Consumer/NumStability_Algorithms_LinearSystems_Underdetermined_QR_Givens_StoredReplay_Closure.lean` |
| A | `NumStabilityTest/Reorganization/R11/Consumer/NumStability_Algorithms_LinearSystems_Underdetermined_QR_Givens_StoredReplay_RoundedReplay.lean` |
| A | `NumStabilityTest/Reorganization/R11/Consumer/NumStability_Algorithms_LinearSystems_Underdetermined_QR_ModifiedGramSchmidt_CorrectedRecurrence_Core.lean` |
| A | `NumStabilityTest/Reorganization/R11/Consumer/NumStability_Algorithms_LinearSystems_Underdetermined_QR_ModifiedGramSchmidt_RoundedReplay_RoundedReplay.lean` |
| A | `NumStabilityTest/Reorganization/R11/Consumer/NumStability_Algorithms_LinearSystems_Underdetermined_RankStability_FullRowRank_UnderdeterminedSolve.lean` |
| A | `NumStabilityTest/Reorganization/R11/Consumer/NumStability_Algorithms_LinearSystems_Underdetermined_SeminormalEquations_ForwardError_ActualOutput.lean` |
| A | `NumStabilityTest/Reorganization/R11/Consumer/NumStability_Algorithms_LinearSystems_Underdetermined_SeminormalEquations_ForwardError_Forward.lean` |
| A | `NumStabilityTest/Reorganization/R11/Consumer/NumStability_Algorithms_LinearSystems_Underdetermined_SeminormalEquations_ForwardError_RemainderBounds.lean` |
| A | `NumStabilityTest/Reorganization/R11/Consumer/NumStability_Algorithms_LinearSystems_Underdetermined_SeminormalEquations_ForwardError_UnderdeterminedSolve.lean` |
| A | `NumStabilityTest/Reorganization/R11/Consumer/NumStability_Algorithms_LinearSystems_Underdetermined_SeminormalEquations_HouseholderClosure_Closure.lean` |
| A | `NumStabilityTest/Reorganization/R11/Consumer/NumStability_Algorithms_LinearSystems_Underdetermined_SeminormalEquations_HouseholderClosure_Uniform.lean` |
| A | `NumStabilityTest/Reorganization/R11/Consumer/NumStability_Algorithms_LinearSystems_Underdetermined_SeminormalEquations_QRTransfer_EnvelopeTransfer.lean` |
| A | `NumStabilityTest/Reorganization/R11/Consumer/NumStability_Algorithms_LinearSystems_Underdetermined_SeminormalEquations_QRTransfer_QRMajorant.lean` |
| A | `NumStabilityTest/Reorganization/R11/Consumer/NumStability_Algorithms_LinearSystems_Underdetermined_SeminormalEquations_QRTransfer_Signed.lean` |
| A | `NumStabilityTest/Reorganization/R11/Consumer/NumStability_Algorithms_LinearSystems_Underdetermined_SeminormalEquations_TriangularSolves_EnvelopeTransfer.lean` |
| A | `NumStabilityTest/Reorganization/R11/Consumer/NumStability_Algorithms_LinearSystems_Underdetermined_SeminormalEquations_TriangularSolves_UnderdeterminedSolve.lean` |
| A | `NumStabilityTest/Reorganization/R11/Consumer/NumStability_Algorithms_TestMatrices_Higham28Stewart.lean` |
| A | `NumStabilityTest/Reorganization/R11/Consumer/NumStability_Analysis_Perturbation_LeastSquares_BackwardError.lean` |
| A | `NumStabilityTest/Reorganization/R11/Consumer/NumStability_Analysis_Perturbation_LeastSquares_Basic.lean` |
| A | `NumStabilityTest/Reorganization/R11/Consumer/NumStability_Analysis_Perturbation_LeastSquares_Contract.lean` |
| A | `NumStabilityTest/Reorganization/R11/Consumer/NumStability_Analysis_Perturbation_LeastSquares_Equality_RowwiseBackwardError.lean` |
| A | `NumStabilityTest/Reorganization/R11/Consumer/NumStability_Analysis_TestMatrices_Cauchy_Cauchy.lean` |
| A | `NumStabilityTest/Reorganization/R11/Consumer/NumStability_Analysis_TestMatrices_Cauchy_Contracts.lean` |
| A | `NumStabilityTest/Reorganization/R11/Consumer/NumStability_Analysis_TestMatrices_Companion_Companion.lean` |
| A | `NumStabilityTest/Reorganization/R11/Consumer/NumStability_Analysis_TestMatrices_Companion_CompanionSpectral.lean` |
| A | `NumStabilityTest/Reorganization/R11/Consumer/NumStability_Analysis_TestMatrices_Companion_Contracts.lean` |
| A | `NumStabilityTest/Reorganization/R11/Consumer/NumStability_Analysis_TestMatrices_Orthogonal_OrthogonalFibers.lean` |
| A | `NumStabilityTest/Reorganization/R11/Consumer/NumStability_Analysis_TestMatrices_Pascal_Contracts.lean` |
| A | `NumStabilityTest/Reorganization/R11/Consumer/NumStability_Analysis_TestMatrices_Pascal_PascalDualFlag.lean` |
| A | `NumStabilityTest/Reorganization/R11/Consumer/NumStability_Analysis_TestMatrices_Pascal_PascalOscillation.lean` |
| A | `NumStabilityTest/Reorganization/R11/Consumer/NumStability_Analysis_TestMatrices_Pascal_PascalOscillationCore.lean` |
| A | `NumStabilityTest/Reorganization/R11/Consumer/NumStability_Analysis_TestMatrices_Pascal_PascalSpectral.lean` |
| A | `NumStabilityTest/Reorganization/R11/Consumer/NumStability_Analysis_TestMatrices_Pascal_PascalTotalPositivity.lean` |
| A | `NumStabilityTest/Reorganization/R11/Consumer/NumStability_Analysis_TestMatrices_RandomSVD_Stewart.lean` |
| A | `NumStabilityTest/Reorganization/R11/Consumer/NumStability_Analysis_TestMatrices_RandomSVD_StewartHaar.lean` |
| A | `NumStabilityTest/Reorganization/R11/Consumer/NumStability_Analysis_TestMatrices_RandomSVD_StewartRecursion.lean` |
| A | `NumStabilityTest/Reorganization/R11/Consumer/NumStability_Analysis_TestMatrices_RealGinibre_GinibreRoots.lean` |
| A | `NumStabilityTest/Reorganization/R11/Consumer/NumStability_Analysis_TestMatrices_Toeplitz_Contracts.lean` |
| A | `NumStabilityTest/Reorganization/R11/Consumer/NumStability_Source_DrineasMahoney_RandNLA2016_Equation08_LeastSquaresSketch_Endpoints.lean` |
| A | `NumStabilityTest/Reorganization/R11/Consumer/NumStability_Source_Higham_Chapter19_Algorithm12_MGSPaddedClosure.lean` |
| A | `NumStabilityTest/Reorganization/R11/Consumer/NumStability_Source_Higham_Chapter19_Labels.lean` |
| A | `NumStabilityTest/Reorganization/R11/Consumer/NumStability_Source_Higham_Chapter19_Lemma03_ActualSequence.lean` |
| A | `NumStabilityTest/Reorganization/R11/Consumer/NumStability_Source_Higham_Chapter19_PolarNearest.lean` |
| A | `NumStabilityTest/Reorganization/R11/Consumer/NumStability_Source_Higham_Chapter19_Problem09.lean` |
| A | `NumStabilityTest/Reorganization/R11/Consumer/NumStability_Source_Higham_Chapter19_Sensitivity_Closure.lean` |
| A | `NumStabilityTest/Reorganization/R11/Consumer/NumStability_Source_Higham_Chapter19_StoredLoop_AllPivots.lean` |
| A | `NumStabilityTest/Reorganization/R11/Consumer/NumStability_Source_Higham_Chapter19_StoredLoop_StrongModel.lean` |
| A | `NumStabilityTest/Reorganization/R11/Consumer/NumStability_Source_Higham_Chapter19_Theorem06_CoxHigham.lean` |
| A | `NumStabilityTest/Reorganization/R11/Consumer/NumStability_Source_Higham_Chapter20_Theorem03_QRSolve.lean` |
| A | `NumStabilityTest/Reorganization/R11/Consumer/NumStability_Source_Higham_Chapter20_Theorem07.lean` |
| A | `NumStabilityTest/Reorganization/R11/Consumer/NumStability_Source_Higham_Chapter20_Theorem07_ActualBackSub.lean` |
| A | `NumStabilityTest/Reorganization/R11/Consumer/NumStability_Source_Higham_Chapter20_Theorem07_ActualClosure.lean` |
| A | `NumStabilityTest/Reorganization/R11/Consumer/NumStability_Source_Higham_Chapter20_Theorem07_ActualRhs.lean` |
| A | `NumStabilityTest/Reorganization/R11/Consumer/NumStability_Source_Higham_Chapter20_Theorem07_ActualTrace.lean` |
| A | `NumStabilityTest/Reorganization/R11/Consumer/NumStability_Source_Higham_Chapter20_Theorem07_Contract.lean` |
| A | `NumStabilityTest/Reorganization/R11/Consumer/NumStability_Source_Higham_Chapter20_Theorem07_Elimination.lean` |
| A | `NumStabilityTest/Reorganization/R11/Consumer/NumStability_Source_Higham_Chapter20_Theorem07_QdR.lean` |
| A | `NumStabilityTest/Reorganization/R11/Consumer/NumStability_Source_Higham_Chapter20_Theorem07_RowPolicy.lean` |
| A | `NumStabilityTest/Reorganization/R11/Consumer/NumStability_Source_Higham_Chapter20_Theorem07_SourceTrace.lean` |
| A | `NumStabilityTest/Reorganization/R11/Consumer/NumStability_Source_Higham_Chapter28_Section01_Cauchy_Cauchy.lean` |
| A | `NumStabilityTest/Reorganization/R11/Consumer/NumStability_Source_Higham_Chapter28_Section01_HilbertConditioning_Cauchy.lean` |
| A | `NumStabilityTest/Reorganization/R11/Consumer/NumStability_Source_Higham_Chapter28_Section01_HilbertConditioning_HilbertCondition.lean` |
| A | `NumStabilityTest/Reorganization/R11/Consumer/NumStability_Source_Higham_Chapter28_Section02_RealGinibre_FiniteExpectation_Ginibre.lean` |
| A | `NumStabilityTest/Reorganization/R11/Consumer/NumStability_Source_Higham_Chapter28_Section02_RealGinibre_FiniteExpectation_GinibreAbsoluteDetRecurrence.lean` |
| A | `NumStabilityTest/Reorganization/R11/Consumer/NumStability_Source_Higham_Chapter28_Section02_RealGinibre_FiniteExpectation_GinibreCharacteristicProduct.lean` |
| A | `NumStabilityTest/Reorganization/R11/Consumer/NumStability_Source_Higham_Chapter28_Section02_RealGinibre_FiniteExpectation_GinibreCorollary31Factor.lean` |
| A | `NumStabilityTest/Reorganization/R11/Consumer/NumStability_Source_Higham_Chapter28_Section02_RealGinibre_FiniteExpectation_GinibreDeterminantMoment.lean` |
| A | `NumStabilityTest/Reorganization/R11/Consumer/NumStability_Source_Higham_Chapter28_Section02_RealGinibre_FiniteExpectation_GinibreExpectationGlue.lean` |
| A | `NumStabilityTest/Reorganization/R11/Consumer/NumStability_Source_Higham_Chapter28_Section02_RealGinibre_FiniteExpectation_GinibreFiniteFormula.lean` |
| A | `NumStabilityTest/Reorganization/R11/Consumer/NumStability_Source_Higham_Chapter28_Section02_RealGinibre_FiniteExpectation_GinibreGaussianBridge.lean` |
| A | `NumStabilityTest/Reorganization/R11/Consumer/NumStability_Source_Higham_Chapter28_Section02_RealGinibre_FiniteExpectation_GinibreRecurrence.lean` |
| A | `NumStabilityTest/Reorganization/R11/Consumer/NumStability_Source_Higham_Chapter28_Section02_RealGinibre_FiniteExpectation_GinibreSignedExpectation.lean` |
| A | `NumStabilityTest/Reorganization/R11/Consumer/NumStability_Source_Higham_Chapter28_Section02_RealGinibre_Incidence_GinibreIncidence.lean` |
| A | `NumStabilityTest/Reorganization/R11/Consumer/NumStability_Source_Higham_Chapter28_Section02_RealGinibre_Incidence_GinibrePlaneIncidence.lean` |
| A | `NumStabilityTest/Reorganization/R11/Consumer/NumStability_Source_Higham_Chapter28_Section02_RealGinibre_Incidence_GinibreSignedIncidenceAlgebra.lean` |
| A | `NumStabilityTest/Reorganization/R11/Consumer/NumStability_Source_Higham_Chapter28_Section02_RealGinibre_Incidence_GinibreTruncatedIncidence.lean` |
| A | `NumStabilityTest/Reorganization/R11/Consumer/NumStability_Source_Higham_Chapter28_Section02_RealGinibre_InvariantPlanes_GinibreAtlas.lean` |
| A | `NumStabilityTest/Reorganization/R11/Consumer/NumStability_Source_Higham_Chapter28_Section02_RealGinibre_InvariantPlanes_GinibreComplexPairs.lean` |
| A | `NumStabilityTest/Reorganization/R11/Consumer/NumStability_Source_Higham_Chapter28_Section02_RealGinibre_InvariantPlanes_GinibreDimensionTwo.lean` |
| A | `NumStabilityTest/Reorganization/R11/Consumer/NumStability_Source_Higham_Chapter28_Section02_RealGinibre_InvariantPlanes_GinibreOrthogonalFiber.lean` |
| A | `NumStabilityTest/Reorganization/R11/Consumer/NumStability_Source_Higham_Chapter28_Section02_RealGinibre_InvariantPlanes_GinibrePlaneChart.lean` |
| A | `NumStabilityTest/Reorganization/R11/Consumer/NumStability_Source_Higham_Chapter28_Section02_RealGinibre_InvariantPlanes_GinibrePlaneSylvester.lean` |
| A | `NumStabilityTest/Reorganization/R11/Consumer/NumStability_Source_Higham_Chapter28_Section02_RealGinibre_ProbabilityLaw_GinibreJointDensity.lean` |
| A | `NumStabilityTest/Reorganization/R11/Consumer/NumStability_Source_Higham_Chapter28_Section02_RealGinibre_ProbabilityLaw_GinibreMeasure.lean` |
| A | `NumStabilityTest/Reorganization/R11/Consumer/NumStability_Source_Higham_Chapter28_Section02_RealGinibre_ProbabilityLaw_GinibreTraceDensity.lean` |
| A | `NumStabilityTest/Reorganization/R11/Consumer/NumStability_Source_Higham_Chapter28_Section02_RealGinibre_ProbabilityLaw_Probability.lean` |
| A | `NumStabilityTest/Reorganization/R11/Consumer/NumStability_Source_Higham_Chapter28_Section02_RealGinibre_RootMeasurability_GinibreMultiplicity.lean` |
| A | `NumStabilityTest/Reorganization/R11/Consumer/NumStability_Source_Higham_Chapter28_Section02_RealGinibre_RootMeasurability_GinibreRoots.lean` |
| A | `NumStabilityTest/Reorganization/R11/Consumer/NumStability_Source_Higham_Chapter28_Section02_RealGinibre_SignedIncidence_GinibreParity.lean` |
| A | `NumStabilityTest/Reorganization/R11/Consumer/NumStability_Source_Higham_Chapter28_Section02_RealGinibre_SignedIncidence_GinibreSignedConclusion.lean` |
| A | `NumStabilityTest/Reorganization/R11/Consumer/NumStability_Source_Higham_Chapter28_Section02_RealGinibre_SignedIncidence_GinibreSignedGaussian.lean` |
| A | `NumStabilityTest/Reorganization/R11/Consumer/NumStability_Source_Higham_Chapter28_Section02_RealGinibre_SignedIncidence_GinibreSignedIncidence.lean` |
| A | `NumStabilityTest/Reorganization/R11/Consumer/NumStability_Source_Higham_Chapter28_Section02_RealGinibre_SignedIncidence_GinibreSignedKernel.lean` |
| A | `NumStabilityTest/Reorganization/R11/Consumer/NumStability_Source_Higham_Chapter28_Section02_RealGinibre_SignedIncidence_GinibreSignedRank.lean` |
| A | `NumStabilityTest/Reorganization/R11/Consumer/NumStability_Source_Higham_Chapter28_Section02_RealGinibre_SignedIncidence_GinibreSignedRankTransfer.lean` |
| A | `NumStabilityTest/Reorganization/R11/Consumer/NumStability_Source_Higham_Chapter28_Section02_RealGinibre_SignedIncidence_GinibreSignedScalar.lean` |
| A | `NumStabilityTest/Reorganization/R11/Consumer/NumStability_Source_Higham_Chapter28_Section03_RandomSVD_RandsvdNorm.lean` |
| A | `NumStabilityTest/Reorganization/R11/Consumer/NumStability_Source_Higham_Chapter28_Section03_Theorem01_StewartHaar_GaussianQRHaar.lean` |
| A | `NumStabilityTest/Reorganization/R11/Consumer/NumStability_Source_Higham_Chapter28_Section03_Theorem01_StewartHaar_Stewart.lean` |
| A | `NumStabilityTest/Reorganization/R11/Consumer/NumStability_Source_Higham_Chapter28_Section03_Theorem01_StewartHaar_StewartRawFiber.lean` |
| A | `NumStabilityTest/Reorganization/R11/Consumer/NumStability_Source_Higham_Chapter28_Section04_Pascal_PascalCondition.lean` |
| A | `NumStabilityTest/Reorganization/R11/Consumer/NumStability_Source_Higham_Chapter28_Section04_Pascal_PascalOscillation.lean` |
| A | `NumStabilityTest/Reorganization/R11/Consumer/NumStability_Source_Higham_Chapter28_Section04_Pascal_PascalSpectral.lean` |
| A | `NumStabilityTest/Reorganization/R11/Consumer/NumStability_Source_Higham_Chapter28_Section04_ReciprocalSpectrumSPD_ReciprocalSPD.lean` |
| A | `NumStabilityTest/Reorganization/R11/Consumer/NumStability_Source_Higham_Chapter28_Section05_TridiagonalToeplitz_ToeplitzCondition.lean` |
| A | `NumStabilityTest/Reorganization/R11/Consumer/NumStability_Source_Higham_Chapter28_Section05_TridiagonalToeplitz_ToeplitzGeneral.lean` |
| A | `NumStabilityTest/Reorganization/R11/Consumer/NumStability_Source_Higham_Chapter28_Section06_Companion_Companion.lean` |
| A | `NumStabilityTest/Reorganization/R11/Consumer/NumStability_Source_Higham_Chapter28_Section06_Companion_CompanionSpectral.lean` |
| A | `NumStabilityTest/Reorganization/R11/Focused/NumStability_Algorithms_LinearSystems_QR_Householder_PanelApplication.lean` |
| A | `NumStabilityTest/Reorganization/R11/Focused/NumStability_Algorithms_LinearSystems_QR_Householder_StoredQR.lean` |
| A | `NumStabilityTest/Reorganization/R11/Focused/NumStability_Algorithms_LinearSystems_QR_Householder_TrailingPanels.lean` |
| A | `NumStabilityTest/Reorganization/R11/Focused/NumStability_Source_Higham_Chapter19_Sensitivity_Bounds_Results.lean` |
| A | `NumStabilityTest/Reorganization/R11/Focused/NumStability_Source_Higham_Chapter19_StoredLoop_Perturbation_Bridge.lean` |
| A | `NumStabilityTest/Reorganization/R11/OldOnly/NumStability_Algorithms_LinearSystems_QR_HouseholderApplySupport.lean` |
| A | `NumStabilityTest/Reorganization/R11/OldOnly/NumStability_Algorithms_LinearSystems_QR_HouseholderQRSupport.lean` |
| A | `NumStabilityTest/Reorganization/R11/OldOnly/NumStability_Algorithms_LinearSystems_QR_HouseholderSpecSupport.lean` |
| A | `NumStabilityTest/Reorganization/R11/OldOnly/NumStability_Algorithms_QR_GivensMatrixStep.lean` |
| A | `NumStabilityTest/Reorganization/R11/OldOnly/NumStability_Algorithms_QR_GivensQR.lean` |
| A | `NumStabilityTest/Reorganization/R11/OldOnly/NumStability_Algorithms_QR_GivensSpec.lean` |
| A | `NumStabilityTest/Reorganization/R11/OldOnly/NumStability_Algorithms_QR_GramSchmidt.lean` |
| A | `NumStabilityTest/Reorganization/R11/OldOnly/NumStability_Algorithms_QR_GramSchmidtPolar.lean` |
| A | `NumStabilityTest/Reorganization/R11/OldOnly/NumStability_Algorithms_QR_Higham19.lean` |
| A | `NumStabilityTest/Reorganization/R11/OldOnly/NumStability_Algorithms_QR_Higham19Alg11CGSRounded.lean` |
| A | `NumStabilityTest/Reorganization/R11/OldOnly/NumStability_Algorithms_QR_Higham19Alg12MGSClosure.lean` |
| A | `NumStabilityTest/Reorganization/R11/OldOnly/NumStability_Algorithms_QR_Higham19Alg12MGSNonbreakdown.lean` |
| A | `NumStabilityTest/Reorganization/R11/OldOnly/NumStability_Algorithms_QR_Higham19Alg12MGSPaddedClosure.lean` |
| A | `NumStabilityTest/Reorganization/R11/OldOnly/NumStability_Algorithms_QR_Higham19Alg12MGSRepair.lean` |
| A | `NumStabilityTest/Reorganization/R11/OldOnly/NumStability_Algorithms_QR_Higham19Alg12MGSRounded.lean` |
| A | `NumStabilityTest/Reorganization/R11/OldOnly/NumStability_Algorithms_QR_Higham19Alg12MGSSourceRate.lean` |
| A | `NumStabilityTest/Reorganization/R11/OldOnly/NumStability_Algorithms_QR_Higham19FormedQ.lean` |
| A | `NumStabilityTest/Reorganization/R11/OldOnly/NumStability_Algorithms_QR_Higham19Labels.lean` |
| A | `NumStabilityTest/Reorganization/R11/OldOnly/NumStability_Algorithms_QR_Higham19Lemma3ActualSequence.lean` |
| A | `NumStabilityTest/Reorganization/R11/OldOnly/NumStability_Algorithms_QR_Higham19Lemma7Gamma4.lean` |
| A | `NumStabilityTest/Reorganization/R11/OldOnly/NumStability_Algorithms_QR_Higham19Lemma9DisjointSweep.lean` |
| A | `NumStabilityTest/Reorganization/R11/OldOnly/NumStability_Algorithms_QR_Higham19PolarNearest.lean` |
| A | `NumStabilityTest/Reorganization/R11/OldOnly/NumStability_Algorithms_QR_Higham19Problem19_10.lean` |
| A | `NumStabilityTest/Reorganization/R11/OldOnly/NumStability_Algorithms_QR_Higham19Problem19_9.lean` |
| A | `NumStabilityTest/Reorganization/R11/OldOnly/NumStability_Algorithms_QR_Higham19Problem6ActualStep.lean` |
| A | `NumStabilityTest/Reorganization/R11/OldOnly/NumStability_Algorithms_QR_Higham19Sensitivity.lean` |
| A | `NumStabilityTest/Reorganization/R11/OldOnly/NumStability_Algorithms_QR_Higham19SensitivityClosure.lean` |
| A | `NumStabilityTest/Reorganization/R11/OldOnly/NumStability_Algorithms_QR_Higham19StoredLoop.lean` |
| A | `NumStabilityTest/Reorganization/R11/OldOnly/NumStability_Algorithms_QR_Higham19StoredLoopAllPivots.lean` |
| A | `NumStabilityTest/Reorganization/R11/OldOnly/NumStability_Algorithms_QR_Higham19StoredLoopStrongModel.lean` |
| A | `NumStabilityTest/Reorganization/R11/OldOnly/NumStability_Algorithms_QR_Higham19SunBischof.lean` |
| A | `NumStabilityTest/Reorganization/R11/OldOnly/NumStability_Algorithms_QR_Higham19Theorem10ActualMatrix.lean` |
| A | `NumStabilityTest/Reorganization/R11/OldOnly/NumStability_Algorithms_QR_Higham19Theorem5Nonbreakdown.lean` |
| A | `NumStabilityTest/Reorganization/R11/OldOnly/NumStability_Algorithms_QR_Higham19Theorem5SourceClosure.lean` |
| A | `NumStabilityTest/Reorganization/R11/OldOnly/NumStability_Algorithms_QR_Higham19Theorem6ActualSource.lean` |
| A | `NumStabilityTest/Reorganization/R11/OldOnly/NumStability_Algorithms_QR_Higham19Thm6ColPivot.lean` |
| A | `NumStabilityTest/Reorganization/R11/OldOnly/NumStability_Algorithms_QR_Higham19Thm6ColPivotFull.lean` |
| A | `NumStabilityTest/Reorganization/R11/OldOnly/NumStability_Algorithms_QR_Higham19Thm6CoxHigham.lean` |
| A | `NumStabilityTest/Reorganization/R11/OldOnly/NumStability_Algorithms_QR_Higham19Thm6CoxHighamAssembly.lean` |
| A | `NumStabilityTest/Reorganization/R11/OldOnly/NumStability_Algorithms_QR_Higham19Thm6CoxHighamConcrete.lean` |
| A | `NumStabilityTest/Reorganization/R11/OldOnly/NumStability_Algorithms_QR_Higham19Thm6CoxHighamFull.lean` |
| A | `NumStabilityTest/Reorganization/R11/OldOnly/NumStability_Algorithms_QR_Higham19Thm6Elementwise.lean` |
| A | `NumStabilityTest/Reorganization/R11/OldOnly/NumStability_Algorithms_QR_Higham19Thm6ElementwiseEntry.lean` |
| A | `NumStabilityTest/Reorganization/R11/OldOnly/NumStability_Algorithms_QR_Higham19Thm6ElementwisePackaged.lean` |
| A | `NumStabilityTest/Reorganization/R11/OldOnly/NumStability_Algorithms_QR_Higham19Thm6Final.lean` |
| A | `NumStabilityTest/Reorganization/R11/OldOnly/NumStability_Algorithms_QR_Higham19Thm6Pivoted.lean` |
| A | `NumStabilityTest/Reorganization/R11/OldOnly/NumStability_Algorithms_QR_Higham19Thm6RowSpecific.lean` |
| A | `NumStabilityTest/Reorganization/R11/OldOnly/NumStability_Algorithms_QR_Higham19Thm6StrongModel.lean` |
| A | `NumStabilityTest/Reorganization/R11/OldOnly/NumStability_Algorithms_QR_Higham19TurnbullAitken.lean` |
| A | `NumStabilityTest/Reorganization/R11/OldOnly/NumStability_Algorithms_QR_Higham19WYApplicationClosure.lean` |
| A | `NumStabilityTest/Reorganization/R11/OldOnly/NumStability_Algorithms_QR_HouseholderApply.lean` |
| A | `NumStabilityTest/Reorganization/R11/OldOnly/NumStability_Algorithms_QR_HouseholderApplySupport.lean` |
| A | `NumStabilityTest/Reorganization/R11/OldOnly/NumStability_Algorithms_QR_HouseholderConstruction2.lean` |
| A | `NumStabilityTest/Reorganization/R11/OldOnly/NumStability_Algorithms_QR_HouseholderMatrixStep.lean` |
| A | `NumStabilityTest/Reorganization/R11/OldOnly/NumStability_Algorithms_QR_HouseholderOneStep.lean` |
| A | `NumStabilityTest/Reorganization/R11/OldOnly/NumStability_Algorithms_QR_HouseholderQApply.lean` |
| A | `NumStabilityTest/Reorganization/R11/OldOnly/NumStability_Algorithms_QR_HouseholderQR.lean` |
| A | `NumStabilityTest/Reorganization/R11/OldOnly/NumStability_Algorithms_QR_HouseholderQRSupport.lean` |
| A | `NumStabilityTest/Reorganization/R11/OldOnly/NumStability_Algorithms_QR_HouseholderReflector.lean` |
| A | `NumStabilityTest/Reorganization/R11/OldOnly/NumStability_Algorithms_QR_HouseholderSpec.lean` |
| A | `NumStabilityTest/Reorganization/R11/OldOnly/NumStability_Algorithms_QR_HouseholderSpecSupport.lean` |
| A | `NumStabilityTest/Reorganization/R11/OldOnly/NumStability_Algorithms_QR_QRSolve.lean` |
| A | `NumStabilityTest/Reorganization/R11/OldOnly/NumStability_Source_Higham_Chapter19_Core.lean` |
| A | `NumStabilityTest/Reorganization/R11/OldOnly/NumStability_Source_Higham_Chapter19_Sensitivity.lean` |
| A | `NumStabilityTest/Reorganization/R11/OldOnly/NumStability_Source_Higham_Chapter19_StoredLoop.lean` |

## Delivery evidence

16 added paths under `docs/architecture/deliveries/R11/`.

| status | path |
| --- | --- |
| A | `docs/architecture/deliveries/R11/CHANGED_PATHS.md` |
| A | `docs/architecture/deliveries/R11/CHECK_PROJECTION.py` |
| A | `docs/architecture/deliveries/R11/CHECK_REQUEST_REPLAY.py` |
| A | `docs/architecture/deliveries/R11/CHECK_SCOPE.py` |
| A | `docs/architecture/deliveries/R11/CHECK_STATIC.py` |
| A | `docs/architecture/deliveries/R11/DECLARATION_ROUTES.tsv` |
| A | `docs/architecture/deliveries/R11/DELIVERY.md` |
| A | `docs/architecture/deliveries/R11/GATE_RESULTS.tsv` |
| A | `docs/architecture/deliveries/R11/INTEGRATOR_REQUESTS.md` |
| A | `docs/architecture/deliveries/R11/PRIVATE_CLOSURE.md` |
| A | `docs/architecture/deliveries/R11/PRIVATE_CLOSURE.tsv` |
| A | `docs/architecture/deliveries/R11/PRIVATE_NORMALIZATION.tsv` |
| A | `docs/architecture/deliveries/R11/PROJECTION.md` |
| A | `docs/architecture/deliveries/R11/RETENTION.tsv` |
| A | `docs/architecture/deliveries/R11/ROUTING.md` |
| A | `docs/architecture/deliveries/R11/TEST_MATRIX.tsv` |
