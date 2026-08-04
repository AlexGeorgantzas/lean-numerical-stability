# W09 changed paths

Branch `codex/reorg-2026-08-w09-test-matrices-ch28`, base `a32095e6e50189f7dcc39312bb4c6a36f421fab5`.

* **72** modified files
* **294** new files

## Authority

`apply.py` refuses to write until every target is either an owned path or under an authorized destination prefix, reading B0009 itself and honouring each entry's declared `match` kind. `NumStability/Algorithms.lean` and `NumStability/Algorithms/LinearSystems/LeastSquares/Equality/Basic.lean` are integrator-owned and are rejected outright. Zero unauthorized targets were found.

New destination modules need **no aggregator edit**: every owner remains a compatibility module importing its own destinations, and the aggregators already import the owners. That is what keeps the integrator-owned files untouched.

## Modified (historical owners rewritten as compatibility modules)

* `NumStability/Algorithms/TestMatrices/Higham28.lean`
* `NumStability/Algorithms/TestMatrices/Higham28Asymptotics.lean`
* `NumStability/Algorithms/TestMatrices/Higham28Cauchy.lean`
* `NumStability/Algorithms/TestMatrices/Higham28Companion.lean`
* `NumStability/Algorithms/TestMatrices/Higham28CompanionSpectral.lean`
* `NumStability/Algorithms/TestMatrices/Higham28Contracts.lean`
* `NumStability/Algorithms/TestMatrices/Higham28Exact.lean`
* `NumStability/Algorithms/TestMatrices/Higham28GaussianDirection.lean`
* `NumStability/Algorithms/TestMatrices/Higham28GaussianOrthogonal.lean`
* `NumStability/Algorithms/TestMatrices/Higham28GaussianQRHaar.lean`
* `NumStability/Algorithms/TestMatrices/Higham28Ginibre.lean`
* `NumStability/Algorithms/TestMatrices/Higham28GinibreAbsoluteDetRecurrence.lean`
* `NumStability/Algorithms/TestMatrices/Higham28GinibreAtlas.lean`
* `NumStability/Algorithms/TestMatrices/Higham28GinibreCharacteristicProduct.lean`
* `NumStability/Algorithms/TestMatrices/Higham28GinibreComplexPairs.lean`
* `NumStability/Algorithms/TestMatrices/Higham28GinibreCorollary31Factor.lean`
* `NumStability/Algorithms/TestMatrices/Higham28GinibreDeterminantIntegral.lean`
* `NumStability/Algorithms/TestMatrices/Higham28GinibreDeterminantMoment.lean`
* `NumStability/Algorithms/TestMatrices/Higham28GinibreDimensionTwo.lean`
* `NumStability/Algorithms/TestMatrices/Higham28GinibreExpectationGlue.lean`
* `NumStability/Algorithms/TestMatrices/Higham28GinibreFiniteFormula.lean`
* `NumStability/Algorithms/TestMatrices/Higham28GinibreGaussianBridge.lean`
* `NumStability/Algorithms/TestMatrices/Higham28GinibreIncidence.lean`
* `NumStability/Algorithms/TestMatrices/Higham28GinibreIntegral.lean`
* `NumStability/Algorithms/TestMatrices/Higham28GinibreJointDensity.lean`
* `NumStability/Algorithms/TestMatrices/Higham28GinibreMeasure.lean`
* `NumStability/Algorithms/TestMatrices/Higham28GinibreMultiplicity.lean`
* `NumStability/Algorithms/TestMatrices/Higham28GinibreOrthogonalFiber.lean`
* `NumStability/Algorithms/TestMatrices/Higham28GinibreParity.lean`
* `NumStability/Algorithms/TestMatrices/Higham28GinibrePlaneChart.lean`
* `NumStability/Algorithms/TestMatrices/Higham28GinibrePlaneIncidence.lean`
* `NumStability/Algorithms/TestMatrices/Higham28GinibrePlaneSylvester.lean`
* `NumStability/Algorithms/TestMatrices/Higham28GinibreProjectiveIntegral.lean`
* `NumStability/Algorithms/TestMatrices/Higham28GinibreRecurrence.lean`
* `NumStability/Algorithms/TestMatrices/Higham28GinibreRoots.lean`
* `NumStability/Algorithms/TestMatrices/Higham28GinibreSignedConclusion.lean`
* `NumStability/Algorithms/TestMatrices/Higham28GinibreSignedExpectation.lean`
* `NumStability/Algorithms/TestMatrices/Higham28GinibreSignedGaussian.lean`
* `NumStability/Algorithms/TestMatrices/Higham28GinibreSignedIncidence.lean`
* `NumStability/Algorithms/TestMatrices/Higham28GinibreSignedIncidenceAlgebra.lean`
* `NumStability/Algorithms/TestMatrices/Higham28GinibreSignedKernel.lean`
* `NumStability/Algorithms/TestMatrices/Higham28GinibreSignedRank.lean`
* `NumStability/Algorithms/TestMatrices/Higham28GinibreSignedRankTransfer.lean`
* `NumStability/Algorithms/TestMatrices/Higham28GinibreSignedScalar.lean`
* `NumStability/Algorithms/TestMatrices/Higham28GinibreTraceDensity.lean`
* `NumStability/Algorithms/TestMatrices/Higham28GinibreTruncatedIncidence.lean`
* `NumStability/Algorithms/TestMatrices/Higham28HilbertAsymptotic.lean`
* `NumStability/Algorithms/TestMatrices/Higham28HilbertCondition.lean`
* `NumStability/Algorithms/TestMatrices/Higham28Moments.lean`
* `NumStability/Algorithms/TestMatrices/Higham28OrthogonalCoordinates.lean`
* `NumStability/Algorithms/TestMatrices/Higham28OrthogonalFibers.lean`
* `NumStability/Algorithms/TestMatrices/Higham28OrthogonalHaar.lean`
* `NumStability/Algorithms/TestMatrices/Higham28OrthogonalSphere.lean`
* `NumStability/Algorithms/TestMatrices/Higham28Pascal.lean`
* `NumStability/Algorithms/TestMatrices/Higham28PascalCondition.lean`
* `NumStability/Algorithms/TestMatrices/Higham28PascalDualFlag.lean`
* `NumStability/Algorithms/TestMatrices/Higham28PascalOscillation.lean`
* `NumStability/Algorithms/TestMatrices/Higham28PascalOscillationCore.lean`
* `NumStability/Algorithms/TestMatrices/Higham28PascalOscillationExact.lean`
* `NumStability/Algorithms/TestMatrices/Higham28PascalSpectral.lean`
* `NumStability/Algorithms/TestMatrices/Higham28PascalTotalPositivity.lean`
* `NumStability/Algorithms/TestMatrices/Higham28Probability.lean`
* `NumStability/Algorithms/TestMatrices/Higham28RandsvdNorm.lean`
* `NumStability/Algorithms/TestMatrices/Higham28ReciprocalSPD.lean`
* `NumStability/Algorithms/TestMatrices/Higham28ShiftedHilbert.lean`
* `NumStability/Algorithms/TestMatrices/Higham28Stewart.lean`
* `NumStability/Algorithms/TestMatrices/Higham28StewartHaar.lean`
* `NumStability/Algorithms/TestMatrices/Higham28StewartRawFiber.lean`
* `NumStability/Algorithms/TestMatrices/Higham28StewartRecursion.lean`
* `NumStability/Algorithms/TestMatrices/Higham28ToeplitzCondition.lean`
* `NumStability/Algorithms/TestMatrices/Higham28ToeplitzGeneral.lean`
* `NumStability/Algorithms/TestMatrices/Higham28ToeplitzSpectrum.lean`

## New files

* 10 delivery evidence
* 93 destination modules
* 191 tests
