# R02 changed paths

Every path lies inside B0002's owned paths, its exact
destination prefixes, or the R02 test and delivery prefixes. `apply.py` enforces
this by reading B0002 and honouring each entry's declared `match` kind; it
reported 0 unauthorized targets over all 42 emitted Lean files.

| class | paths |
| --- | ---: |
| R02 evidence | 8 |
| R02 test | 63 |
| historical wrapper | 26 |
| reusable destination | 4 |
| source destination | 12 |
| **total** | **113** |

## Integrator-owned files: untouched

`NumStability/Algorithms.lean`, `NumStability/Analysis/MatrixAlgebra.lean`, the
five shared consumers named in `INTEGRATOR_REQUESTS.md`, and every control
registry are unmodified; `git status` shows none of them.

## All paths

- `NumStability/Algorithms/Ch15CondEstimators.lean`
- `NumStability/Algorithms/Ch15DixonClosure.lean`
- `NumStability/Algorithms/Ch15DixonProbability.lean`
- `NumStability/Algorithms/Chapter15CondEst.lean`
- `NumStability/Algorithms/HighamChapter15BoydBridges.lean`
- `NumStability/Algorithms/HighamChapter15BoydConcreteLemma3.lean`
- `NumStability/Algorithms/HighamChapter15BoydLocalStability.lean`
- `NumStability/Algorithms/HighamChapter15BoydRowwiseDomain.lean`
- `NumStability/Algorithms/HighamChapter15BoydScalar.lean`
- `NumStability/Algorithms/HighamChapter15BoydSourceClosure.lean`
- `NumStability/Algorithms/HighamChapter15BoydSourceDomain.lean`
- `NumStability/Algorithms/HighamChapter15BoydSourceLocal.lean`
- `NumStability/Algorithms/HighamChapter15BoydSourceSecondDerivative.lean`
- `NumStability/Algorithms/HighamChapter15BoydUniqueness.lean`
- `NumStability/Algorithms/HighamChapter15ConvergenceProse.lean`
- `NumStability/Algorithms/HighamChapter15RectTermination.lean`
- `NumStability/Algorithms/LU/Higham15Problem15_4.lean`
- `NumStability/Algorithms/LU/Higham15Problem15_6.lean`
- `NumStability/Algorithms/LU/Higham15Problem15_6Closure.lean`
- `NumStability/Algorithms/LU/Higham15Problem15_6Operational.lean`
- `NumStability/Algorithms/LU/TridiagonalCondCh15.lean`
- `NumStability/Algorithms/LU/TridiagonalCondCh15Closure.lean`
- `NumStability/Algorithms/LU/TridiagonalCondCh15IkebeClosure.lean`
- `NumStability/Algorithms/NormEstimation/PNorm/Endpoints/ConvergenceStatements.lean`
- `NumStability/Algorithms/NormEstimation/PNorm/Endpoints/PNormRectangular.lean`
- `NumStability/Algorithms/NormEstimation/PNorm/OneAndInfinityNorms/Rectangular.lean`
- `NumStability/Algorithms/NormEstimation/PNorm/OneAndInfinityNorms/Square.lean`
- `NumStability/Algorithms/PNormPowerMethod.lean`
- `NumStability/Algorithms/PNormPowerMethodGeneralP.lean`
- `NumStability/Algorithms/PNormPowerMethodRect.lean`
- `NumStability/Source/Higham/Chapter15/Algorithm04/LAPACKNormEstimator/ConditionEstimate/Bounds.lean`
- `NumStability/Source/Higham/Chapter15/Algorithm05/LINPACKConditionEstimator/InverseNormBound/TriangularSolve.lean`
- `NumStability/Source/Higham/Chapter15/Problem06/TridiagonalInverseNorm/Recurrences/ArrayExecution.lean`
- `NumStability/Source/Higham/Chapter15/Problem06/TridiagonalInverseNorm/Recurrences/EntryFormulas.lean`
- `NumStability/Source/Higham/Chapter15/Problem06/TridiagonalInverseNorm/Recurrences/FactorizationAndNorm.lean`
- `NumStability/Source/Higham/Chapter15/Section02/Boyd/EndpointTermination/InfinityCounterexample/Trace.lean`
- `NumStability/Source/Higham/Chapter15/Section02/Boyd/GlobalConvergence/ScalarCase/Iteration.lean`
- `NumStability/Source/Higham/Chapter15/Section02/Boyd/LocalConvergence/ConstrainedLagrangian/Differentiation.lean`
- `NumStability/Source/Higham/Chapter15/Section02/Boyd/SourceDomain/SecondDerivative/Rowwise.lean`
- `NumStability/Source/Higham/Chapter15/Section02/Boyd/SourceDomain/StrongLocalMaximum/Convergence.lean`
- `NumStability/Source/Higham/Chapter15/Section06/TridiagonalLUConditionBounds/ExactBounds.lean`
- `NumStability/Source/Higham/Chapter15/Theorem09/Ikebe/IrreducibleRightInverse/RankOneStructure.lean`
- `NumStabilityTest/Reorganization/R02/Canonical/AlgorithmsNormEstimationPNormOneAndInfinityNormsRectangular.lean`
- `NumStabilityTest/Reorganization/R02/Canonical/AlgorithmsNormEstimationPNormOneAndInfinityNormsSquare.lean`
- `NumStabilityTest/Reorganization/R02/Canonical/SourceHighamChapter15Algorithm04LAPACKNormEstimatorConditionEstimateBounds.lean`
- `NumStabilityTest/Reorganization/R02/Canonical/SourceHighamChapter15Algorithm05LINPACKConditionEstimatorInverseNormBoundTriangularSolve.lean`
- `NumStabilityTest/Reorganization/R02/Canonical/SourceHighamChapter15Problem06TridiagonalInverseNormRecurrencesArrayExecution.lean`
- `NumStabilityTest/Reorganization/R02/Canonical/SourceHighamChapter15Problem06TridiagonalInverseNormRecurrencesEntryFormulas.lean`
- `NumStabilityTest/Reorganization/R02/Canonical/SourceHighamChapter15Problem06TridiagonalInverseNormRecurrencesFactorizationAndNorm.lean`
- `NumStabilityTest/Reorganization/R02/Canonical/SourceHighamChapter15Section02BoydEndpointTerminationInfinityCounterexampleTrace.lean`
- `NumStabilityTest/Reorganization/R02/Canonical/SourceHighamChapter15Section02BoydGlobalConvergenceScalarCaseIteration.lean`
- `NumStabilityTest/Reorganization/R02/Canonical/SourceHighamChapter15Section02BoydLocalConvergenceConstrainedLagrangianDifferentiation.lean`
- `NumStabilityTest/Reorganization/R02/Canonical/SourceHighamChapter15Section02BoydSourceDomainSecondDerivativeRowwise.lean`
- `NumStabilityTest/Reorganization/R02/Canonical/SourceHighamChapter15Section02BoydSourceDomainStrongLocalMaximumConvergence.lean`
- `NumStabilityTest/Reorganization/R02/Canonical/SourceHighamChapter15Section06TridiagonalLUConditionBoundsExactBounds.lean`
- `NumStabilityTest/Reorganization/R02/Canonical/SourceHighamChapter15Theorem09IkebeIrreducibleRightInverseRankOneStructure.lean`
- `NumStabilityTest/Reorganization/R02/Consumer/Algorithms.lean`
- `NumStabilityTest/Reorganization/R02/Consumer/AlgorithmsNormEstimationPNormAll.lean`
- `NumStabilityTest/Reorganization/R02/Consumer/AlgorithmsNormEstimationPNormRectangularRectangularTermination.lean`
- `NumStabilityTest/Reorganization/R02/Consumer/SourceHighamChapter15.lean`
- `NumStabilityTest/Reorganization/R02/Consumer/SourceHighamChapter15Lemma02PNormPowerMethodPNormRectangular.lean`
- `NumStabilityTest/Reorganization/R02/Consumer/SourceHighamChapter15Section02BoydEndpointTerminationConvergenceStatements.lean`
- `NumStabilityTest/Reorganization/R02/Consumer/SourceHighamChapter15Section02BoydEndpointTerminationRectangularTermination.lean`
- `NumStabilityTest/Reorganization/R02/Focused/AlgorithmsNormEstimationPNormOneAndInfinityNormsRectangular.lean`
- `NumStabilityTest/Reorganization/R02/Focused/AlgorithmsNormEstimationPNormOneAndInfinityNormsSquare.lean`
- `NumStabilityTest/Reorganization/R02/Focused/SourceHighamChapter15Algorithm04LAPACKNormEstimatorConditionEstimateBounds.lean`
- `NumStabilityTest/Reorganization/R02/Focused/SourceHighamChapter15Algorithm05LINPACKConditionEstimatorInverseNormBoundTriangularSolve.lean`
- `NumStabilityTest/Reorganization/R02/Focused/SourceHighamChapter15Problem06TridiagonalInverseNormRecurrencesArrayExecution.lean`
- `NumStabilityTest/Reorganization/R02/Focused/SourceHighamChapter15Problem06TridiagonalInverseNormRecurrencesEntryFormulas.lean`
- `NumStabilityTest/Reorganization/R02/Focused/SourceHighamChapter15Problem06TridiagonalInverseNormRecurrencesFactorizationAndNorm.lean`
- `NumStabilityTest/Reorganization/R02/Focused/SourceHighamChapter15Section02BoydEndpointTerminationInfinityCounterexampleTrace.lean`
- `NumStabilityTest/Reorganization/R02/Focused/SourceHighamChapter15Section02BoydGlobalConvergenceScalarCaseIteration.lean`
- `NumStabilityTest/Reorganization/R02/Focused/SourceHighamChapter15Section02BoydLocalConvergenceConstrainedLagrangianDifferentiation.lean`
- `NumStabilityTest/Reorganization/R02/Focused/SourceHighamChapter15Section02BoydSourceDomainSecondDerivativeRowwise.lean`
- `NumStabilityTest/Reorganization/R02/Focused/SourceHighamChapter15Section02BoydSourceDomainStrongLocalMaximumConvergence.lean`
- `NumStabilityTest/Reorganization/R02/Focused/SourceHighamChapter15Section06TridiagonalLUConditionBoundsExactBounds.lean`
- `NumStabilityTest/Reorganization/R02/Focused/SourceHighamChapter15Theorem09IkebeIrreducibleRightInverseRankOneStructure.lean`
- `NumStabilityTest/Reorganization/R02/OldOnly/AlgorithmsCh15CondEstimators.lean`
- `NumStabilityTest/Reorganization/R02/OldOnly/AlgorithmsCh15DixonClosure.lean`
- `NumStabilityTest/Reorganization/R02/OldOnly/AlgorithmsCh15DixonProbability.lean`
- `NumStabilityTest/Reorganization/R02/OldOnly/AlgorithmsChapter15CondEst.lean`
- `NumStabilityTest/Reorganization/R02/OldOnly/AlgorithmsHighamChapter15BoydBridges.lean`
- `NumStabilityTest/Reorganization/R02/OldOnly/AlgorithmsHighamChapter15BoydConcreteLemma3.lean`
- `NumStabilityTest/Reorganization/R02/OldOnly/AlgorithmsHighamChapter15BoydLocalStability.lean`
- `NumStabilityTest/Reorganization/R02/OldOnly/AlgorithmsHighamChapter15BoydRowwiseDomain.lean`
- `NumStabilityTest/Reorganization/R02/OldOnly/AlgorithmsHighamChapter15BoydScalar.lean`
- `NumStabilityTest/Reorganization/R02/OldOnly/AlgorithmsHighamChapter15BoydSourceClosure.lean`
- `NumStabilityTest/Reorganization/R02/OldOnly/AlgorithmsHighamChapter15BoydSourceDomain.lean`
- `NumStabilityTest/Reorganization/R02/OldOnly/AlgorithmsHighamChapter15BoydSourceLocal.lean`
- `NumStabilityTest/Reorganization/R02/OldOnly/AlgorithmsHighamChapter15BoydSourceSecondDerivative.lean`
- `NumStabilityTest/Reorganization/R02/OldOnly/AlgorithmsHighamChapter15BoydUniqueness.lean`
- `NumStabilityTest/Reorganization/R02/OldOnly/AlgorithmsHighamChapter15ConvergenceProse.lean`
- `NumStabilityTest/Reorganization/R02/OldOnly/AlgorithmsHighamChapter15RectTermination.lean`
- `NumStabilityTest/Reorganization/R02/OldOnly/AlgorithmsLUHigham15Problem15_4.lean`
- `NumStabilityTest/Reorganization/R02/OldOnly/AlgorithmsLUHigham15Problem15_6.lean`
- `NumStabilityTest/Reorganization/R02/OldOnly/AlgorithmsLUHigham15Problem15_6Closure.lean`
- `NumStabilityTest/Reorganization/R02/OldOnly/AlgorithmsLUHigham15Problem15_6Operational.lean`
- `NumStabilityTest/Reorganization/R02/OldOnly/AlgorithmsLUTridiagonalCondCh15.lean`
- `NumStabilityTest/Reorganization/R02/OldOnly/AlgorithmsLUTridiagonalCondCh15Closure.lean`
- `NumStabilityTest/Reorganization/R02/OldOnly/AlgorithmsLUTridiagonalCondCh15IkebeClosure.lean`
- `NumStabilityTest/Reorganization/R02/OldOnly/AlgorithmsNormEstimationPNormEndpointsConvergenceStatements.lean`
- `NumStabilityTest/Reorganization/R02/OldOnly/AlgorithmsNormEstimationPNormEndpointsPNormRectangular.lean`
- `NumStabilityTest/Reorganization/R02/OldOnly/AlgorithmsPNormPowerMethod.lean`
- `NumStabilityTest/Reorganization/R02/OldOnly/AlgorithmsPNormPowerMethodGeneralP.lean`
- `NumStabilityTest/Reorganization/R02/OldOnly/AlgorithmsPNormPowerMethodRect.lean`
- `docs/architecture/deliveries/R02/DECLARATION_ROUTES.tsv`
- `docs/architecture/deliveries/R02/GATE_RESULTS.tsv`
- `docs/architecture/deliveries/R02/INTEGRATOR_REQUESTS.md`
- `docs/architecture/deliveries/R02/PRIVATE_CLOSURE.md`
- `docs/architecture/deliveries/R02/PRIVATE_CLOSURE.tsv`
- `docs/architecture/deliveries/R02/RETENTION.tsv`
- `docs/architecture/deliveries/R02/ROUTING.md`
- `docs/architecture/deliveries/R02/TEST_MATRIX.tsv`
