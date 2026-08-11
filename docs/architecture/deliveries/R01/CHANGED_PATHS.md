# R01 changed paths

Base: `b1b18772d80185ec08f49c818919558645c330a1`

Branch: `codex/reorg-completion-2026-08-r01-stationary-semiconvergence`

Total: **98** (`A` 82, `M` 16).

The exact delivery contains **40 production paths** (16 modified historical owners and
24 new canonical leaves/aggregates), **41 test modules**, and **17 delivery artifacts**.
Every path is an exact B0001 owner or lies below an authorized B0001 destination, test,
or delivery prefix. No shared consumer, phase registry, MatrixAlgebra, integrator control,
historical deletion, or Git rename is present.

## Exact path ledger

- `A` `docs/architecture/deliveries/R01/CHANGED_PATHS.md`
- `A` `docs/architecture/deliveries/R01/CHECK_PROJECTION.py`
- `A` `docs/architecture/deliveries/R01/CHECK_REQUEST_REPLAY.py`
- `A` `docs/architecture/deliveries/R01/CHECK_SCOPE.py`
- `A` `docs/architecture/deliveries/R01/CHECK_STATIC.py`
- `A` `docs/architecture/deliveries/R01/DECLARATION_ROUTES.tsv`
- `A` `docs/architecture/deliveries/R01/DELIVERY.md`
- `A` `docs/architecture/deliveries/R01/GATE_RESULTS.tsv`
- `A` `docs/architecture/deliveries/R01/INTEGRATOR_POSTIMAGES.tsv`
- `A` `docs/architecture/deliveries/R01/INTEGRATOR_REQUEST.patch`
- `A` `docs/architecture/deliveries/R01/INTEGRATOR_REQUESTS.md`
- `A` `docs/architecture/deliveries/R01/PRIVATE_CLOSURE.md`
- `A` `docs/architecture/deliveries/R01/PRIVATE_CLOSURE.tsv`
- `A` `docs/architecture/deliveries/R01/PROJECTION.md`
- `A` `docs/architecture/deliveries/R01/RETENTION.tsv`
- `A` `docs/architecture/deliveries/R01/ROUTING.md`
- `A` `docs/architecture/deliveries/R01/TEST_MATRIX.tsv`
- `A` `NumStability/Algorithms/LinearSystems/Iterative/Stationary/Semiconvergence/All.lean`
- `A` `NumStability/Algorithms/LinearSystems/Iterative/Stationary/Semiconvergence/BlockForm/Existence.lean`
- `A` `NumStability/Algorithms/LinearSystems/Iterative/Stationary/Semiconvergence/BlockForm/ProjectorLimit.lean`
- `A` `NumStability/Algorithms/LinearSystems/Iterative/Stationary/Semiconvergence/Execution/RoundedCertificates.lean`
- `A` `NumStability/Algorithms/LinearSystems/Iterative/Stationary/Semiconvergence/Projectors/FixedRange.lean`
- `M` `NumStability/Algorithms/StationaryIteration.lean`
- `M` `NumStability/Algorithms/StationaryIterationDrazin.lean`
- `M` `NumStability/Algorithms/StationaryIterationRounded.lean`
- `M` `NumStability/Algorithms/StationaryIterationSemiconvergent.lean`
- `M` `NumStability/Algorithms/StationaryIterationSemiconvergentExistence.lean`
- `A` `NumStability/Analysis/LinearOperators/MatrixPowers/Semiconvergence/All.lean`
- `A` `NumStability/Analysis/LinearOperators/MatrixPowers/Semiconvergence/Limits/General.lean`
- `A` `NumStability/Analysis/LinearOperators/MatrixPowers/Semiconvergence/Limits/RealSpectrum.lean`
- `A` `NumStability/Analysis/LinearOperators/MatrixPowers/Semiconvergence/PrimarySplitting.lean`
- `A` `NumStability/Analysis/LinearOperators/MatrixPowers/Semiconvergence/QuasiTriangularBlockForm.lean`
- `A` `NumStability/Analysis/LinearOperators/MatrixPowers/Semiconvergence/TriangularBlockForm.lean`
- `M` `NumStability/Analysis/SemiconvergentBlockFormExists.lean`
- `M` `NumStability/Analysis/SemiconvergentExistenceComplete.lean`
- `M` `NumStability/Analysis/SemiconvergentExistenceFull.lean`
- `M` `NumStability/Analysis/SemiconvergentLimitGeneral.lean`
- `M` `NumStability/Analysis/SemiconvergentRealSpectrumComplete.lean`
- `M` `NumStability/Source/Higham/Chapter17/Equation08.lean`
- `M` `NumStability/Source/Higham/Chapter17/Equation12.lean`
- `M` `NumStability/Source/Higham/Chapter17/Equation15.lean`
- `M` `NumStability/Source/Higham/Chapter17/Equation16.lean`
- `M` `NumStability/Source/Higham/Chapter17/Equation17.lean`
- `M` `NumStability/Source/Higham/Chapter17/Equation20.lean`
- `A` `NumStability/Source/Higham/Chapter17/Results/All.lean`
- `A` `NumStability/Source/Higham/Chapter17/Results/Equation08/GeometricSummability.lean`
- `A` `NumStability/Source/Higham/Chapter17/Results/Equation12/AttainedPartialSumBound.lean`
- `A` `NumStability/Source/Higham/Chapter17/Results/Equation15/UniformForwardBound.lean`
- `A` `NumStability/Source/Higham/Chapter17/Results/Equation16/JacobiForwardBound.lean`
- `A` `NumStability/Source/Higham/Chapter17/Results/Equation17/SORForwardBound.lean`
- `A` `NumStability/Source/Higham/Chapter17/Results/Equation20/DiagonalizableBounds.lean`
- `A` `NumStability/Source/Higham/Chapter17/Results/Equation20/ResidualSigmaEnvelope.lean`
- `A` `NumStability/Source/Higham/Chapter17/Results/Equation27/SingularErrorSplit.lean`
- `A` `NumStability/Source/Higham/Chapter17/Results/Equation29/SingularBounds.lean`
- `A` `NumStability/Source/Higham/Chapter17/Results/Section01/RoundedExecution.lean`
- `A` `NumStability/Source/Higham/Chapter17/Results/Section04/DrazinConsequences.lean`
- `A` `NumStability/Source/Higham/Chapter17/Results/Series.lean`
- `A` `NumStabilityTest/Reorganization/R01/Canonical/C01.lean`
- `A` `NumStabilityTest/Reorganization/R01/Canonical/C02.lean`
- `A` `NumStabilityTest/Reorganization/R01/Canonical/C03.lean`
- `A` `NumStabilityTest/Reorganization/R01/Canonical/C04.lean`
- `A` `NumStabilityTest/Reorganization/R01/Canonical/C05.lean`
- `A` `NumStabilityTest/Reorganization/R01/Canonical/C06.lean`
- `A` `NumStabilityTest/Reorganization/R01/Canonical/C07.lean`
- `A` `NumStabilityTest/Reorganization/R01/Canonical/C08.lean`
- `A` `NumStabilityTest/Reorganization/R01/Canonical/C09.lean`
- `A` `NumStabilityTest/Reorganization/R01/Canonical/C10.lean`
- `A` `NumStabilityTest/Reorganization/R01/Canonical/C11.lean`
- `A` `NumStabilityTest/Reorganization/R01/Canonical/C12.lean`
- `A` `NumStabilityTest/Reorganization/R01/Canonical/C13.lean`
- `A` `NumStabilityTest/Reorganization/R01/Canonical/C14.lean`
- `A` `NumStabilityTest/Reorganization/R01/Canonical/C15.lean`
- `A` `NumStabilityTest/Reorganization/R01/Canonical/C16.lean`
- `A` `NumStabilityTest/Reorganization/R01/Canonical/C17.lean`
- `A` `NumStabilityTest/Reorganization/R01/Canonical/C18.lean`
- `A` `NumStabilityTest/Reorganization/R01/Canonical/C19.lean`
- `A` `NumStabilityTest/Reorganization/R01/Canonical/C20.lean`
- `A` `NumStabilityTest/Reorganization/R01/Focused/Equation22TypedConsumers.lean`
- `A` `NumStabilityTest/Reorganization/R01/Focused/PrivateNormalization.lean`
- `A` `NumStabilityTest/Reorganization/R01/Focused/PublicNameRetention.lean`
- `A` `NumStabilityTest/Reorganization/R01/Focused/RootAggregates.lean`
- `A` `NumStabilityTest/Reorganization/R01/Focused/StationaryIterationSeries.lean`
- `A` `NumStabilityTest/Reorganization/R01/OldPath/O01.lean`
- `A` `NumStabilityTest/Reorganization/R01/OldPath/O02.lean`
- `A` `NumStabilityTest/Reorganization/R01/OldPath/O03.lean`
- `A` `NumStabilityTest/Reorganization/R01/OldPath/O04.lean`
- `A` `NumStabilityTest/Reorganization/R01/OldPath/O05.lean`
- `A` `NumStabilityTest/Reorganization/R01/OldPath/O06.lean`
- `A` `NumStabilityTest/Reorganization/R01/OldPath/O07.lean`
- `A` `NumStabilityTest/Reorganization/R01/OldPath/O08.lean`
- `A` `NumStabilityTest/Reorganization/R01/OldPath/O09.lean`
- `A` `NumStabilityTest/Reorganization/R01/OldPath/O10.lean`
- `A` `NumStabilityTest/Reorganization/R01/OldPath/O11.lean`
- `A` `NumStabilityTest/Reorganization/R01/OldPath/O12.lean`
- `A` `NumStabilityTest/Reorganization/R01/OldPath/O13.lean`
- `A` `NumStabilityTest/Reorganization/R01/OldPath/O14.lean`
- `A` `NumStabilityTest/Reorganization/R01/OldPath/O15.lean`
- `A` `NumStabilityTest/Reorganization/R01/OldPath/O16.lean`
