# W04 changed paths

This report is generated from the exact Git path/status inventory for
`a32095e6e50189f7dcc39312bb4c6a36f421fab5..DELIVERY_HEAD`. Before the delivery commit, the writer mode
combines the equivalent base-to-worktree diff with untracked additions;
the committed-tip checker requires the identical inventory and a clean tree.

| Category | Count |
| --- | ---: |
| Modified historical owners | 29 |
| Added reusable underdetermined modules | 31 |
| Added Chapter 21 source modules | 53 |
| Added canonical-only tests | 84 |
| Added old-path-only tests | 29 |
| Added focused tests | 11 |
| Added delivery evidence | 16 |
| **Total** | **253** |

B0008 scope result: **0 unowned paths; 0 forbidden paths**.

All 29 exact historical owners appear as `M`. Every `A` path is beneath one of B0008's exact destination, test, or delivery prefixes.

## Modified historical owners (29)

- `M` `NumStability/Algorithms/Underdetermined/Higham21.lean`
- `M` `NumStability/Algorithms/Underdetermined/Higham21Attainability.lean`
- `M` `NumStability/Algorithms/Underdetermined/Higham21Eq21_11Uniform.lean`
- `M` `NumStability/Algorithms/Underdetermined/Higham21Eq21_8.lean`
- `M` `NumStability/Algorithms/Underdetermined/Higham21Eq21_9.lean`
- `M` `NumStability/Algorithms/Underdetermined/Higham21Equation21_11.lean`
- `M` `NumStability/Algorithms/Underdetermined/Higham21Equation21_11Scalar.lean`
- `M` `NumStability/Algorithms/Underdetermined/Higham21Givens.lean`
- `M` `NumStability/Algorithms/Underdetermined/Higham21GivensClosure.lean`
- `M` `NumStability/Algorithms/Underdetermined/Higham21GivensRounded.lean`
- `M` `NumStability/Algorithms/Underdetermined/Higham21MGS.lean`
- `M` `NumStability/Algorithms/Underdetermined/Higham21MGSRounded.lean`
- `M` `NumStability/Algorithms/Underdetermined/Higham21Perturbation.lean`
- `M` `NumStability/Algorithms/Underdetermined/Higham21PerturbationRadius.lean`
- `M` `NumStability/Algorithms/Underdetermined/Higham21ProjectorNorm.lean`
- `M` `NumStability/Algorithms/Underdetermined/Higham21QRFoundations.lean`
- `M` `NumStability/Algorithms/Underdetermined/Higham21RankStability.lean`
- `M` `NumStability/Algorithms/Underdetermined/Higham21SNEActualOutput.lean`
- `M` `NumStability/Algorithms/Underdetermined/Higham21SNEClosure.lean`
- `M` `NumStability/Algorithms/Underdetermined/Higham21SNEConditionTransfer.lean`
- `M` `NumStability/Algorithms/Underdetermined/Higham21SNEEnvelopeTransfer.lean`
- `M` `NumStability/Algorithms/Underdetermined/Higham21SNEForward.lean`
- `M` `NumStability/Algorithms/Underdetermined/Higham21SNEQRMajorant.lean`
- `M` `NumStability/Algorithms/Underdetermined/Higham21SNERemainderBounds.lean`
- `M` `NumStability/Algorithms/Underdetermined/Higham21SNESigned.lean`
- `M` `NumStability/Algorithms/Underdetermined/Higham21SNEUniform.lean`
- `M` `NumStability/Algorithms/Underdetermined/Higham21Theorem214SourceClosure.lean`
- `M` `NumStability/Algorithms/Underdetermined/UnderdeterminedSolve.lean`
- `M` `NumStability/Algorithms/Underdetermined/UnderdeterminedSpec.lean`

## Added reusable underdetermined modules (31)

- `A` `NumStability/Algorithms/LinearSystems/Underdetermined/BackwardError/Normwise/UnderdeterminedSolve.lean`
- `A` `NumStability/Algorithms/LinearSystems/Underdetermined/BackwardError/Rowwise/UnderdeterminedSolve.lean`
- `A` `NumStability/Algorithms/LinearSystems/Underdetermined/Conditioning/Componentwise/Radius.lean`
- `A` `NumStability/Algorithms/LinearSystems/Underdetermined/Conditioning/Componentwise/UnderdeterminedSolve.lean`
- `A` `NumStability/Algorithms/LinearSystems/Underdetermined/MinimumNorm/Pseudoinverse/UnderdeterminedSpec.lean`
- `A` `NumStability/Algorithms/LinearSystems/Underdetermined/MinimumNorm/Solvers/UnderdeterminedSolve.lean`
- `A` `NumStability/Algorithms/LinearSystems/Underdetermined/MinimumNorm/Solvers/UnderdeterminedSpec.lean`
- `A` `NumStability/Algorithms/LinearSystems/Underdetermined/MinimumNorm/Specifications/UnderdeterminedSolve.lean`
- `A` `NumStability/Algorithms/LinearSystems/Underdetermined/MinimumNorm/Specifications/UnderdeterminedSpec.lean`
- `A` `NumStability/Algorithms/LinearSystems/Underdetermined/Perturbation/Componentwise/Radius.lean`
- `A` `NumStability/Algorithms/LinearSystems/Underdetermined/Perturbation/Componentwise/UnderdeterminedSolve.lean`
- `A` `NumStability/Algorithms/LinearSystems/Underdetermined/Perturbation/FixedRadius/Radius.lean`
- `A` `NumStability/Algorithms/LinearSystems/Underdetermined/Projectors/ComplementNorm/ProjectorNorm.lean`
- `A` `NumStability/Algorithms/LinearSystems/Underdetermined/QR/Foundations/UnderdeterminedSolve.lean`
- `A` `NumStability/Algorithms/LinearSystems/Underdetermined/QR/Givens/BackwardError/Core.lean`
- `A` `NumStability/Algorithms/LinearSystems/Underdetermined/QR/Givens/StoredReplay/Closure.lean`
- `A` `NumStability/Algorithms/LinearSystems/Underdetermined/QR/Givens/StoredReplay/RoundedReplay.lean`
- `A` `NumStability/Algorithms/LinearSystems/Underdetermined/QR/ModifiedGramSchmidt/CorrectedRecurrence/Core.lean`
- `A` `NumStability/Algorithms/LinearSystems/Underdetermined/QR/ModifiedGramSchmidt/RoundedReplay/RoundedReplay.lean`
- `A` `NumStability/Algorithms/LinearSystems/Underdetermined/RankStability/FullRowRank/UnderdeterminedSolve.lean`
- `A` `NumStability/Algorithms/LinearSystems/Underdetermined/SeminormalEquations/ForwardError/ActualOutput.lean`
- `A` `NumStability/Algorithms/LinearSystems/Underdetermined/SeminormalEquations/ForwardError/Forward.lean`
- `A` `NumStability/Algorithms/LinearSystems/Underdetermined/SeminormalEquations/ForwardError/RemainderBounds.lean`
- `A` `NumStability/Algorithms/LinearSystems/Underdetermined/SeminormalEquations/ForwardError/UnderdeterminedSolve.lean`
- `A` `NumStability/Algorithms/LinearSystems/Underdetermined/SeminormalEquations/HouseholderClosure/Closure.lean`
- `A` `NumStability/Algorithms/LinearSystems/Underdetermined/SeminormalEquations/HouseholderClosure/Uniform.lean`
- `A` `NumStability/Algorithms/LinearSystems/Underdetermined/SeminormalEquations/QRTransfer/EnvelopeTransfer.lean`
- `A` `NumStability/Algorithms/LinearSystems/Underdetermined/SeminormalEquations/QRTransfer/QRMajorant.lean`
- `A` `NumStability/Algorithms/LinearSystems/Underdetermined/SeminormalEquations/QRTransfer/Signed.lean`
- `A` `NumStability/Algorithms/LinearSystems/Underdetermined/SeminormalEquations/TriangularSolves/EnvelopeTransfer.lean`
- `A` `NumStability/Algorithms/LinearSystems/Underdetermined/SeminormalEquations/TriangularSolves/UnderdeterminedSolve.lean`

## Added Chapter 21 source modules (53)

- `A` `NumStability/Source/Higham/Chapter21/Corrections/Problem19_12/RoundedReplay.lean`
- `A` `NumStability/Source/Higham/Chapter21/Equation01/QRFoundations.lean`
- `A` `NumStability/Source/Higham/Chapter21/Equation01/UnderdeterminedSolve.lean`
- `A` `NumStability/Source/Higham/Chapter21/Equation02/UnderdeterminedSolve.lean`
- `A` `NumStability/Source/Higham/Chapter21/Equation03/QRFoundations.lean`
- `A` `NumStability/Source/Higham/Chapter21/Equation03/UnderdeterminedSolve.lean`
- `A` `NumStability/Source/Higham/Chapter21/Equation04/Pseudoinverse.lean`
- `A` `NumStability/Source/Higham/Chapter21/Equation04/QRFoundations.lean`
- `A` `NumStability/Source/Higham/Chapter21/Equation04/UnderdeterminedSpec.lean`
- `A` `NumStability/Source/Higham/Chapter21/Equation05/UnderdeterminedSolve.lean`
- `A` `NumStability/Source/Higham/Chapter21/Equation05/UnderdeterminedSpec.lean`
- `A` `NumStability/Source/Higham/Chapter21/Equation06/Perturbation.lean`
- `A` `NumStability/Source/Higham/Chapter21/Equation07/ConditionTransfer.lean`
- `A` `NumStability/Source/Higham/Chapter21/Equation07/UnderdeterminedSolve.lean`
- `A` `NumStability/Source/Higham/Chapter21/Equation08/EquationClosure.lean`
- `A` `NumStability/Source/Higham/Chapter21/Equation08/ProjectorNorm.lean`
- `A` `NumStability/Source/Higham/Chapter21/Equation09/EquationClosure.lean`
- `A` `NumStability/Source/Higham/Chapter21/Equation09/ProjectorNorm.lean`
- `A` `NumStability/Source/Higham/Chapter21/Equation10/Closure.lean`
- `A` `NumStability/Source/Higham/Chapter21/Equation10/RoundedReplay.lean`
- `A` `NumStability/Source/Higham/Chapter21/Equation10/UnderdeterminedSolve.lean`
- `A` `NumStability/Source/Higham/Chapter21/Equation11/ActualOutput.lean`
- `A` `NumStability/Source/Higham/Chapter21/Equation11/Closure.lean`
- `A` `NumStability/Source/Higham/Chapter21/Equation11/Equation.lean`
- `A` `NumStability/Source/Higham/Chapter21/Equation11/Forward.lean`
- `A` `NumStability/Source/Higham/Chapter21/Equation11/RemainderBounds.lean`
- `A` `NumStability/Source/Higham/Chapter21/Equation11/Scalar.lean`
- `A` `NumStability/Source/Higham/Chapter21/Equation11/UnderdeterminedSolve.lean`
- `A` `NumStability/Source/Higham/Chapter21/Equation11/Uniform.lean`
- `A` `NumStability/Source/Higham/Chapter21/Equation11/UniformClosure.lean`
- `A` `NumStability/Source/Higham/Chapter21/Lemma02/Symmetrization/UnderdeterminedSolve.lean`
- `A` `NumStability/Source/Higham/Chapter21/Lemma02/Symmetrization/UnderdeterminedSpec.lean`
- `A` `NumStability/Source/Higham/Chapter21/Section03/MethodComparison/Core.lean`
- `A` `NumStability/Source/Higham/Chapter21/Theorem01/Attainability/Attainability.lean`
- `A` `NumStability/Source/Higham/Chapter21/Theorem01/ComponentwisePerturbation/Radius.lean`
- `A` `NumStability/Source/Higham/Chapter21/Theorem01/ComponentwisePerturbation/RankStability.lean`
- `A` `NumStability/Source/Higham/Chapter21/Theorem01/ComponentwisePerturbation/UnderdeterminedSpec.lean`
- `A` `NumStability/Source/Higham/Chapter21/Theorem03/NormwiseBackwardError/UnderdeterminedSolve.lean`
- `A` `NumStability/Source/Higham/Chapter21/Theorem04/GivensQMethod/Closure.lean`
- `A` `NumStability/Source/Higham/Chapter21/Theorem04/GivensQMethod/Core.lean`
- `A` `NumStability/Source/Higham/Chapter21/Theorem04/GivensQMethod/RoundedReplay.lean`
- `A` `NumStability/Source/Higham/Chapter21/Theorem04/HouseholderQMethod/UnderdeterminedSolve.lean`
- `A` `NumStability/Source/Higham/Chapter21/Theorem04/ModifiedGramSchmidtQMethod/Core.lean`
- `A` `NumStability/Source/Higham/Chapter21/Theorem04/ModifiedGramSchmidtQMethod/RoundedReplay.lean`
- `A` `NumStability/Source/Higham/Chapter21/Theorem04/SeminormalEquations/ActualOutput.lean`
- `A` `NumStability/Source/Higham/Chapter21/Theorem04/SeminormalEquations/Closure.lean`
- `A` `NumStability/Source/Higham/Chapter21/Theorem04/SeminormalEquations/EnvelopeTransfer.lean`
- `A` `NumStability/Source/Higham/Chapter21/Theorem04/SeminormalEquations/Forward.lean`
- `A` `NumStability/Source/Higham/Chapter21/Theorem04/SeminormalEquations/QRMajorant.lean`
- `A` `NumStability/Source/Higham/Chapter21/Theorem04/SeminormalEquations/RemainderBounds.lean`
- `A` `NumStability/Source/Higham/Chapter21/Theorem04/SeminormalEquations/Signed.lean`
- `A` `NumStability/Source/Higham/Chapter21/Theorem04/SeminormalEquations/Uniform.lean`
- `A` `NumStability/Source/Higham/Chapter21/Theorem04/SourceClosure/SourceClosure.lean`

## Added canonical-only tests (84)

- `A` `NumStabilityTest/Reorganization/W04/Canonical/C001.lean`
- `A` `NumStabilityTest/Reorganization/W04/Canonical/C002.lean`
- `A` `NumStabilityTest/Reorganization/W04/Canonical/C003.lean`
- `A` `NumStabilityTest/Reorganization/W04/Canonical/C004.lean`
- `A` `NumStabilityTest/Reorganization/W04/Canonical/C005.lean`
- `A` `NumStabilityTest/Reorganization/W04/Canonical/C006.lean`
- `A` `NumStabilityTest/Reorganization/W04/Canonical/C007.lean`
- `A` `NumStabilityTest/Reorganization/W04/Canonical/C008.lean`
- `A` `NumStabilityTest/Reorganization/W04/Canonical/C009.lean`
- `A` `NumStabilityTest/Reorganization/W04/Canonical/C010.lean`
- `A` `NumStabilityTest/Reorganization/W04/Canonical/C011.lean`
- `A` `NumStabilityTest/Reorganization/W04/Canonical/C012.lean`
- `A` `NumStabilityTest/Reorganization/W04/Canonical/C013.lean`
- `A` `NumStabilityTest/Reorganization/W04/Canonical/C014.lean`
- `A` `NumStabilityTest/Reorganization/W04/Canonical/C015.lean`
- `A` `NumStabilityTest/Reorganization/W04/Canonical/C016.lean`
- `A` `NumStabilityTest/Reorganization/W04/Canonical/C017.lean`
- `A` `NumStabilityTest/Reorganization/W04/Canonical/C018.lean`
- `A` `NumStabilityTest/Reorganization/W04/Canonical/C019.lean`
- `A` `NumStabilityTest/Reorganization/W04/Canonical/C020.lean`
- `A` `NumStabilityTest/Reorganization/W04/Canonical/C021.lean`
- `A` `NumStabilityTest/Reorganization/W04/Canonical/C022.lean`
- `A` `NumStabilityTest/Reorganization/W04/Canonical/C023.lean`
- `A` `NumStabilityTest/Reorganization/W04/Canonical/C024.lean`
- `A` `NumStabilityTest/Reorganization/W04/Canonical/C025.lean`
- `A` `NumStabilityTest/Reorganization/W04/Canonical/C026.lean`
- `A` `NumStabilityTest/Reorganization/W04/Canonical/C027.lean`
- `A` `NumStabilityTest/Reorganization/W04/Canonical/C028.lean`
- `A` `NumStabilityTest/Reorganization/W04/Canonical/C029.lean`
- `A` `NumStabilityTest/Reorganization/W04/Canonical/C030.lean`
- `A` `NumStabilityTest/Reorganization/W04/Canonical/C031.lean`
- `A` `NumStabilityTest/Reorganization/W04/Canonical/C032.lean`
- `A` `NumStabilityTest/Reorganization/W04/Canonical/C033.lean`
- `A` `NumStabilityTest/Reorganization/W04/Canonical/C034.lean`
- `A` `NumStabilityTest/Reorganization/W04/Canonical/C035.lean`
- `A` `NumStabilityTest/Reorganization/W04/Canonical/C036.lean`
- `A` `NumStabilityTest/Reorganization/W04/Canonical/C037.lean`
- `A` `NumStabilityTest/Reorganization/W04/Canonical/C038.lean`
- `A` `NumStabilityTest/Reorganization/W04/Canonical/C039.lean`
- `A` `NumStabilityTest/Reorganization/W04/Canonical/C040.lean`
- `A` `NumStabilityTest/Reorganization/W04/Canonical/C041.lean`
- `A` `NumStabilityTest/Reorganization/W04/Canonical/C042.lean`
- `A` `NumStabilityTest/Reorganization/W04/Canonical/C043.lean`
- `A` `NumStabilityTest/Reorganization/W04/Canonical/C044.lean`
- `A` `NumStabilityTest/Reorganization/W04/Canonical/C045.lean`
- `A` `NumStabilityTest/Reorganization/W04/Canonical/C046.lean`
- `A` `NumStabilityTest/Reorganization/W04/Canonical/C047.lean`
- `A` `NumStabilityTest/Reorganization/W04/Canonical/C048.lean`
- `A` `NumStabilityTest/Reorganization/W04/Canonical/C049.lean`
- `A` `NumStabilityTest/Reorganization/W04/Canonical/C050.lean`
- `A` `NumStabilityTest/Reorganization/W04/Canonical/C051.lean`
- `A` `NumStabilityTest/Reorganization/W04/Canonical/C052.lean`
- `A` `NumStabilityTest/Reorganization/W04/Canonical/C053.lean`
- `A` `NumStabilityTest/Reorganization/W04/Canonical/C054.lean`
- `A` `NumStabilityTest/Reorganization/W04/Canonical/C055.lean`
- `A` `NumStabilityTest/Reorganization/W04/Canonical/C056.lean`
- `A` `NumStabilityTest/Reorganization/W04/Canonical/C057.lean`
- `A` `NumStabilityTest/Reorganization/W04/Canonical/C058.lean`
- `A` `NumStabilityTest/Reorganization/W04/Canonical/C059.lean`
- `A` `NumStabilityTest/Reorganization/W04/Canonical/C060.lean`
- `A` `NumStabilityTest/Reorganization/W04/Canonical/C061.lean`
- `A` `NumStabilityTest/Reorganization/W04/Canonical/C062.lean`
- `A` `NumStabilityTest/Reorganization/W04/Canonical/C063.lean`
- `A` `NumStabilityTest/Reorganization/W04/Canonical/C064.lean`
- `A` `NumStabilityTest/Reorganization/W04/Canonical/C065.lean`
- `A` `NumStabilityTest/Reorganization/W04/Canonical/C066.lean`
- `A` `NumStabilityTest/Reorganization/W04/Canonical/C067.lean`
- `A` `NumStabilityTest/Reorganization/W04/Canonical/C068.lean`
- `A` `NumStabilityTest/Reorganization/W04/Canonical/C069.lean`
- `A` `NumStabilityTest/Reorganization/W04/Canonical/C070.lean`
- `A` `NumStabilityTest/Reorganization/W04/Canonical/C071.lean`
- `A` `NumStabilityTest/Reorganization/W04/Canonical/C072.lean`
- `A` `NumStabilityTest/Reorganization/W04/Canonical/C073.lean`
- `A` `NumStabilityTest/Reorganization/W04/Canonical/C074.lean`
- `A` `NumStabilityTest/Reorganization/W04/Canonical/C075.lean`
- `A` `NumStabilityTest/Reorganization/W04/Canonical/C076.lean`
- `A` `NumStabilityTest/Reorganization/W04/Canonical/C077.lean`
- `A` `NumStabilityTest/Reorganization/W04/Canonical/C078.lean`
- `A` `NumStabilityTest/Reorganization/W04/Canonical/C079.lean`
- `A` `NumStabilityTest/Reorganization/W04/Canonical/C080.lean`
- `A` `NumStabilityTest/Reorganization/W04/Canonical/C081.lean`
- `A` `NumStabilityTest/Reorganization/W04/Canonical/C082.lean`
- `A` `NumStabilityTest/Reorganization/W04/Canonical/C083.lean`
- `A` `NumStabilityTest/Reorganization/W04/Canonical/C084.lean`

## Added old-path-only tests (29)

- `A` `NumStabilityTest/Reorganization/W04/OldPath/O001.lean`
- `A` `NumStabilityTest/Reorganization/W04/OldPath/O002.lean`
- `A` `NumStabilityTest/Reorganization/W04/OldPath/O003.lean`
- `A` `NumStabilityTest/Reorganization/W04/OldPath/O004.lean`
- `A` `NumStabilityTest/Reorganization/W04/OldPath/O005.lean`
- `A` `NumStabilityTest/Reorganization/W04/OldPath/O006.lean`
- `A` `NumStabilityTest/Reorganization/W04/OldPath/O007.lean`
- `A` `NumStabilityTest/Reorganization/W04/OldPath/O008.lean`
- `A` `NumStabilityTest/Reorganization/W04/OldPath/O009.lean`
- `A` `NumStabilityTest/Reorganization/W04/OldPath/O010.lean`
- `A` `NumStabilityTest/Reorganization/W04/OldPath/O011.lean`
- `A` `NumStabilityTest/Reorganization/W04/OldPath/O012.lean`
- `A` `NumStabilityTest/Reorganization/W04/OldPath/O013.lean`
- `A` `NumStabilityTest/Reorganization/W04/OldPath/O014.lean`
- `A` `NumStabilityTest/Reorganization/W04/OldPath/O015.lean`
- `A` `NumStabilityTest/Reorganization/W04/OldPath/O016.lean`
- `A` `NumStabilityTest/Reorganization/W04/OldPath/O017.lean`
- `A` `NumStabilityTest/Reorganization/W04/OldPath/O018.lean`
- `A` `NumStabilityTest/Reorganization/W04/OldPath/O019.lean`
- `A` `NumStabilityTest/Reorganization/W04/OldPath/O020.lean`
- `A` `NumStabilityTest/Reorganization/W04/OldPath/O021.lean`
- `A` `NumStabilityTest/Reorganization/W04/OldPath/O022.lean`
- `A` `NumStabilityTest/Reorganization/W04/OldPath/O023.lean`
- `A` `NumStabilityTest/Reorganization/W04/OldPath/O024.lean`
- `A` `NumStabilityTest/Reorganization/W04/OldPath/O025.lean`
- `A` `NumStabilityTest/Reorganization/W04/OldPath/O026.lean`
- `A` `NumStabilityTest/Reorganization/W04/OldPath/O027.lean`
- `A` `NumStabilityTest/Reorganization/W04/OldPath/O028.lean`
- `A` `NumStabilityTest/Reorganization/W04/OldPath/O029.lean`

## Added focused tests (11)

- `A` `NumStabilityTest/Reorganization/W04/Focused/Chapter21SourceEndpoints.lean`
- `A` `NumStabilityTest/Reorganization/W04/Focused/IntegratorCanonicalRetarget.lean`
- `A` `NumStabilityTest/Reorganization/W04/Focused/PerturbationConditioningProjectorsRankStability.lean`
- `A` `NumStabilityTest/Reorganization/W04/Focused/ProtectedAcceptedInterfaces.lean`
- `A` `NumStabilityTest/Reorganization/W04/Focused/ProtectedW90Consumers.lean`
- `A` `NumStabilityTest/Reorganization/W04/Focused/ProtectedW90Dependencies.lean`
- `A` `NumStabilityTest/Reorganization/W04/Focused/QRGivensModifiedGramSchmidt.lean`
- `A` `NumStabilityTest/Reorganization/W04/Focused/RetainedPrivateClosure.lean`
- `A` `NumStabilityTest/Reorganization/W04/Focused/ReusableUnderdeterminedApi.lean`
- `A` `NumStabilityTest/Reorganization/W04/Focused/SeminormalEquationsPipeline.lean`
- `A` `NumStabilityTest/Reorganization/W04/Focused/SpecificationsAndSolvers.lean`

## Added delivery evidence (16)

- `A` `docs/architecture/deliveries/W04/CHANGED_PATHS.md`
- `A` `docs/architecture/deliveries/W04/CHECK_PROJECTION.py`
- `A` `docs/architecture/deliveries/W04/CHECK_SCOPE.py`
- `A` `docs/architecture/deliveries/W04/CHECK_STATIC.py`
- `A` `docs/architecture/deliveries/W04/DECLARATION_ROUTES.tsv`
- `A` `docs/architecture/deliveries/W04/DELIVERY.md`
- `A` `docs/architecture/deliveries/W04/GATE_RESULTS.tsv`
- `A` `docs/architecture/deliveries/W04/GENERATE_MIGRATION.py`
- `A` `docs/architecture/deliveries/W04/INTEGRATOR_REQUESTS.md`
- `A` `docs/architecture/deliveries/W04/PRIVATE_CLOSURE.md`
- `A` `docs/architecture/deliveries/W04/PRIVATE_CLOSURE.tsv`
- `A` `docs/architecture/deliveries/W04/PRIVATE_CLOSURE_PLAN.py`
- `A` `docs/architecture/deliveries/W04/PROJECTION.md`
- `A` `docs/architecture/deliveries/W04/RETENTION.tsv`
- `A` `docs/architecture/deliveries/W04/ROUTING.md`
- `A` `docs/architecture/deliveries/W04/TEST_MATRIX.tsv`
