# W05 changed paths

This file is generated from the exact Git diff from the frozen C0004 base
`b56f609f3bf66b5d7d0b677567cce82fee0c275b` to the W05 delivery tree. Untracked delivery files are treated as
additions before the delivery commit; rerunning the generator on the committed
tip yields the same path/status inventory.

| Category | Count |
| --- | ---: |
| Modified historical owners | 10 |
| Added reusable Sylvester modules | 24 |
| Added reusable Schur modules | 15 |
| Added reusable inverse-bound modules | 4 |
| Added source-numbered modules | 36 |
| Added canonical-only tests | 79 |
| Added old-path-only tests | 10 |
| Added focused tests | 3 |
| Added delivery evidence | 12 |
| **Total** | **193** |

B0005 scope result: **0 unowned paths; 0 forbidden paths**.

There are no deletions or renames. `M` denotes one of B0005's exact historical
owners; `A` denotes a path below an authorized destination prefix.

## Modified historical owners (10)

- `M` `NumStability/Algorithms/Sylvester/Higham16.lean`
- `M` `NumStability/Algorithms/Sylvester/Higham16Lyapunov.lean`
- `M` `NumStability/Algorithms/Sylvester/Higham16Psi.lean`
- `M` `NumStability/Algorithms/Sylvester/SylvesterBackward.lean`
- `M` `NumStability/Algorithms/Sylvester/SylvesterPerturbation.lean`
- `M` `NumStability/Algorithms/Sylvester/SylvesterSpec.lean`
- `M` `NumStability/Analysis/InverseOpNorm2.lean`
- `M` `NumStability/Analysis/RealInvariantSubspace.lean`
- `M` `NumStability/Analysis/RealQuasiSchur.lean`
- `M` `NumStability/Analysis/SchurTriangulation.lean`

## Added reusable Sylvester modules (24)

- `A` `NumStability/Algorithms/MatrixEquations/Sylvester/BackwardError/All.lean`
- `A` `NumStability/Algorithms/MatrixEquations/Sylvester/BackwardError/LyapunovSpectral.lean`
- `A` `NumStability/Algorithms/MatrixEquations/Sylvester/BackwardError/Specification.lean`
- `A` `NumStability/Algorithms/MatrixEquations/Sylvester/BackwardError/SylvesterSVD.lean`
- `A` `NumStability/Algorithms/MatrixEquations/Sylvester/Conditioning/All.lean`
- `A` `NumStability/Algorithms/MatrixEquations/Sylvester/Conditioning/FirstOrder.lean`
- `A` `NumStability/Algorithms/MatrixEquations/Sylvester/Conditioning/PracticalErrorBounds.lean`
- `A` `NumStability/Algorithms/MatrixEquations/Sylvester/Conditioning/Separation.lean`
- `A` `NumStability/Algorithms/MatrixEquations/Sylvester/Conditioning/SingularValue.lean`
- `A` `NumStability/Algorithms/MatrixEquations/Sylvester/Conditioning/StructuredLyapunov.lean`
- `A` `NumStability/Algorithms/MatrixEquations/Sylvester/Conditioning/StructuredSylvester.lean`
- `A` `NumStability/Algorithms/MatrixEquations/Sylvester/Equation/All.lean`
- `A` `NumStability/Algorithms/MatrixEquations/Sylvester/Equation/Basic.lean`
- `A` `NumStability/Algorithms/MatrixEquations/Sylvester/Equation/Diagonal.lean`
- `A` `NumStability/Algorithms/MatrixEquations/Sylvester/Equation/Lyapunov.lean`
- `A` `NumStability/Algorithms/MatrixEquations/Sylvester/Equation/Rectangular.lean`
- `A` `NumStability/Algorithms/MatrixEquations/Sylvester/Equation/SchurCoordinates.lean`
- `A` `NumStability/Algorithms/MatrixEquations/Sylvester/Equation/Vectorization.lean`
- `A` `NumStability/Algorithms/MatrixEquations/Sylvester/GeneralizedEquations/All.lean`
- `A` `NumStability/Algorithms/MatrixEquations/Sylvester/GeneralizedEquations/Basic.lean`
- `A` `NumStability/Algorithms/MatrixEquations/Sylvester/Perturbation/All.lean`
- `A` `NumStability/Algorithms/MatrixEquations/Sylvester/Perturbation/Basic.lean`
- `A` `NumStability/Algorithms/MatrixEquations/Sylvester/Perturbation/SeparationBounds.lean`
- `A` `NumStability/Algorithms/MatrixEquations/Sylvester/Perturbation/Vectorization.lean`

## Added reusable Schur modules (15)

- `A` `NumStability/Analysis/LinearOperators/Schur/All.lean`
- `A` `NumStability/Analysis/LinearOperators/Schur/Complex/BlockEmbedding.lean`
- `A` `NumStability/Analysis/LinearOperators/Schur/Complex/Deflation.lean`
- `A` `NumStability/Analysis/LinearOperators/Schur/Complex/Triangulation.lean`
- `A` `NumStability/Analysis/LinearOperators/Schur/Real/InvariantSubspace/Complexification.lean`
- `A` `NumStability/Analysis/LinearOperators/Schur/Real/InvariantSubspace/Existence.lean`
- `A` `NumStability/Analysis/LinearOperators/Schur/Real/InvariantSubspace/TwoByTwo.lean`
- `A` `NumStability/Analysis/LinearOperators/Schur/Real/QuasiTriangular/API.lean`
- `A` `NumStability/Analysis/LinearOperators/Schur/Real/QuasiTriangular/Basic.lean`
- `A` `NumStability/Analysis/LinearOperators/Schur/Real/QuasiTriangular/BlockEmbedding.lean`
- `A` `NumStability/Analysis/LinearOperators/Schur/Real/QuasiTriangular/Deflation.lean`
- `A` `NumStability/Analysis/LinearOperators/Schur/Real/QuasiTriangular/Existence.lean`
- `A` `NumStability/Analysis/LinearOperators/Schur/Real/QuasiTriangular/OrthogonalFrame.lean`
- `A` `NumStability/Analysis/LinearOperators/Schur/Real/QuasiTriangular/Reindex.lean`
- `A` `NumStability/Analysis/LinearOperators/Schur/Real/QuasiTriangular/TrailingConjugation.lean`

## Added reusable inverse-bound modules (4)

- `A` `NumStability/Analysis/SingularValues/InverseBounds/All.lean`
- `A` `NumStability/Analysis/SingularValues/InverseBounds/Gram.lean`
- `A` `NumStability/Analysis/SingularValues/InverseBounds/OperatorTwo.lean`
- `A` `NumStability/Analysis/SingularValues/InverseBounds/Rayleigh.lean`

## Added source-numbered modules (36)

- `A` `NumStability/Source/Higham/Chapter16/Section01/SylvesterEquation/All.lean`
- `A` `NumStability/Source/Higham/Chapter16/Section01/SylvesterEquation/Equation01.lean`
- `A` `NumStability/Source/Higham/Chapter16/Section01/SylvesterEquation/Equation02.lean`
- `A` `NumStability/Source/Higham/Chapter16/Section01/SylvesterEquation/Equation03.lean`
- `A` `NumStability/Source/Higham/Chapter16/Section02/RealSchurDecomposition/All.lean`
- `A` `NumStability/Source/Higham/Chapter16/Section02/RealSchurDecomposition/InvariantSubspace.lean`
- `A` `NumStability/Source/Higham/Chapter16/Section02/RealSchurDecomposition/QuasiTriangular.lean`
- `A` `NumStability/Source/Higham/Chapter16/Section02/SylvesterAndLyapunovBackwardError/All.lean`
- `A` `NumStability/Source/Higham/Chapter16/Section02/SylvesterAndLyapunovBackwardError/Equation09.lean`
- `A` `NumStability/Source/Higham/Chapter16/Section02/SylvesterAndLyapunovBackwardError/Equation10.lean`
- `A` `NumStability/Source/Higham/Chapter16/Section02/SylvesterAndLyapunovBackwardError/Equation11.lean`
- `A` `NumStability/Source/Higham/Chapter16/Section02/SylvesterAndLyapunovBackwardError/Equation12.lean`
- `A` `NumStability/Source/Higham/Chapter16/Section02/SylvesterAndLyapunovBackwardError/Equation13.lean`
- `A` `NumStability/Source/Higham/Chapter16/Section02/SylvesterAndLyapunovBackwardError/Equation15.lean`
- `A` `NumStability/Source/Higham/Chapter16/Section02/SylvesterAndLyapunovBackwardError/Equation16.lean`
- `A` `NumStability/Source/Higham/Chapter16/Section02/SylvesterAndLyapunovBackwardError/Equation18.lean`
- `A` `NumStability/Source/Higham/Chapter16/Section02/SylvesterAndLyapunovBackwardError/Equation19.lean`
- `A` `NumStability/Source/Higham/Chapter16/Section02/SylvesterAndLyapunovBackwardError/Equation21.lean`
- `A` `NumStability/Source/Higham/Chapter16/Section02/SylvesterAndLyapunovBackwardError/LyapunovDefinition.lean`
- `A` `NumStability/Source/Higham/Chapter16/Section03/PerturbationAndConditioning/All.lean`
- `A` `NumStability/Source/Higham/Chapter16/Section03/PerturbationAndConditioning/Equation22.lean`
- `A` `NumStability/Source/Higham/Chapter16/Section03/PerturbationAndConditioning/Equation23.lean`
- `A` `NumStability/Source/Higham/Chapter16/Section03/PerturbationAndConditioning/Equation24.lean`
- `A` `NumStability/Source/Higham/Chapter16/Section03/PerturbationAndConditioning/Equation25.lean`
- `A` `NumStability/Source/Higham/Chapter16/Section03/PerturbationAndConditioning/Equation26.lean`
- `A` `NumStability/Source/Higham/Chapter16/Section03/PerturbationAndConditioning/Equation27.lean`
- `A` `NumStability/Source/Higham/Chapter16/Section03/PerturbationAndConditioning/LyapunovSolutions.lean`
- `A` `NumStability/Source/Higham/Chapter16/Section04/PracticalErrorBounds/All.lean`
- `A` `NumStability/Source/Higham/Chapter16/Section04/PracticalErrorBounds/Equation28.lean`
- `A` `NumStability/Source/Higham/Chapter16/Section04/PracticalErrorBounds/Equation29.lean`
- `A` `NumStability/Source/Higham/Chapter16/Section05/GeneralizedMatrixEquations/All.lean`
- `A` `NumStability/Source/Higham/Chapter16/Section05/GeneralizedMatrixEquations/Equation30.lean`
- `A` `NumStability/Source/Higham/Chapter16/Section05/GeneralizedMatrixEquations/Equation31.lean`
- `A` `NumStability/Source/Higham/Chapter16/Section05/GeneralizedMatrixEquations/Equation32.lean`
- `A` `NumStability/Source/Higham/Chapter18/Section01/SchurDecomposition/All.lean`
- `A` `NumStability/Source/Higham/Chapter18/Section01/SchurDecomposition/ComplexTriangulation.lean`

## Added canonical-only tests (79)

- `A` `NumStabilityTest/Reorganization/W05/Canonical/C001.lean`
- `A` `NumStabilityTest/Reorganization/W05/Canonical/C002.lean`
- `A` `NumStabilityTest/Reorganization/W05/Canonical/C003.lean`
- `A` `NumStabilityTest/Reorganization/W05/Canonical/C004.lean`
- `A` `NumStabilityTest/Reorganization/W05/Canonical/C005.lean`
- `A` `NumStabilityTest/Reorganization/W05/Canonical/C006.lean`
- `A` `NumStabilityTest/Reorganization/W05/Canonical/C007.lean`
- `A` `NumStabilityTest/Reorganization/W05/Canonical/C008.lean`
- `A` `NumStabilityTest/Reorganization/W05/Canonical/C009.lean`
- `A` `NumStabilityTest/Reorganization/W05/Canonical/C010.lean`
- `A` `NumStabilityTest/Reorganization/W05/Canonical/C011.lean`
- `A` `NumStabilityTest/Reorganization/W05/Canonical/C012.lean`
- `A` `NumStabilityTest/Reorganization/W05/Canonical/C013.lean`
- `A` `NumStabilityTest/Reorganization/W05/Canonical/C014.lean`
- `A` `NumStabilityTest/Reorganization/W05/Canonical/C015.lean`
- `A` `NumStabilityTest/Reorganization/W05/Canonical/C016.lean`
- `A` `NumStabilityTest/Reorganization/W05/Canonical/C017.lean`
- `A` `NumStabilityTest/Reorganization/W05/Canonical/C018.lean`
- `A` `NumStabilityTest/Reorganization/W05/Canonical/C019.lean`
- `A` `NumStabilityTest/Reorganization/W05/Canonical/C020.lean`
- `A` `NumStabilityTest/Reorganization/W05/Canonical/C021.lean`
- `A` `NumStabilityTest/Reorganization/W05/Canonical/C022.lean`
- `A` `NumStabilityTest/Reorganization/W05/Canonical/C023.lean`
- `A` `NumStabilityTest/Reorganization/W05/Canonical/C024.lean`
- `A` `NumStabilityTest/Reorganization/W05/Canonical/C025.lean`
- `A` `NumStabilityTest/Reorganization/W05/Canonical/C026.lean`
- `A` `NumStabilityTest/Reorganization/W05/Canonical/C027.lean`
- `A` `NumStabilityTest/Reorganization/W05/Canonical/C028.lean`
- `A` `NumStabilityTest/Reorganization/W05/Canonical/C029.lean`
- `A` `NumStabilityTest/Reorganization/W05/Canonical/C030.lean`
- `A` `NumStabilityTest/Reorganization/W05/Canonical/C031.lean`
- `A` `NumStabilityTest/Reorganization/W05/Canonical/C032.lean`
- `A` `NumStabilityTest/Reorganization/W05/Canonical/C033.lean`
- `A` `NumStabilityTest/Reorganization/W05/Canonical/C034.lean`
- `A` `NumStabilityTest/Reorganization/W05/Canonical/C035.lean`
- `A` `NumStabilityTest/Reorganization/W05/Canonical/C036.lean`
- `A` `NumStabilityTest/Reorganization/W05/Canonical/C037.lean`
- `A` `NumStabilityTest/Reorganization/W05/Canonical/C038.lean`
- `A` `NumStabilityTest/Reorganization/W05/Canonical/C039.lean`
- `A` `NumStabilityTest/Reorganization/W05/Canonical/C040.lean`
- `A` `NumStabilityTest/Reorganization/W05/Canonical/C041.lean`
- `A` `NumStabilityTest/Reorganization/W05/Canonical/C042.lean`
- `A` `NumStabilityTest/Reorganization/W05/Canonical/C043.lean`
- `A` `NumStabilityTest/Reorganization/W05/Canonical/C044.lean`
- `A` `NumStabilityTest/Reorganization/W05/Canonical/C045.lean`
- `A` `NumStabilityTest/Reorganization/W05/Canonical/C046.lean`
- `A` `NumStabilityTest/Reorganization/W05/Canonical/C047.lean`
- `A` `NumStabilityTest/Reorganization/W05/Canonical/C048.lean`
- `A` `NumStabilityTest/Reorganization/W05/Canonical/C049.lean`
- `A` `NumStabilityTest/Reorganization/W05/Canonical/C050.lean`
- `A` `NumStabilityTest/Reorganization/W05/Canonical/C051.lean`
- `A` `NumStabilityTest/Reorganization/W05/Canonical/C052.lean`
- `A` `NumStabilityTest/Reorganization/W05/Canonical/C053.lean`
- `A` `NumStabilityTest/Reorganization/W05/Canonical/C054.lean`
- `A` `NumStabilityTest/Reorganization/W05/Canonical/C055.lean`
- `A` `NumStabilityTest/Reorganization/W05/Canonical/C056.lean`
- `A` `NumStabilityTest/Reorganization/W05/Canonical/C057.lean`
- `A` `NumStabilityTest/Reorganization/W05/Canonical/C058.lean`
- `A` `NumStabilityTest/Reorganization/W05/Canonical/C059.lean`
- `A` `NumStabilityTest/Reorganization/W05/Canonical/C060.lean`
- `A` `NumStabilityTest/Reorganization/W05/Canonical/C061.lean`
- `A` `NumStabilityTest/Reorganization/W05/Canonical/C062.lean`
- `A` `NumStabilityTest/Reorganization/W05/Canonical/C063.lean`
- `A` `NumStabilityTest/Reorganization/W05/Canonical/C064.lean`
- `A` `NumStabilityTest/Reorganization/W05/Canonical/C065.lean`
- `A` `NumStabilityTest/Reorganization/W05/Canonical/C066.lean`
- `A` `NumStabilityTest/Reorganization/W05/Canonical/C067.lean`
- `A` `NumStabilityTest/Reorganization/W05/Canonical/C068.lean`
- `A` `NumStabilityTest/Reorganization/W05/Canonical/C069.lean`
- `A` `NumStabilityTest/Reorganization/W05/Canonical/C070.lean`
- `A` `NumStabilityTest/Reorganization/W05/Canonical/C071.lean`
- `A` `NumStabilityTest/Reorganization/W05/Canonical/C072.lean`
- `A` `NumStabilityTest/Reorganization/W05/Canonical/C073.lean`
- `A` `NumStabilityTest/Reorganization/W05/Canonical/C074.lean`
- `A` `NumStabilityTest/Reorganization/W05/Canonical/C075.lean`
- `A` `NumStabilityTest/Reorganization/W05/Canonical/C076.lean`
- `A` `NumStabilityTest/Reorganization/W05/Canonical/C077.lean`
- `A` `NumStabilityTest/Reorganization/W05/Canonical/C078.lean`
- `A` `NumStabilityTest/Reorganization/W05/Canonical/C079.lean`

## Added old-path-only tests (10)

- `A` `NumStabilityTest/Reorganization/W05/Compatibility/O01.lean`
- `A` `NumStabilityTest/Reorganization/W05/Compatibility/O02.lean`
- `A` `NumStabilityTest/Reorganization/W05/Compatibility/O03.lean`
- `A` `NumStabilityTest/Reorganization/W05/Compatibility/O04.lean`
- `A` `NumStabilityTest/Reorganization/W05/Compatibility/O05.lean`
- `A` `NumStabilityTest/Reorganization/W05/Compatibility/O06.lean`
- `A` `NumStabilityTest/Reorganization/W05/Compatibility/O07.lean`
- `A` `NumStabilityTest/Reorganization/W05/Compatibility/O08.lean`
- `A` `NumStabilityTest/Reorganization/W05/Compatibility/O09.lean`
- `A` `NumStabilityTest/Reorganization/W05/Compatibility/O10.lean`

## Added focused tests (3)

- `A` `NumStabilityTest/Reorganization/W05/Focused/InverseBounds.lean`
- `A` `NumStabilityTest/Reorganization/W05/Focused/Schur.lean`
- `A` `NumStabilityTest/Reorganization/W05/Focused/Sylvester.lean`

## Added delivery evidence (12)

- `A` `docs/architecture/deliveries/W05/CHANGED_PATHS.md`
- `A` `docs/architecture/deliveries/W05/CHECK_SCOPE.py`
- `A` `docs/architecture/deliveries/W05/DECLARATION_ROUTES.tsv`
- `A` `docs/architecture/deliveries/W05/DELIVERY.md`
- `A` `docs/architecture/deliveries/W05/GENERATE_MIGRATION.py`
- `A` `docs/architecture/deliveries/W05/INTEGRATOR_REQUESTS.md`
- `A` `docs/architecture/deliveries/W05/PRIVATE_CLOSURE.md`
- `A` `docs/architecture/deliveries/W05/PRIVATE_CLOSURE.tsv`
- `A` `docs/architecture/deliveries/W05/PRIVATE_CLOSURE_PLAN.py`
- `A` `docs/architecture/deliveries/W05/PROJECTION.md`
- `A` `docs/architecture/deliveries/W05/ROUTING.md`
- `A` `docs/architecture/deliveries/W05/TEST_MATRIX.tsv`
