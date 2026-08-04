# R0005 integration-overlap evidence

Base checkpoint: C0005 / `240c0d041781385a647fbec461d6863537e562cb`.

Every existing path below was verified to change import lines only: after
removing import commands, the C0005 and integrated texts are identical.
Every null-preimage path is an import-and-docstring-only aggregate. Blob
OIDs are Git SHA-1 object IDs; rows are sorted by path.

| Path | C0005 preimage | Integrated postimage | Class |
| --- | --- | --- | --- |
| `NumStability/Algorithms/MatrixEquations/Sylvester/Conditioning/AttainedMinima.lean` | `null` | `e6cd9e6b5ab6612dce9034293eb259017704b1ef` | nested-retired-scope-aggregate |
| `NumStability/Algorithms/MatrixEquations/Sylvester/Conditioning/AutomaticBounds.lean` | `null` | `f0b0837de02b413e18135cf1db0bba368bdd930d` | nested-retired-scope-aggregate |
| `NumStability/Algorithms/MatrixEquations/Sylvester/Conditioning/PracticalEstimator.lean` | `null` | `9bfcf12922b2af6b0ed3c9614a1208dee63d4755` | nested-retired-scope-aggregate |
| `NumStability/Algorithms/MatrixEquations/Sylvester/Conditioning/SigmaMinBounds.lean` | `null` | `3904605f2b0dede19ca96e560ea7a7c492f9c62e` | nested-retired-scope-aggregate |
| `NumStability/Algorithms/MatrixEquations/Sylvester/Equation/VectorizationIdentities.lean` | `null` | `6f6a0068187b655f13078320cb0937890e91d735` | nested-retired-scope-aggregate |
| `NumStability/Algorithms/StationaryIteration.lean` | `251bbb2dcd74492e076c7776e675a896be4cfa4e` | `08cfea98cba754d35f7de2d620c00d0cc84300f8` | W07-import-only-refresh |
| `NumStability/Algorithms/StationaryIterationDrazin.lean` | `f1a3be1f6f625fa32d751d52b37e477a1303c80b` | `258490a358f3991f2cc206f99c33c76033fb3c8e` | W07-import-only-refresh |
| `NumStability/Algorithms/StationaryIterationSemiconvergent.lean` | `0239b2e47b0a590cc8e7c685e7957a6015b9341e` | `38461840f7f6f4c856c1986087de86786356c0b8` | W07-import-only-refresh |
| `NumStability/Analysis/Error/RoundingProducts/Core.lean` | `040c8383c8bc4308bc30694440a00962325d9214` | `b748351ed87b0a90429448dfd9d422bb3b6a4959` | accepted-consumer |
| `NumStability/Analysis/LinearOperators/Schur/Real.lean` | `null` | `d01baa215d646fbc7702fea764585470b2dbb50f` | nested-retired-scope-aggregate |
| `NumStability/Analysis/LinearOperators/Schur/Real/Triangularization.lean` | `null` | `d70b7ba495395f9ed4ae27f70b186e5593e74f75` | nested-retired-scope-aggregate |
| `NumStability/Analysis/SemiconvergentExistenceGaps.lean` | `760ba924ec970291a113c037656dbc109470ca20` | `4c462b3d8b4000f207e4f369e9d968d49ebcaaa6` | accepted-consumer |
| `NumStability/Analysis/SemiconvergentLimitGeneral.lean` | `59ea98fa1820566e6a1aef6d2bbcbac1df688271` | `e84fd5893d97fc6bdb3e34b9e1374733fcdd600d` | accepted-consumer |
| `NumStability/Analysis/SemiconvergentRealSpectrumComplete.lean` | `d580c8c50364b5d44b8263b5325522990858eef3` | `86ac278b764a1205d4df25268e7a8eec4f05f8bd` | accepted-consumer |
| `NumStability/Source/Higham/Chapter01/FloatingPointArithmetic/CancellationOfRoundingErrors.lean` | `785ad0b3cdb2531eb27aa2dc93e55dc89c096f74` | `7b663ac5d54f29d60a100b66360654b1d8b14bac` | accepted-consumer |
| `NumStability/Source/Higham/Chapter01/FloatingPointArithmetic/IncreasingPrecision.lean` | `c14ccc8c5f0f16483537a1967086e23ba5891ecb` | `00374a7274bfd8e34a1195e993f1ebff305f2c97` | accepted-consumer |
| `NumStability/Source/Higham/Chapter01/FloatingPointArithmetic/InstabilityWithoutCancellation.lean` | `27c4fc74af8f342dd923d18b7fe9b3e295f7eca8` | `f753b42f2b7f46b790637a96926eaa67f68cb24a` | accepted-consumer |
| `NumStability/Source/Higham/Chapter03/Problem02/ProductBounds/PositiveFactors.lean` | `9a6e33058e1aaa6624e122640071ac5fdf44ca56` | `3972c6a3478a9f8ed9b243ef6bdbcf754779506f` | accepted-consumer |
| `NumStability/Source/Higham/Chapter14/Section05/SpectralConvergence.lean` | `86a3492bad89d86f36889dd696d27c87e21fddc3` | `a6ecabeb11c2ed9af5950d69d8946f809fce857f` | accepted-consumer |
| `NumStability/Source/Higham/Chapter16/Section01/SylvesterEquation/ComplexSolvability.lean` | `null` | `fefa2fdcba1e4d29c81f030f0625543c340cdc9f` | nested-retired-scope-aggregate |
| `NumStability/Source/Higham/Chapter16/Section01/SylvesterEquation/VectorizationNotes.lean` | `null` | `75e1b11d4109545ddf75a3d83b6d9a0899c1195b` | nested-retired-scope-aggregate |
| `NumStability/Source/Higham/Chapter16/Section02/SylvesterAndLyapunovBackwardError/AttainedMinima.lean` | `null` | `4edc07b2079b276d27f27660341a0e7b72f7f606` | nested-retired-scope-aggregate |
| `NumStability/Source/Higham/Chapter16/Section03/PerturbationAndConditioning/AttainedSeparation.lean` | `null` | `e52bc71c265cc388a5412998e82cc2b69b5d7a45` | nested-retired-scope-aggregate |
| `NumStability/Source/Higham/Chapter16/Section03/PerturbationAndConditioning/AutomaticBounds.lean` | `null` | `a38390777187022aa3606f7f34db0cffd5cab677` | nested-retired-scope-aggregate |
| `NumStability/Source/Higham/Chapter16/Section03/PerturbationAndConditioning/SigmaMinCorollaries.lean` | `null` | `5f82a61d0be5fb2cd09a01c7319b75de15ef7a93` | nested-retired-scope-aggregate |
| `NumStability/Source/Higham/Chapter16/Section04/PracticalErrorBounds/Equation29Extensions.lean` | `null` | `e0b603f8f1d5cf97b631080eb592743429c238b8` | nested-retired-scope-aggregate |
| `NumStability/Source/Higham/Chapter16/Section04/PracticalErrorBounds/NormEstimator.lean` | `null` | `ceea2e74fa2ced45a0008cdd1bdfacafef5c0501` | nested-retired-scope-aggregate |
| `NumStability/Source/Higham/Chapter17/Problem01.lean` | `0ffaca593d6ae73b75245ffb3ab8b37e340420af` | `b0b9ad212f28db295498f72a3d49f0503086829b` | accepted-consumer |

Verified rows: 28.
