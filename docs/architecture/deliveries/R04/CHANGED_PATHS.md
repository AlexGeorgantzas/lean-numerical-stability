# R04 changed paths

Total 122 paths: 15 modified, 107 added.

## Modified B0008-owned paths (15; the 4 retained owners are unmodified)

- `NumStability/Algorithms/Ch10ActualSourceClosure.lean`
- `NumStability/Algorithms/Ch10ComplexPositiveDefiniteSourceClosure.lean`
- `NumStability/Algorithms/Ch10KahanSharpnessSource.lean`
- `NumStability/Algorithms/Ch10PivotedPSDSourceClosure.lean`
- `NumStability/Algorithms/Ch10Theorem108Componentwise.lean`
- `NumStability/Algorithms/Ch10Theorem108Source.lean`
- `NumStability/Algorithms/Cholesky/CholeskyPSD.lean`
- `NumStability/Algorithms/Cholesky/Higham1014Equation1022.lean`
- `NumStability/Algorithms/Cholesky/Higham1014SourceError.lean`
- `NumStability/Algorithms/Cholesky/Higham1029Source.lean`
- `NumStability/Algorithms/Cholesky/HighamMathiasSource.lean`
- `NumStability/Algorithms/HighamChapter10.lean`
- `NumStability/Source/Higham/Chapter06/Lemma06.lean`
- `NumStability/Source/Higham/Chapter10/Theorem07.lean`
- `NumStability/Source/Higham/Chapter11/Theorem07.lean`

## New canonical destinations (31)

- `NumStability/Algorithms/LinearSystems/Cholesky/ErrorAnalysis/PositivePivots/Certificate.lean`
- `NumStability/Algorithms/LinearSystems/Cholesky/PositiveSemidefinite/KahanTelescope/Identity.lean`
- `NumStability/Algorithms/LinearSystems/Cholesky/PositiveSemidefinite/PivotedFactorization/Existence.lean`
- `NumStability/Algorithms/LinearSystems/Cholesky/PositiveSemidefinite/StageEmbedding/InteriorMass.lean`
- `NumStability/Analysis/MatrixNorms/SpectralExtrema/PrincipalSubmatrices/Bounds.lean`
- `NumStability/Source/Higham/Chapter06/Lemma06/Core/Results.lean`
- `NumStability/Source/Higham/Chapter10/Equation29/Mathias/RoundedSchur/Bounds.lean`
- `NumStability/Source/Higham/Chapter10/Equation30/ComplexPositiveDefinite/NoPivotLU/SourceBounds.lean`
- `NumStability/Source/Higham/Chapter10/Lemma13/KahanSharpness/OperatorNorm/SourceBound.lean`
- `NumStability/Source/Higham/Chapter10/Lemma13/KahanSharpness/UnboundedGrowth/Construction.lean`
- `NumStability/Source/Higham/Chapter10/Problem01/PositiveSemidefiniteEntries/EntryBounds/Results.lean`
- `NumStability/Source/Higham/Chapter10/Problem04/UnpivotedGrowth/PositivePivots/Bounds.lean`
- `NumStability/Source/Higham/Chapter10/Section01/Factorization/ExistenceUniqueness/Results.lean`
- `NumStability/Source/Higham/Chapter10/Section02/ErrorAnalysis/FactorizationAndSolve/Bounds.lean`
- `NumStability/Source/Higham/Chapter10/Section03/PositiveSemidefinite/ConstructiveFactorization/Existence.lean`
- `NumStability/Source/Higham/Chapter10/Section03/PositiveSemidefinite/PivotingAndScaling/Results.lean`
- `NumStability/Source/Higham/Chapter10/Section03/PositiveSemidefinite/QuadraticFormBounds/WeightedNorm.lean`
- `NumStability/Source/Higham/Chapter10/Section03/PositiveSemidefinite/TrailingTermination/Bound.lean`
- `NumStability/Source/Higham/Chapter10/Section04/PositiveDefiniteSymmetricPart/LUGrowth/Equation29.lean`
- `NumStability/Source/Higham/Chapter10/Section04/PositiveDefiniteSymmetricPart/SchurStages/Bounds.lean`
- `NumStability/Source/Higham/Chapter10/Theorem06/RoundedCholesky/ForwardError/ActualAlgorithm.lean`
- `NumStability/Source/Higham/Chapter10/Theorem07/Core/Results.lean`
- `NumStability/Source/Higham/Chapter10/Theorem07/SuccessThreshold/Factorization.lean`
- `NumStability/Source/Higham/Chapter10/Theorem08/ComponentwisePerturbation/NormalizedResolvent/SourceBound.lean`
- `NumStability/Source/Higham/Chapter10/Theorem08/NormwiseDiscrepancy/Counterexample/Uniqueness.lean`
- `NumStability/Source/Higham/Chapter10/Theorem14/CompletePivotedPSD/ActualComputation/ErrorBounds.lean`
- `NumStability/Source/Higham/Chapter10/Theorem14/CompletePivotedPSD/RankSensitiveError/Bounds.lean`
- `NumStability/Source/Higham/Chapter10/Theorem14/CompletePivotedPSD/RoundedErrorAnalysis/Bounds.lean`
- `NumStability/Source/Higham/Chapter10/Theorem14/CompletePivotedPSD/SchurPerturbation/Family.lean`
- `NumStability/Source/Higham/Chapter10/Theorem14/CompletePivotedPSD/SuccessfulRun/StageBounds.lean`
- `NumStability/Source/Higham/Chapter11/Theorem07/Core/Results.lean`

## New R04 tests (76)

See TEST_MATRIX.tsv.

## Boundary proof

Modified paths are a subset of B0008 `owned_paths`; the unmodified owned
paths are exactly the four `retain_document` owners. Zero forbidden-path
hits (exact and prefix). Every added production module lies under a
declared B0008 `destination_prefixes` entry; every added test lies under
`NumStabilityTest/Reorganization/R04/`. No R0009 shared path, no B0009/R08
path, no phase control, tool, root manifest, CI or Lake file is touched.
