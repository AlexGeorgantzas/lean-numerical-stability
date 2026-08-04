# B0010 C0006 activation and joint W04/W09/W11 overlap review

Branch base: `C0006` at `a32095e6e50189f7dcc39312bb4c6a36f421fab5`.

This review is pinned to inventory SHA-256
`5A8C01FE644CC2DD1190E2DDFEFBAD0EE16D01BD5F7863086E7D2DE5EE307FCC`,
combined-baseline SHA-256
`E9207AA896EAA547E791FB1CECAC7A6B4E6344E8DC8E15D2EF2372FF90570625`,
raw format-2 graph SHA-256
`3BFEFF5663DA3FB5327B9D3AB22806654C9A79A48E1DDFE3C6E2E79073F9DE11`,
and projection-checker SHA-256
`29691CD63DB83A156247EA2C627407F4E90D127128A945B5AF97D014E11AB443`.
The 18-owner W11 selector has SHA-256
`24E3BD565946AECFDBAB9D2D21BF1201B86ECD16197F892E1B62A30162D9EE00`.
P0011 has SHA-256
`0A13EF31C40C997E2A692AC595E96DD3416BA603C6EC4ED47AB60765E6EBB3E2`
and freezes 3,354 declarations, 19,096 signature edges, 26,201 body/proof
edges, and 28,652 union edges.

## Reviewed destinations

The declaration audit authorizes exactly these 33 vacant production children:

```text
NumStability/Algorithms/RandomizedLinearAlgebra/Concentration/HitCounts/
NumStability/Algorithms/RandomizedLinearAlgebra/Concentration/SpectralTransfer/
NumStability/Algorithms/RandomizedLinearAlgebra/Concentration/TraceMGF/
NumStability/Algorithms/RandomizedLinearAlgebra/LeastSquaresSketching/FloatingPoint/
NumStability/Algorithms/RandomizedLinearAlgebra/LeastSquaresSketching/Objectives/
NumStability/Algorithms/RandomizedLinearAlgebra/LeastSquaresSketching/RowSampling/
NumStability/Algorithms/RandomizedLinearAlgebra/LeastSquaresSketching/SolverTransfer/
NumStability/Algorithms/RandomizedLinearAlgebra/LeastSquaresSketching/SubspaceEmbeddings/
NumStability/Algorithms/RandomizedLinearAlgebra/LowRankApproximation/ColumnSketches/
NumStability/Algorithms/RandomizedLinearAlgebra/LowRankApproximation/FloatingPoint/
NumStability/Algorithms/RandomizedLinearAlgebra/LowRankApproximation/Norms/
NumStability/Algorithms/RandomizedLinearAlgebra/LowRankApproximation/Projectors/
NumStability/Algorithms/RandomizedLinearAlgebra/LowRankApproximation/RankFactorizations/
NumStability/Algorithms/RandomizedLinearAlgebra/LowRankApproximation/SVD/
NumStability/Algorithms/RandomizedLinearAlgebra/Preconditioning/CountSketch/
NumStability/Algorithms/RandomizedLinearAlgebra/Preconditioning/ExactTransforms/
NumStability/Algorithms/RandomizedLinearAlgebra/Preconditioning/FloatingPoint/
NumStability/Algorithms/RandomizedLinearAlgebra/Preconditioning/Orthogonal/
NumStability/Algorithms/RandomizedLinearAlgebra/Preconditioning/SRHT/
NumStability/Algorithms/RandomizedLinearAlgebra/Sampling/Elementwise/
NumStability/Algorithms/RandomizedLinearAlgebra/Sampling/LeverageScore/
NumStability/Algorithms/RandomizedLinearAlgebra/Sampling/RowNorm/
NumStability/Algorithms/RandomizedLinearAlgebra/Sampling/UniformRows/
NumStability/Source/DrineasMahoney/RandNLA2016/Algorithm01/ElementwiseSampling/
NumStability/Source/DrineasMahoney/RandNLA2016/Algorithm02/RowSampling/
NumStability/Source/DrineasMahoney/RandNLA2016/Algorithm03/RandomProjectionPreconditioning/
NumStability/Source/DrineasMahoney/RandNLA2016/Equation02/SpectralApproximation/
NumStability/Source/DrineasMahoney/RandNLA2016/Equation04/RowSamplingProbability/
NumStability/Source/DrineasMahoney/RandNLA2016/Equation05/GramApproximation/
NumStability/Source/DrineasMahoney/RandNLA2016/Equation06/LeverageProbability/
NumStability/Source/DrineasMahoney/RandNLA2016/Equation07/SubspaceEmbedding/
NumStability/Source/DrineasMahoney/RandNLA2016/Equation08/LeastSquaresSketch/
NumStability/Source/DrineasMahoney/RandNLA2016/Equation09/LowRankApproximation/
```

Every prefix is casefold-vacant in the C0006 tree and scope. Pairwise exact,
ancestor/descendant, and shared-path intersections are zero. No broad
RandomizedLinearAlgebra, Preconditioning, LowRankApproximation, or paper-source
root is authorized.

## Declaration-level routing and private closure

The graph contains 3,354 declarations: 2,469 theorems, 813 definitions, and 24
each of inductives, constructors, and recursors; 3,351 are public and three are
private. The reverse-private floor is 225 declarations: three private and 222
public. The sorted union-closure payload SHA-256 is
`FAD5DC5D7CD80112157031E012D32593FBF33ACED6C1B9F94D60DEC55D1EA7F9`.
The three disjoint roots span nine owners; command, generated, and ambient
closure may enlarge the floor. No private declaration moves.

Generic sampling, concentration, leverage-score, sketching, preconditioning,
least-squares, and low-rank APIs route only to reviewed reusable children.
Numbered algorithms, equations, and paper endpoints route only to the exact
source hierarchy. `ElementwiseSpectral` requires declaration review rather
than name-based wholesale routing. `LowRankApprox` contains 805 declarations
and substantial Equation 09/source-SVD material, so generic rank, norm,
projector, SVD, column-sketch, and floating-point APIs must be separated
declaration-by-declaration from paper material.

Exactly six public `LeastSquaresSketch` declarations form the typed reverse
closure of its Chapter 20 source dependency. That closure routes under exact
Equation08/LeastSquaresSketch source children or remains historical; reusable
least-squares modules must never import Source. The owner must not be routed
wholesale.

The C0006 `LowRankApprox` imports of
`MatrixInversion.LUFactors.ErrorAnalysis.MatrixInversion`,
`MatrixInversion.LUFactors.Methods.MatrixInversion`, and
`MatrixInversion.Residuals.MatrixInversion` account for 19 union edges and
must be preserved. Its historical broad MatrixInversion import must never be
restored. Accepted W02 Doolittle surfaces and W06
`MatrixInequalities.LiebTrace.Concavity` are retained canonical boundaries.

## Protected boundaries and joint proof

Accepted W02/W06, MatrixInversion, and Chapter 20 interfaces remain untouched.
The W04, W09, and W11 selectors have zero owned-path overlap. Their reviewed
production destinations have zero equal or ancestor/descendant overlap.
C0006 imports and typed edges are zero in all six cross-wave directions.
`NumStability/Algorithms.lean` is their integrator-owned common aggregate.
The additional W04/W11 consumer
`NumStability/Algorithms/LinearSystems/LeastSquares/Equality/Basic.lean` is
integrator-owned and forbidden to both workers.

No source migration is authorized by this activation record.
