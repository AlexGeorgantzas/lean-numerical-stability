# B0008 C0006 activation and joint W04/W09/W11 overlap review

Branch base: `C0006` at `a32095e6e50189f7dcc39312bb4c6a36f421fab5`.

This review is pinned to inventory SHA-256
`5A8C01FE644CC2DD1190E2DDFEFBAD0EE16D01BD5F7863086E7D2DE5EE307FCC`,
combined-baseline SHA-256
`E9207AA896EAA547E791FB1CECAC7A6B4E6344E8DC8E15D2EF2372FF90570625`,
raw format-2 graph SHA-256
`3BFEFF5663DA3FB5327B9D3AB22806654C9A79A48E1DDFE3C6E2E79073F9DE11`,
and projection-checker SHA-256
`29691CD63DB83A156247EA2C627407F4E90D127128A945B5AF97D014E11AB443`.
The 29-owner W04 selector has SHA-256
`92446B8EBF571733212239DBD471A377EA889FC2A7061F1500DE7B03DB96518F`.
P0009 has SHA-256
`EAA15F18127E7B77F8AF442760590687B66A8860485590F2EB13D57E3A6F3814`
and freezes 1,238 declarations, 5,684 signature edges, 10,044 body/proof
edges, and 10,624 union edges.

## Reviewed destinations

The declaration audit authorizes exactly these 42 vacant production children:

```text
NumStability/Algorithms/LinearSystems/Underdetermined/BackwardError/Normwise/
NumStability/Algorithms/LinearSystems/Underdetermined/BackwardError/Rowwise/
NumStability/Algorithms/LinearSystems/Underdetermined/Conditioning/Componentwise/
NumStability/Algorithms/LinearSystems/Underdetermined/MinimumNorm/Pseudoinverse/
NumStability/Algorithms/LinearSystems/Underdetermined/MinimumNorm/Solvers/
NumStability/Algorithms/LinearSystems/Underdetermined/MinimumNorm/Specifications/
NumStability/Algorithms/LinearSystems/Underdetermined/Perturbation/Componentwise/
NumStability/Algorithms/LinearSystems/Underdetermined/Perturbation/FixedRadius/
NumStability/Algorithms/LinearSystems/Underdetermined/Projectors/ComplementNorm/
NumStability/Algorithms/LinearSystems/Underdetermined/QR/Foundations/
NumStability/Algorithms/LinearSystems/Underdetermined/QR/Givens/BackwardError/
NumStability/Algorithms/LinearSystems/Underdetermined/QR/Givens/StoredReplay/
NumStability/Algorithms/LinearSystems/Underdetermined/QR/ModifiedGramSchmidt/CorrectedRecurrence/
NumStability/Algorithms/LinearSystems/Underdetermined/QR/ModifiedGramSchmidt/RoundedReplay/
NumStability/Algorithms/LinearSystems/Underdetermined/RankStability/FullRowRank/
NumStability/Algorithms/LinearSystems/Underdetermined/SeminormalEquations/ConditionTransfer/
NumStability/Algorithms/LinearSystems/Underdetermined/SeminormalEquations/ForwardError/
NumStability/Algorithms/LinearSystems/Underdetermined/SeminormalEquations/HouseholderClosure/
NumStability/Algorithms/LinearSystems/Underdetermined/SeminormalEquations/QRTransfer/
NumStability/Algorithms/LinearSystems/Underdetermined/SeminormalEquations/TriangularSolves/
NumStability/Source/Higham/Chapter21/Corrections/Problem19_12/
NumStability/Source/Higham/Chapter21/Equation01/
NumStability/Source/Higham/Chapter21/Equation02/
NumStability/Source/Higham/Chapter21/Equation03/
NumStability/Source/Higham/Chapter21/Equation04/
NumStability/Source/Higham/Chapter21/Equation05/
NumStability/Source/Higham/Chapter21/Equation06/
NumStability/Source/Higham/Chapter21/Equation07/
NumStability/Source/Higham/Chapter21/Equation08/
NumStability/Source/Higham/Chapter21/Equation09/
NumStability/Source/Higham/Chapter21/Equation10/
NumStability/Source/Higham/Chapter21/Equation11/
NumStability/Source/Higham/Chapter21/Lemma02/Symmetrization/
NumStability/Source/Higham/Chapter21/Section03/MethodComparison/
NumStability/Source/Higham/Chapter21/Theorem01/Attainability/
NumStability/Source/Higham/Chapter21/Theorem01/ComponentwisePerturbation/
NumStability/Source/Higham/Chapter21/Theorem03/NormwiseBackwardError/
NumStability/Source/Higham/Chapter21/Theorem04/GivensQMethod/
NumStability/Source/Higham/Chapter21/Theorem04/HouseholderQMethod/
NumStability/Source/Higham/Chapter21/Theorem04/ModifiedGramSchmidtQMethod/
NumStability/Source/Higham/Chapter21/Theorem04/SeminormalEquations/
NumStability/Source/Higham/Chapter21/Theorem04/SourceClosure/
```

Case-folded comparison against the C0006 tree and scope gives zero matches for
every prefix. Pairwise exact and ancestor/descendant comparison gives zero
overlaps, and shared-path comparison gives zero intersections. No broad
`LinearSystems`, `Underdetermined`, `Perturbation`, or `Chapter21` destination
is authorized. Existing Chapter 21 canonical/source modules outside W04,
including RowScalingInvariance, Theorem03/Attainment, and
Theorem04/RowwiseBackwardError, remain untouched.

## Declaration-level routing and private closure

The graph contains 1,238 declarations: 904 theorems, 283 definitions, and 17
each of inductives, constructors, and recursors; 1,198 are public and 40 are
private. `Higham21` is a declaration-free facade. Every substantive owner is
mixed and must be split by declaration, command, and ambient context.

Reusable minimum-norm and pseudoinverse contracts, generic solvers, error
definitions, QR foundations, Givens replay, corrected/rounded MGS,
perturbation radii, conditioning, projectors, rank stability, and SNE
solver/transfer APIs route only to reviewed reusable children. Printed
equations 21.1--21.11, Theorems 21.1, 21.3, and 21.4, Lemma 21.2, method
comparison, source closures, and the Problem 19.12 correction route only to
exact source children. `UnderdeterminedSpec` and the 474-declaration
`UnderdeterminedSolve` are especially mixed and may not move wholesale.
Givens, MGS, perturbation, projector, rank-stability, and SNE owners also
require declaration-level splits. Demmel--Higham 1993 equations 3.10--3.20 in
`SNESigned` stay on the source side.

The reverse-private graph floor is:

```text
signature: 40 = 40 private + 0 public
body:     220 = 40 private + 180 public
union:    220 = 40 private + 180 public
```

The sorted union-closure payload SHA-256 is
`3E027CF02FDBFA2BFD9692166855245BDA0D8A9428540EA77F2938D819C86D84`.
Command roots, generated families, section state, attributes, and ambient
imports may enlarge this floor. No private declaration may move.

## Protected boundaries and joint proof

W04 imports accepted W02 material and W90 MatrixAlgebra, FloatingPoint.Model,
and exact Chapter 19/20 source modules. W90 also consumes W04. The pinned graph
has 2,029 W04-to-W90 signature and 3,534 body edges, and 261 W90-to-W04
signature and 281 body edges. All W90 paths are forbidden and unchanged.

The W04, W09, and W11 selectors have zero owned-path overlap. Their reviewed
production destinations have zero equal or ancestor/descendant overlap.
Parsing C0006 imports gives zero direct imports in all six directions.
Filtering the pinned graph gives zero signature and zero body/proof edges in
all six directions. `NumStability/Algorithms.lean` is integrator-owned. The
additional W04/W11 consumer
`NumStability/Algorithms/LinearSystems/LeastSquares/Equality/Basic.lean` is
also integrator-owned; neither worker may edit it.

No source migration is authorized by this activation record.
