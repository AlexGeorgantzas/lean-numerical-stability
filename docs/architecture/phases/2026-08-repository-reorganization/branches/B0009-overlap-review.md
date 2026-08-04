# B0009 C0006 activation and joint W04/W09/W11 overlap review

Branch base: `C0006` at `a32095e6e50189f7dcc39312bb4c6a36f421fab5`.

This review is pinned to inventory SHA-256
`5A8C01FE644CC2DD1190E2DDFEFBAD0EE16D01BD5F7863086E7D2DE5EE307FCC`,
combined-baseline SHA-256
`E9207AA896EAA547E791FB1CECAC7A6B4E6344E8DC8E15D2EF2372FF90570625`,
raw format-2 graph SHA-256
`3BFEFF5663DA3FB5327B9D3AB22806654C9A79A48E1DDFE3C6E2E79073F9DE11`,
and projection-checker SHA-256
`29691CD63DB83A156247EA2C627407F4E90D127128A945B5AF97D014E11AB443`.
The 72-owner W09 selector has SHA-256
`53909C680B3054E03558983B2812E83374571483D19DE7B647E88AAF96C901C3`.
P0010 has SHA-256
`2F01FAA44AF7984DAA3769512E879DEB4C1EF328130EF24E93E712C9602E1F71`
and freezes 1,865 declarations, 3,639 signature edges, 7,414 body/proof
edges, and 7,721 union edges.

## Reviewed destinations

The declaration audit authorizes exactly these 30 vacant production children:

```text
NumStability/Analysis/TestMatrices/Cauchy/
NumStability/Analysis/TestMatrices/Companion/
NumStability/Analysis/TestMatrices/Gaussian/
NumStability/Analysis/TestMatrices/Hilbert/
NumStability/Analysis/TestMatrices/Orthogonal/
NumStability/Analysis/TestMatrices/Pascal/
NumStability/Analysis/TestMatrices/RandomSVD/
NumStability/Analysis/TestMatrices/RealGinibre/
NumStability/Analysis/TestMatrices/Toeplitz/
NumStability/Source/Higham/Chapter28/Equation01/HilbertInverse/
NumStability/Source/Higham/Chapter28/Equation02/ExactHilbertDeterminant/
NumStability/Source/Higham/Chapter28/Equation03/HilbertCholeskyFactor/
NumStability/Source/Higham/Chapter28/Equation04/HilbertCholeskyInverse/
NumStability/Source/Higham/Chapter28/Section01/Cauchy/
NumStability/Source/Higham/Chapter28/Section01/HilbertConditioning/
NumStability/Source/Higham/Chapter28/Section02/RealGinibre/Asymptotics/
NumStability/Source/Higham/Chapter28/Section02/RealGinibre/FiniteExpectation/
NumStability/Source/Higham/Chapter28/Section02/RealGinibre/Incidence/
NumStability/Source/Higham/Chapter28/Section02/RealGinibre/InvariantPlanes/
NumStability/Source/Higham/Chapter28/Section02/RealGinibre/ProbabilityLaw/
NumStability/Source/Higham/Chapter28/Section02/RealGinibre/ProjectiveIntegral/
NumStability/Source/Higham/Chapter28/Section02/RealGinibre/RootMeasurability/
NumStability/Source/Higham/Chapter28/Section02/RealGinibre/SignedIncidence/
NumStability/Source/Higham/Chapter28/Section02/UniformPerron/
NumStability/Source/Higham/Chapter28/Section03/RandomSVD/
NumStability/Source/Higham/Chapter28/Section03/Theorem01/StewartHaar/
NumStability/Source/Higham/Chapter28/Section04/Pascal/
NumStability/Source/Higham/Chapter28/Section04/ReciprocalSpectrumSPD/
NumStability/Source/Higham/Chapter28/Section05/TridiagonalToeplitz/
NumStability/Source/Higham/Chapter28/Section06/Companion/
```

Case-folded tree and scope checks give zero matches for every prefix; pairwise
exact and ancestor/descendant checks and shared-path checks are also zero. No
broad `Analysis/TestMatrices` or Chapter 28 source tree is authorized.

## Declaration-level routing and private closure

The graph contains 1,865 declarations: 1,408 theorems, 454 definitions, one
inductive, one constructor, and one recursor; 1,700 are public and 165 are
private. The 21 reusable, 48 source, and three mixed queue labels are frozen
suggestions, not a legal final dependency proof.

`Higham28` has 80 public declarations and must split source-neutral matrix
constructions from printed equations, schedules, and source conclusions.
`Higham28Contracts` has 73 public and seven private declarations. Its private
closure pins those seven and eight public companion/Toeplitz declarations at
the historical owner. `Higham28GinibreProjectiveIntegral` has three public and
ten private declarations; all 13 are in the private closure, so the complete
declaration-bearing owner stays historical and is exposed through the exact
ProjectiveIntegral source leaf. None of these owners may be classified
wholesale.

The reverse-private graph floor is:

```text
signature: 186 = 165 private + 21 public
body:      423 = 165 private + 258 public
union:     423 = 165 private + 258 public
```

The union-closure payload SHA-256 is
`07D43B378AB6CC169B19A8A0897F5149D1FD5C97C0F87072EA34544D93199CF6`.
No private declaration moves; command and ambient closure may enlarge this
floor.

Twelve current reusable-suggestion-to-source/mixed imports must be resolved by
extracting neutral prerequisites, routing the dependent declaration to
Source, or retaining a dependency-closed historical surface. A canonical
Analysis module may never import Source. `GinibreDimensionTwo`,
`ToeplitzSpectrum`, and `StewartRawFiber` are source-flavored despite their
preliminary labels and require declaration-level review.

`Higham28Companion` has three signature and four body edges into accepted
`NumStability.Analysis.LinearOperators.Jordan.NormalForm.PrimaryDecomposition`.
Its reusable child imports that canonical module directly, never the
historical Jordan implementation or compatibility facade.

## Protected boundaries and joint proof

Future W10 owners `Ch15DixonClosure` and `Ch15DixonProbability` consume the
historical `Higham28OrthogonalCoordinates` surface. They carry 28 signature
and 48 body edges into four W09 owners. W09 must preserve that complete import
surface and must not edit W10. Accepted
`Source.Higham.Chapter28.Equation02.RatioDiscrepancy` is also untouched.

The W04, W09, and W11 selectors have zero owned-path overlap. Their reviewed
production destinations have zero equal or ancestor/descendant overlap.
C0006 imports and typed edges are zero in all six cross-wave directions.
`NumStability/Algorithms.lean` is their integrator-owned common aggregate.
The additional W04/W11 consumer
`NumStability/Algorithms/LinearSystems/LeastSquares/Equality/Basic.lean` is
integrator-owned and forbidden to every worker.

No source migration is authorized by this activation record.
