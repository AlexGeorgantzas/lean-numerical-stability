# W11 integrator requests

These edits are required to integrate W11 but are outside B0010 ownership.
The worker intentionally did not modify any path named below.

## 1. Wire the W11 tests into the shared test root

Create `NumStabilityTest/Reorganization/W11.lean` as an import-only aggregate
containing, in lexicographic order, every one of the 76 `test_module` values in
`TEST_MATRIX.tsv`.  Then add

```lean
import NumStabilityTest.Reorganization.W11
```

to `NumStabilityTest.lean`, sorted between the existing W08 and W12 imports.
The base `NumStabilityTest.lean` blob is
`b65fb6f2fe4ef2d48807482d15d7ad185f2e1a75`; its base file SHA-256 is
`8FE4B60A533FD55596F1C9D36A1D66EBD1490C59E7B93498F38F4AF84CF51588`.
Do not change any W11 test body while wiring the aggregate.

## 2. Classify and expose the canonical production modules

Add the 19 reusable modules listed in `ROUTING.md` and
`DECLARATION_ROUTES.tsv` to the reusable tier under
`NumStability.Algorithms.RandomizedLinearAlgebra`.  Add the 18 reviewed
source modules to the source tier under
`NumStability.Source.DrineasMahoney.RandNLA2016`.  Do not classify a historical
W11 facade as reusable: nine facades necessarily retain private reverse
closure and every historical facade preserves source-specific declarations.

Wire the source discovery aggregate so that `NumStability.Source` reaches the
following ten currently independent source leaves:

- `Algorithm01.ElementwiseSampling.HitCountConcentration`
- `Algorithm01.ElementwiseSampling.Sampling`
- `Algorithm01.ElementwiseSampling.TraceMGF`
- `Algorithm03.RandomProjectionPreconditioning.FloatingPoint`
- `Algorithm03.RandomProjectionPreconditioning.UniformRowComposition`
- `Equation02.SpectralApproximation.ElementwiseSpectral`
- `Equation07.SubspaceEmbedding.ComputedBasis`
- `Equation07.SubspaceEmbedding.LeverageTraceMGF`
- `Equation07.SubspaceEmbedding.RowNormTraceMGF`
- `Equation08.LeastSquaresSketch.Endpoints`

The other eight source leaves are already reached transitively.  Update the
layout baseline to accept the new module documentation on the historical
`NumStability.Algorithms.RandNLA` umbrella; do not remove that documentation.

## 3. Retarget the forbidden shared least-squares consumer

In
`NumStability/Algorithms/LinearSystems/LeastSquares/Equality/Basic.lean`,
replace only

```lean
import NumStability.Algorithms.RandNLA.LowRankApprox
```

with

```lean
import NumStability.Algorithms.RandomizedLinearAlgebra.LowRankApproximation.RankFactorizations.Core
```

The two body edges at the base source lines 8,400 and 8,792 both target
`NumStability.partialColOrthonormal_exists_fullColOrthonormal`, whose exact W11
destination is `RankFactorizations.Core`.  The delivery-head consumer blob is
`d2ab6d9ea8689c3fd9fd0e2b134856e9484c149a`.  Preserve those two uses and make
no other source change.  `Focused.SharedConsumerRetargetTarget` compiles the
requested destination in isolation.

## 4. Remove accepted consumers' stale LowRank facade imports

These accepted paths are outside W11 ownership but cause reusable consumers or
the retained Equation 08 Chapter 20 closure to reach the historical LowRank
facade.  Apply these route-exact import-only retargets while preserving every
declaration and public interface:

- In `Source/Higham/Chapter20/Theorem03/QRSolve.lean`, replace
  `RandNLA.LowRankApprox` with
  `RandomizedLinearAlgebra.LowRankApproximation.ColumnSketches.Core` (7
  signature and 5 body edges; blob
  `702d660203a57d55dc0d8e46858e88b333c03485`).
- In `Algorithms/LinearSystems/LeastSquares/GramBasis.lean`, replace the facade
  with both `LowRankApproximation.ColumnSketches.Core` (8 signature and 28 body
  edges) and `LowRankApproximation.RankFactorizations.Core` (4 body edges; blob
  `c8052a308d6f12efed291ff07eccc3098f8f3f48`).
- In `Algorithms/LinearSystems/QR/GramSchmidtPolar.lean`, replace the facade
  with both `LowRankApproximation.ColumnSketches.Core` (32 signature and 81
  body edges) and `LowRankApproximation.RankFactorizations.Core` (1 body edge;
  blob `9efd74d56bc571d424cec540eb97405e0015eea8`).
- In `Analysis/Perturbation/LeastSquares/GramBasis.lean`, replace the facade
  with `LowRankApproximation.ColumnSketches.Core` (9 signature and 11 body
  edges; blob `77b5699877195fe29ff9184626e9822141bac479`).
- In
  `NumStabilityTest/Import/Compatibility/Algorithms/LeastSquares/CanonicalDependencies.lean`,
  replace its old LowRank import with both canonical low-rank destinations.
  This is an import-only canonical-dependency smoke test and consequently has
  no P0011 declaration edge; do not delete it (blob
  `4a6412b18db3f23622d1b2c545b3e4c209874abc`).

Together with request 3, the five declaration-bearing consumers account for
exactly 188 P0011 incident rows: 56 signature and 132 body/proof edges.  The
two consumers with direct edges to both destinations should import both
destinations explicitly even though `ColumnSketches.Core` currently imports
`RankFactorizations.Core` transitively.

Before those integration edits, the exact three-element source-closure
allowance in `CHECK_STATIC.py` is:

```text
Equation08.Endpoints -> Chapter20.Theorem03.QRSolve -> RandNLA.LowRankApprox
Equation08.Endpoints -> Algorithms.LinearSystems.LeastSquares.GramBasis -> RandNLA.LowRankApprox
Equation08.Endpoints -> Analysis.Perturbation.LeastSquares.GramBasis -> RandNLA.LowRankApprox
```

`CHECK_STATIC.py` permits exactly this three-element source-only set and still
requires zero reusable canonical-to-facade and zero reusable canonical-to-Source
paths.  After integration, tighten/remove the pending set and rerun the checker.

Across the repository there are exactly nine outside-W11 modules containing 11
historical RandNLA import lines.  Requests 3--4 retarget six modules and six old
lines to nine canonical lines (three replacements expand to two explicit
canonical imports); request 5 preserves three modules and five old lines
intentionally.

Before these retargets, the repository strict-source scan has exactly four
reusable roots, each reaching the same eight W11 source targets: direct roots
`Algorithms.LinearSystems.LeastSquares.GramBasis`,
`Algorithms.LinearSystems.QR.GramSchmidtPolar`, and
`Analysis.Perturbation.LeastSquares.GramBasis`, plus the
`Algorithms.LinearSystems.QR` aggregate through `GramSchmidtPolar`.  The eight
targets are:

- `NumStability.Source.DrineasMahoney.RandNLA2016.Algorithm02.RowSampling.Endpoints`
- `NumStability.Source.DrineasMahoney.RandNLA2016.Algorithm03.RandomProjectionPreconditioning.Preconditioning`
- `NumStability.Source.DrineasMahoney.RandNLA2016.Algorithm03.RandomProjectionPreconditioning.UniformRows`
- `NumStability.Source.DrineasMahoney.RandNLA2016.Equation04.RowSamplingProbability.Normalization`
- `NumStability.Source.DrineasMahoney.RandNLA2016.Equation05.GramApproximation.Bounds`
- `NumStability.Source.DrineasMahoney.RandNLA2016.Equation06.LeverageProbability.Normalization`
- `NumStability.Source.DrineasMahoney.RandNLA2016.Equation07.SubspaceEmbedding.Leverage`
- `NumStability.Source.DrineasMahoney.RandNLA2016.Equation09.LowRankApproximation.Endpoints`

Thus the observed count is exactly 4 x 8 = 32, with zero mixed targets and zero
direct forbidden edges.  An in-memory import retarget simulation reduces this
count to zero.

## 5. Preserve compatibility and aggregate surfaces

Keep the import-only `NumStability.Algorithms.RandNLA` root aggregate, its eight
pure import shims, and its nine declaration-bearing private-closure facades as
historical compatibility surfaces.  Classify the declaration-bearing facades
as mixed retention surfaces, never as reusable canonical APIs.  The 18 W11
old-path-only tests and accepted W06 `ProtectedW11` test intentionally exercise
those old paths; this does not include the canonical-dependency smoke retargeted
in request 4.  Do not move the 225 retained declarations.

In particular, preserve these intentional old-path surfaces unchanged:

- `NumStability/Algorithms.lean` importing the `RandNLA` aggregate (blob
  `f59bed9a5a837256bc6b4822eb27116ebd9cc617`);
- `NumStability/Algorithms/LeastSquares/LSQRSolve.lean` importing the LowRank
  compatibility facade (blob `87f54aa8cf952e5023812f7bb834a8c141625ff7`);
- the three old W11 imports in
  `NumStabilityTest/Reorganization/W06/Focused/ProtectedW11.lean` (blob
  `0469207ab042fa8179ef0cf8713e761ace21e0b8`).

After completing requests 1--5, rerun layout, strict-source, all 76 W11 tests,
`lake build NumStability NumStabilityTest`, and `lake test` under
`Local\lean-reorganization-2026-08`.
