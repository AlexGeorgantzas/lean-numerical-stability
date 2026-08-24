# C0006 R09/R10 tier amendment

Primary-human authorized amendment re-anchoring exactly one row of the
reviewed 25-path R0012/R0013 union: `docs/architecture/tiers.json`. The
frozen union patch and its `patch_sha256` pin are deliberately left
unmodified, following the C0005 precedent
`reviews/R0009-R0010-union-migration-amendment.md`.

## Why

The integrated tree fails `generate_baseline.py --strict-source` with **66
classified reusable-to-source reachable pairs** arising from **29 direct
forbidden edges**. 13 destinations created by the two waves are tiered
`reusable` while importing `Source.*` material directly: seven
`Algorithms.RandomizedLinearAlgebra.*` leaves from R10 and six
`Analysis.*` leaves from R09. A `reusable` module must not reach `source`.

The tier assignments, not the code, are what is wrong: these destinations
depend on the Drineas-Mahoney RandNLA 2016 and Higham Chapter 04/23/26/28
correspondence, so they are source-tied rather than reusable. The route plan
assigned them `reusable` and the strict-source gate was never run against the
integrated tree before this amendment.

## Measured convergence

Re-tiering only the thirteen `reusable` offenders reduces 66 pairs to 10 and
then stalls: the residual ten all originate from the aggregate
`NumStability.Analysis.Probability`, which re-exports one re-tiered child and is
itself a **declared reusable entry point**, so it is not `reusable`-tiered
and cannot be moved. Re-tiering the thirteen and withdrawing that one entry-
point declaration converges to zero.

## What this amendment changes

- 13 exact tier assignments, `reusable` -> `source`:

  - `NumStability.Algorithms.RandomizedLinearAlgebra.Preconditioning.CountSketch.HashCollisionProbabilities`
  - `NumStability.Algorithms.RandomizedLinearAlgebra.Preconditioning.CountSketch.SketchInjectivityBounds`
  - `NumStability.Algorithms.RandomizedLinearAlgebra.Preconditioning.CountSketch.SketchedGramLoewnerCovers`
  - `NumStability.Algorithms.RandomizedLinearAlgebra.Preconditioning.CountSketch.SketchedGramMoments`
  - `NumStability.Algorithms.RandomizedLinearAlgebra.Preconditioning.ExactTransforms.UniformRowEmbedding`
  - `NumStability.Algorithms.RandomizedLinearAlgebra.Sampling.UniformRows.GramDotFloatingPoint`
  - `NumStability.Algorithms.RandomizedLinearAlgebra.Sampling.UniformRows.GramMoments`
  - `NumStability.Analysis.Polynomials.RealRootCounting`
  - `NumStability.Analysis.Probability.Haar.NormalizedOrthogonalMatrixLaw`
  - `NumStability.Analysis.TestMatrices.Orthogonal.HaarFiberMeasure`
  - `NumStability.Analysis.TestMatrices.RandomSVD.GroupLawRecursion`
  - `NumStability.Analysis.TestMatrices.RandomSVD.StewartMeasurability`
  - `NumStability.Analysis.TestMatrices.RealGinibre.ProjectiveWeightIntegral`

- one declared reusable entry point withdrawn: `NumStability.Analysis.Probability`
  (entry points 24 -> 23).

## Disclosed architectural cost

`NumStability.Analysis.Probability` was a declared reusable entry point before
R09 and is withdrawn here. That is a real reduction in the declared reusable
surface, not a bookkeeping change. It is withdrawn rather than preserved
because R09 routed source-dependent material beneath it, which made the
declaration false; the alternative -- re-routing those declarations out of the
`Analysis.Probability` subtree to `Source.*` destinations -- preserves the
entry point but requires new postimages, re-materialization and a fresh
delivery pair. Both restore truth; this one is recorded so the trade is
visible rather than implied.

## Union row re-anchor

| path | reviewed postimage | amended postimage |
| --- | --- | --- |
| `docs/architecture/tiers.json` | `87AABC9303DD8D66BC5219A8679995B1756383068D47EE41B829E5717981F4BA` | `3695B84D0644E447765FD5CF30FDD9FF65FBEC794276F494EC3FC2D3709C4C1E` |

The other 24 union postimages are unchanged and remain byte-exact against
`requests/R0012-R0013-union-postimages.tsv`.

