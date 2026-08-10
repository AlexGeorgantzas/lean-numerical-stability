# W10 changed paths

Every path W10 writes lies inside B0012's owned paths, its authorized destination
prefixes, `NumStabilityTest/Reorganization/W10/`, or
`docs/architecture/deliveries/W10/`. `apply.py` enforces this structurally by reading
B0012 and honouring each entry's declared `match` kind; it reported 0 unauthorized
targets over all 124 emitted Lean files.

| class | paths |
| --- | ---: |
| evidence | 10 |
| owner facade | 27 |
| reusable destination | 49 |
| source destination | 47 |
| test | 135 |
| **total** | **268** |

## Integrator-owned files: untouched

`NumStability/Algorithms.lean` and
`NumStability/Algorithms/LinearSystems/LeastSquares/Equality/Basic.lean` are rejected by
`apply.py` structurally, not by convention, and `git status` shows neither. No root
aggregate, test root, `tiers.json`, layout exception, compatibility manifest, accepted
consumer, CI or toolchain file is modified. No new aggregator edit was needed: each of the
27 owners remains a facade importing its own destinations, and the aggregates already
import the owners.

## Modified (27)

- `NumStability/Algorithms/Ch15CondEstimators.lean`
- `NumStability/Algorithms/Ch15DixonClosure.lean`
- `NumStability/Algorithms/Ch15DixonProbability.lean`
- `NumStability/Algorithms/Chapter15CondEst.lean`
- `NumStability/Algorithms/CondEstimation.lean`
- `NumStability/Algorithms/HighamChapter15BoydBridges.lean`
- `NumStability/Algorithms/HighamChapter15BoydConcreteLemma3.lean`
- `NumStability/Algorithms/HighamChapter15BoydLocalStability.lean`
- `NumStability/Algorithms/HighamChapter15BoydRowwiseDomain.lean`
- `NumStability/Algorithms/HighamChapter15BoydScalar.lean`
- `NumStability/Algorithms/HighamChapter15BoydSourceClosure.lean`
- `NumStability/Algorithms/HighamChapter15BoydSourceDomain.lean`
- `NumStability/Algorithms/HighamChapter15BoydSourceLocal.lean`
- `NumStability/Algorithms/HighamChapter15BoydSourceSecondDerivative.lean`
- `NumStability/Algorithms/HighamChapter15BoydUniqueness.lean`
- `NumStability/Algorithms/HighamChapter15ConvergenceProse.lean`
- `NumStability/Algorithms/HighamChapter15RectTermination.lean`
- `NumStability/Algorithms/LU/Higham15Problem15_4.lean`
- `NumStability/Algorithms/LU/Higham15Problem15_6.lean`
- `NumStability/Algorithms/LU/Higham15Problem15_6Closure.lean`
- `NumStability/Algorithms/LU/Higham15Problem15_6Operational.lean`
- `NumStability/Algorithms/LU/TridiagonalCondCh15.lean`
- `NumStability/Algorithms/LU/TridiagonalCondCh15Closure.lean`
- `NumStability/Algorithms/LU/TridiagonalCondCh15IkebeClosure.lean`
- `NumStability/Algorithms/PNormPowerMethod.lean`
- `NumStability/Algorithms/PNormPowerMethodGeneralP.lean`
- `NumStability/Algorithms/PNormPowerMethodRect.lean`

## Added (241)

New trees:

- `NumStability/Algorithms/NormEstimation/OneNorm/FiniteIndex/`
- `NumStability/Algorithms/NormEstimation/OneNorm/LAPACK/`
- `NumStability/Algorithms/NormEstimation/OneNorm/LINPACK/`
- `NumStability/Algorithms/NormEstimation/OneNorm/PowerMethod/`
- `NumStability/Algorithms/NormEstimation/PNorm/`
- `NumStability/Algorithms/NormEstimation/TwoNorm/`
- `NumStability/Source/Higham/Chapter15/`
- `NumStabilityTest/Reorganization/W10/`
- `docs/architecture/deliveries/W10/`
