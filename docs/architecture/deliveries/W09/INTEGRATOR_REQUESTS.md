# W09 integrator requests

Nothing in this wave required an integrator-owned file to change. The two files forbidden to every worker -- `NumStability/Algorithms.lean` and `NumStability/Algorithms/LinearSystems/LeastSquares/Equality/Basic.lean` -- are untouched, and `apply.py` rejects them structurally rather than by convention.

## Consumers outside the wave that keep working through the facades

`importgraph.py` found exactly five modules outside W09 that import a W09 owner. All continue to resolve, because every owner remains a compatibility module.

| consumer | note |
| --- | --- |
| `NumStability.Algorithms` | integrator-owned aggregator; not edited |
| `NumStability.Algorithms.Ch15DixonClosure` | out-of-wave |
| `NumStability.Algorithms.Ch15DixonProbability` | out-of-wave |
| `NumStability.Source.Higham.Chapter28.Equation02.RatioDiscrepancy` | pre-existing tracked module under a W09 destination prefix; not owned by W09 and never written or deleted |
| `NumStabilityTest.Reorganization.W06.Focused.ProtectedW09` | W06's test of the W09 surface; root tests are not edited |

## Protected surfaces

W10 consumes four W09 owners through `Higham28OrthogonalCoordinates` across 28 signature and 48 body edges. W09 does not edit W10, W04 or W11; it keeps that surface resolvable from the historical path, and `Focused/W10ProtectedSurface` tests it directly.
