# W10 private reverse closure

Recomputed from the frozen P0013 graph, not taken from the brief. The reverse closure of
the 80 private declarations over the union of signature and body edges has
**132 members = 80 private + 52 public**,
reproducing the preliminary floor of 132 exactly.

Every member is retained at its historical owner. Two independent reasons make this
non-negotiable for the private seeds, and the first alone is decisive:

1. A Lean private declaration's name literally encodes the module that declares it
   (`_private.<module>.0.<name>`). Relocating one renames it, and P0013 pins the exact
   name, so the projection replay would fail on a declaration that still exists.
2. A private is not exported, so any declaration that mentions it cannot leave the module
   either. That is what generates the 52 public dependents.

## Closure by owner

| owner | private seeds | public dependents | total |
| --- | ---: | ---: | ---: |
| `NumStability.Algorithms.Ch15CondEstimators` | 4 | 3 | 7 |
| `NumStability.Algorithms.Chapter15CondEst` | 0 | 3 | 3 |
| `NumStability.Algorithms.CondEstimation` | 4 | 2 | 6 |
| `NumStability.Algorithms.HighamChapter15BoydConcreteLemma3` | 3 | 3 | 6 |
| `NumStability.Algorithms.HighamChapter15BoydScalar` | 1 | 8 | 9 |
| `NumStability.Algorithms.HighamChapter15BoydSourceClosure` | 0 | 4 | 4 |
| `NumStability.Algorithms.HighamChapter15BoydSourceSecondDerivative` | 2 | 2 | 4 |
| `NumStability.Algorithms.HighamChapter15RectTermination` | 43 | 2 | 45 |
| `NumStability.Algorithms.LU.Higham15Problem15_6` | 3 | 2 | 5 |
| `NumStability.Algorithms.LU.Higham15Problem15_6Closure` | 0 | 17 | 17 |
| `NumStability.Algorithms.LU.Higham15Problem15_6Operational` | 0 | 3 | 3 |
| `NumStability.Algorithms.LU.TridiagonalCondCh15Closure` | 19 | 2 | 21 |
| `NumStability.Algorithms.LU.TridiagonalCondCh15IkebeClosure` | 1 | 1 | 2 |
| **total** | **80** | **52** | **132** |

Two owners dominate. `HighamChapter15RectTermination` contributes 43 of the 80 private
seeds, and `LU.Higham15Problem15_6Closure` contributes 17 public dependents while
declaring no private of its own -- it is pinned entirely through what it consumes.
