# W10 private reverse closure

Recomputed from the frozen P0013 graph, not taken from the brief. The reverse closure of
the 80 private declarations over the union of signature and body edges has
**132 members = 80 private + 52 public**,
reproducing the preliminary floor of 132 exactly.

Actual physical retention is **134**. Two additional public declarations in
`NumStability.Algorithms.Chapter15CondEst` are full-graph re-entry hazards outside this
selected-induced closure:

- `NumStability.Higham15.H15_Algorithm15_4_condEstimate_le_kappaOne`;
- `NumStability.Higham15.H15_Algorithm15_4_scaled_le_kappaOne`.

They remain at their exact C0007 owner so P0013 preserves the incident body edges that
leave W10 through `NumStability.Analysis.ConditionEstimatorLowerBound` and re-enter a
selected retained declaration. The 132-name closure payload hash remains
`19B36D816074EEC2401724AC84EFA107FB4ACD3672F7D91960247E65223B570E`; the ordinal-sorted
134-name actual-retention payload hash is
`E241404E2D4F7CC3A6B1BD6B3E8EA074BDB93AC064B0897FEAFB59CD1D093A37`.

Every member is retained at its historical owner. Two independent reasons make this
non-negotiable for the private seeds, and the first alone is decisive:

1. A Lean private declaration's name literally encodes the module that declares it
   (`_private.<module>.0.<name>`). Relocating one renames it, and P0013 pins the exact
   name, so the projection replay would fail on a declaration that still exists.
2. A private is not exported, so any declaration that mentions it cannot leave the module
either. That is what generates the 52 public dependents.

`CHECK_STATIC.py` independently requires 132 unique closure rows, the exact 80/52 role
split, equality with the 132 pinned route rows, exactly the two unpinned re-entry routes,
and equality of every per-owner total in `RETENTION.tsv`. It also proves that no private
declaration is moved or promoted.

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
