# Endpoint-module reviews

The repository report identified seven modules because every declaration was
an apparent leaf. The corrected signature/body extractor subsequently exposed
three more. This is a review queue, not deletion evidence. Each module was read
and classified semantically before deciding whether it belonged in the first
move pilot.

| Historical module | Classification | Canonical destination | Action |
| --- | --- | --- | --- |
| `Algorithms.Ch14SourceCorrections` | Higham §14.6 source discrepancy | `Higham.Chapter14.Discrepancies` | Move; retain old import wrapper. |
| `Algorithms.LU.BlockLUTable13_1Families` | Higham Table 13.1 and Equation 13.25 capstone | `Higham.Chapter13.Table13_1` | Move; retain old import wrapper. |
| `Algorithms.LeastSquares.Higham20SourceAliases` | Higham 20.32, Lemma 20.6, and Theorem 20.1 aliases | `Higham.Chapter20.SourceAliases` | Move aliases; retain old import wrapper. Reusable perturbation results remain under algorithms. |
| `Algorithms.TriangularSolveCombined` | Reusable combined triangular-solve theorem | `Algorithms.LinearSystems.Triangular.Combined` | Move into the reusable API; retain old import wrapper. |
| `Analysis.Problem2_22` | Higham Problem 2.22 wrappers over reusable Heron results | `Higham.Chapter02.Problem22` | Move; retain old import wrapper. |
| `Analysis.Problem2_4` | Higham Problem 2.4 wrappers over the inverse-error relation | `Higham.Chapter02.Problem04` | Move; retain old import wrapper. |
| `Analysis.Problem2_7` | Mixed generic operation laws and source counterexamples | `FloatingPoint.OperationLaws` plus `Higham.Chapter02.Problem07` | Split by meaning; retain an old wrapper importing both. |
| `Algorithms.QR.Higham19Lemma3ActualSequence` | Higham Lemma 19.3 source endpoint over reusable stored-Householder producers | Future `Higham.Chapter19` module | Retain for this slice; move with the Chapter 19 QR source cluster so its broad support imports can be reviewed together. |
| `Algorithms.QR.Higham19Theorem6ActualSource` | Import-and-alias endpoint for Higham Theorem 19.6 | Future `Higham.Chapter19` source-alias module | Retain for this slice; co-migrate with the Theorem 20.7 assembly dependency rather than hiding the current cross-chapter direction. |
| `Analysis.MatrixPowersSpijkerClosure` | Higham Chapter 18 Kreiss/Spijker source capstone | Future `Higham.Chapter18` module | Retain for this slice; queue with the MatrixPowers source cluster and preserve the public endpoint. |

## Conclusions

- None of the ten modules is dead code.
- Nine are useful source-facing endpoints or compatibility surfaces.
- `TriangularSolveCombined` is reusable despite having no current project
  consumer; downstream reuse is an API-design question, not a graph-degree
  threshold.
- `Problem2_7` demonstrates why whole-file moves based on filenames are unsafe:
  the generic round-to-even identities belong below the Higham layer, while the
  numbered problem and counterexamples belong in it.
- Compatibility wrappers preserve historical imports during the migration.
