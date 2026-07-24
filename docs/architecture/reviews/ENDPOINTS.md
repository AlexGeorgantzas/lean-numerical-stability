# Endpoint-module reviews

The repository report identified seven modules because every declaration was
an apparent leaf. The corrected signature/body extractor subsequently exposed
three more. This is a review queue, not deletion evidence. Each module was read
and classified semantically before deciding whether it belonged in the first
move pilot.

| Historical module | Classification | Canonical destination | Action |
| --- | --- | --- | --- |
| `Algorithms.Ch14SourceCorrections` | Higham §14.6 source discrepancy | `Source.Higham.Chapter14.Discrepancies` | Moved; both historical paths remain import-only wrappers. |
| `Algorithms.LU.BlockLUTable13_1Families` | Higham Table 13.1 and Equation 13.25 capstone | `Source.Higham.Chapter13.Table01` and `Equation25` | Moved by locator; both historical paths remain import-only wrappers. |
| `Algorithms.LeastSquares.Higham20SourceAliases` | Higham 20.32, Lemma 20.6, and Theorem 20.1 aliases | `Source.Higham.Chapter20.Equation32`, `Lemma06`, and `Theorem01` | Moved by locator; both historical paths remain import-only wrappers. Reusable perturbation results remain under algorithms. |
| `Algorithms.TriangularSolveCombined` | Reusable combined triangular-solve theorem | `Algorithms.LinearSystems.Triangular.Combined` | Move into the reusable API; retain old import wrapper. |
| `Analysis.Problem2_21` | Printed Higham Problem 2.22, the naive IEEE maximum branch with NaN operands | `FloatingPoint.IEEE.NaiveMaximum`, located from `Source.Higham.Chapter02.Problem22` | Moved into the reusable IEEE API; the historical Analysis path remains an import-only wrapper. |
| `Analysis.Problem2_22` | Printed Higham Problem 2.23 wrappers over reusable Heron results | `Source.Higham.Chapter02.Problem23` | Corrected from the former canonical Problem 22 locator; both historical paths remain import-only wrappers. |
| `Analysis.Problem2_4` | Higham Problem 2.4 wrappers over the inverse-error relation | `Source.Higham.Chapter02.Problem04` | Moved; both historical paths remain import-only wrappers. |
| `Analysis.Problem2_7` | Mixed generic operation laws and source counterexamples | `FloatingPoint.OperationLaws` plus `Source.Higham.Chapter02.Problem07` | Split by meaning; retain an old wrapper importing both. |
| `Algorithms.QR.Higham19Lemma3ActualSequence` | Higham Lemma 19.3 source endpoint over reusable stored-Householder producers | Future `Source.Higham.Chapter19` module | Retain for this slice; move with the Chapter 19 QR source cluster so its broad support imports can be reviewed together. |
| `Algorithms.QR.Higham19Theorem6ActualSource` | Import-and-alias endpoint for Higham Theorem 19.6 | Future `Source.Higham.Chapter19` source-alias module | Retain for this slice; co-migrate with the Theorem 20.7 assembly dependency rather than hiding the current cross-chapter direction. |
| `Analysis.MatrixPowersSpijkerClosure` | Higham Chapter 18 Kreiss/Spijker source capstone | Future `Source.Higham.Chapter18` module | Retain for this slice; queue with the MatrixPowers source cluster and preserve the public endpoint. |

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

## Historical follow-up: Phase 10B small frontiers

Phase 10B re-ran the endpoint review at execution base
`21e130ac8355de8ec1a74f22a73bf103e00bc48f` using the compiled
signature/body graph. Three additional source-facing owners had zero external
declaration consumers and were moved into the source hierarchy:

| Historical module | Compiled consumer result | Canonical destination | Historical outcome |
| --- | --- | --- | --- |
| `Analysis.Problem2_2` | Zero external declaration consumers. | `Source.Higham.Chapter02.Problem02` | Moved as source material; the historical path remains an exact one-import compatibility wrapper. |
| `Algorithms.Ch14Problem1413Boundary` | Zero incoming external declaration consumers. | `Source.Higham.Chapter14.Problem13` | Moved as source material; the historical path remains an exact one-import compatibility wrapper. |
| `Algorithms.Underdetermined.Higham21Condition` | Zero incoming external declaration consumers; its direct importers were organizational or source-family surfaces. | `Source.Higham.Chapter21.RowScalingInvariance` | Moved as source material; the historical path remains an exact one-import compatibility wrapper. |

### Low fan-in is not an endpoint criterion

`Algorithms.TestMatrices.Higham28GaussianAbsoluteMoment` was reviewed in the
same batch, but it was not an endpoint. Its declarations have one compiled
external consumer, `realGinibreAbsoluteCharacteristicMoment_one` in
`Algorithms.TestMatrices.Higham28GinibreDeterminantMoment`. More importantly,
the declarations form a source-neutral Gaussian probability API. They were
moved to the reusable module `Analysis.Probability.Gaussian.AbsoluteMoment`,
while the historical path became an exact one-import compatibility wrapper.
This reinforces that semantic role, rather than fan-in alone, determines
whether a module is a source endpoint or reusable library code.

The original ten-module introduction, table, and conclusions above remain the
historical record of the initial endpoint-review pilot; this follow-up records
the later Phase 10B decisions without rewriting that earlier assessment.
