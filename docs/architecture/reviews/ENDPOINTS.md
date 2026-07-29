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

## Historical follow-up: Phase 10D leading-digit family

Phase 10D reviewed the three flat Chapter 2 leading-digit owners against the
Phase 10C compiled signature/body graph. No declaration outside this
three-module family consumed their APIs, but the declarations were not dead:
they formed two reusable analysis families and two supported Higham source
surfaces.

| Historical module | Semantic result | Canonical destinations | Historical outcome |
| --- | --- | --- | --- |
| `Analysis.LeadingDigitDistribution` | Reusable logarithmic leading-digit probability law. | `Analysis.LeadingDigits.LogarithmicDistribution` | Moved intact; the old path remains an import-only compatibility wrapper. |
| `Analysis.Problem2_11` | Mixed reusable decimal predicates and empirical histograms with source-specific power, factorial, and survey samples. | `Analysis.LeadingDigits.Decimal`, `Analysis.LeadingDigits.Empirical`, and `Source.Higham.Chapter02.Problem11` | Split by role; canonical Problem 11 re-exports the reusable analysis needed to preserve the complete old import surface. |
| `Analysis.HighamChapter2PowerLeadingDigits` | Mixed reusable AddCircle equidistribution and decimal-power reductions with one Section 2.7 source conclusion. | `Analysis.Equidistribution.AddCircle`, `Analysis.LeadingDigits.DecimalPowers`, and `Source.Higham.Chapter02.Section07.PowerLeadingDigits` | Split by role; the old path forwards to canonical Problem 11 and the Section 2.7 leaf so its transitive historical surface remains complete. |

The review preserves all 172 compiled constants and their public names. It
also illustrates why endpoint status cannot determine placement: the generic
Fourier/Haar convergence and decimal-distribution APIs belong in reusable
analysis even though they currently have no consumer outside their source
family, while the empirical sample catalog and final Higham conclusion belong
under the source hierarchy.

## Historical follow-up: Phase 10E Higham frontiers

Phase 10E selected three independent ownership frontiers from Chapters 14,
21, and 28. The Phase 10D declaration graph again distinguishes source
endpoints from a reusable low-fan-in API:

| Historical module | Compiled consumer result | Canonical destination | Historical outcome |
| --- | --- | --- | --- |
| `Algorithms.Ch14HymanDeterminant` | Zero incoming declaration edges from outside the owner. | `Source.Higham.Chapter14.Problem14` | Moved as Problem 14.14 source material; the old path remains an exact one-import compatibility wrapper. |
| `Algorithms.Underdetermined.Higham21Theorem21_3Attainment` | Zero incoming declaration edges from outside the owner. | `Source.Higham.Chapter21.Theorem03.Attainment` | Moved as Theorem 21.3 source material below a declaration-free `Theorem03` aggregate; the old path remains an exact one-import compatibility wrapper. |
| `Algorithms.TestMatrices.Higham28HaarFibers` | Three incoming compiled edges, from `Higham28OrthogonalFibers`, `Higham28OrthogonalCoordinates`, and `Higham28StewartRawFiber`; all are downstream of the sole direct importer, `Higham28OrthogonalSphere`. | `Analysis.Probability.Haar.HomogeneousSpaceUniqueness` | Moved to reusable probability analysis and its direct consumer retargeted; the old path remains an exact one-import compatibility wrapper. |

The batch preserves all 72 compiled constants owned by these modules. The Haar
case is deliberately not placed below `Source.Higham.Chapter28`: its three
measure-uniqueness theorems are generic homogeneous-space results, and
their existing Chapter 28 consumers do not make the API source-specific.

## Historical follow-up: Phase 10F Higham source frontiers

Phase 10F reviewed the next three Chapter 14, 21, and 28 owners against the
Phase 10E compiled signature/body graph. The result is one semantic split and
two source-owner moves:

| Historical module | Compiled consumer result | Canonical destination | Historical outcome |
| --- | --- | --- | --- |
| `Algorithms.Chapter14Problem1415Weyl` | The generic singular-value layer has reusable least-squares consumers; the determinant endpoint is source-specific and has one cross-split body dependency on that generic layer. | `Analysis.SingularValues.WeylMirsky` and `Source.Higham.Chapter14.Problem15` | Split by semantic role. The reusable leaf owns the all-index Weyl--Mirsky API; the source leaf owns the Problem 14.15 determinant bound and counterexample. The old path is an exact one-import wrapper to `Problem15`, whose import surface re-exports the reusable declarations. |
| `Algorithms.Underdetermined.Higham21RowwiseMeasure` | The direct consumers are the historical Chapter 21 Givens/MGS family and its discovery umbrella; the declarations state the printed row-wise measure and Theorem 21.4 criterion. | `Source.Higham.Chapter21.Theorem04.RowwiseBackwardError` | Moved intact below a declaration-free `Theorem04` aggregate; direct consumers were retargeted and the old path remains an exact one-import wrapper. |
| `Algorithms.TestMatrices.Higham28HilbertRatioDiscrepancy` | No incoming compiled declaration consumers. Its declarations are the equation (28.2) ratio interpretation, growth proof, and source-discrepancy witness. | `Source.Higham.Chapter28.Equation02.RatioDiscrepancy` | Moved intact below declaration-free Chapter 28 and `Equation02` aggregates; the old path remains an exact one-import wrapper. |

The Chapter 28 leaf deliberately retains its direct import of the historical
`Algorithms.TestMatrices.Higham28HilbertAsymptotic` owner. That dependency is
recorded debt, not evidence that the broader Hilbert family has already moved.
Likewise, the Chapter 14 split establishes a reusable singular-value API and a
source endpoint without migrating the remaining Chapter 14 proof families.

## Phase 11A follow-up: Higham Theorem 6.4 source tail

The compiled signature/body graph found 21 declarations in the ambient-radius
tail of the former `Analysis.Norms` implementation, with no incoming
declaration edge from outside that tail. They are not dead code: together they
realize the literal source statement and closure of Higham's Theorem 6.4, so
Phase 11A moved them to the canonical
`Source.Higham.Chapter06.Theorem04` leaf.

The split retains 166 one-way cross-owner dependencies from the source leaf to
`Analysis.Norms.Core`: 67 occur in declaration signatures and 99 in bodies.
There was no reverse dependency from the core into the source leaf. At the
Phase 11A checkpoint, the old `Analysis.Norms` path became a two-target
compatibility facade, production consumers used the canonical owners, and
`Analysis.Norms.Core` remained explicitly unclassified pending the
signature-graph-guided Phase 11B semantic split.

## Phase 11B1 follow-up: semantic norm ownership

Phase 11B1 completed that bounded semantic split. The frozen ownership
manifest maps all 1,783 former Core constants to 24 declaration-bearing
owners: 20 reusable leaves below semantic Analysis families and four source
leaves for Higham Problems 6.1, 6.5, 6.9, and 6.10. The normalized declaration
and signature/body dependency graph is preserved exactly, with no reusable-to-
source path.

`Analysis.Norms.Core` is now a declaration-free reusable aggregate, and the
historical `Analysis.Norms` facade imports Core plus the dedicated
`Source.Higham.Chapter06.Norms` aggregate. Direct production consumers were
retargeted to their narrow canonical owners; no declaration-bearing production
module still imports Core. At the Phase 11B1 checkpoint, compatibility stood at
104 wrappers and 204 direct targets.

That phase deliberately did not move `Algorithms.Chapter06Lemma66`,
`Analysis.Higham6Asides`, `Analysis.Higham6BlockAntidiag`, or
`Analysis.HighamChapter6Duality`. Those four historically named source owners
therefore remained in the unclassified/noncanonical queues for the separately
bounded Phase 11B2 move.

## Phase 11B2 follow-up: Chapter 6 source tail

Phase 11B2 completed that bounded move. The frozen ownership map assigns all 69
declarations from the four historical owners to nine declaration-bearing
source leaves, with no declaration or proof-strength change:

| Historical owner | Canonical ownership | Compatibility target |
| --- | --- | --- |
| `Algorithms.Chapter06Lemma66` | `Source.Higham.Chapter06.Lemma06` | `Source.Higham.Chapter06.Lemma06` |
| `Analysis.Higham6Asides` | `Source.Higham.Chapter06.Asides.ConditionNumberBounds`, `EuclideanNormDifferentiability`, `MaxNormInconsistency`, and `UnitaryInvariance`; sibling `Equation01`; and `BlockAntidiagonalNorm.OperatorTwo` | `Source.Higham.Chapter06.Asides` |
| `Analysis.Higham6BlockAntidiag` | `Source.Higham.Chapter06.BlockAntidiagonalNorm.InducedLp` | `Source.Higham.Chapter06.BlockAntidiagonalNorm.InducedLp` |
| `Analysis.HighamChapter6Duality` | `Source.Higham.Chapter06.Equation02` | `Source.Higham.Chapter06.Equation02` |

`Chapter06.Asides` and `Chapter06.BlockAntidiagonalNorm` are declaration-free
family aggregates; the four historical paths are exact one-target wrappers.
The two declaration-consuming Lemma 6.6 importers,
`Algorithms.Ch10Ch14Lemma66Op2Bridge` and
`Algorithms.QR.Higham19Theorem5SourceClosure`, now import `Lemma06` directly.
At the Phase 11B2 checkpoint, the compatibility inventory was 108 wrappers and
208 direct targets. The Phase 12 two-target BlockLU facade brings the current
inventory to 109 wrappers and 210 direct targets.
