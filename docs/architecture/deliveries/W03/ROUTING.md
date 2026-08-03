# W03 declaration routing

Wave `W03`, branch `codex/reorg-2026-08-w03-cholesky-ch10`, phase branch `B0004`, base checkpoint
`C0004` at `b56f609f3bf66b5d7d0b677567cce82fee0c275b`.

Every one of the 1,034 declarations selected by `W03.tsv` appears exactly once in
`ROUTING.tsv`. A destination equal to the owner marks a *retained* declaration.
`P0005` lists all 26 owners under `--allow-module`, so retention preserves each
declaration's name, kind, visibility and every incident edge.

## Structural decisions

**Prefixes are shared; modules are not.** B0004 authorizes 32 production prefixes,
and several legitimately receive material from two owners -- `Lemma13/KahanSharpness`
takes the limit calculation from `Ch10KahanSharpness` and the Gram packaging from
`Ch10KahanSharpnessSource`. Each destination *module*, however, is sourced from
exactly one owner: a module fed by two owners inherits the union of both owners'
imports and widens the transitive surface for downstream consumers.

**Reusable destinations do not inherit Source imports.** `HighamChapter10` is a
genuinely mixed owner that directly imports ten `Source.Higham.Chapter09.*` modules.
Its source-numbered declarations need them; its reusable eigenvalue and matrix-norm
lemmas do not. Inheriting the owner's ambient set wholesale would drag Source into
the reusable tier, so Source imports are pruned from reusable destinations and the
build is the proof that nothing reusable needed them.

## The three declaration-level splits B0004 requires

| owner | signal | outcome |
| --- | --- | --- |
| `CholeskyIndefinite` | the 13 printed Chapter 11 endpoints are exactly the declarations whose names contain `printed` (measured count 13, matching B0004's review) | 13 to `Chapter11.Theorem07.TridiagonalTwoByTwoResidual`, 199 reusable to `SymmetricIndefinite.{Pivoting,ErrorAnalysis}` |
| `CholeskyPSD` | no declaration name carries a source number, so routing is by section position against the file's own section comments (lines 32, 55, 220, 361, 1184, 1205, 1223, 3857, 4020, 4084, 4116) | reusable predicate and pivoted factorization stay reusable; Theorem 10.9, Lemma 10.10, Lemma 10.12, Lemma 10.13, Theorem 10.14 and the termination criteria become source |
| `HighamChapter10` | explicit `higham10_NN` and `higham10_problem_10_N` numbering | 100 numbered declarations to their Chapter 10 results, 4 to Problem 10.1, 5 to Problem 10.4, 4 to Problem 10.8, and 51 unnumbered reusable declarations to `MatrixNorms.{SpectralExtrema,EntrywiseAbsolute}` and the Cholesky reusable roots |

`Ch10Ch14Lemma66Op2Bridge` holds four declarations spanning three chapters and is
split accordingly: two to `Chapter06.Lemma06.OperatorTwoNormBound`, one to
`Chapter14.Section03.ResidualOperatorTwoNorm`, one to
`Chapter10.Equation07.AbsoluteFactorNorm`.

## Per-owner routing

### `NumStability.Algorithms.Ch10ActualSourceClosure`

7 declarations; 1 retained, 6 relocated.

| destination | declarations |
| --- | ---: |
| `NumStability.Source.Higham.Chapter10.Theorem06.RoundedCholesky.ActualClosure` | 6 |
| `NumStability.Algorithms.Ch10ActualSourceClosure` *(retained)* | 1 |

### `NumStability.Algorithms.Ch10Ch14Lemma66Op2Bridge`

4 declarations; 0 retained, 4 relocated.

| destination | declarations |
| --- | ---: |
| `NumStability.Source.Higham.Chapter06.Lemma06.OperatorTwoNormBound.Bridge` | 2 |
| `NumStability.Source.Higham.Chapter10.Equation07.AbsoluteFactorNorm.Bridge` | 1 |
| `NumStability.Source.Higham.Chapter14.Section03.ResidualOperatorTwoNorm.Bridge` | 1 |

### `NumStability.Algorithms.Ch10ComplexPositiveDefiniteSourceClosure`

95 declarations; 69 retained, 26 relocated.

| destination | declarations |
| --- | ---: |
| `NumStability.Algorithms.Ch10ComplexPositiveDefiniteSourceClosure` *(retained)* | 69 |
| `NumStability.Source.Higham.Chapter10.Equation30.ComplexPositiveDefinite.SourceClosure` | 26 |

### `NumStability.Algorithms.Ch10KahanSharpness`

14 declarations; 0 retained, 14 relocated.

| destination | declarations |
| --- | ---: |
| `NumStability.Source.Higham.Chapter10.Lemma13.KahanSharpness.Limit` | 14 |

### `NumStability.Algorithms.Ch10KahanSharpnessSource`

36 declarations; 10 retained, 26 relocated.

| destination | declarations |
| --- | ---: |
| `NumStability.Source.Higham.Chapter10.Lemma13.KahanSharpness.GramFamily` | 26 |
| `NumStability.Algorithms.Ch10KahanSharpnessSource` *(retained)* | 10 |

### `NumStability.Algorithms.Ch10Lemma1011Source`

7 declarations; 0 retained, 7 relocated.

| destination | declarations |
| --- | ---: |
| `NumStability.Source.Higham.Chapter10.Lemma11.PivotSequenceStability.SourceClosure` | 7 |

### `NumStability.Algorithms.Ch10PivotedPSDSourceClosure`

60 declarations; 6 retained, 54 relocated.

| destination | declarations |
| --- | ---: |
| `NumStability.Source.Higham.Chapter10.Theorem14.CompletePivotedPSD.ActualRun` | 54 |
| `NumStability.Algorithms.Ch10PivotedPSDSourceClosure` *(retained)* | 6 |

### `NumStability.Algorithms.Ch10Theorem107FailureVacuity`

3 declarations; 0 retained, 3 relocated.

| destination | declarations |
| --- | ---: |
| `NumStability.Source.Higham.Chapter10.Theorem07.FailureVacuity.Vacuity` | 3 |

### `NumStability.Algorithms.Ch10Theorem108Componentwise`

13 declarations; 10 retained, 3 relocated.

| destination | declarations |
| --- | ---: |
| `NumStability.Algorithms.Ch10Theorem108Componentwise` *(retained)* | 10 |
| `NumStability.Source.Higham.Chapter10.Theorem08.ComponentwisePerturbation.Resolvent` | 3 |

### `NumStability.Algorithms.Ch10Theorem108Source`

32 declarations; 1 retained, 31 relocated.

| destination | declarations |
| --- | ---: |
| `NumStability.Source.Higham.Chapter10.Theorem08.NormwiseDiscrepancy.LiteralSource` | 31 |
| `NumStability.Algorithms.Ch10Theorem108Source` *(retained)* | 1 |

### `NumStability.Algorithms.Cholesky.CholeskyDemmel`

21 declarations; 1 retained, 20 relocated.

| destination | declarations |
| --- | ---: |
| `NumStability.Algorithms.LinearSystems.Cholesky.ErrorAnalysis.Demmel` | 20 |
| `NumStability.Algorithms.Cholesky.CholeskyDemmel` *(retained)* | 1 |

### `NumStability.Algorithms.Cholesky.CholeskyFl`

53 declarations; 25 retained, 28 relocated.

| destination | declarations |
| --- | ---: |
| `NumStability.Algorithms.LinearSystems.Cholesky.RoundedFactorization.Basic` | 28 |
| `NumStability.Algorithms.Cholesky.CholeskyFl` *(retained)* | 25 |

### `NumStability.Algorithms.Cholesky.CholeskyIndefinite`

212 declarations; 0 retained, 212 relocated.

| destination | declarations |
| --- | ---: |
| `NumStability.Algorithms.LinearSystems.SymmetricIndefinite.ErrorAnalysis.BlockLDLT` | 96 |
| `NumStability.Algorithms.LinearSystems.SymmetricIndefinite.Pivoting.Basic` | 45 |
| `NumStability.Algorithms.LinearSystems.SymmetricIndefinite.Pivoting.Tridiagonal` | 44 |
| `NumStability.Source.Higham.Chapter11.Theorem07.TridiagonalTwoByTwoResidual.Basic` | 13 |
| `NumStability.Algorithms.LinearSystems.SymmetricIndefinite.ErrorAnalysis.BlockLDLTStep` | 6 |
| `NumStability.Algorithms.LinearSystems.SymmetricIndefinite.ErrorAnalysis.Predicates` | 5 |
| `NumStability.Algorithms.LinearSystems.SymmetricIndefinite.ErrorAnalysis.SkewSymmetric` | 3 |

### `NumStability.Algorithms.Cholesky.CholeskyNonsym`

19 declarations; 4 retained, 15 relocated.

| destination | declarations |
| --- | ---: |
| `NumStability.Algorithms.LinearSystems.LU.NonsymmetricPositiveDefinite.Basic` | 15 |
| `NumStability.Algorithms.Cholesky.CholeskyNonsym` *(retained)* | 4 |

### `NumStability.Algorithms.Cholesky.CholeskyPSD`

99 declarations; 18 retained, 81 relocated.

| destination | declarations |
| --- | ---: |
| `NumStability.Source.Higham.Chapter10.Section03.PositiveSemidefinite.SchurComplement` | 46 |
| `NumStability.Algorithms.Cholesky.CholeskyPSD` *(retained)* | 18 |
| `NumStability.Algorithms.LinearSystems.Cholesky.PositiveSemidefinite.Basic` | 18 |
| `NumStability.Source.Higham.Chapter10.Section03.PositiveSemidefinite.Existence` | 9 |
| `NumStability.Source.Higham.Chapter10.Section03.PositiveSemidefinite.WNormBound` | 4 |
| `NumStability.Source.Higham.Chapter10.Lemma13.KahanSharpness.CompletePivotingBound` | 2 |
| `NumStability.Source.Higham.Chapter10.Section03.PositiveSemidefinite.Termination` | 1 |
| `NumStability.Source.Higham.Chapter10.Theorem14.CompletePivotedPSD.PsdErrorAnalysis` | 1 |

### `NumStability.Algorithms.Cholesky.CholeskyPerturbation`

43 declarations; 0 retained, 43 relocated.

| destination | declarations |
| --- | ---: |
| `NumStability.Algorithms.LinearSystems.Cholesky.Perturbation.Basic` | 43 |

### `NumStability.Algorithms.Cholesky.CholeskySolve`

3 declarations; 0 retained, 3 relocated.

| destination | declarations |
| --- | ---: |
| `NumStability.Algorithms.LinearSystems.Cholesky.Solve.Basic` | 3 |

### `NumStability.Algorithms.Cholesky.CholeskySpec`

30 declarations; 7 retained, 23 relocated.

| destination | declarations |
| --- | ---: |
| `NumStability.Algorithms.LinearSystems.Cholesky.Factorization.Spec` | 23 |
| `NumStability.Algorithms.Cholesky.CholeskySpec` *(retained)* | 7 |

### `NumStability.Algorithms.Cholesky.Higham1014Equation1022`

32 declarations; 9 retained, 23 relocated.

| destination | declarations |
| --- | ---: |
| `NumStability.Source.Higham.Chapter10.Theorem14.CompletePivotedPSD.Equation22` | 23 |
| `NumStability.Algorithms.Cholesky.Higham1014Equation1022` *(retained)* | 9 |

### `NumStability.Algorithms.Cholesky.Higham1014SourceError`

18 declarations; 13 retained, 5 relocated.

| destination | declarations |
| --- | ---: |
| `NumStability.Algorithms.Cholesky.Higham1014SourceError` *(retained)* | 13 |
| `NumStability.Source.Higham.Chapter10.Theorem14.CompletePivotedPSD.SourceError` | 5 |

### `NumStability.Algorithms.Cholesky.Higham1014SourceSuccess`

1 declarations; 0 retained, 1 relocated.

| destination | declarations |
| --- | ---: |
| `NumStability.Source.Higham.Chapter10.Theorem14.CompletePivotedPSD.SourceSuccess` | 1 |

### `NumStability.Algorithms.Cholesky.Higham1029Source`

17 declarations; 3 retained, 14 relocated.

| destination | declarations |
| --- | ---: |
| `NumStability.Source.Higham.Chapter10.Section04.PositiveDefiniteSymmetricPart.Equation29` | 14 |
| `NumStability.Algorithms.Cholesky.Higham1029Source` *(retained)* | 3 |

### `NumStability.Algorithms.Cholesky.Higham10Problem10_3`

1 declarations; 0 retained, 1 relocated.

| destination | declarations |
| --- | ---: |
| `NumStability.Source.Higham.Chapter10.Problem03.ArbitraryEvaluationOrder.Basic` | 1 |

### `NumStability.Algorithms.Cholesky.HighamMathiasFirstBreakdown`

3 declarations; 0 retained, 3 relocated.

| destination | declarations |
| --- | ---: |
| `NumStability.Source.Higham.Chapter10.Equation29.Mathias.FirstBreakdown` | 3 |

### `NumStability.Algorithms.Cholesky.HighamMathiasSource`

47 declarations; 5 retained, 42 relocated.

| destination | declarations |
| --- | ---: |
| `NumStability.Source.Higham.Chapter10.Equation29.Mathias.SourceIngredients` | 42 |
| `NumStability.Algorithms.Cholesky.HighamMathiasSource` *(retained)* | 5 |

### `NumStability.Algorithms.HighamChapter10`

164 declarations; 46 retained, 118 relocated.

| destination | declarations |
| --- | ---: |
| `NumStability.Algorithms.HighamChapter10` *(retained)* | 46 |
| `NumStability.Analysis.MatrixNorms.EntrywiseAbsolute.Basic` | 16 |
| `NumStability.Analysis.MatrixNorms.SpectralExtrema.Basic` | 15 |
| `NumStability.Source.Higham.Chapter10.Section03.PositiveSemidefinite.Endpoints` | 15 |
| `NumStability.Source.Higham.Chapter10.Section02.ErrorAnalysis.Basic` | 8 |
| `NumStability.Source.Higham.Chapter10.Lemma11.PivotSequenceStability.Endpoints` | 7 |
| `NumStability.Source.Higham.Chapter10.Section04.PositiveDefiniteSymmetricPart.Endpoints` | 7 |
| `NumStability.Source.Higham.Chapter10.Theorem07.FailureVacuity.Endpoints` | 7 |
| `NumStability.Algorithms.LinearSystems.Cholesky.ErrorAnalysis.Certificates` | 6 |
| `NumStability.Algorithms.LinearSystems.Cholesky.PositiveSemidefinite.ScaledStage` | 6 |
| `NumStability.Source.Higham.Chapter10.Problem01.PositiveSemidefiniteEntries.Basic` | 5 |
| `NumStability.Source.Higham.Chapter10.Theorem06.RoundedCholesky.Endpoints` | 5 |
| `NumStability.Source.Higham.Chapter10.Lemma13.KahanSharpness.Endpoints` | 4 |
| `NumStability.Source.Higham.Chapter10.Problem08.LeadingMinorsCounterexample.Basic` | 4 |
| `NumStability.Source.Higham.Chapter10.Section01.Factorization.Basic` | 4 |
| `NumStability.Source.Higham.Chapter10.Theorem14.CompletePivotedPSD.Endpoints` | 2 |
| `NumStability.Algorithms.LinearSystems.Cholesky.PositiveSemidefinite.KahanMatrix` | 1 |
| `NumStability.Source.Higham.Chapter10.Equation07.AbsoluteFactorNorm.Endpoints` | 1 |
| `NumStability.Source.Higham.Chapter10.Equation29.Mathias.Endpoints` | 1 |
| `NumStability.Source.Higham.Chapter10.Equation30.ComplexPositiveDefinite.Endpoints` | 1 |
| `NumStability.Source.Higham.Chapter10.Problem04.UnpivotedGrowth.Basic` | 1 |
| `NumStability.Source.Higham.Chapter10.Theorem08.ComponentwisePerturbation.Endpoints` | 1 |
| `NumStability.Source.Higham.Chapter10.Theorem08.NormwiseDiscrepancy.Endpoints` | 1 |
