# W08 declaration routing

Wave `W08`, branch `codex/reorg-2026-08-w08-matrix-inversion-ch14`, phase branch `B0007`, base checkpoint `C0005`
at `240c0d041781385a647fbec461d6863537e562cb`.

B0007's per-owner routing table is authoritative and was transcribed, not
inferred. Where it delegates to a declaration's own source heading, the heading
or doc-comment attribution in the file was read. Nothing is routed by filename.

## Verified against B0007

| quantity | measured | B0007 |
| --- | ---: | ---: |
| declarations selected | 2179 | 2,179 |
| semantic reusable | 276 | 276 |
| semantic source | 1903 | 1,903 |
| `MatrixInversion` reusable/source | 92 / 223 | 92 / 223 |
| `Ch14AsymptoticFamilies` | 8 / 96 | 8 / 96 |
| `Ch14ProductErrorNotation` | 112 / 7 | 112 / 7 |
| reusable-to-source declaration edges | 0 | 0 |
| retained | 185 | 179 floor |
| relocated | 1994 | 2,000 graph-only max |
| canonical destination modules | 73 | — |

## Structural decisions

**Prefixes are shared; modules are not.** B0007 authorizes 42 production
prefixes, and some receive material from up to seven owners. Each destination
*module* is sourced from exactly one owner via a sanitised owner leaf, because a
module fed by two owners inherits the union of both owners' imports and widens
the transitive surface for downstream consumers.

**Leaf sanitisation.** `check_layout.py` rejects a `Source.Higham.ChapterNN`
leaf beginning with an abbreviated locator (`Ch1`, `Cor1`), with `Higham`, or
with `Chapter`, and requires a `Theorem|Lemma|Equation|...` locator leaf to carry
exactly two digits. Owner names such as `Ch14Corollary146Closure` violate both,
so each leaf strips a leading `Ch14` and then a leading locator-plus-number
token, falling back to `Basic`. All 73 emitted module names validate.

**Reusable destinations do not inherit Source imports.** Source imports are
pruned from D01-D09, and the import closure is checked to confirm no reusable
module reaches a Source module directly or transitively.

**Endpoint cuts are acyclic by construction.** B0007 splits two owners by
execution versus Theorem 14.5 endpoint. Name patterns alone could not get this
right: each pattern fix exposed another endpoint consumer sitting in the
execution module, which is a cycle. Dependencies flow execution to endpoint, so
the endpoint module is built as an upper set: seed with the pattern matches, then
add every declaration that transitively depends on one. 12 declarations were
promoted this way and the result is acyclic by construction.

## The three mixed owners

| owner | reusable | source | basis |
| --- | ---: | ---: | --- |
| `MatrixInversion` | 92 | 223 | B0007's six reusable categories; source by printed equation/method/problem number |
| `Ch14AsymptoticFamilies` | 8 | 96 | the eight declarations B0007 names, by exact name; the rest by source heading |
| `Ch14ProductErrorNotation` | 112 | 7 | the seven source declarations B0007 names, by exact name |

`GaussJordan` routes wholly to reusable D01. `GaussJordanPivoting` routes wholly
to source D12: B0007 confirms it formalizes Chapter 14 Algorithm 4 pivoting and
explicitly overrides the stale reusable suggestion for that owner.

## D38 is authorized but unpopulated

`D38 = Source/Higham/Chapter14/Section03/LUFactorInversion/MethodA/` receives no
declarations. Method A's only material is the eleven declarations under
`MatrixInversion`'s own `§14.3.1  Method A: solve Ax̂ⱼ = eⱼ for each column`
heading: one construction and ten column-backward-error, right-residual and
forward-error analyses. All eleven are mathematically generic, and they are
exactly what makes that owner reach B0007's stated 92 reusable declarations.
Relabelling any as source would simultaneously break the 276 reusable total, the
92/223 split and the zero-reusable-to-source-edge property. A prefix is
authorization, not an obligation to populate. 41 of 42 populated.

## Per-owner routing

### `NumStability.Algorithms.Ch14AsymptoticFamilies`

104 declarations; 10 retained, 94 relocated.

| destination | code | tier | declarations |
| --- | --- | --- | ---: |
| `NumStability.Source.Higham.Chapter14.Section01.InverseErrorAnalysis.AsymptoticFamilies` | D31 | source | 78 |
| `NumStability.Algorithms.Ch14AsymptoticFamilies` *(retained facade)* | — | — | 10 |
| `NumStability.Analysis.FirstOrder.MatrixFamilies.AsymptoticFamilies` | D09 | reusable | 8 |
| `NumStability.Source.Higham.Chapter14.Section02.TriangularInversion.Method1.AsymptoticFamilies` | D33 | source | 6 |
| `NumStability.Source.Higham.Chapter14.Problem05.InverseBasedSolve.AsymptoticFamilies` | D22 | source | 2 |

### `NumStability.Algorithms.Ch14BlockTriInverse`

19 declarations; 0 retained, 19 relocated.

| destination | code | tier | declarations |
| --- | --- | --- | ---: |
| `NumStability.Source.Higham.Chapter14.Section02.TriangularInversion.Method1B.BlockTriInverse` | D34 | source | 19 |

### `NumStability.Algorithms.Ch14Cor146UniformInverseBridge`

3 declarations; 2 retained, 1 relocated.

| destination | code | tier | declarations |
| --- | --- | --- | ---: |
| `NumStability.Algorithms.Ch14Cor146UniformInverseBridge` *(retained facade)* | — | — | 2 |
| `NumStability.Source.Higham.Chapter14.Corollary06.SPD.UniformInverseBridge` | D14 | source | 1 |

### `NumStability.Algorithms.Ch14Cor147FinalDivisionFamilyClosure`

55 declarations; 20 retained, 35 relocated.

| destination | code | tier | declarations |
| --- | --- | --- | ---: |
| `NumStability.Source.Higham.Chapter14.Corollary07.DiagonalDominance.FinalDivisionFamilyClosure` | D15 | source | 35 |
| `NumStability.Algorithms.Ch14Cor147FinalDivisionFamilyClosure` *(retained facade)* | — | — | 20 |

### `NumStability.Algorithms.Ch14Cor147SourceDomainConstructor`

3 declarations; 0 retained, 3 relocated.

| destination | code | tier | declarations |
| --- | --- | --- | ---: |
| `NumStability.Source.Higham.Chapter14.Corollary07.DiagonalDominance.SourceDomainConstructor` | D15 | source | 3 |

### `NumStability.Algorithms.Ch14Corollary146Closure`

145 declarations; 0 retained, 145 relocated.

| destination | code | tier | declarations |
| --- | --- | --- | ---: |
| `NumStability.Source.Higham.Chapter14.Corollary06.SPD.Closure` | D14 | source | 145 |

### `NumStability.Algorithms.Ch14Corollary146Concrete`

10 declarations; 0 retained, 10 relocated.

| destination | code | tier | declarations |
| --- | --- | --- | ---: |
| `NumStability.Source.Higham.Chapter14.Corollary06.SPD.Concrete` | D14 | source | 10 |

### `NumStability.Algorithms.Ch14Corollary146SourceClosure`

49 declarations; 0 retained, 49 relocated.

| destination | code | tier | declarations |
| --- | --- | --- | ---: |
| `NumStability.Source.Higham.Chapter14.Corollary06.SPD.SourceClosure` | D14 | source | 49 |

### `NumStability.Algorithms.Ch14Corollary147`

9 declarations; 0 retained, 9 relocated.

| destination | code | tier | declarations |
| --- | --- | --- | ---: |
| `NumStability.Source.Higham.Chapter14.Corollary07.DiagonalDominance.Basic` | D15 | source | 9 |

### `NumStability.Algorithms.Ch14Corollary147Closure`

32 declarations; 0 retained, 32 relocated.

| destination | code | tier | declarations |
| --- | --- | --- | ---: |
| `NumStability.Source.Higham.Chapter14.Corollary07.DiagonalDominance.Closure` | D15 | source | 32 |

### `NumStability.Algorithms.Ch14Corollary147Concrete`

18 declarations; 0 retained, 18 relocated.

| destination | code | tier | declarations |
| --- | --- | --- | ---: |
| `NumStability.Source.Higham.Chapter14.Corollary07.DiagonalDominance.Concrete` | D15 | source | 18 |

### `NumStability.Algorithms.Ch14Corollary147SourceClosure`

95 declarations; 18 retained, 77 relocated.

| destination | code | tier | declarations |
| --- | --- | --- | ---: |
| `NumStability.Source.Higham.Chapter14.Corollary07.DiagonalDominance.SourceClosure` | D15 | source | 77 |
| `NumStability.Algorithms.Ch14Corollary147SourceClosure` *(retained facade)* | — | — | 18 |

### `NumStability.Algorithms.Ch14Corollary147WeakFamily`

65 declarations; 11 retained, 54 relocated.

| destination | code | tier | declarations |
| --- | --- | --- | ---: |
| `NumStability.Source.Higham.Chapter14.Corollary07.DiagonalDominance.WeakFamily` | D15 | source | 54 |
| `NumStability.Algorithms.Ch14Corollary147WeakFamily` *(retained facade)* | — | — | 11 |

### `NumStability.Algorithms.Ch14ForwardErrorEndpoint`

44 declarations; 12 retained, 32 relocated.

| destination | code | tier | declarations |
| --- | --- | --- | ---: |
| `NumStability.Source.Higham.Chapter14.Section01.InverseErrorAnalysis.ForwardErrorEndpoint` | D31 | source | 25 |
| `NumStability.Algorithms.Ch14ForwardErrorEndpoint` *(retained facade)* | — | — | 12 |
| `NumStability.Source.Higham.Chapter14.Problem05.InverseBasedSolve.ForwardErrorEndpoint` | D22 | source | 4 |
| `NumStability.Source.Higham.Chapter14.Section02.TriangularInversion.Method1.ForwardErrorEndpoint` | D33 | source | 3 |

### `NumStability.Algorithms.Ch14GJEActualDoolittleAdapter`

6 declarations; 0 retained, 6 relocated.

| destination | code | tier | declarations |
| --- | --- | --- | ---: |
| `NumStability.Source.Higham.Chapter14.Algorithm04.Execution.GJEActualDoolittleAdapter` | D11 | source | 6 |

### `NumStability.Algorithms.Ch14GJEAsymptoticFamilies`

62 declarations; 22 retained, 40 relocated.

| destination | code | tier | declarations |
| --- | --- | --- | ---: |
| `NumStability.Source.Higham.Chapter14.Theorem05.ForwardError.GJEAsymptoticFamilies` | D42 | source | 40 |
| `NumStability.Algorithms.Ch14GJEAsymptoticFamilies` *(retained facade)* | — | — | 22 |

### `NumStability.Algorithms.Ch14GJEFinalDivisionClosure`

137 declarations; 14 retained, 123 relocated.

| destination | code | tier | declarations |
| --- | --- | --- | ---: |
| `NumStability.Source.Higham.Chapter14.Algorithm04.Execution.GJEFinalDivisionClosure` | D11 | source | 115 |
| `NumStability.Algorithms.Ch14GJEFinalDivisionClosure` *(retained facade)* | — | — | 14 |
| `NumStability.Source.Higham.Chapter14.Theorem05.ForwardError.GJEFinalDivisionClosure` | D42 | source | 8 |

### `NumStability.Algorithms.Ch14GJEOperationalBridge`

41 declarations; 0 retained, 41 relocated.

| destination | code | tier | declarations |
| --- | --- | --- | ---: |
| `NumStability.Source.Higham.Chapter14.Algorithm04.Execution.GJEOperationalBridge` | D11 | source | 41 |

### `NumStability.Algorithms.Ch14GJEPrintedEnvelopeClosure`

68 declarations; 22 retained, 46 relocated.

| destination | code | tier | declarations |
| --- | --- | --- | ---: |
| `NumStability.Source.Higham.Chapter14.Theorem05.ForwardError.GJEPrintedEnvelopeClosure` | D42 | source | 46 |
| `NumStability.Algorithms.Ch14GJEPrintedEnvelopeClosure` *(retained facade)* | — | — | 22 |

### `NumStability.Algorithms.Ch14GJESourceAccumulationBridge`

3 declarations; 0 retained, 3 relocated.

| destination | code | tier | declarations |
| --- | --- | --- | ---: |
| `NumStability.Source.Higham.Chapter14.Algorithm04.Accumulation.GJESourceAccumulationBridge` | D10 | source | 3 |

### `NumStability.Algorithms.Ch14GJETheorem145SourceClosure`

62 declarations; 7 retained, 55 relocated.

| destination | code | tier | declarations |
| --- | --- | --- | ---: |
| `NumStability.Source.Higham.Chapter14.Theorem05.ForwardError.GJETheorem145SourceClosure` | D42 | source | 55 |
| `NumStability.Algorithms.Ch14GJETheorem145SourceClosure` *(retained facade)* | — | — | 7 |

### `NumStability.Algorithms.Ch14GaussJordanAccumulation`

30 declarations; 0 retained, 30 relocated.

| destination | code | tier | declarations |
| --- | --- | --- | ---: |
| `NumStability.Source.Higham.Chapter14.Algorithm04.Accumulation.GaussJordanAccumulation` | D10 | source | 30 |

### `NumStability.Algorithms.Ch14GaussJordanQConstruction`

93 declarations; 0 retained, 93 relocated.

| destination | code | tier | declarations |
| --- | --- | --- | ---: |
| `NumStability.Source.Higham.Chapter14.Algorithm04.SecondStage.GaussJordanQConstruction` | D13 | source | 89 |
| `NumStability.Source.Higham.Chapter14.Theorem05.ForwardError.GaussJordanQConstruction` | D42 | source | 4 |

### `NumStability.Algorithms.Ch14GaussJordanSPDCorollary`

35 declarations; 0 retained, 35 relocated.

| destination | code | tier | declarations |
| --- | --- | --- | ---: |
| `NumStability.Source.Higham.Chapter14.Corollary06.SPD.GaussJordanSPDCorollary` | D14 | source | 35 |

### `NumStability.Algorithms.Ch14GaussJordanSourceClosure`

54 declarations; 0 retained, 54 relocated.

| destination | code | tier | declarations |
| --- | --- | --- | ---: |
| `NumStability.Source.Higham.Chapter14.Algorithm04.Execution.GaussJordanSourceClosure` | D11 | source | 54 |

### `NumStability.Algorithms.Ch14GaussJordanStep`

14 declarations; 0 retained, 14 relocated.

| destination | code | tier | declarations |
| --- | --- | --- | ---: |
| `NumStability.Source.Higham.Chapter14.Algorithm04.SecondStage.GaussJordanStep` | D13 | source | 14 |

### `NumStability.Algorithms.Ch14Method1BWhole`

18 declarations; 7 retained, 11 relocated.

| destination | code | tier | declarations |
| --- | --- | --- | ---: |
| `NumStability.Source.Higham.Chapter14.Section02.TriangularInversion.Method1B.Method1BWhole` | D34 | source | 11 |
| `NumStability.Algorithms.Ch14Method1BWhole` *(retained facade)* | — | — | 7 |

### `NumStability.Algorithms.Ch14Method2C`

14 declarations; 4 retained, 10 relocated.

| destination | code | tier | declarations |
| --- | --- | --- | ---: |
| `NumStability.Source.Higham.Chapter14.Section02.TriangularInversion.Method2C.Method2C` | D37 | source | 10 |
| `NumStability.Algorithms.Ch14Method2C` *(retained facade)* | — | — | 4 |

### `NumStability.Algorithms.Ch14Method2CWhole`

11 declarations; 3 retained, 8 relocated.

| destination | code | tier | declarations |
| --- | --- | --- | ---: |
| `NumStability.Source.Higham.Chapter14.Section02.TriangularInversion.Method2C.Method2CWhole` | D37 | source | 8 |
| `NumStability.Algorithms.Ch14Method2CWhole` *(retained facade)* | — | — | 3 |

### `NumStability.Algorithms.Ch14Method2Loop`

9 declarations; 0 retained, 9 relocated.

| destination | code | tier | declarations |
| --- | --- | --- | ---: |
| `NumStability.Source.Higham.Chapter14.Section02.TriangularInversion.Method2.Method2Loop` | D35 | source | 9 |

### `NumStability.Algorithms.Ch14MethodDLeftResidual`

5 declarations; 0 retained, 5 relocated.

| destination | code | tier | declarations |
| --- | --- | --- | ---: |
| `NumStability.Source.Higham.Chapter14.Section03.LUFactorInversion.MethodD.MethodDLeftResidual` | D41 | source | 5 |

### `NumStability.Algorithms.Ch14MethodDProductDischarge`

5 declarations; 0 retained, 5 relocated.

| destination | code | tier | declarations |
| --- | --- | --- | ---: |
| `NumStability.Source.Higham.Chapter14.Section03.LUFactorInversion.MethodD.MethodDProductDischarge` | D41 | source | 5 |

### `NumStability.Algorithms.Ch14MethodDUpperCertificate`

9 declarations; 0 retained, 9 relocated.

| destination | code | tier | declarations |
| --- | --- | --- | ---: |
| `NumStability.Source.Higham.Chapter14.Section03.LUFactorInversion.MethodD.MethodDUpperCertificate` | D41 | source | 9 |

### `NumStability.Algorithms.Ch14MethodsBC`

55 declarations; 0 retained, 55 relocated.

| destination | code | tier | declarations |
| --- | --- | --- | ---: |
| `NumStability.Source.Higham.Chapter14.Section03.LUFactorInversion.MethodC.MethodsBC` | D40 | source | 48 |
| `NumStability.Source.Higham.Chapter14.Section03.LUFactorInversion.MethodB.MethodsBC` | D39 | source | 7 |

### `NumStability.Algorithms.Ch14Problem142`

62 declarations; 8 retained, 54 relocated.

| destination | code | tier | declarations |
| --- | --- | --- | ---: |
| `NumStability.Source.Higham.Chapter14.Problem02.TriangularInversion.Basic` | D19 | source | 54 |
| `NumStability.Algorithms.Ch14Problem142` *(retained facade)* | — | — | 8 |

### `NumStability.Algorithms.Ch14Problem142Families`

113 declarations; 5 retained, 108 relocated.

| destination | code | tier | declarations |
| --- | --- | --- | ---: |
| `NumStability.Source.Higham.Chapter14.Problem02.TriangularInversion.Families` | D19 | source | 108 |
| `NumStability.Algorithms.Ch14Problem142Families` *(retained facade)* | — | — | 5 |

### `NumStability.Algorithms.Ch14Problem142Method2B`

20 declarations; 1 retained, 19 relocated.

| destination | code | tier | declarations |
| --- | --- | --- | ---: |
| `NumStability.Source.Higham.Chapter14.Problem02.TriangularInversion.Method2B` | D19 | source | 19 |
| `NumStability.Algorithms.Ch14Problem142Method2B` *(retained facade)* | — | — | 1 |

### `NumStability.Algorithms.Ch14ProductErrorNotation`

119 declarations; 0 retained, 119 relocated.

| destination | code | tier | declarations |
| --- | --- | --- | ---: |
| `NumStability.Analysis.Error.MatrixProducts.EvaluationTrees.ProductErrorNotation` | D08 | reusable | 112 |
| `NumStability.Source.Higham.Chapter14.Section01.ProductErrorNotation.ProductErrorNotation` | D32 | source | 7 |

### `NumStability.Algorithms.GaussJordan`

64 declarations; 6 retained, 58 relocated.

| destination | code | tier | declarations |
| --- | --- | --- | ---: |
| `NumStability.Algorithms.LinearSystems.GaussJordan.ErrorAnalysis.GaussJordan` | D01 | reusable | 58 |
| `NumStability.Algorithms.GaussJordan` *(retained facade)* | — | — | 6 |

### `NumStability.Algorithms.GaussJordanPivoting`

58 declarations; 0 retained, 58 relocated.

| destination | code | tier | declarations |
| --- | --- | --- | ---: |
| `NumStability.Source.Higham.Chapter14.Algorithm04.Pivoting.GaussJordanPivoting` | D12 | source | 58 |

### `NumStability.Algorithms.MatrixInversion`

315 declarations; 13 retained, 302 relocated.

| destination | code | tier | declarations |
| --- | --- | --- | ---: |
| `NumStability.Algorithms.MatrixInversion.Triangular.ErrorAnalysis.MatrixInversion` | D05 | reusable | 40 |
| `NumStability.Source.Higham.Chapter14.Problem13.GEJBound.MatrixInversion` | D28 | source | 29 |
| `NumStability.Source.Higham.Chapter14.Problem11.HadamardCondition.MatrixInversion` | D26 | source | 28 |
| `NumStability.Algorithms.MatrixInversion.Triangular.Specifications.MatrixInversion` | D06 | reusable | 23 |
| `NumStability.Source.Higham.Chapter14.Problem15.DeterminantPerturbation.MatrixInversion` | D30 | source | 23 |
| `NumStability.Source.Higham.Chapter14.Section03.LUFactorInversion.MethodD.MatrixInversion` | D41 | source | 22 |
| `NumStability.Source.Higham.Chapter14.Problem08.ComplexInverseRealBlock.MatrixInversion` | D24 | source | 16 |
| `NumStability.Algorithms.MatrixInversion.LUFactors.ErrorAnalysis.MatrixInversion` | D02 | reusable | 15 |
| `NumStability.Source.Higham.Chapter14.Problem14.HymanDeterminant.MatrixInversion` | D29 | source | 15 |
| `NumStability.Source.Higham.Chapter14.Section02.TriangularInversion.Method2B.MatrixInversion` | D36 | source | 14 |
| `NumStability.Algorithms.MatrixInversion` *(retained facade)* | — | — | 13 |
| `NumStability.Source.Higham.Chapter14.Problem05.InverseBasedSolve.MatrixInversion` | D22 | source | 11 |
| `NumStability.Source.Higham.Chapter14.Problem04.ResidualCounterexample.MatrixInversion` | D21 | source | 10 |
| `NumStability.Source.Higham.Chapter14.Problem12.HadamardExamples.MatrixInversion` | D27 | source | 10 |
| `NumStability.Algorithms.MatrixInversion.Residuals.MatrixInversion` | D04 | reusable | 7 |
| `NumStability.Source.Higham.Chapter14.Equation35.HymanBlockFactorization.MatrixInversion` | D17 | source | 7 |
| `NumStability.Source.Higham.Chapter14.Section01.InverseErrorAnalysis.MatrixInversion` | D31 | source | 7 |
| `NumStability.Analysis.Error.MatrixProducts.Contracts.MatrixInversion` | D07 | reusable | 6 |
| `NumStability.Source.Higham.Chapter14.Equation34.DeterminantFromLU.MatrixInversion` | D16 | source | 5 |
| `NumStability.Source.Higham.Chapter14.Problem03.ResidualComparison.MatrixInversion` | D20 | source | 5 |
| `NumStability.Source.Higham.Chapter14.Problem10.EntryPerturbation.MatrixInversion` | D25 | source | 4 |
| `NumStability.Source.Higham.Chapter14.Equation36.HymanDeterminant.MatrixInversion` | D18 | source | 2 |
| `NumStability.Source.Higham.Chapter14.Problem07.OnesVector.MatrixInversion` | D23 | source | 2 |
| `NumStability.Algorithms.MatrixInversion.LUFactors.Methods.MatrixInversion` | D03 | reusable | 1 |

### `NumStability.Algorithms.MatrixInversionMethod2BInstance`

46 declarations; 0 retained, 46 relocated.

| destination | code | tier | declarations |
| --- | --- | --- | ---: |
| `NumStability.Source.Higham.Chapter14.Section02.TriangularInversion.Method2B.MatrixInversionMethod2BInstance` | D36 | source | 46 |
