# B0007 C0005 activation and W06/W08 overlap review

Branch base checkpoint: `C0005`

Branch base commit: `240c0d041781385a647fbec461d6863537e562cb`

Wave: `W08`

This review is pinned to C0005 inventory SHA-256
`1210D2D774406964AF0359ADF6DEA9296B5EF95B3E0F8F1A582D6AFB2D3FE940`
and combined-baseline SHA-256
`D961829AA197564A94193B9909695E6DA077D02B64F07EFC6FC531BB291EF190`.
The raw format-2 TSV has SHA-256
`1DA19910927D41F4B45266ABA3F5E1A1F165637F7E984F8A19E15DA4FBB4A8D0`.
The immutable W08 selector contains 42 production owners and has SHA-256
`03AB94EAAE95A1FD2BDC0E9F3ACBD663D6CA4297008DF958A098D4D6E1038BD3`.
P0008 has SHA-256
`032F33236618FD21D318344A80F8E5EA02F18CCA533C4E183BD61945E6D77D74`
and freezes 2,179 declarations, 9,266 signature edges, 15,315 body/proof
edges, and 16,573 union edges. The projection checker has SHA-256
`29691CD63DB83A156247EA2C627407F4E90D127128A945B5AF97D014E11AB443`.

## Reviewed destinations

The declaration audit authorizes exactly these 42 production child prefixes:

```text
NumStability/Algorithms/LinearSystems/GaussJordan/ErrorAnalysis/
NumStability/Algorithms/MatrixInversion/LUFactors/ErrorAnalysis/
NumStability/Algorithms/MatrixInversion/LUFactors/Methods/
NumStability/Algorithms/MatrixInversion/Residuals/
NumStability/Algorithms/MatrixInversion/Triangular/ErrorAnalysis/
NumStability/Algorithms/MatrixInversion/Triangular/Specifications/
NumStability/Analysis/Error/MatrixProducts/Contracts/
NumStability/Analysis/Error/MatrixProducts/EvaluationTrees/
NumStability/Analysis/FirstOrder/MatrixFamilies/
NumStability/Source/Higham/Chapter14/Algorithm04/Accumulation/
NumStability/Source/Higham/Chapter14/Algorithm04/Execution/
NumStability/Source/Higham/Chapter14/Algorithm04/Pivoting/
NumStability/Source/Higham/Chapter14/Algorithm04/SecondStage/
NumStability/Source/Higham/Chapter14/Corollary06/SPD/
NumStability/Source/Higham/Chapter14/Corollary07/DiagonalDominance/
NumStability/Source/Higham/Chapter14/Equation34/DeterminantFromLU/
NumStability/Source/Higham/Chapter14/Equation35/HymanBlockFactorization/
NumStability/Source/Higham/Chapter14/Equation36/HymanDeterminant/
NumStability/Source/Higham/Chapter14/Problem02/TriangularInversion/
NumStability/Source/Higham/Chapter14/Problem03/ResidualComparison/
NumStability/Source/Higham/Chapter14/Problem04/ResidualCounterexample/
NumStability/Source/Higham/Chapter14/Problem05/InverseBasedSolve/
NumStability/Source/Higham/Chapter14/Problem07/OnesVector/
NumStability/Source/Higham/Chapter14/Problem08/ComplexInverseRealBlock/
NumStability/Source/Higham/Chapter14/Problem10/EntryPerturbation/
NumStability/Source/Higham/Chapter14/Problem11/HadamardCondition/
NumStability/Source/Higham/Chapter14/Problem12/HadamardExamples/
NumStability/Source/Higham/Chapter14/Problem13/GEJBound/
NumStability/Source/Higham/Chapter14/Problem14/HymanDeterminant/
NumStability/Source/Higham/Chapter14/Problem15/DeterminantPerturbation/
NumStability/Source/Higham/Chapter14/Section01/InverseErrorAnalysis/
NumStability/Source/Higham/Chapter14/Section01/ProductErrorNotation/
NumStability/Source/Higham/Chapter14/Section02/TriangularInversion/Method1/
NumStability/Source/Higham/Chapter14/Section02/TriangularInversion/Method1B/
NumStability/Source/Higham/Chapter14/Section02/TriangularInversion/Method2/
NumStability/Source/Higham/Chapter14/Section02/TriangularInversion/Method2B/
NumStability/Source/Higham/Chapter14/Section02/TriangularInversion/Method2C/
NumStability/Source/Higham/Chapter14/Section03/LUFactorInversion/MethodA/
NumStability/Source/Higham/Chapter14/Section03/LUFactorInversion/MethodB/
NumStability/Source/Higham/Chapter14/Section03/LUFactorInversion/MethodC/
NumStability/Source/Higham/Chapter14/Section03/LUFactorInversion/MethodD/
NumStability/Source/Higham/Chapter14/Theorem05/ForwardError/
```

The vacancy proof is deterministic. It uses these sorted, UTF-8, LF-terminated
payloads:

| Input | Rows | SHA-256 |
| --- | ---: | --- |
| `git ls-tree -r --name-only 240c0d041781385a647fbec461d6863537e562cb` | 3,616 | `4BA60CB40B50730F4EF1276EFAA7402D479E4D94A23E9A166AD3EADB8345DA40` |
| C0005 `scope.tsv` path column | 1,390 | `99A625603C3974BAA7868420B5D8312C7689F1AF00BA09E9D6956B1E15DF5FC1` |
| C0005 `phase.json.shared_paths` path column | 100 | `C54B8515F3F7BF00C6F24DACDC45A234237B4F7178B01F2202C6B5572A1D905F` |
| production prefixes above | 42 | `8EE89726DD14466F8A9B0CC0317454108819BA08A0F69EAC1E8D3B8877AC3C0B` |
| sibling umbrellas (`prefix.TrimEnd('/') + '.lean'`) | 42 | `522E1EC5E30F9E3BA822DF884BA727B963EDDDA069217F15E4B2BDF785B5341D` |
| B0006 production prefixes | 49 | `3C76127CBAF401DA1DF3083EBB8B3F846D424D9601D406F404599221CB8B3BB4` |

The checker normalizes separators to `/`, retains the ordinal-sorted payloads
above for hashing, and uses `ToLowerInvariant()` only for collision tests. For
each proposed prefix `p`, it tests that no C0005 tracked path or immutable
scope path starts with `p`, and that no tracked path equals its sibling
umbrella. It then compares every prefix pair and every B0006/B0007 pair in
both ancestor directions, and compares every destination with every shared
path in both ancestor directions. The result is exactly:

```text
tracked descendants below W08 prefixes: 0
scope descendants below W08 prefixes: 0
tracked W08 sibling umbrellas: 0
case-fold duplicate W08 prefixes: 0
W08 ancestor/descendant prefix pairs: 0
W06/W08 ancestor/descendant prefix pairs: 0
W08/shared ancestor/descendant overlaps: 0
```

Thus the 42 prefixes and their 42 sibling umbrella paths are vacant, unique,
pairwise non-ancestral, and disjoint from current shared paths and W06
destinations. Existing `Problem13.lean`, `Problem14.lean`, and
`Problem15.lean` are sibling umbrellas, not descendants. All umbrellas,
roots, manifests, root tests, and phase controls remain integrator-owned and
forbidden to the worker.

## Declaration-level routing

The routing table uses `D01` through `D42` for the exact production prefixes
in the `Reviewed destinations` block, in the order printed there. Counts come
from the hash-pinned P0008 declaration rows. `Retained` is the typed reverse
closure floor described below, not an additional declaration count.

| Historical owner | Declarations | Exact semantic route | Retained |
| --- | ---: | --- | ---: |
| `NumStability.Algorithms.Ch14AsymptoticFamilies` | 104 | mixed: 8 reusable to D09; 96 source to D31, D33, and D22 | 10 |
| `NumStability.Algorithms.Ch14BlockTriInverse` | 19 | source: D34 | 0 |
| `NumStability.Algorithms.Ch14Cor146UniformInverseBridge` | 3 | source: D14 | 2 |
| `NumStability.Algorithms.Ch14Cor147FinalDivisionFamilyClosure` | 55 | source: D15 | 20 |
| `NumStability.Algorithms.Ch14Cor147SourceDomainConstructor` | 3 | source: D15 | 0 |
| `NumStability.Algorithms.Ch14Corollary146Closure` | 145 | source: D14 | 0 |
| `NumStability.Algorithms.Ch14Corollary146Concrete` | 10 | source: D14 | 0 |
| `NumStability.Algorithms.Ch14Corollary146SourceClosure` | 49 | source: D14 | 0 |
| `NumStability.Algorithms.Ch14Corollary147` | 9 | source: D15 | 0 |
| `NumStability.Algorithms.Ch14Corollary147Closure` | 32 | source: D15 | 0 |
| `NumStability.Algorithms.Ch14Corollary147Concrete` | 18 | source: D15 | 0 |
| `NumStability.Algorithms.Ch14Corollary147SourceClosure` | 95 | source: D15 | 18 |
| `NumStability.Algorithms.Ch14Corollary147WeakFamily` | 65 | source: D15 | 11 |
| `NumStability.Algorithms.Ch14ForwardErrorEndpoint` | 44 | source: D31, D33, and D22 | 12 |
| `NumStability.Algorithms.Ch14GJEActualDoolittleAdapter` | 6 | source: D11 | 0 |
| `NumStability.Algorithms.Ch14GJEAsymptoticFamilies` | 62 | source: D42 | 22 |
| `NumStability.Algorithms.Ch14GJEFinalDivisionClosure` | 137 | source: D11 and D42, split by execution versus Theorem 14.5 endpoint | 14 |
| `NumStability.Algorithms.Ch14GJEOperationalBridge` | 41 | source: D11 | 0 |
| `NumStability.Algorithms.Ch14GJEPrintedEnvelopeClosure` | 68 | source: D42 | 22 |
| `NumStability.Algorithms.Ch14GJESourceAccumulationBridge` | 3 | source: D10 | 0 |
| `NumStability.Algorithms.Ch14GJETheorem145SourceClosure` | 62 | source: D42 | 7 |
| `NumStability.Algorithms.Ch14GaussJordanAccumulation` | 30 | source: D10 | 0 |
| `NumStability.Algorithms.Ch14GaussJordanQConstruction` | 93 | source: D13 and D42, split by second-stage construction versus Theorem 14.5 endpoint | 0 |
| `NumStability.Algorithms.Ch14GaussJordanSPDCorollary` | 35 | source: D14 | 0 |
| `NumStability.Algorithms.Ch14GaussJordanSourceClosure` | 54 | source: D11 | 0 |
| `NumStability.Algorithms.Ch14GaussJordanStep` | 14 | source: D13 | 0 |
| `NumStability.Algorithms.Ch14Method1BWhole` | 18 | source: D34 | 7 |
| `NumStability.Algorithms.Ch14Method2C` | 14 | source: D37 | 4 |
| `NumStability.Algorithms.Ch14Method2CWhole` | 11 | source: D37 | 3 |
| `NumStability.Algorithms.Ch14Method2Loop` | 9 | source: D35 | 0 |
| `NumStability.Algorithms.Ch14MethodDLeftResidual` | 5 | source: D41 | 0 |
| `NumStability.Algorithms.Ch14MethodDProductDischarge` | 5 | source: D41 | 0 |
| `NumStability.Algorithms.Ch14MethodDUpperCertificate` | 9 | source: D41 | 0 |
| `NumStability.Algorithms.Ch14MethodsBC` | 55 | source: D39 and D40, split by Method B versus Method C block | 0 |
| `NumStability.Algorithms.Ch14Problem142` | 62 | source: D19 | 8 |
| `NumStability.Algorithms.Ch14Problem142Families` | 113 | source: D19 | 5 |
| `NumStability.Algorithms.Ch14Problem142Method2B` | 20 | source: D19 | 1 |
| `NumStability.Algorithms.Ch14ProductErrorNotation` | 119 | mixed: 112 reusable to D08; 7 source to D32 | 0 |
| `NumStability.Algorithms.GaussJordan` | 64 | reusable: D01 | 0 |
| `NumStability.Algorithms.GaussJordanPivoting` | 58 | source: D12 | 0 |
| `NumStability.Algorithms.MatrixInversion` | 315 | mixed: 92 reusable to D07, D04--D06, and D02--D03; 223 source to D31, D33--D41, D20--D30, and D16--D18 | 13 |
| `NumStability.Algorithms.MatrixInversionMethod2BInstance` | 46 | source: D36 | 0 |

The table sums to exactly 2,179 declarations. Its semantic classification is
276 reusable and 1,903 exact source declarations.

### Three mixed owners

The eight reusable declarations in `Ch14AsymptoticFamilies` are exactly:

```text
NumStability.Ch14Ext.MatrixFamilyIsBigOOne
NumStability.Ch14Ext.VectorFamilyIsBigOOne
NumStability.Ch14Ext.family_mul_fixedMatrix_isBigOOne
NumStability.Ch14Ext.fixedMatrix_mul_family_isBigOOne
NumStability.Ch14Ext.fixedMatrix_mul_vectorFamily_isBigOOne
NumStability.Ch14Ext.matrixFamily_abs_isBigOOne
NumStability.Ch14Ext.matrixFamily_infNorm_isBigO
NumStability.Ch14Ext.matrixFamily_mul_fixedVector_isBigOOne
```

They route to D09. The other 96 declarations route by their explicit source
heading: equation 14.3 and residual-envelope support to D31, equations 14.6
and 14.7 to D33, and Problem 14.5 to D22. The two private gamma-composition
lemmas and their eight-public reverse closure remain in the historical owner.

`Ch14ProductErrorNotation` routes both generated inductive families and all
exact/rounded evaluation, factor-order, recursive-envelope, nonnegativity,
composition, and exact-order-coefficient APIs to D08. Its seven source
declarations, routed to D32, are exactly:

```text
NumStability.Ch14RectProductTree.exists_productDelta_gamma_operationBudget
NumStability.Ch14RectProductTree.exists_productDelta_two_mul_operationBudget_mul_u
NumStability.Ch14RectProductTree.productDelta_abs_le_gamma_operationBudget
NumStability.Ch14RectProductTree.productDelta_abs_le_two_mul_operationBudget_mul_u
NumStability.Ch14RectProductTree.roundedEval_MatProdError_gamma_operationBudget
NumStability.Ch14RectProductTree.roundedEval_RectMatProdError_gamma_operationBudget
NumStability.Ch14RectProductTree.roundedEval_RectMatProdError_two_mul_operationBudget_mul_u
```

`MatrixInversion` routes `MatProdError` and the two generic componentwise-to-
infinity-norm lemmas to D07; generic inverse residuals to D04; triangular
specifications to D06; triangular residual/error APIs to D05; method
constructions to D03; and LU-factor method error analyses to D02. Its 223
source declarations are the remaining `higham14_*` family, the generated
`Method2BBlockUpdateSpec` family, and `matrixEntryPerturb`, routed by their
printed equation, method, or problem number to the exact D16--D18, D20--D31,
and D33--D41 children. These five historically named declarations are
mathematically generic and are among the 92 reusable declarations:

```text
NumStability.higham14_infNorm_le_of_componentwise_abs_matmul_bound
NumStability.higham14_infNorm_le_of_componentwise_matmul_bound
NumStability.higham14_unit_roundoff_add_gamma_le_gamma_succ
NumStability.higham14_unit_roundoff_add_one_plus_u_mul_gamma_le_gamma_succ
NumStability.higham14_unit_roundoff_add_one_plus_u_mul_rounded_gamma_le_gamma_succ_succ
```

With those five on the reusable side, all three mixed-owner cuts have zero
reusable-to-source signature edges and zero reusable-to-source body/proof
edges.

### Gauss--Jordan boundary

All 64 declarations in `GaussJordan` route to reusable D01. Its broad Chapter
9 imports have zero typed declaration edges and therefore do not justify a
Source dependency in the canonical module. All 58 declarations in
`GaussJordanPivoting` route to D12: they formalize Higham Chapter 14 Algorithm
4's pivot candidates, row swaps, multipliers, elimination state, and full
reduction. The semantic review explicitly overrides the stale reusable
suggestion for that owner.

## Private retention boundary

P0008 contains these 45 private declarations, listed in ordinal order:

```text
_private.NumStability.Algorithms.Ch14AsymptoticFamilies.0.NumStability.Ch14Ext.composed_gammaQuadraticCoefficient_isBigO_one
_private.NumStability.Algorithms.Ch14AsymptoticFamilies.0.NumStability.Ch14Ext.composed_gammaUnitCoefficient_isBigO_one
_private.NumStability.Algorithms.Ch14ForwardErrorEndpoint.0.NumStability.Ch14Ext.ch14ext_double_sum_add_scaled
_private.NumStability.Algorithms.Ch14ForwardErrorEndpoint.0.NumStability.Ch14Ext.ch14ext_matMulVec_matrix_add_scaled
_private.NumStability.Algorithms.Ch14ForwardErrorEndpoint.0.NumStability.Ch14Ext.ch14ext_matMulVec_triple_matrix_add_scaled
_private.NumStability.Algorithms.Ch14ForwardErrorEndpoint.0.NumStability.Ch14Ext.ch14ext_matMulVec_vector_add_scaled
_private.NumStability.Algorithms.Ch14ForwardErrorEndpoint.0.NumStability.Ch14Ext.ch14ext_sq_mul_isBigO_of_continuousAt
_private.NumStability.Algorithms.Ch14GJEAsymptoticFamilies.0.NumStability.Ch14Ext.ch14ext_gammaQuadraticCoefficient_family_isBigO_one
_private.NumStability.Algorithms.Ch14GJEAsymptoticFamilies.0.NumStability.Ch14Ext.ch14ext_gammaUnitCoefficient_family_isBigO_one
_private.NumStability.Algorithms.Ch14GJEAsymptoticFamilies.0.NumStability.Ch14Ext.ch14ext_gjeForwardQ1_family_isBigOOne
_private.NumStability.Algorithms.Ch14GJEAsymptoticFamilies.0.NumStability.Ch14Ext.ch14ext_gjeForwardQ2_family_isBigOOne
_private.NumStability.Algorithms.Ch14GJEAsymptoticFamilies.0.NumStability.Ch14Ext.ch14ext_gjeForwardRaw_family_isBigOOne
_private.NumStability.Algorithms.Ch14GJEAsymptoticFamilies.0.NumStability.Ch14Ext.ch14ext_gjeForwardT1_family_isBigOOne
_private.NumStability.Algorithms.Ch14GJEAsymptoticFamilies.0.NumStability.Ch14Ext.ch14ext_gjeForwardT2_family_isBigOOne
_private.NumStability.Algorithms.Ch14GJEAsymptoticFamilies.0.NumStability.Ch14Ext.ch14ext_gjeForwardUinvCorrection_family_isBigOOne
_private.NumStability.Algorithms.Ch14GJEAsymptoticFamilies.0.NumStability.Ch14Ext.ch14ext_gjeResidualS22_family_isBigOOne
_private.NumStability.Algorithms.Ch14GJEAsymptoticFamilies.0.NumStability.Ch14Ext.ch14ext_gjeResidualS23_family_isBigOOne
_private.NumStability.Algorithms.Ch14GJEAsymptoticFamilies.0.NumStability.Ch14Ext.ch14ext_gjeResidualS2_family_isBigOOne
_private.NumStability.Algorithms.Ch14GJEAsymptoticFamilies.0.NumStability.Ch14Ext.ch14ext_one_add_gamma_family_isBigO_one
_private.NumStability.Algorithms.Ch14GJEAsymptoticFamilies.0.NumStability.Ch14Ext.ch14ext_one_add_gamma_pow_family_isBigO_one
_private.NumStability.Algorithms.Ch14GJEAsymptoticFamilies.0.NumStability.Ch14Ext.ch14ext_one_add_gamma_pow_sub_one_family_isBigO_unit
_private.NumStability.Algorithms.Ch14GJEPrintedEnvelopeClosure.0.NumStability.Ch14Ext.ch14ext_gjeInvCumProd_unit_upper
_private.NumStability.Algorithms.Ch14GJEPrintedEnvelopeClosure.0.NumStability.Ch14Ext.ch14ext_gjeInvStageMatrix_diag_one
_private.NumStability.Algorithms.Ch14GJEPrintedEnvelopeClosure.0.NumStability.Ch14Ext.ch14ext_gjeInvStageMatrix_upper_triangular
_private.NumStability.Algorithms.Ch14GJEPrintedEnvelopeClosure.0.NumStability.Ch14Ext.ch14ext_gje_Pabs_le
_private.NumStability.Algorithms.Ch14GJEPrintedEnvelopeClosure.0.NumStability.Ch14Ext.ch14ext_gje_Q_abs_le
_private.NumStability.Algorithms.Ch14GJEPrintedEnvelopeClosure.0.NumStability.Ch14Ext.ch14ext_matMul_diag_one_of_unit_upper
_private.NumStability.Algorithms.Ch14GJEPrintedEnvelopeClosure.0.NumStability.Ch14Ext.ch14ext_matMul_upper_triangular
_private.NumStability.Algorithms.Ch14Method1BWhole.0.NumStability.Ch14Ext.ch14ext_m1b_castAdd_eq_iff
_private.NumStability.Algorithms.Ch14Method1BWhole.0.NumStability.Ch14Ext.ch14ext_m1b_castAdd_ne_natAdd
_private.NumStability.Algorithms.Ch14Method1BWhole.0.NumStability.Ch14Ext.ch14ext_m1b_natAdd_eq_iff
_private.NumStability.Algorithms.Ch14Method2C.0.NumStability.Ch14Ext.ch14ext_castAdd_eq_iff
_private.NumStability.Algorithms.Ch14Method2C.0.NumStability.Ch14Ext.ch14ext_castAdd_ne_natAdd
_private.NumStability.Algorithms.Ch14Method2C.0.NumStability.Ch14Ext.ch14ext_natAdd_eq_iff
_private.NumStability.Algorithms.Ch14Problem142.0.NumStability.Ch14Ext.higham14_problem14_2_castAdd_ne_natAdd
_private.NumStability.Algorithms.Ch14Problem142.0.NumStability.Ch14Ext.higham14_problem14_2_natAdd_ne_castAdd
_private.NumStability.Algorithms.MatrixInversion.0.NumStability.higham14_problem14_12_det_stressUpper_one
_private.NumStability.Algorithms.MatrixInversion.0.NumStability.higham14_problem14_12_peiMatrix_eq_smul_one_add_rankOne
_private.NumStability.Algorithms.MatrixInversion.0.NumStability.higham14_problem14_12_prod_fin_nat_sub_eq_factorial
_private.NumStability.Algorithms.MatrixInversion.0.NumStability.higham14_problem14_12_prod_nat_sub_eq_factorial
_private.NumStability.Algorithms.MatrixInversion.0.NumStability.higham14_problem14_12_prod_rowNorm2_stressUpper_one
_private.NumStability.Algorithms.MatrixInversion.0.NumStability.higham14_problem14_12_rowNorm2_sq_stressUpper_one
_private.NumStability.Algorithms.MatrixInversion.0.NumStability.higham14_problem14_12_rowNorm2_stressUpper_one
_private.NumStability.Algorithms.MatrixInversion.0.NumStability.higham14_problem14_12_stressUpper_one_upper
_private.NumStability.Algorithms.MatrixInversion.0.NumStability.higham14_problem14_12_sum_tail_one
```

The sorted UTF-8, LF-terminated private-root payload has SHA-256
`E4910ADAEF41B4D7988E899A5E9B50D7B833E96C22BDFB2BD6D2224AB1ABEC20`.
The closure derivation is reproducible from the hash-pinned C0005 raw graph
and W08 selector: select exactly declarations whose owner is in W08.tsv; seed
the work queue with every selected declaration whose visibility is `private`;
retain only selected-to-selected `signature` and `body` edges; construct
reverse adjacency `edge.target -> edge.source`; and breadth-first traverse to
a fixed point. Sort the result by declaration name using ordinal comparison,
serialize it as UTF-8 without BOM with LF endings and a final newline, and
hash that payload. It contains exactly 179 declarations and has SHA-256
`B67D6D99436AD99DB2756C929F97B16202FD01FAFC77503F7616F7CD8C8B1724`.

| Historical owner | Private | Pinned public | Closure total |
| --- | ---: | ---: | ---: |
| `NumStability.Algorithms.Ch14AsymptoticFamilies` | 2 | 8 | 10 |
| `NumStability.Algorithms.Ch14Cor146UniformInverseBridge` | 0 | 2 | 2 |
| `NumStability.Algorithms.Ch14Cor147FinalDivisionFamilyClosure` | 0 | 20 | 20 |
| `NumStability.Algorithms.Ch14Corollary147SourceClosure` | 0 | 18 | 18 |
| `NumStability.Algorithms.Ch14Corollary147WeakFamily` | 0 | 11 | 11 |
| `NumStability.Algorithms.Ch14ForwardErrorEndpoint` | 5 | 7 | 12 |
| `NumStability.Algorithms.Ch14GJEAsymptoticFamilies` | 14 | 8 | 22 |
| `NumStability.Algorithms.Ch14GJEFinalDivisionClosure` | 0 | 14 | 14 |
| `NumStability.Algorithms.Ch14GJEPrintedEnvelopeClosure` | 7 | 15 | 22 |
| `NumStability.Algorithms.Ch14GJETheorem145SourceClosure` | 0 | 7 | 7 |
| `NumStability.Algorithms.Ch14Method1BWhole` | 3 | 4 | 7 |
| `NumStability.Algorithms.Ch14Method2C` | 3 | 1 | 4 |
| `NumStability.Algorithms.Ch14Method2CWhole` | 0 | 3 | 3 |
| `NumStability.Algorithms.Ch14Problem142` | 2 | 6 | 8 |
| `NumStability.Algorithms.Ch14Problem142Families` | 0 | 5 | 5 |
| `NumStability.Algorithms.Ch14Problem142Method2B` | 0 | 1 | 1 |
| `NumStability.Algorithms.MatrixInversion` | 9 | 4 | 13 |
| **Total** | **45** | **134** | **179** |

The closure is entirely on the source side. It sets a graph-only maximum of
2,000 relocations (276 reusable and 1,724 source). Command roots,
mutual/generated declarations, sections, attributes, options, namespaces, and
ambient imports may require additional retention. The worker must never move
a private declaration and must document the final command-level closure.

## Cross-wave and accepted boundaries

W08 and W06 have zero owner overlap, zero direct imports, and zero signature or
body/proof edges in either direction. Their production destinations have zero
ancestor/descendant overlap. Their sole common direct downstream importer is
integrator-owned `NumStability/Algorithms.lean`.

W08 has sixteen direct imports of accepted W02 historical owners and preserves
345 signature edges, 512 body/proof edges, and 542 union pairs across that
boundary. It has three accepted W03 canonical imports and twenty body edges:
the Cholesky perturbation API, entrywise-absolute matrix norms, and the exact
Chapter 10 equation 10.7 endpoint. W11 consumes the historical
`MatrixInversion` surface through nineteen typed union edges. W02/W03 paths and
W11 consumers are not worker-owned; only exact worker-side retargets or
integrator requests are permitted.

No W08 source migration is part of this activation record.
