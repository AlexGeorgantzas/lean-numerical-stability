# Block LU semantic migration, phase 12 (2026-07-27)

This document contains the immutable pre-edit ownership record for organization
Phase 12, followed by explicitly marked semantic-contract amendments and
validation evidence. It was written on branch
`codex/organization-blocklu-split` at clean base revision
`b36b4154d296cacb651ba31332f208b421b77ecc`, which was also `origin/main`.
No Phase 12 production, test, entry-point, tier, or compatibility edit precedes
this record. The only Phase 12 artifacts prepared with it are the reviewed
route map, its generated ownership manifest, and their checker.

## Format-2 semantic graph amendment

The original format-1 tables, counts, and hashes below are retained as forensic
evidence of the first compiled inventory. Before the first production
extraction was committed, however, staged comparison proved that its
generated-constant rows were not a durable ownership contract. Lean can
realize reserved equation theorems in a downstream importing module, cache an
`_proof_*` obligation under
an unrelated declaration, and renumber `match_*` or `_simp_*` auxiliaries after
an otherwise semantics-preserving move. The old 2,432-row counts, exact routes,
private rewrites, and two proof-artifact exceptions are therefore historical;
the format-2 contract in this section supersedes them for every operational
Phase 12 gate.

The format-2 extractor was established in commits `77c11767a`, `7590f571c`,
and `115c7a0ff`. It:

- omits names recognized by Lean as reserved;
- strips private module encodings before excluding unforgeable leading-`_`,
  numeric, and compiler `match_<ordinal>` components and their descendants;
- retains authored private helpers and authored source names such as
  `eq_11_15`; and
- contracts every dependency path through omitted project declarations onto
  the authored project declarations reachable through that path, preserving
  signature and body/proof edge kinds separately.

Contracting, rather than dropping or prefix-normalizing generated targets, is
essential. It preserves real dependencies hidden in auxiliary bodies without
inventing a dependency from the textual parent of a cached `_proof_*`. The
extractor self-test covers reserved names, shifted `_simp_*` ordinals, private
prefix removal, match descendants, and the authored `eq_11_15` counterexample.
Its SHA-256 is
`04AE8E46F66A0B8D2FED1FDB83904D8A60398F9B61A3EC4A10ADB3DF2352D771`.

The authoritative semantic input is
`benchmark-results/architecture/phase11b2-declarations-v2.tsv`: 115,717,110
bytes, SHA-256
`FD37F73D83F0206E40291576E1F9496185F09C21928ABED147B5CE2A6EF83AED`.
It contains 56,898 authored declarations, 266,373 signature edges, 382,855
body/proof edges, and 424,065 union edges. Independent contraction of the
original raw stream and direct extraction agree; normalized baseline/stage
Phase 12A comparison covers all 649,228 typed edges exactly.

The semantic Phase 12 selection contains 1,990 declarations:

| Historical owner | Semantic declarations |
| --- | ---: |
| `NumStability.Algorithms.LU.BlockLU` | 1,942 |
| `NumStability.Analysis.FirstOrder` | 37 |
| selected family in `NumStability.Algorithms.LU.GrowthFactor` | 11 |
| **Total** | **1,990** |

The kind partition is 1,665 theorems, 205 definitions, 48 constructors, 36
inductives, and 36 recursors. Visibility is 1,971 public and 19 authored
private declarations; no included declaration is classified as internal.
Reusable destinations own 284 declarations in 14 modules, and source
destinations own 1,706 declarations in 69 modules.

The reviewed semantic route map
`docs/architecture/declaration-ownership/blocklu-phase12-v2-routes.tsv` is
15,414 bytes with 137 ranges, no exact routes, and SHA-256
`D36A1AFAB0B5B1D216BCE0415813A8D35FC3518237766F1DB07826D9812CF7F5`.
The generated semantic manifest
`docs/architecture/declaration-ownership/blocklu-phase12-v2.tsv` is 417,901
bytes with 1,990 rows and SHA-256
`90F28D568A611035DE20839F2C30CB2800B75F2FC1DF2CE1373E9FFDD3D11287`.
Its row payload alone has SHA-256
`A044489211F341F7F724284140CCD8A5103C71419454AC404734BAD804DE8243`.

Under this contract Phase 12A moves exactly 173 public declarations:

| Destination | Source commands | Semantic declarations |
| --- | ---: | ---: |
| `Analysis.FirstOrder.AsymptoticFamilies` | 22 | 37 |
| `Analysis.FirstOrder.FixedPrecision` | 12 | 12 |
| `Analysis.MatrixNorms.EntrywiseMaximum` | 33 | 33 |
| `Algorithms.LinearSystems.LU.BlockLU.BlockMatrices` | 19 | 19 |
| `Algorithms.LinearSystems.LU.BlockLU.FirstOrderModels` | 13 | 61 |
| `Source.Higham.Chapter13.Theorem05.Recurrences` | 11 | 11 |
| **Total** | **110** | **173** |

No authored private declaration moves in Phase 12A, so its rewrite map is
header-only. After this slice, 1,817 declarations remain: 122 reusable and
1,695 source-owned, including all 19 authored private declarations. The fresh
Phase 12A semantic stream is 115,721,129 bytes with SHA-256
`E553EDA4343EFD695C68DE392463DAFE67B38C1E9347A5BB0E7FFC49F0DE1EB7`;
after owner/private normalization, its complete contracted graph equals the
frozen input exactly.

All commands and completion criteria later in this document are read with
these format-2 paths, counts, hashes, and exact-graph semantics. The original
format-1 tables remain useful for explaining why the amendment was required,
but they no longer define acceptance.

The batch separates reusable block-LU mathematics from Higham Chapter 13
correspondence. The canonical reusable family is
`NumStability.Algorithms.LinearSystems.LU.BlockLU`, as promised by the committed
Phase 11B2 record; retaining the implementation below `Algorithms.LU` is not an
allowed alternative. Numbered equations, algorithms, lemmas, problems, tables,
and source-shaped proof chains move below `NumStability.Source.Higham.Chapter13`.

For historical context, the superseded format-1 selection contained exactly
2,432 compiled constants arising from 1,748 source commands:

- all 2,378 constants and all 1,715 `.ilean` source commands owned by
  `NumStability.Algorithms.LU.BlockLU`;
- all 41 constants and all 22 source commands owned by
  `NumStability.Analysis.FirstOrder`; and
- exactly 13 constants generated by 11 source commands at lines 478--620 of
  `NumStability.Algorithms.LU.GrowthFactor`.

Under that superseded format-1 map, no declaration outside the selection was
assigned. Public and internal declaration names, namespaces, kinds,
visibility, types, and proofs were required to remain stable. Lean private
names necessarily encode their physical owner; the post-migration
private-name map could change only that reviewed owner encoding.

## Original format-1 frozen baseline

The authoritative compiled input is
`benchmark-results/architecture/phase11b2-declarations.tsv` (131,969,104
bytes), whose SHA-256 is
`AEBEAB80F4D98177960A830BB965F392DE2D9FD9463CDE7EFCACB7DE1570055E`.
It contains 81,950 compiled declarations, 305,425 signature edges, 439,195
body/proof edges, and 491,557 union edges. Lean is pinned to
`leanprover/lean4:v4.29.0-rc3`; Mathlib is pinned to
`e8ea1afc32790ce1d4e1a4e45cc412ba9388716b`.

| Historical input | Bytes | Lines | Nonblank | Imports | Selected commands | Selected constants | Git blob | File SHA-256 |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | --- | --- |
| `NumStability.Algorithms.LU.BlockLU` | 4,301,324 | 82,083 | 79,549 | 23 | 1,715 | 2,378 | `722dff73bcd4713ff1129a42653aa30c67ab4a22` | `AB15E61A417FF996598516471E55FD2EB582C5F29C867E5B6C04CD90C51EB51A` |
| `NumStability.Analysis.FirstOrder` | 12,777 | 308 | 271 | 1 | 22 | 41 | `03f3d631313b3c3e302eedce59c09f7ce124401d` | `C0140473A636990E9F720546CDCA7D237327D2802A93D59C8798B3A676B1FB5D` |
| selected part of `NumStability.Algorithms.LU.GrowthFactor` | 47,595 total | 1,029 total | 920 total | 13 total | 11 of 44 | 13 of 54 | `a4149b6df584709ee3b2b8ca73398dc6ee5f1fda` | `F9BAB4BBBCD00697BE8C3CD82C4D87486F804F7936D78D62DC6DC2DC17ED7AE5` |

The GrowthFactor selection is exactly:

```text
NumStability.entry_abs_le_infNorm
NumStability.entry_le_maxEntryNorm
NumStability.infNorm_le_card_mul_maxEntryNorm
NumStability.maxEntryNorm
NumStability.maxEntryNorm._proof_1
NumStability.maxEntryNorm.congr_simp
NumStability.maxEntryNorm_le_infNorm
NumStability.maxEntryNorm_le_of_entry_abs_le
NumStability.maxEntryNorm_le_of_entry_le_bound
NumStability.maxEntryNorm_le_of_entry_le_max
NumStability.maxEntryNorm_matTranspose
NumStability.maxEntryNorm_nonneg
NumStability.maxEntryNorm_submatrix_le
```

The 2,432 constants comprise 2,049 theorems, 263 definitions, 48
constructors, 36 inductives, and 36 recursors. Their visibility partition is
2,001 public, 357 generated/internal, and 74 private. The reusable destinations
own 385 constants in 14 modules; the source destinations own 2,047 constants
in 69 modules.

## Original format-1 route and ownership artifacts

The route map
`docs/architecture/declaration-ownership/blocklu-phase12-routes.tsv` is 24,685
bytes and has SHA-256
`189DE488271C3BD8974780A322C9B045C7264D2F22DEC5D7ABE68222EA1EFB64`.
After its `format\t1` header, it contains 137 inclusive source-range routes and
49 exact routes for compiler-generated constants without an unambiguous source
root.

The generated five-column manifest
`docs/architecture/declaration-ownership/blocklu-phase12.tsv` is 499,403 bytes,
contains `format\t1` plus exactly 2,432 sorted rows, and has SHA-256
`AF49C544D0885ADE41A797F8401EAFF307FBC381E49477ED103B4648BF6E41F1`.
Its columns are logical declaration name, historical owner, destination owner,
kind, and visibility. Private logical names normalize only the historical
module and private-scope ordinal to `_private.<module>.`; no other name
normalization is allowed.

`tools/architecture/check_blocklu_phase12_ownership.py` is the executable
contract for both artifacts. Its frozen pre-edit version has SHA-256
`68A5D678559EFB70C4AF9F8DA07CE98226273A33B0621ABA1C848ACF5A802F2C`.
It verifies the baseline hash, exact selection, route coverage, manifest
metadata, generated/private ownership, structural wrappers, the destination
dependency graph, and the normalized full graph in post mode.

The following table is the complete destination partition. "Source commands"
counts the historical `.ilean` declaration roots assigned by the inclusive
route ranges; compiler-generated exact routes add constants but not source
commands. Each per-destination digest hashes that destination's sorted, exact
five-column manifest rows, each terminated by LF, without a format header.

| Destination module | Source commands | Compiled constants | Row-payload SHA-256 |
| --- | ---: | ---: | --- |
| `NumStability.Algorithms.LinearSystems.LU.BlockLU.BlockMatrices` | 19 | 24 | `D0C1D834D6928991C4DC6868BC11155CFE4C8DF4AE756CF35C1787A7947EBD95` |
| `NumStability.Algorithms.LinearSystems.LU.BlockLU.DiagonalDominance` | 8 | 14 | `31FC87B7ACD69A85415B20A1EB7EB8770BAC258DDC9B75E295804D9614DCE6F1` |
| `NumStability.Algorithms.LinearSystems.LU.BlockLU.Factorization` | 49 | 83 | `3509B41137ECAC29DDB4943133F5770CE8C80E6A46302559E28A724B7DBDAD69` |
| `NumStability.Algorithms.LinearSystems.LU.BlockLU.FactorizationError` | 1 | 10 | `6BC38477E92942B29BCF4C7876CB2461F3E54FC8E62727FC59AB8349EB64616D` |
| `NumStability.Algorithms.LinearSystems.LU.BlockLU.FirstOrderModels` | 13 | 72 | `FBAB8405A15B1BE5535390E044B87650ECBDE0723509C9A0CD160497C2C951E6` |
| `NumStability.Algorithms.LinearSystems.LU.BlockLU.GrowthBounds` | 10 | 25 | `E4AA9D8ED4DBC49647867A79F2E8B89E853883B48D9B0A2BF333957EBED2EC77` |
| `NumStability.Algorithms.LinearSystems.LU.BlockLU.PositiveDefinite` | 7 | 7 | `1AC108EA0F11AB90CF236600015AA560566F91933D1772DEB125B3A6734267DE` |
| `NumStability.Algorithms.LinearSystems.LU.BlockLU.RecursiveFactorization` | 8 | 16 | `C7E735EDA1DE8CD07E0D5FBD3336E53DA100FB1BA3051BA181FEBF476B34AA07` |
| `NumStability.Algorithms.LinearSystems.LU.BlockLU.ResidualLifting` | 16 | 22 | `6588EE600949EC0420E496D9582C3336ACCBF8E814E7038D2A592F4D5AC67B93` |
| `NumStability.Algorithms.LinearSystems.LU.BlockLU.SchurComplement` | 4 | 5 | `0DFA3B108F751139322F408BDD4C4F748F07EE5FD1D7D407F1BAD4C5B29790A1` |
| `NumStability.Algorithms.LinearSystems.LU.BlockLU.SolveError` | 3 | 3 | `1659AAB277C4A248B19731F7C176E4D5512FC67CF86F7BD836FE5BA65A484F26` |
| `NumStability.Analysis.FirstOrder.AsymptoticFamilies` | 22 | 41 | `48CC7C91ED910DF5EF1CA8459CA95039F300D7D8513D3D58E44312A838DE2622` |
| `NumStability.Analysis.FirstOrder.FixedPrecision` | 12 | 19 | `DDE4F30D60B0910F82BFA3DD2E961DAB3D2EC5C1283103B309E7D7C6416F4C97` |
| `NumStability.Analysis.MatrixNorms.EntrywiseMaximum` | 33 | 44 | `2A4BCB86D58ACEAA10DFC9EB44B7ED9D0C2B988F388FAA48B3227808B21404F6` |
| `NumStability.Source.Higham.Chapter13.Algorithm01` | 2 | 2 | `46A5EF9D1D9BDE9175A32AFE774E7F4F7DA1BE0F980E89966AE664E8ADE8A769` |
| `NumStability.Source.Higham.Chapter13.Algorithm03` | 2 | 6 | `CD5E59C509402357FD815AE8D5BD3F523482DB4C31B3EF79EFE6A058229B8B84` |
| `NumStability.Source.Higham.Chapter13.Algorithm04` | 1 | 1 | `F20B04B57CAE0DA0857C05B138DF488A128ECF5EF02F0542EE4A73B279C584EC` |
| `NumStability.Source.Higham.Chapter13.Equation01` | 1 | 1 | `E63125080E28F6DCB972A6B1CA4358C65E85A537F3D950DE1E378EC5A30CCC7C` |
| `NumStability.Source.Higham.Chapter13.Equation02` | 1 | 1 | `F7A7244F886100FE2B94F0FB8F49DEDC4F760CDB59FEA51421B63B2656981129` |
| `NumStability.Source.Higham.Chapter13.Equation03` | 1 | 1 | `3E5C9AF26F7BB953260A72DAAE718FA5A30481EF21D2EF8845351A6DBBDFEA98` |
| `NumStability.Source.Higham.Chapter13.Equation18` | 4 | 6 | `E3F823FDDA4D16D74A656E8F83F0E88541D548BDEE37B354361B169E42DBE2D7` |
| `NumStability.Source.Higham.Chapter13.Equation19` | 10 | 11 | `7380F9D702AD5ACAA90E429EEC4CEF8E7D6CD139AD716CF8633D8CA8B82CCD70` |
| `NumStability.Source.Higham.Chapter13.Equation20` | 1 | 1 | `2A1FFD6CBD9140497E3E8524C91671D4B41DF3D305F408DCE1F7A60C8A1973AC` |
| `NumStability.Source.Higham.Chapter13.Equation21` | 132 | 149 | `DCF86481F4E03709A4F97C50229EFDF2494AC940C5CA78E7E5D87F286AA6FA6E` |
| `NumStability.Source.Higham.Chapter13.Equation22` | 9 | 22 | `242DEF68612CBCAF19109138F563B9C1ABF56819C46D1723DD03FFA201D39122` |
| `NumStability.Source.Higham.Chapter13.Equation23` | 3 | 3 | `7F8859EB96458BCE41374FA50631CA5B336890C60975C069C3658F5B317CFD22` |
| `NumStability.Source.Higham.Chapter13.Equation24` | 1 | 1 | `3F2739DCAFA71C2C9DDEE9266AF0FFFBC3D9AC32D712DA12D9CEB55AD9CCA45A` |
| `NumStability.Source.Higham.Chapter13.Equation25` | 2 | 2 | `D2848C02FE180149EEFC3C53A575E0688A92DEDA12D46D0D0D600197A65026AE` |
| `NumStability.Source.Higham.Chapter13.Equation26` | 1 | 1 | `3D9A5A05FC1E9C0B0F2FE6369DA0558AFE334A007BECFC3C02B8FCC8880D5038` |
| `NumStability.Source.Higham.Chapter13.Lemma09` | 64 | 66 | `AAAAB5FACFD8CCEE48E2D157797B9324F89D50F31094BD0ACE17FA4FD6E4E845` |
| `NumStability.Source.Higham.Chapter13.Lemma10.ConditionNumber` | 3 | 3 | `5CCD052BD00C4637B3C923D2A7F347503F69C2C6385A42E30C7BBB2E78CDE97E` |
| `NumStability.Source.Higham.Chapter13.Lemma10.SchurComplement` | 8 | 8 | `C99BEBBF50F1B0338125E4304A77299D64D7AA0C752F98C02175904C2DC92A27` |
| `NumStability.Source.Higham.Chapter13.Problem01` | 2 | 9 | `712D1D1235E4E6C774F9A4A44F80F7C0C94BD9A16053EE2CCA3FD842F69D95D2` |
| `NumStability.Source.Higham.Chapter13.Problem02` | 20 | 55 | `2F9E01E4084D1B022793987A15089AC85B789F249A0291B75333A41C1C3460E0` |
| `NumStability.Source.Higham.Chapter13.Problem03` | 7 | 8 | `1811107AB727891693B82F340EF940C6E464ACD80FF6144B49AA5696A04F81E7` |
| `NumStability.Source.Higham.Chapter13.Problem04.ActiveStageBounds` | 72 | 77 | `A89EDE44B52DC3CA736DB115B0072698C6BDA536B86F3317E771CBFB8838D990` |
| `NumStability.Source.Higham.Chapter13.Problem04.ActiveStageProducts` | 30 | 30 | `12E6EA311E10625563E474B34A41D391E34BAB71883B77ED3385F79D39E0BCC1` |
| `NumStability.Source.Higham.Chapter13.Problem04.ActiveTailProducts` | 20 | 20 | `0B2D66B70A1C1CE0C3613D79E9E810483B968894178A900B8B11ADBA29C2F18B` |
| `NumStability.Source.Higham.Chapter13.Problem04.BlockInverseBounds` | 25 | 27 | `03B12F8B4DE8F3713ADF122525C792E5748A18563B39AE547BEC3359EEC1DECF` |
| `NumStability.Source.Higham.Chapter13.Problem04.ComparisonChains` | 34 | 45 | `FD6E256F2BBDE092236026C5B6D34EB3642BFB256497805BAB075D921032B816` |
| `NumStability.Source.Higham.Chapter13.Problem04.DeterminantChainProducts` | 20 | 20 | `C493B5E1F56D0529428306BCA01223A08A3B5D01F0B7A95693E143F91E866F7D` |
| `NumStability.Source.Higham.Chapter13.Problem04.FactorizationExistence` | 14 | 32 | `C3EA4CE7BB1EF5C13791F40BBAB34396BD0CBBB579A1EE1D3B9C150EE84FCF91` |
| `NumStability.Source.Higham.Chapter13.Problem04.FactorizationProducts.ComparisonUpdates` | 31 | 31 | `C676E4C8B285F2CB55D193A5ECBC5A58DC362DF7C16ED53F1BDE14FE71BF89DC` |
| `NumStability.Source.Higham.Chapter13.Problem04.FactorizationProducts.DeterminantBounds` | 12 | 12 | `E6A96C03D2F505D93D21B0DA5BD2736C4523AEC1E12C5B8D0F5D19378EACCE8E` |
| `NumStability.Source.Higham.Chapter13.Problem04.FactorizationProducts.InverseBounds` | 46 | 46 | `624863FABE7F52E5D12505AC4CFC42A3B1272CB20EFB5A459CFB26D8F8269F1A` |
| `NumStability.Source.Higham.Chapter13.Problem04.FactorizationProducts.LocalComparisons` | 10 | 10 | `49A646EBA746D7C71B5CAF8B2CC9CAC4D6353B13614EF9DD73A490FC7AF7509D` |
| `NumStability.Source.Higham.Chapter13.Problem04.FactorizationProducts.LowerBlockBudgets` | 28 | 28 | `E252B7AD041714BECCC5DEEB191E740D0851BF19D0BA658E9A8546367FAEF08F` |
| `NumStability.Source.Higham.Chapter13.Problem04.GlobalTableauChain` | 50 | 69 | `3406EC4D098E8E4F59D18DB0B3C2F9F97182179FDFA646C51C21D590DF85C51A` |
| `NumStability.Source.Higham.Chapter13.Problem04.GlobalTableauGrowth` | 18 | 18 | `A1A302EEF35FAC9CF2C72E4815590B79FAF33A8D90927AE27A4467B965167F7B` |
| `NumStability.Source.Higham.Chapter13.Problem04.GlobalTableauProducts.ActiveSuffix` | 12 | 12 | `0A9925D8214C1C40297F25A6855C158A096433BC5EFF330D70ABDDE84567B22C` |
| `NumStability.Source.Higham.Chapter13.Problem04.GlobalTableauProducts.DiagonalUpdate` | 30 | 30 | `8B8BC2FEE9FA3430D7B4E9E416C2A3A21D759D579B446AD49CF64730E1C3137A` |
| `NumStability.Source.Higham.Chapter13.Problem04.GlobalTableauProducts.TailChain` | 6 | 6 | `893CB378E8114A4C97D42834DB0E2521B3CCECE5C782EFEAE3353C65C3D27E36` |
| `NumStability.Source.Higham.Chapter13.Problem04.HistoryEnvelope` | 14 | 19 | `77591DAA9A18DCA69843848B0B7544456A02A9B6CA2CB2B0545DB63084DF5EA9` |
| `NumStability.Source.Higham.Chapter13.Problem04.InfNormGrowth` | 95 | 95 | `F5B2E4912476C0103E11E723C38D4E84EF296AF59F71E6853DC75BFD4756924F` |
| `NumStability.Source.Higham.Chapter13.Problem04.InverseRatioChain` | 9 | 20 | `8490151FC1FC15318BDEAAA9AEDC4F37898D43C7BC4AAA086896FF43B9BEAB01` |
| `NumStability.Source.Higham.Chapter13.Problem04.LocalGrowth` | 47 | 69 | `9B12DD95E5081B8FF703240F3706D0BA85DE121CAC6A75D2877E0ED226016A15` |
| `NumStability.Source.Higham.Chapter13.Problem04.LocalNormBounds` | 22 | 22 | `239938B79D64E6EB7593E4BF4B575C891FFA323925D67FA244DCE424B9615CEF` |
| `NumStability.Source.Higham.Chapter13.Problem04.LowerComparisonChain` | 20 | 31 | `8C84E174154ADA7875A6B3036698BF150669F880533192785B6ECE9AF38F5AA1` |
| `NumStability.Source.Higham.Chapter13.Problem04.MatrixStageHistory` | 23 | 27 | `445372D3D2D34A23C758E74D33FFB3A432C47EBFECA204FEE95336950A96E02F` |
| `NumStability.Source.Higham.Chapter13.Problem04.MatrixStages` | 61 | 66 | `D5A3380FEEAA55B24A2F0CCC402D5DB0287D27F2D9928429D0E8834FE7E278BE` |
| `NumStability.Source.Higham.Chapter13.Problem04.OneStepProducts` | 35 | 36 | `0CFE0E376D9E0CDB84846116277AE04C570132FF8EFACC028959298C376F41E3` |
| `NumStability.Source.Higham.Chapter13.Problem04.ProductBounds` | 57 | 57 | `089F844ADC344C9C9E7608DF3379BD9BB0ED152CF85437DB2553E03B3DF9CE28` |
| `NumStability.Source.Higham.Chapter13.Problem04.RecursiveBudgetChains` | 29 | 30 | `F47E2AF5E9386F6778A284A09B53EB719F4489A97E76DC41AC9D07DB61FB720F` |
| `NumStability.Source.Higham.Chapter13.Problem04.StageHistory` | 39 | 42 | `335FEBB823A99B75ED3445733817C2A4E807CECE037C652C0A70591B81AAD18E` |
| `NumStability.Source.Higham.Chapter13.Problem05` | 7 | 10 | `E4803A7F4D2937DD620D631128C4699F14D4E97445CC6664C9B316F7D9D440CA` |
| `NumStability.Source.Higham.Chapter13.Problem06` | 12 | 28 | `A39F6BF20C0C64FF6CEA55F7B7660A73519490A74CA375E34D14693DAF978330` |
| `NumStability.Source.Higham.Chapter13.Problem07` | 2 | 2 | `1F0A7766B7A115E2A3A2B3724BAFAE0311103308161372F5D4FDB0632B7AC2EA` |
| `NumStability.Source.Higham.Chapter13.Problem08` | 1 | 1 | `06956C816D83AE43647FF589447E45750426AFC8DE20B6C8A2571E838362E313` |
| `NumStability.Source.Higham.Chapter13.Problem09` | 2 | 2 | `5C3FAE34EA4B1284208AD6A118CD0C97EF62B71ED3EBA831CD98F5AB625C9C7F` |
| `NumStability.Source.Higham.Chapter13.Section01.NormConventions` | 11 | 12 | `7127DBBE2C1C14056EF0271EB6DC6EC0779918A30053D43320868B42CC6BB4AD` |
| `NumStability.Source.Higham.Chapter13.Section01.OperationModels` | 13 | 38 | `33E2ADA3951D5F74C4DDC3F3945DD78870F645F262A41CB2AA72E1C7D0BFD32D` |
| `NumStability.Source.Higham.Chapter13.Section01.StandardFactorization` | 3 | 4 | `A1EC280A60F883377BA66B7319C444A9555462E6DC71921EAF74F15F61DD53C8` |
| `NumStability.Source.Higham.Chapter13.Section03.SchurStageAnalysis` | 78 | 120 | `906AE5D1F188341A22C8983780554F1F240B5B23BEBCDA86E7B91590AFC1F4ED` |
| `NumStability.Source.Higham.Chapter13.Table01` | 22 | 27 | `586A8D148684870ED669F13760E503F70A78D862AC904018D84772C99ACEAB51` |
| `NumStability.Source.Higham.Chapter13.Theorem02.Factorization` | 18 | 26 | `9053EF0CDC0A44EC475FADD9C594199A1EB7F07DE6711F3C4693AA1C4716ACCB` |
| `NumStability.Source.Higham.Chapter13.Theorem02.Uniqueness` | 28 | 41 | `CBE7108021181CAD09C834EB4AE437DF82A6093C628E67DE1B79EC0D6D2D7590` |
| `NumStability.Source.Higham.Chapter13.Theorem05.ErrorAnalysis` | 27 | 38 | `E38EAB5B32AA98F41B47C6D7D9F7B237DD2D4E99794D4E0259D1B4FE3536339B` |
| `NumStability.Source.Higham.Chapter13.Theorem05.Recurrences` | 11 | 27 | `C77C89038936000B0564B5EF541D9A5C2E9B2AFDDC8C8695742750F6B40C0C78` |
| `NumStability.Source.Higham.Chapter13.Theorem06.AssumptionModel` | 34 | 135 | `0218A18A29F510BE4576BFC905828319CCCA20771D74B312D09FAC4FE4C07792` |
| `NumStability.Source.Higham.Chapter13.Theorem06.FactorAndSolve` | 63 | 115 | `460F70CD610C4C8D8EAE5EB1989994349CA0B8E26C22EE4170DFE1D91A9B8F53` |
| `NumStability.Source.Higham.Chapter13.Theorem07.OneStep` | 2 | 4 | `C2BEB3DEC6904DC3FD26DD95497B5CFFF5321806556A6EB01E0F3C258F63C17E` |
| `NumStability.Source.Higham.Chapter13.Theorem07.PivotExistence` | 24 | 31 | `69ACDBC855529A4637E894A4D6E5BC219703672F50CE06762872EFE49D698BD4` |
| `NumStability.Source.Higham.Chapter13.Theorem08.OneStep` | 1 | 2 | `803E0E28E892CDF617E6DEFF83D9A4F0649C9C1AA4C1E17530B03F91F25B7974` |

The table sums to exactly 1,748 commands and 2,432 constants. Any destination
count or digest change invalidates this record and requires a new reviewed map
before production movement continues.

## Original format-1 Phase 12A inventory

The first implementation slice is deliberately dependency-contained. An
early audit reported 223 compiled constants. Exhaustive compiler-generated
constant accounting corrected that number to 227 before production edits:
`EntrywiseMaximum` also owns `NumStability.nonsingInv.eq_1`, and the two
recurrence definitions generate three additional private match auxiliaries
that the preliminary count omitted.

| Destination | Historical source ranges | Commands | Constants |
| --- | --- | ---: | ---: |
| `Analysis.FirstOrder.AsymptoticFamilies` | all declarations at `Analysis/FirstOrder.lean` lines 19--304 | 22 | 41 |
| `Analysis.FirstOrder.FixedPrecision` | BlockLU 2684--2693 and 2828--2993 | 12 | 19 |
| `Analysis.MatrixNorms.EntrywiseMaximum` | GrowthFactor 478--620; BlockLU 1723--1764, 1775--1801, 2218--2410, and 2492--2678; exact `nonsingInv.eq_1` | 33 | 44 |
| `Algorithms.LinearSystems.LU.BlockLU.BlockMatrices` | BlockLU 1400--1426, 1459--1523, 1564--1589, 1606--1642, and 1707--1721 | 19 | 24 |
| `Algorithms.LinearSystems.LU.BlockLU.FirstOrderModels` | BlockLU 2695--2796 | 13 | 72 |
| `Source.Higham.Chapter13.Theorem05.Recurrences` | BlockLU 7076--7311 plus seven exact private match auxiliaries | 11 | 27 |
| **Total** |  | **110** | **227** |

The dependency direction is:

```text
BlockMatrices -> EntrywiseMaximum -> MatrixAlgebra
FirstOrderModels -> FixedPrecision -> Rounding / FloatingPoint.Model
```

Here an arrow points from a consumer to a dependency. `AsymptoticFamilies` and
the source-owned `Theorem05.Recurrences` are independent of those chains.
`blockErrorDelta` and `blockErrorTheta` stay source-owned; they are Higham
Theorem 13.5 recurrence constants, not generic fixed-precision API.

`NumStability.growthFactorEntry.congr_simp` is not placed in Analysis. It moves
to reusable `BlockLU.GrowthBounds`, because `growthFactorEntry` remains an
algorithmic GrowthFactor definition and moving its generated congruence theorem
into Analysis would create an Analysis-to-Algorithms dependency.

## Problem 13.4 split

The dominant Problem 13.4 tail is divided into 29 declaration-bearing leaves
and three declaration-free umbrellas: `Problem04`,
`Problem04.FactorizationProducts`, and
`Problem04.GlobalTableauProducts`. The historical line ranges below are
one-based and inclusive.

| Leaf below `Source.Higham.Chapter13.Problem04` | Historical tail lines | Final tail commands |
| --- | ---: | ---: |
| `StageHistory` | 24194--25371 | 39 |
| `MatrixStages` | 25373--27379 | 61 |
| `MatrixStageHistory` | 27381--28174 | 23 |
| `ActiveStageBounds` | 28176--31001 | 72 |
| `InfNormGrowth` | 31003--34536 | 95 |
| `LocalNormBounds` | 34538--35137 | 22 |
| `BlockInverseBounds` | 36486--38054 | 21 |
| `LocalGrowth` | 38056--41190 | 47 |
| `ProductBounds` | 41192--45009 | 57 |
| `FactorizationProducts.LowerBlockBudgets` | 45011--47167 | 28 |
| `FactorizationProducts.LocalComparisons` | 47169--47904 | 10 |
| `FactorizationProducts.InverseBounds` | 47906--51222 | 46 |
| `FactorizationProducts.ComparisonUpdates` | 51224--54224 | 31 |
| `FactorizationProducts.DeterminantBounds` | 54226--55086 | 12 |
| `ActiveStageProducts` | 55088--57383 | 30 |
| `HistoryEnvelope` | 57385--57778 | 14 |
| `RecursiveBudgetChains` | 57780--60349 | 29 |
| `InverseRatioChain` | 60351--60869 | 9 |
| `LowerComparisonChain` | 60871--61900 | 20 |
| `GlobalTableauChain` | 61902--65383 | 50 |
| `ActiveTailProducts` | 65385--67843 | 20 |
| `GlobalTableauGrowth` | 67845--69860 | 18 |
| `GlobalTableauProducts.ActiveSuffix` | 69862--71056 | 12 |
| `GlobalTableauProducts.DiagonalUpdate` | 71058--74568 | 30 |
| `GlobalTableauProducts.TailChain` | 74570--75079 | 6 |
| `ComparisonChains` | 75081--76544 | 34 |
| `DeterminantChainProducts` | 76546--78271 | 20 |
| `OneStepProducts` | 78273--81098 | 35 |
| `FactorizationExistence` | 81100--82010 | 14 |

The raw tail ranges contain 923 source commands. The preliminary audit called
17 commands generic and moved two commands to Lemma 13.10, yielding a reported
904 Problem04 commands. Exact source and dependency review corrected that map:

- 15 commands move to reusable `Factorization`, `GrowthBounds`, or
  `SchurComplement`;
- `maxEntryNorm_blockMatrixFirstSplitFlat_pos_of_all_leadingBlockPrefixes`
  belongs to `Theorem02.Factorization`;
- `growthFactorEntry_blockMatrixFirstSplitFlat_eq_blockMatrixFlatFin` remains
  Problem04 source material in `MatrixStageHistory`; and
- the two lines 37293--37486 commands move to
  `Lemma10.ConditionNumber`.

The final tail therefore contains 905 Problem04 commands, not 904. Four earlier
Problem04 commands at lines 4071--4203 and 4796--4831 also move into
`BlockInverseBounds`, so the 29 leaves own 909 source commands and 1,027
compiled constants in total. Equation (13.26), lines 6886--6899, is correctly
owned by the separate `Source.Higham.Chapter13.Equation26` leaf and is not
counted as Problem04 ownership.

The locator gap is intentionally not absorbed by Problem04:

- 35139--35359: equations (13.22)--(13.23);
- 35361--35735: Table 13.1;
- 35736--35761: equation (13.24);
- 35763--35827: equation (13.25);
- 35829--35884: Problem 13.1;
- 35886--36136: Problem 13.2;
- 36138--36212: Problem 13.3;
- 36214--36430: Problem 13.5;
- 36432--36467: Problem 13.7; and
- 36469--36484: Problem 13.8.

The dependency roots are `StageHistory`, `MatrixStages`, and
`LocalNormBounds`. `MatrixStageHistory` builds on `MatrixStages`;
`BlockInverseBounds` builds on `LocalNormBounds`; `ActiveStageBounds` builds on
the matrix-stage leaves. `InfNormGrowth`, `LocalGrowth`, and `HistoryEnvelope`
form parallel branches. `GlobalTableauProducts.ActiveSuffix` precedes its
`DiagonalUpdate` and `TailChain` siblings; determinant and one-step product
leaves use `DiagonalUpdate`; `FactorizationExistence` uses `ActiveSuffix` but
does not require the terminal determinant and one-step leaves. The umbrella
imports all supported terminal branches instead of imposing an artificial
linear chain.

## Original format-1 dependency boundary and audited artifacts

The frozen selected-owner graph has 83 destination nodes and 440 typed
cross-owner edges. After exactly two reviewed body-only elaboration artifacts
are removed, it is acyclic and has zero reusable-to-source edges. No signature
edge is exempted.

In the monolith Lean reused `NumStability.blockMaxNorm._proof_1` for two
structurally identical nonempty-Finset proof obligations:

```text
body: NumStability.maxEntryNormRect
   -> NumStability.blockMaxNorm._proof_1

body: NumStability.maxEntryNormRect_le_of_entry_abs_le
   -> NumStability.blockMaxNorm._proof_1
```

Those edges reflect elaboration order, not a mathematical dependency of a
generic rectangular max-entry norm on block LU. Importing `BlockMatrices` from
`Analysis.MatrixNorms.EntrywiseMaximum` would create both an architectural
violation and a real cycle. The post checker instead requires exactly these two
edges to regenerate against EntrywiseMaximum-owned proof targets matching the
reviewed pattern, permits no other graph drift, and rejects any remaining
reverse dependency.

## Aggregate and compatibility contracts

Every module named below is declaration-free, has a module docstring, and has
sorted unique imports.

- `NumStability.Analysis.FirstOrder` becomes the family aggregate over
  `AsymptoticFamilies` and `FixedPrecision`.
- `NumStability.Analysis.MatrixNorms` adds `EntrywiseMaximum` to its existing
  canonical children.
- `NumStability.Algorithms.LinearSystems.LU.BlockLU` imports exactly the eleven
  reusable BlockLU leaves listed in the ownership table; it imports no source
  module.
- `NumStability.Algorithms.LinearSystems.LU` imports the BlockLU umbrella, and
  `NumStability.Algorithms.LinearSystems` imports the `LU` and `Triangular`
  family umbrellas.
- `Section01`, `Theorem02`, `Theorem05`, `Theorem06`, `Theorem07`, `Theorem08`,
  `Lemma10`, and `Section03` are source-family umbrellas over their physical
  children in the ownership table.
- `Problem04.FactorizationProducts` imports its five named children;
  `Problem04.GlobalTableauProducts` imports its three named children; and
  `Problem04` imports those two umbrellas plus its other 21 leaves.
- `NumStability.Source.Higham.Chapter13.BlockLU` imports every source leaf in
  this 1,990-declaration semantic migration and no historical path.
- `NumStability.Source.Higham.Chapter13` imports `Chapter13.BlockLU` and the
  independently existing canonical `DemmelSharpMultiplier` surface without
  duplicating BlockLU descendants.
- historical `NumStability.Algorithms.LU.BlockLU` becomes a declaration-free
  compatibility facade importing exactly
  `Algorithms.LinearSystems.LU.BlockLU` and `Source.Higham.Chapter13.BlockLU`.

The compatibility facade is retained until an announced breaking release. It
must not contain declarations, options, opens, local instances, or unrelated
imports. Production modules are retargeted to canonical leaves or umbrellas;
only isolated compatibility tests intentionally import it.

## Consumers and retargets

The historical BlockLU file has exactly nine direct import carriers outside
itself. "Referenced targets" is the number of distinct BlockLU compiled
constants used by that module in the frozen declaration graph; aggregates and
the example own no compiled declaration.

| Direct import carrier | Referenced targets | Required treatment |
| --- | ---: | --- |
| `NumStability.Algorithms` | 0 | import canonical reusable and documented source aggregates, not the old facade |
| `NumStability.Algorithms.Ch14Problem142` | 17 | add the exact canonical reusable/source leaves its declarations use |
| `NumStability.Algorithms.HighamChapter9` | 9 | add the exact canonical leaves its declarations use |
| `NumStability.Algorithms.LU.BlockLUFirstOrderFamilies` | 9 | retarget to the first-order and source leaves it uses |
| `NumStability.Algorithms.LU.BlockLUPointRowGrowthSourceClosure` | 1 | retarget to its canonical source owner |
| `NumStability.Algorithms.LU.BlockLUSourceClosure` | 20 | retarget to canonical source leaves |
| `NumStability.Algorithms.LU.BlockLUVarying` | 0 | remove the transitive carrier and add only its actual explicit dependencies |
| `NumStability.Algorithms.MatrixInversionMethod2BInstance` | 5 | retarget to reusable factorization leaves |
| `examples/LibraryLookup.lean` | 0 | use the documented canonical aggregate; retain a separate old-only smoke test |

The declaration graph additionally drives explicit-import fixes for downstream
consumers that currently receive BlockLU, FirstOrder, or the selected
GrowthFactor declarations transitively. `Analysis.FirstOrder`'s three direct
importers and every user of the selected max-entry family are retargeted to the
narrow canonical leaf when they do not need the complete family aggregate.

The declaration-bearing sibling files
`BlockLUArbitraryNormSourceClosure`, `BlockLUComputationSourceClosure`,
`BlockLUFirstOrderFamilies`, `BlockLUPointRowGrowthSourceClosure`,
`BlockLURowSourceClosure`, `BlockLUScalarGrowthBridge`,
`BlockLUSourceClosure`, `BlockLUSPDFamilies`, `BlockLUSPDSourceClosure`, and
`BlockLUVarying` are consumers in this record; their own constants are not
silently absorbed into the 1,990-declaration semantic partition. Before those declarations
move, a second committed ownership map must assign them to Chapter 13 source
leaves or reusable owners. `BlockLUTable13_1Families` is already a documented
compatibility facade.

## Staged implementation sequence

1. Commit this record, the route map, the 1,990-row semantic manifest, and the checker
   before moving production Lean code.
2. Implement Phase 12A's six dependency-contained destinations and their
   aggregates. Retarget immediate imports, run canonical-only and legacy
   surface tests, and commit only after the exact 173-declaration staged gate
   passes.
3. Extract the remaining reusable leaves in dependency order, keeping
   declaration names and proofs unchanged and making hidden imports explicit.
4. Move the numbered/source-owned commands into Chapter 13 leaves. Build the
   29 Problem04 leaves in their actual DAG rather than source-file order.
5. Create and verify all family, problem, chapter, reusable, and source
   umbrellas. Replace the old BlockLU implementation with its two-target
   compatibility facade and retarget every production consumer.
6. Commit a second pre-edit ownership record for the sibling BlockLU files,
   migrate them, and leave their historical paths as tested wrappers where
   required. Phase 12 is not complete before this follow-on is complete.
7. Update tier, compatibility, entry-point, source-coverage, and architecture
   documentation; regenerate the structural baseline; run the full validation
   suite from a clean implementation commit; then push the completed phase.

No step may be skipped merely because a broad aggregate happens to provide the
same declarations transitively.

## Tests and validation gates

Phase 12 is complete only after all applicable gates pass:

1. the checker self-test and pinned pre check pass against the frozen hashes:

   ```text
   python tools/architecture/check_blocklu_phase12_ownership.py --self-test
   python tools/architecture/check_blocklu_phase12_ownership.py \
     --mode pre \
     --dependency-tsv benchmark-results/architecture/phase11b2-declarations-v2.tsv \
     --routes docs/architecture/declaration-ownership/blocklu-phase12-v2-routes.tsv \
     --manifest docs/architecture/declaration-ownership/blocklu-phase12-v2.tsv \
     --expected-manifest-sha256 90F28D568A611035DE20839F2C30CB2800B75F2FC1DF2CE1373E9FFDD3D11287
   ```

   Route-map validation normally belongs to pre mode. Stage and post
   invocations omit `--routes` because live `.ilean` files no longer preserve
   historical source ranges after extraction. If route validation is
   deliberately repeated later, every routed historical module must be
   supplied through a frozen pre-migration `.ilean` override.

2. every declaration-bearing canonical destination builds in isolation and has
   a one-import canonical smoke test checking representative public signatures;
3. the old BlockLU facade, `Analysis.FirstOrder`, and GrowthFactor's preserved
   max-entry surface each compile in genuinely isolated old-only tests;
4. reusable, source, Problem04, Lemma10, theorem-family, chapter, and historical
   entry-point tests prove the documented aggregate reachability contracts;
5. the staged checker proves exact ownership for the completed subset after
   each slice, and post mode proves all 1,990 semantic declaration destinations
   plus all 19 explicit authored-private name rewrites;
6. the final generated declaration TSV matches the frozen complete contracted
   declaration and dependency graph exactly after owner/private normalization;
7. the final destination graph is acyclic, and reusable destinations have zero
   direct or transitive source dependency;
8. no production declaration-bearing module imports a historical wrapper, and
   no declaration-free aggregate or wrapper owns a compiled constant;
9. tier and compatibility manifests cover every new leaf, aggregate, and
   wrapper; aggregate imports are sorted, unique, exact, and reachable;
10. layout, compatibility, provenance, source-boundary, placeholder,
    exact-debt, and strict-source reproducibility checks pass;
11. `git diff --check`, `lake build NumStability`, `lake test`, and
    `lake build NumStability NumStabilityTest` pass sequentially;
12. `lake env lean examples/LibraryLookup.lean` and all direct/downstream
    consumer builds pass;
13. representative `#print axioms` checks introduce nothing beyond the
    repository's accepted `[propext, Classical.choice, Quot.sound]` set;
14. no `sorry`, `admit`, or new top-level `axiom` or `constant` command is
    introduced, and no generated artifact or private skill is tracked; and
15. full gates are repeated from a clean implementation commit before final
    baseline and evidence commits.

## Phase 12A validation evidence

Implementation commit `9db375750` moves the exact 173-declaration Phase 12A
subset into six canonical leaves. The tracked implementation tree was clean
before the full validation sequence began.

The format-2 graph contract was reproduced independently:

- the ownership checker self-test passed;
- a clean `lake build NumStability` of detached baseline-evidence revision
  `62131d961` passed all 4,826 jobs;
- direct extraction from that worktree produced 115,717,110 bytes with
  SHA-256
  `FD37F73D83F0206E40291576E1F9496185F09C21928ABED147B5CE2A6EF83AED`,
  exactly matching the frozen format-2 baseline;
- direct extraction from the Phase 12A implementation produced 115,721,129
  bytes with SHA-256
  `E553EDA4343EFD695C68DE392463DAFE67B38C1E9347A5BB0E7FFC49F0DE1EB7`,
  exactly matching the independently prepared candidate; and
- the pinned pre check passed for 1,990 declarations and the stage check
  passed for 173 moved declarations across six destinations. Both checks
  reported an acyclic 83-destination graph with 437 cross-owner edges, and
  stage mode preserved the complete normalized contracted graph exactly.

Focused implementation validation also passed:

- isolated builds of all six declaration-bearing leaves plus the canonical
  Block LU and Theorem 05 umbrellas completed successfully with 2,545 jobs;
- canonical-only import tests, family-umbrella tests, and isolated historical
  `BlockLU` and `GrowthFactor` tests completed successfully with 3,017 jobs;
  and
- representative declarations from every new leaf reported only the accepted
  `[propext, Classical.choice, Quot.sound]` axiom set.

The static gates reported 1,045 production modules: 442 classified and 603
unclassified, with zero mixed classified modules. Within the reviewed
classified graph, there were zero reusable-to-source direct or transitive
paths. The import graph had zero unresolved project imports and zero cycles;
the layout ratchet had zero declaration-bearing umbrellas and zero unsorted
aggregate imports. It still records 216 legacy modules without module
documentation and 399 historical naming exceptions; those repository-wide
queues are deferred and did not increase in Phase 12A. The strict-source tree
SHA-256 was
`15cde7412e25d91fba6916cd154c333b7c76803b11fc2778dbe5b10a48d90d9b`.
Layout, compatibility, provenance, placeholder/debt, and `git diff --check`
all passed; compatibility covered 108 wrappers and 208 targets, and provenance
covered 207 Apache-licensed files plus five evidenced upstream files.

The final clean implementation-commit verification then passed
`lake build NumStability` with all 4,836 jobs, `lake test` with all 5,356 jobs,
and `lake build NumStability NumStabilityTest` with all 5,358 jobs. The
repository lookup example compiled successfully, as did an explicit build of
the historical BlockLU/GrowthFactor entry points and every direct or downstream
BlockLU consumer (4,698 jobs). A fresh candidate extraction, stage ownership
check, strict-source capture, and complete static-gate rerun reproduced the
same hashes and counts recorded above.

This evidence completed only the six-leaf Phase 12A extraction. At that
checkpoint, 1,817 declarations assigned to the other 77 destinations remained,
together with the sibling BlockLU modules requiring a separate ownership map.

## Phase 12B Wave 1 implementation

The first reusable Phase 12B wave extracts 43 public semantic declarations
from 35 authored source commands:

| Canonical destination | Commands | Semantic declarations |
| --- | ---: | ---: |
| `Algorithms.LinearSystems.LU.BlockLU.DiagonalDominance` | 8 | 8 |
| `Algorithms.LinearSystems.LU.BlockLU.FactorizationError` | 1 | 9 |
| `Algorithms.LinearSystems.LU.BlockLU.GrowthBounds` | 10 | 10 |
| `Algorithms.LinearSystems.LU.BlockLU.ResidualLifting` | 16 | 16 |
| **Total** | **35** | **43** |

The 806 declaration and attached-comment lines in those leaves are verbatim
copies of their reviewed current-source spans. Removing those spans plus their
single shared separator deletes exactly 807 lines from the historical file;
its complete declaration-bearing namespace tail is otherwise text-identical.
The historical module imports the four leaves, and the canonical Block LU
aggregate exposes them without adding a source dependency.

This wave changes no authored-private owner, so the private-rewrite file remains
header-only. Its cumulative stage target is 216 of 1,990 declarations across
ten destinations. After it, 1,774 mapped declarations remain: 79 reusable and
1,695 source-owned across 73 destinations.

### Phase 12B Wave 1 validation evidence

Pre-commit validation reproduced the format-2 graph contract. The fresh
`benchmark-results/architecture/phase12b-wave1-declarations-v2.tsv` stream is
115,722,432 bytes with SHA-256
`645DAC58F4DA835168F8E29EDB6DD0D247EF6BA5F8B8A59D8D46C51928526665`;
the frozen baseline remains 115,717,110 bytes with SHA-256
`FD37F73D83F0206E40291576E1F9496185F09C21928ABED147B5CE2A6EF83AED`.
The ownership-checker self-test and pinned pre check passed for all 1,990
declarations. The cumulative stage check passed for 216 moved declarations
across ten destinations, reporting an acyclic 83-destination graph with 437
cross-owner edges and exact preservation of the complete normalized contracted
graph.

A focused build of the four new declaration-bearing leaves, the canonical
Block LU aggregate, their four canonical import tests, and the isolated
old-only historical BlockLU test passed all 3,003 jobs. Representative
declarations from every new leaf reported exactly the accepted
`[propext, Classical.choice, Quot.sound]` axiom set. The full
`lake build NumStability` passed all 4,840 jobs and a warm repeat exited
successfully. `lake test` passed all 5,364 jobs, and
`lake build NumStability NumStabilityTest` passed all 5,366 jobs.
`lake env lean examples/LibraryLookup.lean` also succeeded. An explicit build
of every direct or downstream BlockLU consumer listed above passed all 4,702
jobs, and each target was then warm-confirmed independently.

The static gates reported 1,049 production modules: 446 classified and 603
unclassified, with zero mixed classified modules and zero direct or transitive
reusable-to-source paths. The import graph had zero unresolved project imports
and zero cycles; the layout ratchet had zero declaration-bearing umbrellas and
zero unsorted aggregate imports. The existing repository-wide queues remain
216 modules without module documentation and 399 historical naming exceptions.
Compatibility covered 108 wrappers and 208 targets, while provenance covered
207 Apache-licensed files plus five evidenced upstream files. The strict-source
tree SHA-256 was
`9c2f4a5377b7020899786a31eec353806eec13d848a404efda8814c98cfd4731`.
Layout, compatibility, provenance, source-boundary, placeholder/debt,
strict-source reproducibility, and `git diff --check` all passed.

Implementation commit `78debf173` left the tracked worktree and index clean.
The clean-commit repeat then reproduced the candidate declaration stream
byte-for-byte and repeated the checker self-test, pinned pre check, cumulative
stage check, strict-source capture, and every static gate with the same hashes,
counts, and exact graph result recorded above. From that clean commit,
`lake build NumStability` passed all 4,840 jobs, `lake test` exited successfully
with 5,364 planned jobs, and `lake build NumStability NumStabilityTest` passed
all 5,366 jobs. The repository lookup, eight-target downstream build with all
4,702 jobs, and representative axiom checks also passed again. This satisfies
the clean-implementation repeat for Wave 1; the final Phase 12 baseline remains
reserved for the completed 1,990-declaration migration. Phase 12 remains open
for the other 1,774 mapped declarations across 73 destinations and for the
separately mapped sibling BlockLU modules.

## Phase 12B safe reusable slice implementation

The next dependency-contained reusable slice extracts 71 public semantic
declarations from 63 authored source commands. `Factorization` moves first;
the other three leaves depend on it but not on one another.

| Canonical destination | Commands | Semantic declarations |
| --- | ---: | ---: |
| `Algorithms.LinearSystems.LU.BlockLU.Factorization` | 49 | 57 |
| `Algorithms.LinearSystems.LU.BlockLU.PositiveDefinite` | 7 | 7 |
| `Algorithms.LinearSystems.LU.BlockLU.SchurComplement` | 4 | 4 |
| `Algorithms.LinearSystems.LU.BlockLU.SolveError` | 3 | 3 |
| **Total** | **63** | **71** |

The 1,161 declaration and attached-comment lines in these leaves are verbatim
copies of their frozen reviewed source spans. The historical module imports the
four leaves, and the canonical Block LU aggregate exposes them without adding
a source dependency. One-import leaf tests check every public declaration,
including the generated `BlockLUFactSpec` constructor, projections, recursor,
and eliminators.

This slice changes no authored-private owner and deliberately leaves the eight
`RecursiveFactorization` declarations in the historical module. The cumulative
stage target is now 287 of 1,990 declarations across fourteen completed
destinations. The remaining mapped partition contains 1,703 declarations
across 69 destinations: eight reusable declarations assigned to
`RecursiveFactorization` and 1,695 source-owned declarations across 68 source
destinations.

### Phase 12B safe reusable slice validation evidence

Pre-commit validation reproduced the format-2 graph contract. The fresh
`benchmark-results/architecture/phase12b-safe-reusable-declarations-v2.tsv`
stream is 115,724,440 bytes with SHA-256
`7572D4BDF1939E0FCF36CE21CA1BFB43E7512FC59D24045D74F9AF2A23B1D42F`;
the frozen baseline remains 115,717,110 bytes with SHA-256
`FD37F73D83F0206E40291576E1F9496185F09C21928ABED147B5CE2A6EF83AED`.
The ownership-checker self-test and pinned pre check passed for all 1,990
declarations. The cumulative stage check passed for 287 moved declarations
across fourteen destinations, reporting an acyclic 83-destination graph with
437 cross-owner edges and exact preservation of the complete normalized
contracted graph. The only seven structural owners are the expected canonical
LinearSystems/LU, FirstOrder, MatrixNorms, and Chapter 13 umbrellas; no
structural module is in the broad `NumStability.Algorithms` namespace.

Standalone and focused aggregate builds covered every declaration in the four
new leaves and passed up to 3,004 planned jobs. The full
`lake build NumStability` passed all 4,844 jobs. `lake test` passed all 5,372
jobs, and `lake build NumStability NumStabilityTest` passed all 5,374 jobs.
`lake env lean examples/LibraryLookup.lean` also succeeded. An explicit build
of the historical entry point and all ten direct or downstream BlockLU
consumers passed all 4,706 jobs. The ignored API/axiom probe verified the
`BlockLUFactSpec` structure, fields, constructor, cases, and recursors; each
representative theorem reported exactly the accepted
`[propext, Classical.choice, Quot.sound]` axiom set.

The static gates reported 1,053 production modules: 450 classified and 603
unclassified, with zero mixed classified modules and zero direct or transitive
reusable-to-source paths. Tier coverage is 42.735 percent, comprising 92
aggregate modules, 108 compatibility modules, two internal modules, 91
reusable modules, 152 source modules, and five evidenced upstream modules.
The import graph has 4,258 direct imports, zero unresolved project imports,
and zero cycles; the layout ratchet has zero declaration-bearing umbrellas and
zero unsorted aggregate imports. The existing repository-wide queues remain
216 modules without module documentation and 399 historical naming
exceptions. Compatibility covers 108 wrappers and 208 targets, while
provenance covers 207 Apache-licensed files plus five evidenced upstream
files. The strict-source tree SHA-256 is
`48DE4005B319B0F437E736F1A37177D6D9C619AA88D4D9B036638954C86BE73B`;
its JSON capture is 95,825 bytes with SHA-256
`F6F2AD0261E6C2DA8EEA49258C4BA005114ECCEE7BC3E367070FD9A2E5484648`,
and its rendered Markdown is 4,962 bytes with SHA-256
`DCA002BE59D250D9E85458954064B3DA719BC772FC8F388D6A68A18A6F124C15`.
Layout, compatibility, provenance, source-boundary, placeholder/debt,
strict-source reproducibility, `git diff --check`, and index checks all pass.

Implementation commit `88c73e6c0` left the tracked worktree and index clean.
The clean-commit repeat reproduced the candidate declaration stream
byte-for-byte and repeated the checker self-test, pinned pre check, cumulative
stage check, strict-source capture, and every static gate with the same source
tree hash, counts, and exact graph result recorded above. Its clean JSON
capture is 95,398 bytes with SHA-256
`4C690F7A9CACFCF13BCE00CAF1FEF5FA432417143AD8164A54FAAB570B8A5997`,
and its clean rendered Markdown is 4,500 bytes with SHA-256
`BD657A4E01DBFFDA79207B4C4B365636E5B46C33C689B867BE68AD3626470C8F`.
From that clean commit, `lake build NumStability` passed all 4,844 jobs,
`lake test` passed its 5,372-job graph, and
`lake build NumStability NumStabilityTest` passed all 5,374 jobs. The
repository lookup, ten-target downstream build with all 4,706 jobs, and the
complete `BlockLUFactSpec` API and representative axiom checks also passed
again. This satisfies the clean-implementation repeat for the safe reusable
slice; the final Phase 12 baseline remains reserved for the completed
1,990-declaration migration.

## Bounded exclusions and completion boundary

This batch does not rename public declarations or namespaces, change
visibility, rewrite proofs for style, adopt a new module-system dialect, remove
compatibility paths, reorganize Chapter 9 or Chapter 11 monoliths, begin the
least-squares/QR phases, or create a second physical Lake library. No authored
proof rewrite is permitted. Compiler-generated auxiliaries may change identity
or elaboration order, but the format-2 checker requires exact equality of the
contracted authored signature/body graph after owner and private-name
normalization.

The sibling BlockLU declaration migration is explicitly outside this first
1,990-declaration semantic partition but inside the overall BlockLU phase. It
requires its own pre-edit map and all the same compatibility gates. After that
work, the strict repository order proceeds to LSQRSolve, LSE/GQR/KKT, QR and
Chapters 19--20,
the smaller source/outlier queues, the Chapter 9 and Chapter 11 monoliths, and
the global organization completion gate. No broader repository-complete claim
is made by this record.
