# W08 changed-path evidence

Generated from the exact base-to-delivery diff:

```console
git diff --cached --name-status 240c0d041781385a647fbec461d6863537e562cb
```

`--cached` is required: a plain `git diff` reports only tracked changes and
would omit every newly added canonical module, test and evidence file.

**250 changed paths.**

| classification | paths |
| --- | ---: |
| owned historical source | 42 |
| authorized destination | 73 |
| W08 test | 125 |
| W08 delivery evidence | 10 |
| UNOWNED | 0 |

## Proofs

- **42/42 owners accounted for:** 42 of 42 B0007 owned paths appear in the diff.
- **Zero forbidden paths:** 0. `tiers.json`, `layout-exceptions.json`, `COMPATIBILITY.md`, the global/family/chapter aggregates, `NumStabilityTest.lean`, the phase records, CI, Lake, the toolchain and `tools/architecture/` are all unmodified.
- **Zero unowned paths:** 0.
- **Every destination is under B0007:** each added production path lies inside one of B0007's 42 authorized production prefixes; the two worker prefixes hold the tests and this evidence.
- **No generated artifact tracked:** 0 (`.olean`/`.ilean`/`.c`/`.lake/`/`benchmark-results/`).

## Modified: the 42 owned historical paths (42)

| status | path | sha256 (16) |
| --- | --- | --- |
| `M` | `NumStability/Algorithms/Ch14AsymptoticFamilies.lean` | `994CDCBC6D31CAD1` |
| `M` | `NumStability/Algorithms/Ch14BlockTriInverse.lean` | `7311ADCF65FBDFEA` |
| `M` | `NumStability/Algorithms/Ch14Cor146UniformInverseBridge.lean` | `00621DB7EF49985D` |
| `M` | `NumStability/Algorithms/Ch14Cor147FinalDivisionFamilyClosure.lean` | `9C1FC777B7BFC5D2` |
| `M` | `NumStability/Algorithms/Ch14Cor147SourceDomainConstructor.lean` | `F85A5BCB94B11B11` |
| `M` | `NumStability/Algorithms/Ch14Corollary146Closure.lean` | `45E20B36C1961FDC` |
| `M` | `NumStability/Algorithms/Ch14Corollary146Concrete.lean` | `A85A724CED31A983` |
| `M` | `NumStability/Algorithms/Ch14Corollary146SourceClosure.lean` | `56D2B37FC21C6C27` |
| `M` | `NumStability/Algorithms/Ch14Corollary147.lean` | `1DF572B4484E941B` |
| `M` | `NumStability/Algorithms/Ch14Corollary147Closure.lean` | `9F72E5668E889DEA` |
| `M` | `NumStability/Algorithms/Ch14Corollary147Concrete.lean` | `E77CDFEA63F71CA9` |
| `M` | `NumStability/Algorithms/Ch14Corollary147SourceClosure.lean` | `B1CC5FAF52805295` |
| `M` | `NumStability/Algorithms/Ch14Corollary147WeakFamily.lean` | `8CD98E7F44C09598` |
| `M` | `NumStability/Algorithms/Ch14ForwardErrorEndpoint.lean` | `C770FC1B661E07C5` |
| `M` | `NumStability/Algorithms/Ch14GJEActualDoolittleAdapter.lean` | `2FAA7513B4669F73` |
| `M` | `NumStability/Algorithms/Ch14GJEAsymptoticFamilies.lean` | `FDE48963874BDCF5` |
| `M` | `NumStability/Algorithms/Ch14GJEFinalDivisionClosure.lean` | `EC7911C1B9640A06` |
| `M` | `NumStability/Algorithms/Ch14GJEOperationalBridge.lean` | `A7721A6E1063F822` |
| `M` | `NumStability/Algorithms/Ch14GJEPrintedEnvelopeClosure.lean` | `5D63FEC6A25770D9` |
| `M` | `NumStability/Algorithms/Ch14GJESourceAccumulationBridge.lean` | `6814E66F522A085F` |
| `M` | `NumStability/Algorithms/Ch14GJETheorem145SourceClosure.lean` | `4C7967E7C3226579` |
| `M` | `NumStability/Algorithms/Ch14GaussJordanAccumulation.lean` | `97E4E772A4CD671E` |
| `M` | `NumStability/Algorithms/Ch14GaussJordanQConstruction.lean` | `17F34546CE9F6E31` |
| `M` | `NumStability/Algorithms/Ch14GaussJordanSPDCorollary.lean` | `105C8F6E04FFF849` |
| `M` | `NumStability/Algorithms/Ch14GaussJordanSourceClosure.lean` | `73ED5F81D388A2AD` |
| `M` | `NumStability/Algorithms/Ch14GaussJordanStep.lean` | `057989615725AEEB` |
| `M` | `NumStability/Algorithms/Ch14Method1BWhole.lean` | `239D2884AA273772` |
| `M` | `NumStability/Algorithms/Ch14Method2C.lean` | `B9FC00B3E9307D5B` |
| `M` | `NumStability/Algorithms/Ch14Method2CWhole.lean` | `18008A2695651572` |
| `M` | `NumStability/Algorithms/Ch14Method2Loop.lean` | `1712886DB1AA24BD` |
| `M` | `NumStability/Algorithms/Ch14MethodDLeftResidual.lean` | `8832E74496F48A18` |
| `M` | `NumStability/Algorithms/Ch14MethodDProductDischarge.lean` | `CCAAC64B4CB62B38` |
| `M` | `NumStability/Algorithms/Ch14MethodDUpperCertificate.lean` | `8548FFA6D27293BB` |
| `M` | `NumStability/Algorithms/Ch14MethodsBC.lean` | `9AB4014EB3FDAC41` |
| `M` | `NumStability/Algorithms/Ch14Problem142.lean` | `F525532B06159308` |
| `M` | `NumStability/Algorithms/Ch14Problem142Families.lean` | `17F7D09D20EEF6CA` |
| `M` | `NumStability/Algorithms/Ch14Problem142Method2B.lean` | `45ED0BFB53AFCAEE` |
| `M` | `NumStability/Algorithms/Ch14ProductErrorNotation.lean` | `4B0B34EAEE943EBE` |
| `M` | `NumStability/Algorithms/GaussJordan.lean` | `3876D43185D8E18B` |
| `M` | `NumStability/Algorithms/GaussJordanPivoting.lean` | `835A4D29F5FF6BE0` |
| `M` | `NumStability/Algorithms/MatrixInversion.lean` | `A7BEBDE7AF16A286` |
| `M` | `NumStability/Algorithms/MatrixInversionMethod2BInstance.lean` | `3C87DA26C3EE0D18` |

## Added: authorized canonical destinations (73)

| status | path | sha256 (16) |
| --- | --- | --- |
| `A` | `NumStability/Algorithms/LinearSystems/GaussJordan/ErrorAnalysis/GaussJordan.lean` | `6DCD388147628436` |
| `A` | `NumStability/Algorithms/MatrixInversion/LUFactors/ErrorAnalysis/MatrixInversion.lean` | `E0322D7A6043050E` |
| `A` | `NumStability/Algorithms/MatrixInversion/LUFactors/Methods/MatrixInversion.lean` | `D14E73172FDA8310` |
| `A` | `NumStability/Algorithms/MatrixInversion/Residuals/MatrixInversion.lean` | `5AF4D2A49C23CC75` |
| `A` | `NumStability/Algorithms/MatrixInversion/Triangular/ErrorAnalysis/MatrixInversion.lean` | `C9FDA3FDE38B7DBE` |
| `A` | `NumStability/Algorithms/MatrixInversion/Triangular/Specifications/MatrixInversion.lean` | `1B377ACA9B61D8ED` |
| `A` | `NumStability/Analysis/Error/MatrixProducts/Contracts/MatrixInversion.lean` | `23E3B9DEEA1F9DB0` |
| `A` | `NumStability/Analysis/Error/MatrixProducts/EvaluationTrees/ProductErrorNotation.lean` | `25FCBED68576B072` |
| `A` | `NumStability/Analysis/FirstOrder/MatrixFamilies/AsymptoticFamilies.lean` | `7FEFE0A0E3576BDC` |
| `A` | `NumStability/Source/Higham/Chapter14/Algorithm04/Accumulation/GJESourceAccumulationBridge.lean` | `BBB5EA79B1E59C68` |
| `A` | `NumStability/Source/Higham/Chapter14/Algorithm04/Accumulation/GaussJordanAccumulation.lean` | `271C901D88C788D9` |
| `A` | `NumStability/Source/Higham/Chapter14/Algorithm04/Execution/GJEActualDoolittleAdapter.lean` | `4A7F49128874739C` |
| `A` | `NumStability/Source/Higham/Chapter14/Algorithm04/Execution/GJEFinalDivisionClosure.lean` | `8ED2EE8D3F2283C2` |
| `A` | `NumStability/Source/Higham/Chapter14/Algorithm04/Execution/GJEOperationalBridge.lean` | `FB34D5CEA1C5F4EF` |
| `A` | `NumStability/Source/Higham/Chapter14/Algorithm04/Execution/GaussJordanSourceClosure.lean` | `31C4F359FBCBC45B` |
| `A` | `NumStability/Source/Higham/Chapter14/Algorithm04/Pivoting/GaussJordanPivoting.lean` | `C3495FD0C08A3F32` |
| `A` | `NumStability/Source/Higham/Chapter14/Algorithm04/SecondStage/GaussJordanQConstruction.lean` | `E1A1E8DE3F10B0EF` |
| `A` | `NumStability/Source/Higham/Chapter14/Algorithm04/SecondStage/GaussJordanStep.lean` | `A867118246E61EBF` |
| `A` | `NumStability/Source/Higham/Chapter14/Corollary06/SPD/Closure.lean` | `38535935D5C3BF63` |
| `A` | `NumStability/Source/Higham/Chapter14/Corollary06/SPD/Concrete.lean` | `EE54AB283090268A` |
| `A` | `NumStability/Source/Higham/Chapter14/Corollary06/SPD/GaussJordanSPDCorollary.lean` | `125B500987B3E89F` |
| `A` | `NumStability/Source/Higham/Chapter14/Corollary06/SPD/SourceClosure.lean` | `A2E9435917599635` |
| `A` | `NumStability/Source/Higham/Chapter14/Corollary06/SPD/UniformInverseBridge.lean` | `FD7085B606564181` |
| `A` | `NumStability/Source/Higham/Chapter14/Corollary07/DiagonalDominance/Basic.lean` | `64E767EC053BA448` |
| `A` | `NumStability/Source/Higham/Chapter14/Corollary07/DiagonalDominance/Closure.lean` | `F127FF0AF8E0F223` |
| `A` | `NumStability/Source/Higham/Chapter14/Corollary07/DiagonalDominance/Concrete.lean` | `47998836D20B45D6` |
| `A` | `NumStability/Source/Higham/Chapter14/Corollary07/DiagonalDominance/FinalDivisionFamilyClosure.lean` | `A2C787A5FFD37B87` |
| `A` | `NumStability/Source/Higham/Chapter14/Corollary07/DiagonalDominance/SourceClosure.lean` | `6DA2470064B47C48` |
| `A` | `NumStability/Source/Higham/Chapter14/Corollary07/DiagonalDominance/SourceDomainConstructor.lean` | `36BDAD81BFE74DBA` |
| `A` | `NumStability/Source/Higham/Chapter14/Corollary07/DiagonalDominance/WeakFamily.lean` | `EDE01ACA78FB7917` |
| `A` | `NumStability/Source/Higham/Chapter14/Equation34/DeterminantFromLU/MatrixInversion.lean` | `AB94D47369EFD0E6` |
| `A` | `NumStability/Source/Higham/Chapter14/Equation35/HymanBlockFactorization/MatrixInversion.lean` | `AB0574BD94A0649F` |
| `A` | `NumStability/Source/Higham/Chapter14/Equation36/HymanDeterminant/MatrixInversion.lean` | `BEFC330BB23B27E1` |
| `A` | `NumStability/Source/Higham/Chapter14/Problem02/TriangularInversion/Basic.lean` | `7DBB62A3BFF93D35` |
| `A` | `NumStability/Source/Higham/Chapter14/Problem02/TriangularInversion/Families.lean` | `7B9400D715B786D2` |
| `A` | `NumStability/Source/Higham/Chapter14/Problem02/TriangularInversion/Method2B.lean` | `6975BADD9FB26170` |
| `A` | `NumStability/Source/Higham/Chapter14/Problem03/ResidualComparison/MatrixInversion.lean` | `07A964DF37C8C03E` |
| `A` | `NumStability/Source/Higham/Chapter14/Problem04/ResidualCounterexample/MatrixInversion.lean` | `086776FC56A5F55A` |
| `A` | `NumStability/Source/Higham/Chapter14/Problem05/InverseBasedSolve/AsymptoticFamilies.lean` | `7BE02A6757C32CDF` |
| `A` | `NumStability/Source/Higham/Chapter14/Problem05/InverseBasedSolve/ForwardErrorEndpoint.lean` | `C6B0F7E59B6D31A7` |
| `A` | `NumStability/Source/Higham/Chapter14/Problem05/InverseBasedSolve/MatrixInversion.lean` | `1DF8459ACDB46635` |
| `A` | `NumStability/Source/Higham/Chapter14/Problem07/OnesVector/MatrixInversion.lean` | `71D9CFCE80459B35` |
| `A` | `NumStability/Source/Higham/Chapter14/Problem08/ComplexInverseRealBlock/MatrixInversion.lean` | `A97FC47ECD9F2B4E` |
| `A` | `NumStability/Source/Higham/Chapter14/Problem10/EntryPerturbation/MatrixInversion.lean` | `4599ABCEE2231ECC` |
| `A` | `NumStability/Source/Higham/Chapter14/Problem11/HadamardCondition/MatrixInversion.lean` | `8F8BF49665844824` |
| `A` | `NumStability/Source/Higham/Chapter14/Problem12/HadamardExamples/MatrixInversion.lean` | `6104A800EF5B4135` |
| `A` | `NumStability/Source/Higham/Chapter14/Problem13/GEJBound/MatrixInversion.lean` | `DA0FD7D385A9C560` |
| `A` | `NumStability/Source/Higham/Chapter14/Problem14/HymanDeterminant/MatrixInversion.lean` | `4F1BCBFD1B368C79` |
| `A` | `NumStability/Source/Higham/Chapter14/Problem15/DeterminantPerturbation/MatrixInversion.lean` | `2093E38B1FA0FD79` |
| `A` | `NumStability/Source/Higham/Chapter14/Section01/InverseErrorAnalysis/AsymptoticFamilies.lean` | `DC677320F5D01D48` |
| `A` | `NumStability/Source/Higham/Chapter14/Section01/InverseErrorAnalysis/ForwardErrorEndpoint.lean` | `C0E3EB052AE63549` |
| `A` | `NumStability/Source/Higham/Chapter14/Section01/InverseErrorAnalysis/MatrixInversion.lean` | `4C3051A3C24CB8A3` |
| `A` | `NumStability/Source/Higham/Chapter14/Section01/ProductErrorNotation/ProductErrorNotation.lean` | `FA3F700FF55CFD43` |
| `A` | `NumStability/Source/Higham/Chapter14/Section02/TriangularInversion/Method1/AsymptoticFamilies.lean` | `4396865C5F687730` |
| `A` | `NumStability/Source/Higham/Chapter14/Section02/TriangularInversion/Method1/ForwardErrorEndpoint.lean` | `CCB36B33B2E8651B` |
| `A` | `NumStability/Source/Higham/Chapter14/Section02/TriangularInversion/Method1B/BlockTriInverse.lean` | `CC942ED51419D0D4` |
| `A` | `NumStability/Source/Higham/Chapter14/Section02/TriangularInversion/Method1B/Method1BWhole.lean` | `AAC6EADA9D02A175` |
| `A` | `NumStability/Source/Higham/Chapter14/Section02/TriangularInversion/Method2/Method2Loop.lean` | `FA9DAD1000D4784B` |
| `A` | `NumStability/Source/Higham/Chapter14/Section02/TriangularInversion/Method2B/MatrixInversion.lean` | `A94A3C6ADF1D752F` |
| `A` | `NumStability/Source/Higham/Chapter14/Section02/TriangularInversion/Method2B/MatrixInversionMethod2BInstance.lean` | `725025E8B8C6024F` |
| `A` | `NumStability/Source/Higham/Chapter14/Section02/TriangularInversion/Method2C/Method2C.lean` | `B474691851E1BD69` |
| `A` | `NumStability/Source/Higham/Chapter14/Section02/TriangularInversion/Method2C/Method2CWhole.lean` | `C3D78781880449D5` |
| `A` | `NumStability/Source/Higham/Chapter14/Section03/LUFactorInversion/MethodB/MethodsBC.lean` | `FB83125FB87989B0` |
| `A` | `NumStability/Source/Higham/Chapter14/Section03/LUFactorInversion/MethodC/MethodsBC.lean` | `C01388D27714AF33` |
| `A` | `NumStability/Source/Higham/Chapter14/Section03/LUFactorInversion/MethodD/MatrixInversion.lean` | `51523E3EFD060602` |
| `A` | `NumStability/Source/Higham/Chapter14/Section03/LUFactorInversion/MethodD/MethodDLeftResidual.lean` | `BC9198349CA1513A` |
| `A` | `NumStability/Source/Higham/Chapter14/Section03/LUFactorInversion/MethodD/MethodDProductDischarge.lean` | `BFD7BBBF876638EB` |
| `A` | `NumStability/Source/Higham/Chapter14/Section03/LUFactorInversion/MethodD/MethodDUpperCertificate.lean` | `9486A6B552B5A404` |
| `A` | `NumStability/Source/Higham/Chapter14/Theorem05/ForwardError/GJEAsymptoticFamilies.lean` | `687E0A602E495CCD` |
| `A` | `NumStability/Source/Higham/Chapter14/Theorem05/ForwardError/GJEFinalDivisionClosure.lean` | `435D4E4A5793F95C` |
| `A` | `NumStability/Source/Higham/Chapter14/Theorem05/ForwardError/GJEPrintedEnvelopeClosure.lean` | `0604C2C5ADB3BAA6` |
| `A` | `NumStability/Source/Higham/Chapter14/Theorem05/ForwardError/GJETheorem145SourceClosure.lean` | `83FFDC012840C655` |
| `A` | `NumStability/Source/Higham/Chapter14/Theorem05/ForwardError/GaussJordanQConstruction.lean` | `774EB0D11DC75317` |

## Added: W08 focused tests (125)

| status | path | sha256 (16) |
| --- | --- | --- |
| `A` | `NumStabilityTest/Reorganization/W08/Canonical/Algorithms/LinearSystems/GaussJordan/ErrorAnalysis/GaussJordan.lean` | `8F2011953354A50B` |
| `A` | `NumStabilityTest/Reorganization/W08/Canonical/Algorithms/MatrixInversion/LUFactors/ErrorAnalysis/MatrixInversion.lean` | `68A2FE820E35DFEC` |
| `A` | `NumStabilityTest/Reorganization/W08/Canonical/Algorithms/MatrixInversion/LUFactors/Methods/MatrixInversion.lean` | `E68805018D0CAC85` |
| `A` | `NumStabilityTest/Reorganization/W08/Canonical/Algorithms/MatrixInversion/Residuals/MatrixInversion.lean` | `CA39EE27CFFF9168` |
| `A` | `NumStabilityTest/Reorganization/W08/Canonical/Algorithms/MatrixInversion/Triangular/ErrorAnalysis/MatrixInversion.lean` | `DB3FFA8C9D267E9C` |
| `A` | `NumStabilityTest/Reorganization/W08/Canonical/Algorithms/MatrixInversion/Triangular/Specifications/MatrixInversion.lean` | `FB6CA441230C593E` |
| `A` | `NumStabilityTest/Reorganization/W08/Canonical/Analysis/Error/MatrixProducts/Contracts/MatrixInversion.lean` | `801D3B5752650144` |
| `A` | `NumStabilityTest/Reorganization/W08/Canonical/Analysis/Error/MatrixProducts/EvaluationTrees/ProductErrorNotation.lean` | `2C06ADB6DDB587B7` |
| `A` | `NumStabilityTest/Reorganization/W08/Canonical/Analysis/FirstOrder/MatrixFamilies/AsymptoticFamilies.lean` | `9DB22AA6AF50AE40` |
| `A` | `NumStabilityTest/Reorganization/W08/Canonical/Chapter14/Algorithm04/Accumulation/GJESourceAccumulationBridge.lean` | `D5340DAD864EA497` |
| `A` | `NumStabilityTest/Reorganization/W08/Canonical/Chapter14/Algorithm04/Accumulation/GaussJordanAccumulation.lean` | `F291F45CCAF508FF` |
| `A` | `NumStabilityTest/Reorganization/W08/Canonical/Chapter14/Algorithm04/Execution/GJEActualDoolittleAdapter.lean` | `1C5C4CC669D08CA9` |
| `A` | `NumStabilityTest/Reorganization/W08/Canonical/Chapter14/Algorithm04/Execution/GJEFinalDivisionClosure.lean` | `51486B9204B7B040` |
| `A` | `NumStabilityTest/Reorganization/W08/Canonical/Chapter14/Algorithm04/Execution/GJEOperationalBridge.lean` | `DEA3E72AF16C41DA` |
| `A` | `NumStabilityTest/Reorganization/W08/Canonical/Chapter14/Algorithm04/Execution/GaussJordanSourceClosure.lean` | `9582BDE176EFB329` |
| `A` | `NumStabilityTest/Reorganization/W08/Canonical/Chapter14/Algorithm04/Pivoting/GaussJordanPivoting.lean` | `448F617E49ABF72A` |
| `A` | `NumStabilityTest/Reorganization/W08/Canonical/Chapter14/Algorithm04/SecondStage/GaussJordanQConstruction.lean` | `D96C7D4C60482230` |
| `A` | `NumStabilityTest/Reorganization/W08/Canonical/Chapter14/Algorithm04/SecondStage/GaussJordanStep.lean` | `CDE887CAF48652F5` |
| `A` | `NumStabilityTest/Reorganization/W08/Canonical/Chapter14/Corollary06/SPD/Closure.lean` | `281DCC8C60A67DE8` |
| `A` | `NumStabilityTest/Reorganization/W08/Canonical/Chapter14/Corollary06/SPD/Concrete.lean` | `95E841037C2CB138` |
| `A` | `NumStabilityTest/Reorganization/W08/Canonical/Chapter14/Corollary06/SPD/GaussJordanSPDCorollary.lean` | `0F4B8E048E542CAC` |
| `A` | `NumStabilityTest/Reorganization/W08/Canonical/Chapter14/Corollary06/SPD/SourceClosure.lean` | `6CF97056837AF04A` |
| `A` | `NumStabilityTest/Reorganization/W08/Canonical/Chapter14/Corollary06/SPD/UniformInverseBridge.lean` | `0891FFF78A8979BF` |
| `A` | `NumStabilityTest/Reorganization/W08/Canonical/Chapter14/Corollary07/DiagonalDominance/Basic.lean` | `E76BD58EE5DF3A89` |
| `A` | `NumStabilityTest/Reorganization/W08/Canonical/Chapter14/Corollary07/DiagonalDominance/Closure.lean` | `D0C88B38B4C77225` |
| `A` | `NumStabilityTest/Reorganization/W08/Canonical/Chapter14/Corollary07/DiagonalDominance/Concrete.lean` | `406482AF4C839B59` |
| `A` | `NumStabilityTest/Reorganization/W08/Canonical/Chapter14/Corollary07/DiagonalDominance/FinalDivisionFamilyClosure.lean` | `F1FE295EA4ADFDBF` |
| `A` | `NumStabilityTest/Reorganization/W08/Canonical/Chapter14/Corollary07/DiagonalDominance/SourceClosure.lean` | `8D7B07C02A331D10` |
| `A` | `NumStabilityTest/Reorganization/W08/Canonical/Chapter14/Corollary07/DiagonalDominance/SourceDomainConstructor.lean` | `1D47906734229EA9` |
| `A` | `NumStabilityTest/Reorganization/W08/Canonical/Chapter14/Corollary07/DiagonalDominance/WeakFamily.lean` | `546D0470D5589A9C` |
| `A` | `NumStabilityTest/Reorganization/W08/Canonical/Chapter14/Equation34/DeterminantFromLU/MatrixInversion.lean` | `F1682CF4F01D51D0` |
| `A` | `NumStabilityTest/Reorganization/W08/Canonical/Chapter14/Equation35/HymanBlockFactorization/MatrixInversion.lean` | `FED0E3662E2C1DBF` |
| `A` | `NumStabilityTest/Reorganization/W08/Canonical/Chapter14/Equation36/HymanDeterminant/MatrixInversion.lean` | `E6C4E2C747AC0EC4` |
| `A` | `NumStabilityTest/Reorganization/W08/Canonical/Chapter14/Problem02/TriangularInversion/Basic.lean` | `F74F759C036489FE` |
| `A` | `NumStabilityTest/Reorganization/W08/Canonical/Chapter14/Problem02/TriangularInversion/Families.lean` | `13E718C535247C8A` |
| `A` | `NumStabilityTest/Reorganization/W08/Canonical/Chapter14/Problem02/TriangularInversion/Method2B.lean` | `714200E703E43BEA` |
| `A` | `NumStabilityTest/Reorganization/W08/Canonical/Chapter14/Problem03/ResidualComparison/MatrixInversion.lean` | `B2CF4D082DD1F19F` |
| `A` | `NumStabilityTest/Reorganization/W08/Canonical/Chapter14/Problem04/ResidualCounterexample/MatrixInversion.lean` | `97D180925FF85C49` |
| `A` | `NumStabilityTest/Reorganization/W08/Canonical/Chapter14/Problem05/InverseBasedSolve/AsymptoticFamilies.lean` | `37A225A05F1FE4B5` |
| `A` | `NumStabilityTest/Reorganization/W08/Canonical/Chapter14/Problem05/InverseBasedSolve/ForwardErrorEndpoint.lean` | `7FD6065F26DCF7FC` |
| `A` | `NumStabilityTest/Reorganization/W08/Canonical/Chapter14/Problem05/InverseBasedSolve/MatrixInversion.lean` | `DB6C35FF238C9DE1` |
| `A` | `NumStabilityTest/Reorganization/W08/Canonical/Chapter14/Problem07/OnesVector/MatrixInversion.lean` | `F1F23F071BC07166` |
| `A` | `NumStabilityTest/Reorganization/W08/Canonical/Chapter14/Problem08/ComplexInverseRealBlock/MatrixInversion.lean` | `984A00229794613C` |
| `A` | `NumStabilityTest/Reorganization/W08/Canonical/Chapter14/Problem10/EntryPerturbation/MatrixInversion.lean` | `A0569197F4AE9B96` |
| `A` | `NumStabilityTest/Reorganization/W08/Canonical/Chapter14/Problem11/HadamardCondition/MatrixInversion.lean` | `550CB349BEE65566` |
| `A` | `NumStabilityTest/Reorganization/W08/Canonical/Chapter14/Problem12/HadamardExamples/MatrixInversion.lean` | `90CE84DE6309720A` |
| `A` | `NumStabilityTest/Reorganization/W08/Canonical/Chapter14/Problem13/GEJBound/MatrixInversion.lean` | `85FE6730AD8B53A3` |
| `A` | `NumStabilityTest/Reorganization/W08/Canonical/Chapter14/Problem14/HymanDeterminant/MatrixInversion.lean` | `A308DB48148A372B` |
| `A` | `NumStabilityTest/Reorganization/W08/Canonical/Chapter14/Problem15/DeterminantPerturbation/MatrixInversion.lean` | `B337696065DC6497` |
| `A` | `NumStabilityTest/Reorganization/W08/Canonical/Chapter14/Section01/InverseErrorAnalysis/AsymptoticFamilies.lean` | `9EF13A4C11C540A5` |
| `A` | `NumStabilityTest/Reorganization/W08/Canonical/Chapter14/Section01/InverseErrorAnalysis/ForwardErrorEndpoint.lean` | `59D1A95D009EC7DA` |
| `A` | `NumStabilityTest/Reorganization/W08/Canonical/Chapter14/Section01/InverseErrorAnalysis/MatrixInversion.lean` | `A849F7F08CB9320B` |
| `A` | `NumStabilityTest/Reorganization/W08/Canonical/Chapter14/Section01/ProductErrorNotation/ProductErrorNotation.lean` | `78A9198CCF09D851` |
| `A` | `NumStabilityTest/Reorganization/W08/Canonical/Chapter14/Section02/TriangularInversion/Method1/AsymptoticFamilies.lean` | `B354CF048DFE4AC5` |
| `A` | `NumStabilityTest/Reorganization/W08/Canonical/Chapter14/Section02/TriangularInversion/Method1/ForwardErrorEndpoint.lean` | `A9466988837DC1C6` |
| `A` | `NumStabilityTest/Reorganization/W08/Canonical/Chapter14/Section02/TriangularInversion/Method1B/BlockTriInverse.lean` | `43EB96B742AB04B7` |
| `A` | `NumStabilityTest/Reorganization/W08/Canonical/Chapter14/Section02/TriangularInversion/Method1B/Method1BWhole.lean` | `53A5D68119FDC3FB` |
| `A` | `NumStabilityTest/Reorganization/W08/Canonical/Chapter14/Section02/TriangularInversion/Method2/Method2Loop.lean` | `670CD7DB253E9D8B` |
| `A` | `NumStabilityTest/Reorganization/W08/Canonical/Chapter14/Section02/TriangularInversion/Method2B/MatrixInversion.lean` | `95F171272E7D87F0` |
| `A` | `NumStabilityTest/Reorganization/W08/Canonical/Chapter14/Section02/TriangularInversion/Method2B/MatrixInversionMethod2BInstance.lean` | `28CFAB9B6351402B` |
| `A` | `NumStabilityTest/Reorganization/W08/Canonical/Chapter14/Section02/TriangularInversion/Method2C/Method2C.lean` | `592CDB85BA1A9616` |
| `A` | `NumStabilityTest/Reorganization/W08/Canonical/Chapter14/Section02/TriangularInversion/Method2C/Method2CWhole.lean` | `0EAB958A7F1C4207` |
| `A` | `NumStabilityTest/Reorganization/W08/Canonical/Chapter14/Section03/LUFactorInversion/MethodB/MethodsBC.lean` | `0F483F9C81EF9AA4` |
| `A` | `NumStabilityTest/Reorganization/W08/Canonical/Chapter14/Section03/LUFactorInversion/MethodC/MethodsBC.lean` | `051998255A002C93` |
| `A` | `NumStabilityTest/Reorganization/W08/Canonical/Chapter14/Section03/LUFactorInversion/MethodD/MatrixInversion.lean` | `38F175C9ACE5FFA3` |
| `A` | `NumStabilityTest/Reorganization/W08/Canonical/Chapter14/Section03/LUFactorInversion/MethodD/MethodDLeftResidual.lean` | `747EDBC3CC8AE2E5` |
| `A` | `NumStabilityTest/Reorganization/W08/Canonical/Chapter14/Section03/LUFactorInversion/MethodD/MethodDProductDischarge.lean` | `0E81C27EE311BE65` |
| `A` | `NumStabilityTest/Reorganization/W08/Canonical/Chapter14/Section03/LUFactorInversion/MethodD/MethodDUpperCertificate.lean` | `FC6370470C051ED3` |
| `A` | `NumStabilityTest/Reorganization/W08/Canonical/Chapter14/Theorem05/ForwardError/GJEAsymptoticFamilies.lean` | `2CDDF723BE95FD18` |
| `A` | `NumStabilityTest/Reorganization/W08/Canonical/Chapter14/Theorem05/ForwardError/GJEFinalDivisionClosure.lean` | `EF16AB3D889EA765` |
| `A` | `NumStabilityTest/Reorganization/W08/Canonical/Chapter14/Theorem05/ForwardError/GJEPrintedEnvelopeClosure.lean` | `75D4A991AC6ECE0C` |
| `A` | `NumStabilityTest/Reorganization/W08/Canonical/Chapter14/Theorem05/ForwardError/GJETheorem145SourceClosure.lean` | `3AAFD902D67AF7D7` |
| `A` | `NumStabilityTest/Reorganization/W08/Canonical/Chapter14/Theorem05/ForwardError/GaussJordanQConstruction.lean` | `9F25873DAC33CAC7` |
| `A` | `NumStabilityTest/Reorganization/W08/Focused/GaussJordanReusableCore.lean` | `FF8F07EF0B2AED29` |
| `A` | `NumStabilityTest/Reorganization/W08/Focused/GaussJordanSourceAlgorithm04.lean` | `ECE9FC0F2EE669E4` |
| `A` | `NumStabilityTest/Reorganization/W08/Focused/MixedCh14AsymptoticFamilies.lean` | `78C8561440E35870` |
| `A` | `NumStabilityTest/Reorganization/W08/Focused/MixedCh14ProductErrorNotation.lean` | `F1438BC28BAC1771` |
| `A` | `NumStabilityTest/Reorganization/W08/Focused/MixedMatrixInversion.lean` | `59E8E3FA9DA222AB` |
| `A` | `NumStabilityTest/Reorganization/W08/Focused/ProtectedW02Surface.lean` | `D1E3455BAD255712` |
| `A` | `NumStabilityTest/Reorganization/W08/Focused/ProtectedW03Surface.lean` | `693CD4E9DBD3CFFD` |
| `A` | `NumStabilityTest/Reorganization/W08/Focused/RetainedPrivateClosure.lean` | `7E089152FD78F758` |
| `A` | `NumStabilityTest/Reorganization/W08/Focused/ReusableInversionApi.lean` | `5F6869E063179AB9` |
| `A` | `NumStabilityTest/Reorganization/W08/Focused/W11HistoricalCompatibility.lean` | `FE808BD9CBE805AE` |
| `A` | `NumStabilityTest/Reorganization/W08/OldPath/Ch14AsymptoticFamilies.lean` | `48DB86565621E658` |
| `A` | `NumStabilityTest/Reorganization/W08/OldPath/Ch14BlockTriInverse.lean` | `F62A7E98459B3D5C` |
| `A` | `NumStabilityTest/Reorganization/W08/OldPath/Ch14Cor146UniformInverseBridge.lean` | `F727D1965BF0CA74` |
| `A` | `NumStabilityTest/Reorganization/W08/OldPath/Ch14Cor147FinalDivisionFamilyClosure.lean` | `01A7E9F4E6F6E7DB` |
| `A` | `NumStabilityTest/Reorganization/W08/OldPath/Ch14Cor147SourceDomainConstructor.lean` | `0F68D9EDCA009E97` |
| `A` | `NumStabilityTest/Reorganization/W08/OldPath/Ch14Corollary146Closure.lean` | `0555497DBD9CD117` |
| `A` | `NumStabilityTest/Reorganization/W08/OldPath/Ch14Corollary146Concrete.lean` | `6F581E95AAD926B5` |
| `A` | `NumStabilityTest/Reorganization/W08/OldPath/Ch14Corollary146SourceClosure.lean` | `B0BEC89AF35F7D70` |
| `A` | `NumStabilityTest/Reorganization/W08/OldPath/Ch14Corollary147.lean` | `402F088EDF11A227` |
| `A` | `NumStabilityTest/Reorganization/W08/OldPath/Ch14Corollary147Closure.lean` | `C6C2319B00DB5CEE` |
| `A` | `NumStabilityTest/Reorganization/W08/OldPath/Ch14Corollary147Concrete.lean` | `AC1AE51BEB948A68` |
| `A` | `NumStabilityTest/Reorganization/W08/OldPath/Ch14Corollary147SourceClosure.lean` | `96C0BCFE72D9A3B0` |
| `A` | `NumStabilityTest/Reorganization/W08/OldPath/Ch14Corollary147WeakFamily.lean` | `844FA63C95F0F9C3` |
| `A` | `NumStabilityTest/Reorganization/W08/OldPath/Ch14ForwardErrorEndpoint.lean` | `559D9482F7F32465` |
| `A` | `NumStabilityTest/Reorganization/W08/OldPath/Ch14GJEActualDoolittleAdapter.lean` | `8BBC5B529AB252AF` |
| `A` | `NumStabilityTest/Reorganization/W08/OldPath/Ch14GJEAsymptoticFamilies.lean` | `F92FB303512DDF14` |
| `A` | `NumStabilityTest/Reorganization/W08/OldPath/Ch14GJEFinalDivisionClosure.lean` | `69865001F81071D4` |
| `A` | `NumStabilityTest/Reorganization/W08/OldPath/Ch14GJEOperationalBridge.lean` | `8019C734DD8BBF30` |
| `A` | `NumStabilityTest/Reorganization/W08/OldPath/Ch14GJEPrintedEnvelopeClosure.lean` | `8B1677D821810AB9` |
| `A` | `NumStabilityTest/Reorganization/W08/OldPath/Ch14GJESourceAccumulationBridge.lean` | `04C049033D9EB844` |
| `A` | `NumStabilityTest/Reorganization/W08/OldPath/Ch14GJETheorem145SourceClosure.lean` | `ABC11763D99D864F` |
| `A` | `NumStabilityTest/Reorganization/W08/OldPath/Ch14GaussJordanAccumulation.lean` | `3DD21DF7F71928CA` |
| `A` | `NumStabilityTest/Reorganization/W08/OldPath/Ch14GaussJordanQConstruction.lean` | `0F6F78C1C380815D` |
| `A` | `NumStabilityTest/Reorganization/W08/OldPath/Ch14GaussJordanSPDCorollary.lean` | `1D60D350E94FCAF0` |
| `A` | `NumStabilityTest/Reorganization/W08/OldPath/Ch14GaussJordanSourceClosure.lean` | `ABF506A2837AEB23` |
| `A` | `NumStabilityTest/Reorganization/W08/OldPath/Ch14GaussJordanStep.lean` | `E2741E910C6DB7C8` |
| `A` | `NumStabilityTest/Reorganization/W08/OldPath/Ch14Method1BWhole.lean` | `AA967504637EDE1A` |
| `A` | `NumStabilityTest/Reorganization/W08/OldPath/Ch14Method2C.lean` | `C3A80E3F3C4421FF` |
| `A` | `NumStabilityTest/Reorganization/W08/OldPath/Ch14Method2CWhole.lean` | `280E9840B30308B7` |
| `A` | `NumStabilityTest/Reorganization/W08/OldPath/Ch14Method2Loop.lean` | `4FD4E5A3F8229B9E` |
| `A` | `NumStabilityTest/Reorganization/W08/OldPath/Ch14MethodDLeftResidual.lean` | `29DCE4C67092CBEA` |
| `A` | `NumStabilityTest/Reorganization/W08/OldPath/Ch14MethodDProductDischarge.lean` | `EABB99DD80C02844` |
| `A` | `NumStabilityTest/Reorganization/W08/OldPath/Ch14MethodDUpperCertificate.lean` | `41A7D123B8E92DAB` |
| `A` | `NumStabilityTest/Reorganization/W08/OldPath/Ch14MethodsBC.lean` | `B39D84A69C975C69` |
| `A` | `NumStabilityTest/Reorganization/W08/OldPath/Ch14Problem142.lean` | `AE6B61CD87A859AB` |
| `A` | `NumStabilityTest/Reorganization/W08/OldPath/Ch14Problem142Families.lean` | `0FB96FDCDCFA42D8` |
| `A` | `NumStabilityTest/Reorganization/W08/OldPath/Ch14Problem142Method2B.lean` | `F566F17F7A6992A5` |
| `A` | `NumStabilityTest/Reorganization/W08/OldPath/Ch14ProductErrorNotation.lean` | `82597B55A374CEAE` |
| `A` | `NumStabilityTest/Reorganization/W08/OldPath/GaussJordan.lean` | `2E5FC819B1B52E6C` |
| `A` | `NumStabilityTest/Reorganization/W08/OldPath/GaussJordanPivoting.lean` | `BDF06D154EBB1901` |
| `A` | `NumStabilityTest/Reorganization/W08/OldPath/MatrixInversion.lean` | `34634DCB34744804` |
| `A` | `NumStabilityTest/Reorganization/W08/OldPath/MatrixInversionMethod2BInstance.lean` | `65D7A37A5CCE8042` |

## Added: W08 delivery evidence (10)

| status | path | sha256 (16) |
| --- | --- | --- |
| `A` | `docs/architecture/deliveries/W08/CHANGED_PATHS.md` | `(self)` |
| `A` | `docs/architecture/deliveries/W08/DECLARATION_ROUTES.tsv` | `32AB38EC44F15C7C` |
| `A` | `docs/architecture/deliveries/W08/DELIVERY.md` | `45411C386032DC17` |
| `A` | `docs/architecture/deliveries/W08/INTEGRATOR_REQUESTS.md` | `E22DF7C80FA6AF6D` |
| `A` | `docs/architecture/deliveries/W08/PRIVATE_CLOSURE.md` | `77BA3D07C159AE0D` |
| `A` | `docs/architecture/deliveries/W08/PRIVATE_CLOSURE.tsv` | `537F20B753C8877B` |
| `A` | `docs/architecture/deliveries/W08/PROJECTION.md` | `965DD9A79B374EA3` |
| `A` | `docs/architecture/deliveries/W08/RETENTION.tsv` | `26F7279C70747664` |
| `A` | `docs/architecture/deliveries/W08/ROUTING.md` | `932A7CCAF7AB1DA3` |
| `A` | `docs/architecture/deliveries/W08/TEST_MATRIX.tsv` | `02A6BB34E9255BE6` |
