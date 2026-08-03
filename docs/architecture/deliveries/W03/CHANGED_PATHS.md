# W03 changed-path evidence

Generated from the exact base-to-delivery diff:

```console
git diff --cached --name-status b56f609f3bf66b5d7d0b677567cce82fee0c275b
```

`--cached` is required: a plain `git diff` reports only tracked changes and would
omit every newly added canonical module, test and evidence file.

**181 changed paths.** Every one is classified below.

| classification | paths |
| --- | ---: |
| owned historical source | 26 |
| authorized destination | 61 |
| W03 test | 87 |
| W03 delivery evidence | 7 |
| UNCLASSIFIED | 0 |

**Forbidden paths touched: 0.** Zero. `tiers.json`, `layout-exceptions.json`, the family, chapter and global aggregates, `NumStabilityTest.lean`, the phase records, CI files, `tools/architecture/`, `lakefile.toml` and `lean-toolchain` are all unmodified.
**Unclassified paths: 0.** Zero.

## Modified: the 26 owned historical paths (26)

| status | path | sha256 (16) |
| --- | --- | --- |
| `M` | `NumStability/Algorithms/Ch10ActualSourceClosure.lean` | `F067B5D737B17742` |
| `M` | `NumStability/Algorithms/Ch10Ch14Lemma66Op2Bridge.lean` | `9E8C4EBBBA03585E` |
| `M` | `NumStability/Algorithms/Ch10ComplexPositiveDefiniteSourceClosure.lean` | `303CF571FE564598` |
| `M` | `NumStability/Algorithms/Ch10KahanSharpness.lean` | `A886CF94D543ABFF` |
| `M` | `NumStability/Algorithms/Ch10KahanSharpnessSource.lean` | `92CEFFCA0645CB0A` |
| `M` | `NumStability/Algorithms/Ch10Lemma1011Source.lean` | `D2AE212E00C9243D` |
| `M` | `NumStability/Algorithms/Ch10PivotedPSDSourceClosure.lean` | `3989946600F32C31` |
| `M` | `NumStability/Algorithms/Ch10Theorem107FailureVacuity.lean` | `47A1833A3646693D` |
| `M` | `NumStability/Algorithms/Ch10Theorem108Componentwise.lean` | `D9E019E2BBF3943F` |
| `M` | `NumStability/Algorithms/Ch10Theorem108Source.lean` | `B68DDD31C4E29D77` |
| `M` | `NumStability/Algorithms/Cholesky/CholeskyDemmel.lean` | `087BDE6C3485397D` |
| `M` | `NumStability/Algorithms/Cholesky/CholeskyFl.lean` | `ED8DFC5C267DF0CD` |
| `M` | `NumStability/Algorithms/Cholesky/CholeskyIndefinite.lean` | `9CA5A580F2EC21A9` |
| `M` | `NumStability/Algorithms/Cholesky/CholeskyNonsym.lean` | `BACC5125C113504F` |
| `M` | `NumStability/Algorithms/Cholesky/CholeskyPSD.lean` | `A3E777BF369051B3` |
| `M` | `NumStability/Algorithms/Cholesky/CholeskyPerturbation.lean` | `A095A0ED7203103A` |
| `M` | `NumStability/Algorithms/Cholesky/CholeskySolve.lean` | `CC281F8E8330C4F8` |
| `M` | `NumStability/Algorithms/Cholesky/CholeskySpec.lean` | `E69A23FCFDBCE344` |
| `M` | `NumStability/Algorithms/Cholesky/Higham1014Equation1022.lean` | `3172D677CFFDE776` |
| `M` | `NumStability/Algorithms/Cholesky/Higham1014SourceError.lean` | `234BFBF4EEDC2E1B` |
| `M` | `NumStability/Algorithms/Cholesky/Higham1014SourceSuccess.lean` | `D9DF287FC3C6001F` |
| `M` | `NumStability/Algorithms/Cholesky/Higham1029Source.lean` | `5DBC8230B9A1A8B0` |
| `M` | `NumStability/Algorithms/Cholesky/Higham10Problem10_3.lean` | `D0310BE67F0ECC23` |
| `M` | `NumStability/Algorithms/Cholesky/HighamMathiasFirstBreakdown.lean` | `AAB2F8984A18FB37` |
| `M` | `NumStability/Algorithms/Cholesky/HighamMathiasSource.lean` | `1E443DA3938671B5` |
| `M` | `NumStability/Algorithms/HighamChapter10.lean` | `3390EF5538B5F335` |

## Added: authorized canonical destinations (61)

| status | path | sha256 (16) |
| --- | --- | --- |
| `A` | `NumStability/Algorithms/LinearSystems/Cholesky/ErrorAnalysis/Certificates.lean` | `F2A9A827A1A2E9AC` |
| `A` | `NumStability/Algorithms/LinearSystems/Cholesky/ErrorAnalysis/Demmel.lean` | `0401DD37AF844D3D` |
| `A` | `NumStability/Algorithms/LinearSystems/Cholesky/Factorization/Spec.lean` | `D50A9D5CEA353B61` |
| `A` | `NumStability/Algorithms/LinearSystems/Cholesky/Perturbation/Basic.lean` | `2E477972655AB852` |
| `A` | `NumStability/Algorithms/LinearSystems/Cholesky/PositiveSemidefinite/Basic.lean` | `ABAE36E0E76DD2E4` |
| `A` | `NumStability/Algorithms/LinearSystems/Cholesky/PositiveSemidefinite/KahanMatrix.lean` | `526A73D50A9DE761` |
| `A` | `NumStability/Algorithms/LinearSystems/Cholesky/PositiveSemidefinite/ScaledStage.lean` | `88E409471ADC8D21` |
| `A` | `NumStability/Algorithms/LinearSystems/Cholesky/RoundedFactorization/Basic.lean` | `FC96C89929968091` |
| `A` | `NumStability/Algorithms/LinearSystems/Cholesky/Solve/Basic.lean` | `361F7B0B83AE272D` |
| `A` | `NumStability/Algorithms/LinearSystems/LU/NonsymmetricPositiveDefinite/Basic.lean` | `69BB68DE66C5C60E` |
| `A` | `NumStability/Algorithms/LinearSystems/SymmetricIndefinite/ErrorAnalysis/BlockLDLT.lean` | `FD6A4DA6ADA3D6D4` |
| `A` | `NumStability/Algorithms/LinearSystems/SymmetricIndefinite/ErrorAnalysis/BlockLDLTStep.lean` | `FDDD2D5674825F36` |
| `A` | `NumStability/Algorithms/LinearSystems/SymmetricIndefinite/ErrorAnalysis/Predicates.lean` | `06DF5ED975F75B76` |
| `A` | `NumStability/Algorithms/LinearSystems/SymmetricIndefinite/ErrorAnalysis/SkewSymmetric.lean` | `B3A5CE770A3E33C1` |
| `A` | `NumStability/Algorithms/LinearSystems/SymmetricIndefinite/Pivoting/Basic.lean` | `B0DBA71FE02D0211` |
| `A` | `NumStability/Algorithms/LinearSystems/SymmetricIndefinite/Pivoting/Tridiagonal.lean` | `F4C292B4826F8BE0` |
| `A` | `NumStability/Analysis/MatrixNorms/EntrywiseAbsolute/Basic.lean` | `3D2EF5CF8FD82854` |
| `A` | `NumStability/Analysis/MatrixNorms/SpectralExtrema/Basic.lean` | `8A53BE9F5456AC4B` |
| `A` | `NumStability/Source/Higham/Chapter06/Lemma06/OperatorTwoNormBound/Bridge.lean` | `3F3262D313A2515B` |
| `A` | `NumStability/Source/Higham/Chapter10/Equation07/AbsoluteFactorNorm/Bridge.lean` | `762B43289494DD7F` |
| `A` | `NumStability/Source/Higham/Chapter10/Equation07/AbsoluteFactorNorm/Endpoints.lean` | `94E4C7BEB008B99F` |
| `A` | `NumStability/Source/Higham/Chapter10/Equation29/Mathias/Endpoints.lean` | `B17BE5DA3DC7A319` |
| `A` | `NumStability/Source/Higham/Chapter10/Equation29/Mathias/FirstBreakdown.lean` | `0FAA59D418D6A055` |
| `A` | `NumStability/Source/Higham/Chapter10/Equation29/Mathias/SourceIngredients.lean` | `553AB119F78218E3` |
| `A` | `NumStability/Source/Higham/Chapter10/Equation30/ComplexPositiveDefinite/Endpoints.lean` | `775522AE13F70A27` |
| `A` | `NumStability/Source/Higham/Chapter10/Equation30/ComplexPositiveDefinite/SourceClosure.lean` | `8925A426E71975A3` |
| `A` | `NumStability/Source/Higham/Chapter10/Lemma11/PivotSequenceStability/Endpoints.lean` | `E07AD730003E815D` |
| `A` | `NumStability/Source/Higham/Chapter10/Lemma11/PivotSequenceStability/SourceClosure.lean` | `0B8C3A841D0CF766` |
| `A` | `NumStability/Source/Higham/Chapter10/Lemma13/KahanSharpness/CompletePivotingBound.lean` | `42DE89879CA83942` |
| `A` | `NumStability/Source/Higham/Chapter10/Lemma13/KahanSharpness/Endpoints.lean` | `60527A8F4BCCF33D` |
| `A` | `NumStability/Source/Higham/Chapter10/Lemma13/KahanSharpness/GramFamily.lean` | `E3506BD7D6D0336C` |
| `A` | `NumStability/Source/Higham/Chapter10/Lemma13/KahanSharpness/Limit.lean` | `EA19C2CE18015B32` |
| `A` | `NumStability/Source/Higham/Chapter10/Problem01/PositiveSemidefiniteEntries/Basic.lean` | `B7266DDF57DB39E4` |
| `A` | `NumStability/Source/Higham/Chapter10/Problem03/ArbitraryEvaluationOrder/Basic.lean` | `8AA2885D607C1EF9` |
| `A` | `NumStability/Source/Higham/Chapter10/Problem04/UnpivotedGrowth/Basic.lean` | `16B165BB3EA4DF6E` |
| `A` | `NumStability/Source/Higham/Chapter10/Problem08/LeadingMinorsCounterexample/Basic.lean` | `7ED6EAB2AB3B5061` |
| `A` | `NumStability/Source/Higham/Chapter10/Section01/Factorization/Basic.lean` | `0746350C0B1EAB47` |
| `A` | `NumStability/Source/Higham/Chapter10/Section02/ErrorAnalysis/Basic.lean` | `8D11844285DB99D1` |
| `A` | `NumStability/Source/Higham/Chapter10/Section03/PositiveSemidefinite/Endpoints.lean` | `861FADD635C5FC0D` |
| `A` | `NumStability/Source/Higham/Chapter10/Section03/PositiveSemidefinite/Existence.lean` | `9909527CEF1A765D` |
| `A` | `NumStability/Source/Higham/Chapter10/Section03/PositiveSemidefinite/SchurComplement.lean` | `BADD94E5FFA99BA2` |
| `A` | `NumStability/Source/Higham/Chapter10/Section03/PositiveSemidefinite/Termination.lean` | `F7FA41C61FD94F84` |
| `A` | `NumStability/Source/Higham/Chapter10/Section03/PositiveSemidefinite/WNormBound.lean` | `3045BCBE870D6101` |
| `A` | `NumStability/Source/Higham/Chapter10/Section04/PositiveDefiniteSymmetricPart/Endpoints.lean` | `6199718DE0A9EA79` |
| `A` | `NumStability/Source/Higham/Chapter10/Section04/PositiveDefiniteSymmetricPart/Equation29.lean` | `15E1C1B80427C081` |
| `A` | `NumStability/Source/Higham/Chapter10/Theorem06/RoundedCholesky/ActualClosure.lean` | `28916F306D98990D` |
| `A` | `NumStability/Source/Higham/Chapter10/Theorem06/RoundedCholesky/Endpoints.lean` | `5594B20A53C64656` |
| `A` | `NumStability/Source/Higham/Chapter10/Theorem07/FailureVacuity/Endpoints.lean` | `9DD7ADA3A80C1C9E` |
| `A` | `NumStability/Source/Higham/Chapter10/Theorem07/FailureVacuity/Vacuity.lean` | `9404E435E3D8577C` |
| `A` | `NumStability/Source/Higham/Chapter10/Theorem08/ComponentwisePerturbation/Endpoints.lean` | `280F9B74280A2718` |
| `A` | `NumStability/Source/Higham/Chapter10/Theorem08/ComponentwisePerturbation/Resolvent.lean` | `9B2B926E2C513B39` |
| `A` | `NumStability/Source/Higham/Chapter10/Theorem08/NormwiseDiscrepancy/Endpoints.lean` | `D7DDDB139C6D71EF` |
| `A` | `NumStability/Source/Higham/Chapter10/Theorem08/NormwiseDiscrepancy/LiteralSource.lean` | `672D4761B89CCA86` |
| `A` | `NumStability/Source/Higham/Chapter10/Theorem14/CompletePivotedPSD/ActualRun.lean` | `16F80B216B2ACA07` |
| `A` | `NumStability/Source/Higham/Chapter10/Theorem14/CompletePivotedPSD/Endpoints.lean` | `AC4FA77BE0DE8C3F` |
| `A` | `NumStability/Source/Higham/Chapter10/Theorem14/CompletePivotedPSD/Equation22.lean` | `CB5ED122DF685F7A` |
| `A` | `NumStability/Source/Higham/Chapter10/Theorem14/CompletePivotedPSD/PsdErrorAnalysis.lean` | `3B19C305EECF6F01` |
| `A` | `NumStability/Source/Higham/Chapter10/Theorem14/CompletePivotedPSD/SourceError.lean` | `0A5997DF57CDD742` |
| `A` | `NumStability/Source/Higham/Chapter10/Theorem14/CompletePivotedPSD/SourceSuccess.lean` | `F2A36CAC9069A601` |
| `A` | `NumStability/Source/Higham/Chapter11/Theorem07/TridiagonalTwoByTwoResidual/Basic.lean` | `6DA5B155D705BB5A` |
| `A` | `NumStability/Source/Higham/Chapter14/Section03/ResidualOperatorTwoNorm/Bridge.lean` | `1C918E85209A8943` |

## Added: W03 focused tests (87)

| status | path | sha256 (16) |
| --- | --- | --- |
| `A` | `NumStabilityTest/Reorganization/W03/Canonical/Algorithms/LinearSystems/Cholesky/ErrorAnalysis/Certificates.lean` | `A63F4324E90E2155` |
| `A` | `NumStabilityTest/Reorganization/W03/Canonical/Algorithms/LinearSystems/Cholesky/ErrorAnalysis/Demmel.lean` | `F73BB80FB7346D45` |
| `A` | `NumStabilityTest/Reorganization/W03/Canonical/Algorithms/LinearSystems/Cholesky/Factorization/Spec.lean` | `85DF1E2AABFEA8C3` |
| `A` | `NumStabilityTest/Reorganization/W03/Canonical/Algorithms/LinearSystems/Cholesky/Perturbation/Basic.lean` | `5EA7FE9E594064ED` |
| `A` | `NumStabilityTest/Reorganization/W03/Canonical/Algorithms/LinearSystems/Cholesky/PositiveSemidefinite/Basic.lean` | `9C9226A041D9F4FB` |
| `A` | `NumStabilityTest/Reorganization/W03/Canonical/Algorithms/LinearSystems/Cholesky/PositiveSemidefinite/KahanMatrix.lean` | `7449C92B63B2273C` |
| `A` | `NumStabilityTest/Reorganization/W03/Canonical/Algorithms/LinearSystems/Cholesky/PositiveSemidefinite/ScaledStage.lean` | `041B0BD209A51EEF` |
| `A` | `NumStabilityTest/Reorganization/W03/Canonical/Algorithms/LinearSystems/Cholesky/RoundedFactorization/Basic.lean` | `BD52D5E2FB4F3013` |
| `A` | `NumStabilityTest/Reorganization/W03/Canonical/Algorithms/LinearSystems/Cholesky/Solve/Basic.lean` | `F836FFA4DD39C863` |
| `A` | `NumStabilityTest/Reorganization/W03/Canonical/Algorithms/LinearSystems/LU/NonsymmetricPositiveDefinite/Basic.lean` | `7BB067083727C223` |
| `A` | `NumStabilityTest/Reorganization/W03/Canonical/Algorithms/LinearSystems/SymmetricIndefinite/ErrorAnalysis/BlockLDLT.lean` | `706DC824A5BC7366` |
| `A` | `NumStabilityTest/Reorganization/W03/Canonical/Algorithms/LinearSystems/SymmetricIndefinite/ErrorAnalysis/BlockLDLTStep.lean` | `6409368FE3A3C925` |
| `A` | `NumStabilityTest/Reorganization/W03/Canonical/Algorithms/LinearSystems/SymmetricIndefinite/ErrorAnalysis/Predicates.lean` | `393B3E1805D995F4` |
| `A` | `NumStabilityTest/Reorganization/W03/Canonical/Algorithms/LinearSystems/SymmetricIndefinite/ErrorAnalysis/SkewSymmetric.lean` | `58AD9FCC8CC917C1` |
| `A` | `NumStabilityTest/Reorganization/W03/Canonical/Algorithms/LinearSystems/SymmetricIndefinite/Pivoting/Basic.lean` | `4CA6C18CF4A44028` |
| `A` | `NumStabilityTest/Reorganization/W03/Canonical/Algorithms/LinearSystems/SymmetricIndefinite/Pivoting/Tridiagonal.lean` | `D9CF4BD561C57AC5` |
| `A` | `NumStabilityTest/Reorganization/W03/Canonical/Chapter06/Lemma06/OperatorTwoNormBound/Bridge.lean` | `10F3425B8084E866` |
| `A` | `NumStabilityTest/Reorganization/W03/Canonical/Chapter10/Equation07/AbsoluteFactorNorm/Bridge.lean` | `50A2DC46BA068CF0` |
| `A` | `NumStabilityTest/Reorganization/W03/Canonical/Chapter10/Equation07/AbsoluteFactorNorm/Endpoints.lean` | `5D1308D61D4BB493` |
| `A` | `NumStabilityTest/Reorganization/W03/Canonical/Chapter10/Equation29/Mathias/Endpoints.lean` | `D56ABD93AD0AE575` |
| `A` | `NumStabilityTest/Reorganization/W03/Canonical/Chapter10/Equation29/Mathias/FirstBreakdown.lean` | `F8392D8912E95791` |
| `A` | `NumStabilityTest/Reorganization/W03/Canonical/Chapter10/Equation29/Mathias/SourceIngredients.lean` | `4BA5DD045BA1DFB1` |
| `A` | `NumStabilityTest/Reorganization/W03/Canonical/Chapter10/Equation30/ComplexPositiveDefinite/Endpoints.lean` | `DEE8FB45138F2037` |
| `A` | `NumStabilityTest/Reorganization/W03/Canonical/Chapter10/Equation30/ComplexPositiveDefinite/SourceClosure.lean` | `F212D18D672DD764` |
| `A` | `NumStabilityTest/Reorganization/W03/Canonical/Chapter10/Lemma11/PivotSequenceStability/Endpoints.lean` | `1C77E35BA67124CF` |
| `A` | `NumStabilityTest/Reorganization/W03/Canonical/Chapter10/Lemma11/PivotSequenceStability/SourceClosure.lean` | `9AB6AAD1FF73124D` |
| `A` | `NumStabilityTest/Reorganization/W03/Canonical/Chapter10/Lemma13/KahanSharpness/CompletePivotingBound.lean` | `3DB57621C42BA40C` |
| `A` | `NumStabilityTest/Reorganization/W03/Canonical/Chapter10/Lemma13/KahanSharpness/Endpoints.lean` | `A3714A96CDE15C7F` |
| `A` | `NumStabilityTest/Reorganization/W03/Canonical/Chapter10/Lemma13/KahanSharpness/GramFamily.lean` | `E192450F098FEA7F` |
| `A` | `NumStabilityTest/Reorganization/W03/Canonical/Chapter10/Lemma13/KahanSharpness/Limit.lean` | `9A5301BDEC65260C` |
| `A` | `NumStabilityTest/Reorganization/W03/Canonical/Chapter10/Problem01/PositiveSemidefiniteEntries/Basic.lean` | `638618E080D29D86` |
| `A` | `NumStabilityTest/Reorganization/W03/Canonical/Chapter10/Problem03/ArbitraryEvaluationOrder/Basic.lean` | `26CAB27F3EBAEA70` |
| `A` | `NumStabilityTest/Reorganization/W03/Canonical/Chapter10/Problem04/UnpivotedGrowth/Basic.lean` | `145AA5244B8DE7CB` |
| `A` | `NumStabilityTest/Reorganization/W03/Canonical/Chapter10/Problem08/LeadingMinorsCounterexample/Basic.lean` | `A0E53AF9046A97F9` |
| `A` | `NumStabilityTest/Reorganization/W03/Canonical/Chapter10/Section01/Factorization/Basic.lean` | `65253C3957183345` |
| `A` | `NumStabilityTest/Reorganization/W03/Canonical/Chapter10/Section02/ErrorAnalysis/Basic.lean` | `CA30FA4C6835F1A7` |
| `A` | `NumStabilityTest/Reorganization/W03/Canonical/Chapter10/Section03/PositiveSemidefinite/Endpoints.lean` | `EA03FE3B069B170E` |
| `A` | `NumStabilityTest/Reorganization/W03/Canonical/Chapter10/Section03/PositiveSemidefinite/Existence.lean` | `4D4F3F4CE96ED163` |
| `A` | `NumStabilityTest/Reorganization/W03/Canonical/Chapter10/Section03/PositiveSemidefinite/SchurComplement.lean` | `6303DE5F73973B9D` |
| `A` | `NumStabilityTest/Reorganization/W03/Canonical/Chapter10/Section03/PositiveSemidefinite/Termination.lean` | `42ACDE8F0E72BE9C` |
| `A` | `NumStabilityTest/Reorganization/W03/Canonical/Chapter10/Section03/PositiveSemidefinite/WNormBound.lean` | `FFAD9C1F204CBEFA` |
| `A` | `NumStabilityTest/Reorganization/W03/Canonical/Chapter10/Section04/PositiveDefiniteSymmetricPart/Endpoints.lean` | `4F9F2E7754668FAD` |
| `A` | `NumStabilityTest/Reorganization/W03/Canonical/Chapter10/Section04/PositiveDefiniteSymmetricPart/Equation29.lean` | `19C50EFCFE0D7BFF` |
| `A` | `NumStabilityTest/Reorganization/W03/Canonical/Chapter10/Theorem06/RoundedCholesky/ActualClosure.lean` | `4ED5DE0CA32D4B62` |
| `A` | `NumStabilityTest/Reorganization/W03/Canonical/Chapter10/Theorem06/RoundedCholesky/Endpoints.lean` | `FAA0FB57635F66E0` |
| `A` | `NumStabilityTest/Reorganization/W03/Canonical/Chapter10/Theorem07/FailureVacuity/Endpoints.lean` | `5F75967CECD54BB5` |
| `A` | `NumStabilityTest/Reorganization/W03/Canonical/Chapter10/Theorem07/FailureVacuity/Vacuity.lean` | `7E9199D8A6FD9FB6` |
| `A` | `NumStabilityTest/Reorganization/W03/Canonical/Chapter10/Theorem08/ComponentwisePerturbation/Endpoints.lean` | `E76A7D820726E9B5` |
| `A` | `NumStabilityTest/Reorganization/W03/Canonical/Chapter10/Theorem08/ComponentwisePerturbation/Resolvent.lean` | `BE0C8D0285A5766B` |
| `A` | `NumStabilityTest/Reorganization/W03/Canonical/Chapter10/Theorem08/NormwiseDiscrepancy/Endpoints.lean` | `644B97BA4B13DB07` |
| `A` | `NumStabilityTest/Reorganization/W03/Canonical/Chapter10/Theorem08/NormwiseDiscrepancy/LiteralSource.lean` | `83BF077A4DDE65AB` |
| `A` | `NumStabilityTest/Reorganization/W03/Canonical/Chapter10/Theorem14/CompletePivotedPSD/ActualRun.lean` | `5305FEF796DAA63B` |
| `A` | `NumStabilityTest/Reorganization/W03/Canonical/Chapter10/Theorem14/CompletePivotedPSD/Endpoints.lean` | `4EA276EAA99005E6` |
| `A` | `NumStabilityTest/Reorganization/W03/Canonical/Chapter10/Theorem14/CompletePivotedPSD/Equation22.lean` | `728AA5745C82BA09` |
| `A` | `NumStabilityTest/Reorganization/W03/Canonical/Chapter10/Theorem14/CompletePivotedPSD/PsdErrorAnalysis.lean` | `32FF3E23C837FD3A` |
| `A` | `NumStabilityTest/Reorganization/W03/Canonical/Chapter10/Theorem14/CompletePivotedPSD/SourceError.lean` | `1A08DEFA4E22B514` |
| `A` | `NumStabilityTest/Reorganization/W03/Canonical/Chapter10/Theorem14/CompletePivotedPSD/SourceSuccess.lean` | `314BE6753FAD0987` |
| `A` | `NumStabilityTest/Reorganization/W03/Canonical/Chapter11/Theorem07/TridiagonalTwoByTwoResidual/Basic.lean` | `7A6E879208E2825F` |
| `A` | `NumStabilityTest/Reorganization/W03/Canonical/Chapter14/Section03/ResidualOperatorTwoNorm/Bridge.lean` | `9FDD5271EC1B71AC` |
| `A` | `NumStabilityTest/Reorganization/W03/Canonical/NumStability/Analysis/MatrixNorms/EntrywiseAbsolute/Basic.lean` | `0D62155A26749702` |
| `A` | `NumStabilityTest/Reorganization/W03/Canonical/NumStability/Analysis/MatrixNorms/SpectralExtrema/Basic.lean` | `3785FEAD63262145` |
| `A` | `NumStabilityTest/Reorganization/W03/Compatibility/Ch10ActualSourceClosure.lean` | `42EC31E43C5A730E` |
| `A` | `NumStabilityTest/Reorganization/W03/Compatibility/Ch10Ch14Lemma66Op2Bridge.lean` | `45C7C82D7A91E119` |
| `A` | `NumStabilityTest/Reorganization/W03/Compatibility/Ch10ComplexPositiveDefiniteSourceClosure.lean` | `BC03BAF0FCB7DD15` |
| `A` | `NumStabilityTest/Reorganization/W03/Compatibility/Ch10KahanSharpness.lean` | `C22D09C81B5F29A1` |
| `A` | `NumStabilityTest/Reorganization/W03/Compatibility/Ch10KahanSharpnessSource.lean` | `871D2B1D0461486A` |
| `A` | `NumStabilityTest/Reorganization/W03/Compatibility/Ch10Lemma1011Source.lean` | `E64DFAF5F65C7CDE` |
| `A` | `NumStabilityTest/Reorganization/W03/Compatibility/Ch10PivotedPSDSourceClosure.lean` | `7FC9440293B1DB4B` |
| `A` | `NumStabilityTest/Reorganization/W03/Compatibility/Ch10Theorem107FailureVacuity.lean` | `8D899746A8B3489D` |
| `A` | `NumStabilityTest/Reorganization/W03/Compatibility/Ch10Theorem108Componentwise.lean` | `27CC22909B373551` |
| `A` | `NumStabilityTest/Reorganization/W03/Compatibility/Ch10Theorem108Source.lean` | `766BF7E15969A6C0` |
| `A` | `NumStabilityTest/Reorganization/W03/Compatibility/CholeskyDemmel.lean` | `B8B7ADD2482F6AB0` |
| `A` | `NumStabilityTest/Reorganization/W03/Compatibility/CholeskyFl.lean` | `4CEEF50ACCEBC775` |
| `A` | `NumStabilityTest/Reorganization/W03/Compatibility/CholeskyIndefinite.lean` | `6E525989D2FB8F4C` |
| `A` | `NumStabilityTest/Reorganization/W03/Compatibility/CholeskyNonsym.lean` | `9DED2D1B71BDED79` |
| `A` | `NumStabilityTest/Reorganization/W03/Compatibility/CholeskyPSD.lean` | `CA32EB4822D6BF0D` |
| `A` | `NumStabilityTest/Reorganization/W03/Compatibility/CholeskyPerturbation.lean` | `A04C514DFDA2A0B6` |
| `A` | `NumStabilityTest/Reorganization/W03/Compatibility/CholeskySolve.lean` | `8A6E630DC9F7D8CA` |
| `A` | `NumStabilityTest/Reorganization/W03/Compatibility/CholeskySpec.lean` | `66A7D223F4F74414` |
| `A` | `NumStabilityTest/Reorganization/W03/Compatibility/Higham1014Equation1022.lean` | `BD58D608028E3CF9` |
| `A` | `NumStabilityTest/Reorganization/W03/Compatibility/Higham1014SourceError.lean` | `42BB9771BE12933B` |
| `A` | `NumStabilityTest/Reorganization/W03/Compatibility/Higham1014SourceSuccess.lean` | `495D5A02F1B37B57` |
| `A` | `NumStabilityTest/Reorganization/W03/Compatibility/Higham1029Source.lean` | `E05AC6D5E498D862` |
| `A` | `NumStabilityTest/Reorganization/W03/Compatibility/Higham10Problem10_3.lean` | `302CC3CB88C11E8B` |
| `A` | `NumStabilityTest/Reorganization/W03/Compatibility/HighamChapter10.lean` | `802CD4CB1496C323` |
| `A` | `NumStabilityTest/Reorganization/W03/Compatibility/HighamMathiasFirstBreakdown.lean` | `3FF217C7B70D3911` |
| `A` | `NumStabilityTest/Reorganization/W03/Compatibility/HighamMathiasSource.lean` | `31FF8F05EE0B43F0` |

## Added: W03 delivery evidence (7)

| status | path | sha256 (16) |
| --- | --- | --- |
| `A` | `docs/architecture/deliveries/W03/CHANGED_PATHS.md` | `(self)` |
| `A` | `docs/architecture/deliveries/W03/DELIVERY.md` | `3E6DFF1FECC6314F` |
| `A` | `docs/architecture/deliveries/W03/INTEGRATOR_REQUESTS.md` | `43D0B3CEA36EEDF6` |
| `A` | `docs/architecture/deliveries/W03/PROJECTION.md` | `20B9B23E7B036510` |
| `A` | `docs/architecture/deliveries/W03/RETENTION.tsv` | `315E5A3620520CDA` |
| `A` | `docs/architecture/deliveries/W03/ROUTING.md` | `3AD11BFB9C86C27E` |
| `A` | `docs/architecture/deliveries/W03/ROUTING.tsv` | `41F685D95EB4FB28` |
