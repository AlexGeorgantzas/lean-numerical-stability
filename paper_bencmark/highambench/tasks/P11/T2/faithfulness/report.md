# Faithfulness audit: P11-T2

- Classification: `faithful-stronger`
- Accepted as paper-faithful: `true`
- Adjudicated: `false`
- Target SHA-256: `7bbb70549d9ce5ddd178c1850b997292c0c3fe2c16ad20d070254c97db9bde49`
- Paper SHA-256: `72b7521848be07971a6721ea0356bb898c63e21b8ad3aa109fee8f41517284a5`

## Decision

The Lean proposition unfolds to the exact expanded identity on printed page 312, with correct dimensions, index shift, residual signs, transpose placement, and retained quadratic term. Its right-inverse hypothesis denotes the paper's ordinary inverse in the finite square real setting, and the expanded core entails the paper's unexpanded intermediate stage. The target omits CGS-P, full-rank, triangularity, and condition-number assumptions, but those assumptions only establish the exact residual relations and invertibility used by this selected equality. Every paper instance therefore instantiates Lean, while Lean also covers genuine nonvacuous tuples outside the paper's algorithmic domain. The result is accepted as faithful-stronger.

## Implications

- **Lean implies paper:** `yes`. For each paper prefix j, take Lean k.val = j - 1, A = A_j, dA = Delta A_j, Q = Q_j, R = R_j, and Rinv = R_j^{-1}. The paper's residual definition gives hQR, and its nonsingularity gives hInv. Unfolding the Lean core yields the paper's expanded equality and, by distributivity, the unexpanded intermediate equality.
- **Paper implies lean:** `no`. As a source-level quantified result, the paper only asserts the identity for coherent CGS-P prefixes of a full-rank input under its theorem context. It does not quantify over all arbitrary real matrices satisfying only hQR and hInv, including rank-deficient inputs and nontriangular inverse-bearing R.

## Findings

- **note / scope-generalization:** This validly broadens the theorem to additional nonvacuous tuples while retaining every paper instance, making it faithful-stronger rather than equivalent.
- **note / two-stage-equality:** No source conclusion is lost despite the absence of a duplicated syntactic equality conjunct.
- **note / inverse-witness:** A right inverse of a finite square real matrix is its unique two-sided ordinary inverse, so this formulation does not weaken or alter the inverse semantics.
- **note / algebraic-generalization:** The translation is stronger in applicability. It retains every paper instance, but the restricted paper statement does not imply the translated universal statement.
- **note / inlined-equality-stage:** There is no semantic loss because standard matrix expansion converts the translated middle expression exactly into the paper's unexpanded one.

## Semantic checklist

| Check | Direct | Round-trip |
|---|---|---|
| `S01` | `pass` | `pass` |
| `S02` | `pass` | `pass` |
| `S03` | `pass` | `fail` |
| `S04` | `pass` | `fail` |
| `S05` | `pass` | `pass` |
| `S06` | `pass` | `pass` |
| `S07` | `pass` | `pass` |
| `S08` | `pass` | `pass` |
| `S09` | `pass` | `not-applicable` |
| `S10` | `pass` | `pass` |
| `S11` | `pass` | `pass` |
| `S12` | `pass` | `pass` |
| `S13` | `pass` | `pass` |
| `S14` | `pass` | `pass` |
| `S15` | `pass` | `pass` |
| `S16` | `pass` | `pass` |

## Dependency coverage

- Blind translator covered `40` dependencies (`0` hash-reused meanings); unclear: `none`.
- Direct judge covered `40` dependencies (`0` hash-reused interpretations); failing or unclear: `none`.

## Remaining uncertainties

No remaining uncertainties were recorded.

## Audit artifacts

- `paper_bencmark/highambench/tasks/P11/T2/faithfulness/agent_outputs/blind_translation.json` (`edc1a42de1f35ff54c87814f1a8523f5c72083e2c852ad540dc155ca58cdba13`)
- `paper_bencmark/highambench/tasks/P11/T2/faithfulness/agent_outputs/direct_judge.json` (`99ec09326907d49746e67d200e5611fad24133306ed28920a899c14e18b81bd4`)
- `paper_bencmark/highambench/tasks/P11/T2/faithfulness/agent_outputs/roundtrip_judge.json` (`b5d71546960f06329a50888fb8abd5f4cf1c51f6663fd03b51f2b12d0d9c392a`)
- `paper_bencmark/highambench/tasks/P11/T2/faithfulness/agent_outputs/source_contract.json` (`cd246aa8578e2e2edf1002724dad959295891de8aa78e71e088f08ae9bc1cff1`)
- `paper_bencmark/highambench/tasks/P11/T2/faithfulness/decision.json` (`3ae4befa6720ea1e4a31bbd145483a75cb7685e7b1dd8a198ca36e3af0e25d33`)
- `paper_bencmark/highambench/tasks/P11/T2/faithfulness/history/20260815T075333Z/agent_outputs/adjudicator.json` (`58027bc895e31027cd9223258fb7f5324c820f4e2491299358f3697631188772`)
- `paper_bencmark/highambench/tasks/P11/T2/faithfulness/history/20260815T075333Z/agent_outputs/blind_translation.json` (`ccbd9b3259835e43f8344955168694cb89770144127cdabfed421d2ab605642d`)
- `paper_bencmark/highambench/tasks/P11/T2/faithfulness/history/20260815T075333Z/agent_outputs/direct_judge.json` (`40e1193f056d775ab0c8245c13c5dcd4af7590b9fd0e7f0014eb75e64798efc8`)
- `paper_bencmark/highambench/tasks/P11/T2/faithfulness/history/20260815T075333Z/agent_outputs/roundtrip_judge.json` (`d1babda4520b70266e7bf79fa4d6448bea29e83d56c4fffdbe9ca87b311b5772`)
- `paper_bencmark/highambench/tasks/P11/T2/faithfulness/history/20260815T075333Z/agent_outputs/source_contract.json` (`3eb4845c275c93ac76ad1216225513ce38b2edb9a1fc467dcab505544414fc20`)
- `paper_bencmark/highambench/tasks/P11/T2/faithfulness/history/20260815T075333Z/decision.json` (`271595e9996c98e396b28bbb4ba637a51c3483b929bc95a2fb932e5aa3e1c712`)
- `paper_bencmark/highambench/tasks/P11/T2/faithfulness/history/20260815T075333Z/inputs/blind_dossier.md` (`8caf1fe2aa2c0287b9c6c1380aa53b2b3af6e367a3fd1f06dc44d39befd6bd20`)
- `paper_bencmark/highambench/tasks/P11/T2/faithfulness/history/20260815T075333Z/inputs/declaration_dossier.md` (`9cf6428bd30c41300100c8cd58bda8d4b2c9c49a42fc1c8130f8cdf2dc80b21f`)
- `paper_bencmark/highambench/tasks/P11/T2/faithfulness/history/20260815T075333Z/inputs/source_locator.json` (`d852b170574fb224f1934e9143f7623c0f0ed210cd7cc6730b4373e98cdf97e7`)
- `paper_bencmark/highambench/tasks/P11/T2/faithfulness/inputs/blind_dependency_inventory.json` (`903d04bb2e9fa5b3365f816daaa45dce6ec0501b14cef7d187cdac20b5dc3436`)
- `paper_bencmark/highambench/tasks/P11/T2/faithfulness/inputs/blind_dossier.md` (`5ecb6da2fa5d468c5a4d59ae0c8d7176d02e698cd7147ddaeaf1feccf6d0a952`)
- `paper_bencmark/highambench/tasks/P11/T2/faithfulness/inputs/blind_review_packet.md` (`5ecb6da2fa5d468c5a4d59ae0c8d7176d02e698cd7147ddaeaf1feccf6d0a952`)
- `paper_bencmark/highambench/tasks/P11/T2/faithfulness/inputs/declaration_dossier.md` (`78ec84324c6343c5a685e4957f48fb5d7eff2014b1035a0f6d57afa19c12694b`)
- `paper_bencmark/highambench/tasks/P11/T2/faithfulness/inputs/dependency_inventory.json` (`ab7e4424bd25f0fd21823f77f9b4f3d665fa73cc4abfbe5104b33f1499136162`)
- `paper_bencmark/highambench/tasks/P11/T2/faithfulness/inputs/direct_review_packet.md` (`b196daad46844278307602065300d4db47bbc6775e9f85e9f1d19c8e400b2332`)
- `paper_bencmark/highambench/tasks/P11/T2/faithfulness/inputs/source_locator.json` (`126668b06d3bb39ef557f1e5b79156f365840b7a474ce5a90bb4023e0eb6bd00`)
