# Faithfulness audit: P13-T3

- Classification: `faithful-stronger`
- Accepted as paper-faithful: `true`
- Adjudicated: `false`
- Target SHA-256: `9801364ece3ddef1c99746e35ce640310ab368a65807caaec587dafc53903042`
- Paper SHA-256: `9ebf8adb699f96c82ccbb153dd6ca592c64475a8bc3e0703a50cb659b012c520`

## Decision

The declaration faithfully models the direct weights, proper barycentric execution, exact and computed values, both condition-number terms, operation counts, relative forward error, and O(u^2) behavior of Theorem 4.1. Its off-node and nonzero assumptions make the displayed formulas defined and are satisfiable. The proposition is not equivalent to the printed theorem because it extends the ideal counter model to arbitrary real inputs and adds an exact finite envelope, explicit remainder, and a concrete one-third first-order sharpness guarantee. Those additions all strengthen the same result and preserve Lean-implies-paper, so the appropriate classification is faithful-stronger.

## Implications

- **Lean implies paper:** `yes`. For floating-representable problem instances, the Lean execution reproduces the paper's direct-weight and proper-barycentric counter expression. The eventual finite-envelope inequality and its exact decomposition imply the two first-order terms plus O(u^2). The normalized directions in FirstOrderSharp can be scaled to admissible local errors for sufficiently small positive u, giving constant-factor first-order attainability; the explicit factor 1/3 is stronger than the paper's unspecified factor.
- **Paper implies lean:** `no`. The printed theorem does not assert the arbitrary-real input generalization, the exact rational finite envelope and explicit remainder identity, or a uniform one-third first-order response. Its unspecified constant-factor sentence and unquantified O(u^2) remainder are insufficient by themselves to entail those strengthened Lean conjuncts.

## Findings

- **note / explicit-finite-envelope:** This makes the formal result more quantitative and prevents the paper statement alone from implying the whole Lean proposition; it does not change the paper's leading bound.
- **note / sharpness-strengthening:** Lean supplies a concrete uniform first-order factor stronger than the printed assertion. It still entails the source's qualitative constant-factor claim.
- **note / input-domain-generalization:** The theorem covers the paper's input domain and additionally proves an idealized exact-input result for arbitrary reals; it does not model initial conversion of nonrepresentable inputs.
- **note / defined-domain-specialization:** These hypotheses make all displayed ratios defined and are nonvacuous. They do not import the later interval restriction or remove a defined case stated by Theorem 4.1.
- **major / input-domain-generalization:** The translation covers the paper's representable instances but proves a broader result, so the reverse implication fails.
- **major / higher-order-strengthening:** These claims imply the paper's asymptotic bound but are not consequences of the stated paper theorem alone.
- **minor / sharpness-strengthening:** The direction witness supports the paper's qualitative sharpness under the same abstract local-error construction, but the numerical factor and directional formulation are stronger than the source statement.
- **note / defined-domain-formalization:** These conditions make the displayed quotient and relative error formally meaningful and are consistent with the paper's operative domain.

## Semantic checklist

| Check | Direct | Round-trip |
|---|---|---|
| `S01` | `pass` | `pass` |
| `S02` | `pass` | `fail` |
| `S03` | `pass` | `fail` |
| `S04` | `pass` | `fail` |
| `S05` | `pass` | `pass` |
| `S06` | `pass` | `pass` |
| `S07` | `pass` | `pass` |
| `S08` | `pass` | `pass` |
| `S09` | `pass` | `pass` |
| `S10` | `pass` | `fail` |
| `S11` | `pass` | `pass` |
| `S12` | `pass` | `fail` |
| `S13` | `pass` | `pass` |
| `S14` | `pass` | `fail` |
| `S15` | `pass` | `fail` |
| `S16` | `pass` | `pass` |

## Dependency coverage

- Blind translator covered `109` dependencies (`0` hash-reused meanings); unclear: `none`.
- Direct judge covered `109` dependencies (`0` hash-reused interpretations); failing or unclear: `none`.

## Remaining uncertainties

No remaining uncertainties were recorded.

## Audit artifacts

- `paper_bencmark/highambench/tasks/P13/T3/faithfulness/agent_outputs/blind_translation.json` (`04f2c52b847f817b3d3f4251aeac96e5bc25e6bf68766542e359516eedc7734a`)
- `paper_bencmark/highambench/tasks/P13/T3/faithfulness/agent_outputs/direct_judge.json` (`ae612af25c0f025be3898e23531f7916028c0d701206aaca8a18b13b35ac7974`)
- `paper_bencmark/highambench/tasks/P13/T3/faithfulness/agent_outputs/roundtrip_judge.json` (`d55bf6569fe91673200abb13a5b9140700302930b95ea135e0b669bd5e8575d2`)
- `paper_bencmark/highambench/tasks/P13/T3/faithfulness/agent_outputs/source_contract.json` (`567849cb57bf811a343b91df55881eba36e49d6a4b1f731332e758f332495933`)
- `paper_bencmark/highambench/tasks/P13/T3/faithfulness/decision.json` (`d4ca92d6f9861124d3109f86fe8ef534a1d40547cd582020fa1f8d5b23495c73`)
- `paper_bencmark/highambench/tasks/P13/T3/faithfulness/history/20260815T092307Z/agent_outputs/blind_translation.json` (`5415f28c58508e5c70e8986e0ff99391c0d7f2a40e3713491707d78e17685f54`)
- `paper_bencmark/highambench/tasks/P13/T3/faithfulness/history/20260815T092307Z/agent_outputs/direct_judge.json` (`a160ee6a7efb0b5d274d820c2b883d82404d76d47ee465ede0648f8db69f07fe`)
- `paper_bencmark/highambench/tasks/P13/T3/faithfulness/history/20260815T092307Z/agent_outputs/paper_source_contract.json` (`0b665a5c91e976eec5d015b1b58ea8cec5aa3023d351689e493b8b019f9b8393`)
- `paper_bencmark/highambench/tasks/P13/T3/faithfulness/history/20260815T092307Z/agent_outputs/roundtrip_judge.json` (`ea921b01be2b2f1de681e5bd1e4f1073da9f9520d571caa6ec7c6ea1b7c3c01f`)
- `paper_bencmark/highambench/tasks/P13/T3/faithfulness/history/20260815T092307Z/agent_outputs/source_contract.json` (`1fd9df97b061759f96f83fd660ddf45bb41e6817ad39dd16101f2a2a8e4c9991`)
- `paper_bencmark/highambench/tasks/P13/T3/faithfulness/history/20260815T092307Z/decision.json` (`66df4af900649f01e6a7aa81226f1723a169fdbaef5c98c9f26d57990ef50910`)
- `paper_bencmark/highambench/tasks/P13/T3/faithfulness/history/20260815T092307Z/inputs/blind_dependency_inventory.json` (`cd883fe849044fc30c3208844f82a59b227acac018ae7ec5b74b0f2ec49ae96d`)
- `paper_bencmark/highambench/tasks/P13/T3/faithfulness/history/20260815T092307Z/inputs/blind_dossier.md` (`f5e8dadbbc1d7f3992108cb38c4302c09faaf7f255a94073b469e9d93a14eb14`)
- `paper_bencmark/highambench/tasks/P13/T3/faithfulness/history/20260815T092307Z/inputs/blind_review_packet.md` (`f5e8dadbbc1d7f3992108cb38c4302c09faaf7f255a94073b469e9d93a14eb14`)
- `paper_bencmark/highambench/tasks/P13/T3/faithfulness/history/20260815T092307Z/inputs/declaration_dossier.md` (`46f9f0036236e0c7ef1cbd9cc3e88c9e7b0d2bae757a6a1a215a9a19f65383d0`)
- `paper_bencmark/highambench/tasks/P13/T3/faithfulness/history/20260815T092307Z/inputs/dependency_inventory.json` (`2249b2efec86ff286a16333d5b0bc6e39b17f3d6144e6adde14a4dc3f188c7f8`)
- `paper_bencmark/highambench/tasks/P13/T3/faithfulness/history/20260815T092307Z/inputs/dependency_reuse_direct.json` (`5fd765fc49342502b4ede143576255ac8f0ac012c362a3b01f3370504b0efebf`)
- `paper_bencmark/highambench/tasks/P13/T3/faithfulness/history/20260815T092307Z/inputs/direct_review_packet.md` (`758f33d8f47f21a93300f14ff299c0f84946c8df33d3d93ee5b45a25efb25bb7`)
- `paper_bencmark/highambench/tasks/P13/T3/faithfulness/history/20260815T092307Z/inputs/paper_source_locator.json` (`ec1d43325cb06b3c0839afb1c4848208a4c9dfd1b54b19aa5048fb5de3fa9f0f`)
- `paper_bencmark/highambench/tasks/P13/T3/faithfulness/history/20260815T092307Z/inputs/source_locator.json` (`cbd7354e603aef1ff5912909ceea5085953d4dbe5a28ae4b8c52e6007bf7885c`)
- `paper_bencmark/highambench/tasks/P13/T3/faithfulness/inputs/blind_dependency_inventory.json` (`3dc41b90886d2ba343a4135d71712290ae2969e33e9f5691254108b9fca0f81d`)
- `paper_bencmark/highambench/tasks/P13/T3/faithfulness/inputs/blind_dossier.md` (`9e4ee2f9f7e3683ed5b5e69f652f227d66bf7a1c6fa6baa27ee4a943f0f7b39d`)
- `paper_bencmark/highambench/tasks/P13/T3/faithfulness/inputs/blind_review_packet.md` (`9e4ee2f9f7e3683ed5b5e69f652f227d66bf7a1c6fa6baa27ee4a943f0f7b39d`)
- `paper_bencmark/highambench/tasks/P13/T3/faithfulness/inputs/declaration_dossier.md` (`1b84a2b1f8390a9cde32ae5c622bbb16cfab5a36c5b60ce190e4824d3a299160`)
- `paper_bencmark/highambench/tasks/P13/T3/faithfulness/inputs/dependency_inventory.json` (`a3819288989a432276364796b7de82933e918bf8f2b57cc4e59d543089450d47`)
- `paper_bencmark/highambench/tasks/P13/T3/faithfulness/inputs/direct_review_packet.md` (`7c97b41a31c15db0f8f051686387e38f21597bb120518cd3bb4de2e7e1595b1a`)
- `paper_bencmark/highambench/tasks/P13/T3/faithfulness/inputs/source_locator.json` (`df7167708141bd7000790b52076c0ab590b0bdf89affc7c58372a31cbbfcc026`)
