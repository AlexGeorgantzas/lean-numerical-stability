# Faithfulness audit: P10-T2

- Classification: `faithful-equivalent`
- Accepted as paper-faithful: `true`
- Adjudicated: `true`
- Target SHA-256: `753c197449d85ead7c0ecf95bd91ffdb31604a0fe1ac917aa9a126b7b85dcfbf`
- Paper SHA-256: `0ee818d060542baefdd85cbb7c7f2fd948efcb927101da84c37e418713f87269`

## Decision

The declaration is a rigorous asymptotic form of equation (8). It measures absolute normwise error against the unperturbed exact product, retains the fresh multiplication contribution and both inherited-error contributions with the correct factors, and absorbs precisely the suppressed mixed and quadratic effects into a locally uniform nonnegative multiple of epsilon^2. The disputed witness dependence is not contrary to any paper quantifier, and the real-square setting does not remove an explicitly asserted complex scope. Both implications therefore hold for the selected result, supporting faithful-equivalent and acceptance.

## Implications

- **Lean implies paper:** `yes`. For every admissible product family, Lean bounds the actual absolute normwise product error by exactly the three contributions in equation (8), plus a fixed O(epsilon^2) remainder on a positive neighborhood. Reading equation (8) as the surrounding recurrence does, namely as first-order error-bound accounting, recovers the paper statement.
- **Paper implies lean:** `yes`. Under the declaration's explicit premises, apply the paper's stable-multiplication model to the perturbed operands, expand (A+DeltaA)(B+DeltaB)-AB, and use the triangle and submultiplicative norm inequalities. The two linear perturbation terms give the inherited-error contributions, while DeltaA times DeltaB and changes in the fresh operand norms are O(epsilon^2), yielding the Lean conclusion.

## Findings

- **note / quantifier-scope:** This is a legitimate explicit local-O formulation and does not weaken an asserted paper quantifier.
- **note / scalar-field-scope:** No explicit paper case is omitted, and the specialization remains substantive and nonvacuous.
- **note / stability-assumption-placement:** The theorem formalizes the local conditional rule used in equation (8), not a standalone proof that every operation in the algorithm bundle is globally stable.

## Semantic checklist

| Check | Direct | Round-trip |
|---|---|---|
| `S01` | `pass` | `pass` |
| `S02` | `pass` | `pass` |
| `S03` | `pass` | `unclear` |
| `S04` | `pass` | `pass` |
| `S05` | `pass` | `pass` |
| `S06` | `pass` | `pass` |
| `S07` | `pass` | `pass` |
| `S08` | `pass` | `pass` |
| `S09` | `pass` | `pass` |
| `S10` | `pass` | `pass` |
| `S11` | `pass` | `pass` |
| `S12` | `pass` | `pass` |
| `S13` | `pass` | `pass` |
| `S14` | `pass` | `pass` |
| `S15` | `pass` | `unclear` |
| `S16` | `pass` | `pass` |

## Dependency coverage

- Blind translator covered `72` dependencies (`0` hash-reused meanings); unclear: `none`.
- Direct judge covered `72` dependencies (`0` hash-reused interpretations); failing or unclear: `none`.

## Remaining uncertainties

- The paper does not formally state whether its O(epsilon^2) witnesses were intended to be uniform over operand families; this adjudication attributes only the standard fixed-instance local meaning actually supported by the text.
- The selected passages do not explicitly declare a scalar field. Whether equation (8) was also intended as a complex-matrix result is unstated and is not treated as part of the adjudicated source claim.

## Audit artifacts

- `paper_bencmark/highambench/tasks/P10/T2/faithfulness/agent_outputs/adjudicator.json` (`c8b6562982205b678a54ec311b60d066f9d40ce5530d5ed86ae41c5bf2b700e2`)
- `paper_bencmark/highambench/tasks/P10/T2/faithfulness/agent_outputs/blind_translation.json` (`f0978898510efb1c56fc96974bdeb63876b64dbc4daedaee7b1f59119d4b7468`)
- `paper_bencmark/highambench/tasks/P10/T2/faithfulness/agent_outputs/direct_judge.json` (`3209343739cb0e5fa2fd1eaaf573d6e27129ee2358cad29a0f7d91ed2a3eaa2e`)
- `paper_bencmark/highambench/tasks/P10/T2/faithfulness/agent_outputs/roundtrip_judge.json` (`c854025480e55b9a7eb9d056d567833bf7e43a25d1f9d241cda4fa8b3a09ea2c`)
- `paper_bencmark/highambench/tasks/P10/T2/faithfulness/agent_outputs/source_contract.json` (`27c9dd314032cd0baab5a9dac17eab7ae1b2d34a0702c0ee13bcc34a5f616c99`)
- `paper_bencmark/highambench/tasks/P10/T2/faithfulness/decision.json` (`adb8312cebecd673f748b7d99ecf9f486afe90b0d95adb6c9ee5527b65980093`)
- `paper_bencmark/highambench/tasks/P10/T2/faithfulness/history/20260815T060718Z/agent_outputs/blind_translation.json` (`559f6d1e96571c9877d952afdb42bb8205c09e30f049a44ad67792352c5349b1`)
- `paper_bencmark/highambench/tasks/P10/T2/faithfulness/history/20260815T060718Z/agent_outputs/direct_judge.json` (`e1a6926a52d5959da1ec2961bb1a850dd23a43ffbdf53c5d7d88d2e52828f281`)
- `paper_bencmark/highambench/tasks/P10/T2/faithfulness/history/20260815T060718Z/agent_outputs/paper_source_contract.json` (`a730fdcbbc543ec8712373b135d8a67dd310f31f635dedabf0ed548f9316414a`)
- `paper_bencmark/highambench/tasks/P10/T2/faithfulness/history/20260815T060718Z/agent_outputs/roundtrip_judge.json` (`59f2c179c5302184cc13a03b919bf67f4b7b663c34b3f02f1b52663194f5885b`)
- `paper_bencmark/highambench/tasks/P10/T2/faithfulness/history/20260815T060718Z/agent_outputs/source_contract.json` (`af7fa355c5dade9d76fb53f107b3b32ff7103edf0361110875f740f9baa89612`)
- `paper_bencmark/highambench/tasks/P10/T2/faithfulness/history/20260815T060718Z/decision.json` (`f2015fec1b645d07a2ffc467365b70355e6084c9c2a0a11410c33ac7ff7a9dde`)
- `paper_bencmark/highambench/tasks/P10/T2/faithfulness/history/20260815T060718Z/inputs/blind_dependency_inventory.json` (`0392614de25d2d2adb2289c0b1899389997494470f2547e1d2c288816cfe5641`)
- `paper_bencmark/highambench/tasks/P10/T2/faithfulness/history/20260815T060718Z/inputs/blind_dossier.md` (`e81fdd6586663abfd118de175147ad1ef6bc5345b5051f82c59672ee854b1a4c`)
- `paper_bencmark/highambench/tasks/P10/T2/faithfulness/history/20260815T060718Z/inputs/blind_review_packet.md` (`e81fdd6586663abfd118de175147ad1ef6bc5345b5051f82c59672ee854b1a4c`)
- `paper_bencmark/highambench/tasks/P10/T2/faithfulness/history/20260815T060718Z/inputs/declaration_dossier.md` (`b333917c31f30480fac3efff76052e6fe2d1a1c8556d546f577c184170017b05`)
- `paper_bencmark/highambench/tasks/P10/T2/faithfulness/history/20260815T060718Z/inputs/dependency_inventory.json` (`f15473cf9706a022eda818c8973023b7e87fff3b5fb42b24be69ec4b51714a74`)
- `paper_bencmark/highambench/tasks/P10/T2/faithfulness/history/20260815T060718Z/inputs/dependency_reuse_direct.json` (`a91219164d34d309cc938ea3b63b91bd83b570c3801ccd20d74c69f6a3afe938`)
- `paper_bencmark/highambench/tasks/P10/T2/faithfulness/history/20260815T060718Z/inputs/direct_review_packet.md` (`d497f433a129b9c8ae7effd6171e0d1c5fdbcf93487c3d83c51e84f131eca76f`)
- `paper_bencmark/highambench/tasks/P10/T2/faithfulness/history/20260815T060718Z/inputs/paper_source_locator.json` (`91f77a26c65c7ca024e216f6cc35327e6521963eee50d0bda4fd50b72060a4dc`)
- `paper_bencmark/highambench/tasks/P10/T2/faithfulness/history/20260815T060718Z/inputs/source_locator.json` (`5024d15fffb84de9174802e1e04a0124e7961850131b58b3ca4190f0248a1ed8`)
- `paper_bencmark/highambench/tasks/P10/T2/faithfulness/history/20260821T200913Z/agent_outputs/blind_translation.json` (`ad8f3eb4a664ba0e61f090092bd821930adc2071585f00ee4b031d6bc272237b`)
- `paper_bencmark/highambench/tasks/P10/T2/faithfulness/history/20260821T200913Z/agent_outputs/direct_judge.json` (`bcdd26e2770193a9b58bf34adcf777cce3e28a4794bb03932390ea2f5655268e`)
- `paper_bencmark/highambench/tasks/P10/T2/faithfulness/history/20260821T200913Z/agent_outputs/roundtrip_judge.json` (`91178079cd9c357be1e63028919496f99d6c6c6e35c79a1e58df2115969f04f8`)
- `paper_bencmark/highambench/tasks/P10/T2/faithfulness/history/20260821T200913Z/agent_outputs/source_contract.json` (`69ec8f212638421b4a01df40f662c4a884d0d95bdc01f447ec4b18764bd14c41`)
- `paper_bencmark/highambench/tasks/P10/T2/faithfulness/history/20260821T200913Z/decision.json` (`503a87c2d191945b478c1adc08bd63c0db647f512ef29707be89f73a2b67230a`)
- `paper_bencmark/highambench/tasks/P10/T2/faithfulness/history/20260821T200913Z/inputs/blind_dependency_inventory.json` (`78b55c122ea7f4e7cae7fa95eac0faa913b593e365f3cb611dbd7c407a747236`)
- `paper_bencmark/highambench/tasks/P10/T2/faithfulness/history/20260821T200913Z/inputs/blind_dossier.md` (`588f3a61a1c9d9a6aa9e908b220c9f05abdcd699b967d25e943c2a9080826e9f`)
- `paper_bencmark/highambench/tasks/P10/T2/faithfulness/history/20260821T200913Z/inputs/blind_review_packet.md` (`588f3a61a1c9d9a6aa9e908b220c9f05abdcd699b967d25e943c2a9080826e9f`)
- `paper_bencmark/highambench/tasks/P10/T2/faithfulness/history/20260821T200913Z/inputs/declaration_dossier.md` (`ca35e7d825093f0a244f30607161e168d1af74a2ec416bef8a06b185554c7497`)
- `paper_bencmark/highambench/tasks/P10/T2/faithfulness/history/20260821T200913Z/inputs/dependency_inventory.json` (`ed2a072c67791456bd4d84fbfc2fab101db00bfeaa5b39831dda2b1352266f5d`)
- `paper_bencmark/highambench/tasks/P10/T2/faithfulness/history/20260821T200913Z/inputs/direct_review_packet.md` (`0159e798ef6db7fba59f235354245d82517b9b920e04f916ddfb741d22b84f21`)
- `paper_bencmark/highambench/tasks/P10/T2/faithfulness/history/20260821T200913Z/inputs/source_locator.json` (`5024d15fffb84de9174802e1e04a0124e7961850131b58b3ca4190f0248a1ed8`)
- `paper_bencmark/highambench/tasks/P10/T2/faithfulness/inputs/blind_dependency_inventory.json` (`4f9c7a4a769745db47110dcfb5e77d14c135ee4bb1a56de6eb88fe75b0aa8edd`)
- `paper_bencmark/highambench/tasks/P10/T2/faithfulness/inputs/blind_dossier.md` (`628982bd63e7222e25a69b66b4cac67474c58ebed9bbfc1b60907c6684cbf7d2`)
- `paper_bencmark/highambench/tasks/P10/T2/faithfulness/inputs/blind_review_packet.md` (`628982bd63e7222e25a69b66b4cac67474c58ebed9bbfc1b60907c6684cbf7d2`)
- `paper_bencmark/highambench/tasks/P10/T2/faithfulness/inputs/declaration_dossier.md` (`ab45f6bb66aa030e6148e62ad8eed998a7b40957992d04b2bcddb111be74642f`)
- `paper_bencmark/highambench/tasks/P10/T2/faithfulness/inputs/dependency_inventory.json` (`491a4173915ce3ca625d9e7ae80245cd8943384a9465c10a9b4f86607668c06b`)
- `paper_bencmark/highambench/tasks/P10/T2/faithfulness/inputs/direct_review_packet.md` (`90e262d2e9130eafad7e3a20771bbb5731be8d53c55da60e50f29496323ad827`)
- `paper_bencmark/highambench/tasks/P10/T2/faithfulness/inputs/source_locator.json` (`5024d15fffb84de9174802e1e04a0124e7961850131b58b3ca4190f0248a1ed8`)
