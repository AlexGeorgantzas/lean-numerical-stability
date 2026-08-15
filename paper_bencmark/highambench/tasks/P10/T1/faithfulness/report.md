# Faithfulness audit: P10-T1

- Classification: `not-faithful-weaker`
- Accepted as paper-faithful: `false`
- Adjudicated: `true`
- Target SHA-256: `935474be1c1fede023141a23fc630c2234eb71c72df1c724133e29163e78a735`
- Paper SHA-256: `0ee818d060542baefdd85cbb7c7f2fd948efcb927101da84c37e418713f87269`

## Decision

The run gives a reasonable explicit perturbation interpretation, and the theorem proves the correct nonvacuous bound for propagation of the right operand's inherited error. Real square matrices and a consistent abstract norm are acceptable specializations, while the generic T1 scope does not require triangular-inversion blocks. Nevertheless, Eq. (8) gives the selected term meaning by making it one contribution to total first-order product error. In Lean, p10FirstOrderProductErrorBudget is only the three-term scalar by definition, and the target's budget equality merely unfolds that definition. No asserted relation connects the component or budget to p10FirstOrderProductError, computedProduct - exactLeft*exactRight, or its norm. The paper therefore implies the weaker Lean conclusions under the explicit interpretation, but Lean does not imply the selected paper claim.

## Implications

- **Lean implies paper:** `no`. The Lean conclusion can hold while its three-term budget remains unrelated to total first-order product error. It therefore establishes the magnitude of one propagated perturbation term but not its paper-level status as a summand of err(C,n).
- **Paper implies lean:** `yes`. Under Lean's explicit specialization, Eq. (8)'s inherited-right interpretation together with the assumed submultiplicative norm and norm(rightPerturbation) <= rightInheritedError yields the first conjunct. The second conjunct follows definitionally. Lean's extra premises only restrict the admissible cases.

## Findings

- **critical / missing-total-error-linkage:** The selected term is not formally established as a contribution to total first-order product error, so the task's required semantic role is absent.
- **major / definitional-budget-equality:** The claimed additive position follows by unfolding a definition and supplies no connection to a product-error quantity.
- **minor / restricted-applicability:** These choices narrow the source claim's applicability and cannot support a faithful-stronger classification.
- **note / valid-component-bound:** The inherited-right inequality itself is genuine and nonvacuous; rejection is due to missing error linkage, not an incorrect orientation or a vacuous theorem.
- **note / task-sensitive-scope:** Neither missing triangular-block structure nor the uncontrolled cross term is an independent fatal defect for this isolated component task.

## Semantic checklist

| Check | Direct | Round-trip |
|---|---|---|
| `S01` | `pass` | `pass` |
| `S02` | `pass` | `fail` |
| `S03` | `fail` | `pass` |
| `S04` | `fail` | `fail` |
| `S05` | `fail` | `fail` |
| `S06` | `pass` | `fail` |
| `S07` | `pass` | `unclear` |
| `S08` | `fail` | `fail` |
| `S09` | `pass` | `pass` |
| `S10` | `pass` | `fail` |
| `S11` | `fail` | `fail` |
| `S12` | `fail` | `fail` |
| `S13` | `fail` | `fail` |
| `S14` | `fail` | `fail` |
| `S15` | `pass` | `unclear` |
| `S16` | `fail` | `fail` |

## Dependency coverage

- Blind translator covered `64` dependencies (`0` hash-reused meanings); unclear: `none`.
- Direct judge covered `64` dependencies (`0` hash-reused interpretations); failing or unclear: `D001, D002, D005, D006, D012`.

## Remaining uncertainties

- Equation (8)'s equals sign may denote first-order bookkeeping that defines an error bound rather than equality with a realized error. Under either reading, the target asserts no relationship between its budget and a total-error quantity.
- The cited passages do not conclusively establish whether Real is the paper's full scalar domain, although real n-by-n matrices are an acceptable specialization.
- The paper does not uniquely determine an exact-plus-perturbation notation or sign convention for inherited operand errors; the run's chosen convention is reasonable but not canonical.

## Audit artifacts

- `paper_bencmark/highambench/tasks/P10/T1/faithfulness/agent_outputs/adjudicator.json` (`1bc811edc48f1ddc9445a04242cd6bf0830c94ef5be45438f15d043a6f6f93b2`)
- `paper_bencmark/highambench/tasks/P10/T1/faithfulness/agent_outputs/blind_translation.json` (`2149442f1888f0661cb4c9c5de8e033b66574adbd96375f7301a639466bcbd73`)
- `paper_bencmark/highambench/tasks/P10/T1/faithfulness/agent_outputs/direct_judge.json` (`ca25bd6b7f065425badd8549b226656af73eacbddcd0a87410c524b9cf833660`)
- `paper_bencmark/highambench/tasks/P10/T1/faithfulness/agent_outputs/roundtrip_judge.json` (`a16d77916ace64469f5e8eb7b85518f10e6b3b2a2509fb8359d6439915b95bc1`)
- `paper_bencmark/highambench/tasks/P10/T1/faithfulness/agent_outputs/source_contract.json` (`78af795e5b4eb407effe9e95b33a8c1fd6258e1fbfda6d3ebd05a4d373998dc4`)
- `paper_bencmark/highambench/tasks/P10/T1/faithfulness/decision.json` (`d9d0e21059297ed0bc51e0a34888170a78748d31534e2ad4e9811fca9003d858`)
- `paper_bencmark/highambench/tasks/P10/T1/faithfulness/history/20260815T073419Z/agent_outputs/adjudicator.json` (`dcbf8141b6ee91f2870aa2f9bc7cec3dd20a1d8f1a2c9d7026abbcc86c227064`)
- `paper_bencmark/highambench/tasks/P10/T1/faithfulness/history/20260815T073419Z/agent_outputs/blind_translation.json` (`13980af30160a3aa94e82252e6b82d855790e04ce8c4506daefdaa10b77c564d`)
- `paper_bencmark/highambench/tasks/P10/T1/faithfulness/history/20260815T073419Z/agent_outputs/direct_judge.json` (`a55dae02340c6957132742a8aec72987d43e9ec606ce0740c2c2bbbf25cb49d0`)
- `paper_bencmark/highambench/tasks/P10/T1/faithfulness/history/20260815T073419Z/agent_outputs/paper_source_contract.json` (`a730fdcbbc543ec8712373b135d8a67dd310f31f635dedabf0ed548f9316414a`)
- `paper_bencmark/highambench/tasks/P10/T1/faithfulness/history/20260815T073419Z/agent_outputs/roundtrip_judge.json` (`29a5613f27a9c472f559fe8e78b2a2f508f9da93acaecfb8445c67f7e1e2a663`)
- `paper_bencmark/highambench/tasks/P10/T1/faithfulness/history/20260815T073419Z/agent_outputs/source_contract.json` (`6377f2213fdc9ed7448bff43d7d5f7b0a5d9342d786adfbedcab4c9c9d3508e2`)
- `paper_bencmark/highambench/tasks/P10/T1/faithfulness/history/20260815T073419Z/decision.json` (`24f16217e9902ce68deeca697892bd2c586c87199b5919abeba6837eb67adc7f`)
- `paper_bencmark/highambench/tasks/P10/T1/faithfulness/history/20260815T073419Z/inputs/blind_dependency_inventory.json` (`ea6f316e924735d4747662729846282e651964bc9b9311bc392658fac8b08ad8`)
- `paper_bencmark/highambench/tasks/P10/T1/faithfulness/history/20260815T073419Z/inputs/blind_dossier.md` (`24476ab5b9b011e4e040fd98de4744aeffdd79fd419e7723ac5f4056362e1c41`)
- `paper_bencmark/highambench/tasks/P10/T1/faithfulness/history/20260815T073419Z/inputs/blind_review_packet.md` (`24476ab5b9b011e4e040fd98de4744aeffdd79fd419e7723ac5f4056362e1c41`)
- `paper_bencmark/highambench/tasks/P10/T1/faithfulness/history/20260815T073419Z/inputs/declaration_dossier.md` (`6086ba071c4de3b7d0d07d015fe11f56534252356248b2f3f966657ca026a9d8`)
- `paper_bencmark/highambench/tasks/P10/T1/faithfulness/history/20260815T073419Z/inputs/dependency_inventory.json` (`2b6c104df908a0a847ee8ea4cfb22f6ef050604370bfaa7f6c87202b68d2a2f2`)
- `paper_bencmark/highambench/tasks/P10/T1/faithfulness/history/20260815T073419Z/inputs/direct_review_packet.md` (`a2dfb6ebbb9e7986c015e15100dba2365d705a6ba8d46d292553222278d2ae75`)
- `paper_bencmark/highambench/tasks/P10/T1/faithfulness/history/20260815T073419Z/inputs/paper_source_locator.json` (`91f77a26c65c7ca024e216f6cc35327e6521963eee50d0bda4fd50b72060a4dc`)
- `paper_bencmark/highambench/tasks/P10/T1/faithfulness/history/20260815T073419Z/inputs/source_locator.json` (`e188951561a2dc17da7c49f73062a5c18c0b4c95b39a01204a693aef5628a233`)
- `paper_bencmark/highambench/tasks/P10/T1/faithfulness/inputs/blind_dependency_inventory.json` (`41fd69351066c3bf3e2955c78439f177b4bc9eafa8139aa84c37e5dd0bb07c25`)
- `paper_bencmark/highambench/tasks/P10/T1/faithfulness/inputs/blind_dossier.md` (`6449e625e49a3f065eed082644fb5555b5d3b216764294552ae5d40f53009a1a`)
- `paper_bencmark/highambench/tasks/P10/T1/faithfulness/inputs/blind_review_packet.md` (`6449e625e49a3f065eed082644fb5555b5d3b216764294552ae5d40f53009a1a`)
- `paper_bencmark/highambench/tasks/P10/T1/faithfulness/inputs/declaration_dossier.md` (`82a2633f16ae52fa058ae8fd11582542e8d14c6f6245114409bec7de2125ebc5`)
- `paper_bencmark/highambench/tasks/P10/T1/faithfulness/inputs/dependency_inventory.json` (`8f280aa54e7755db10827abd8ad4643d67e8378b1727150dbc18c5ed06348c66`)
- `paper_bencmark/highambench/tasks/P10/T1/faithfulness/inputs/direct_review_packet.md` (`135e6810027ec5423b8d1eb848842d4949a47414e52a6491d9eeb12e17f15b95`)
- `paper_bencmark/highambench/tasks/P10/T1/faithfulness/inputs/source_locator.json` (`d8322c6fdbb9ff0df044f34a53d4c16c9d77770889baccf186ed83c90647815c`)
