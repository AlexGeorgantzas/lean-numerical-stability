# Faithfulness audit: P14-T1

- Classification: `faithful-stronger`
- Accepted as paper-faithful: `true`
- Adjudicated: `true`
- Target SHA-256: `1fadb695cd89451b64987663c962bbcc73d042d4cad968f476cba00c9eeb4e90`
- Paper SHA-256: `7247047bc49218e001195edc8a2d66131eea7596d252503f34b0ace6328981cd`

## Decision

Primary PDF evidence makes equation (3.3) an unambiguous coherent aggregate claim despite the missing-u typo in the preceding equation. The declaration preserves the unshifted exponential computation, exact/computed-sum distinction, left-to-right addition model, componentwise exponential errors, additive Delta s identity, and the (n+1)u*s first-order bound. Its gamma accumulation clause does not reproduce the sharper intermediate coefficient distribution, but those displays are derivation context rather than the scoped benchmark result. The explicit finite envelope and quadratic remainder genuinely strengthen equation (3.3) without reducing applicability or creating vacuity. Therefore Lean implies the scoped paper claim, the paper does not imply all added Lean conclusions, and the correct classification is faithful-stronger.

## Implications

- **Lean implies paper:** `yes`. Map exactSum to s, p14RecursiveComputedExpSum to hat(s), and p14BasicSumDelta to Delta s. The target gives hat(s)=s+Delta s and eventually bounds |Delta s| by an envelope equal to (n+1)u*s+R, with R=O(u^2). This directly yields the coherent and literally printed equation (3.3). The different gamma accumulation clause does not obstruct this aggregate implication.
- **Paper implies lean:** `no`. Equation (3.3) and its surrounding first-order analysis leave O(u^2) unspecified. They do not state the target's exact gamma_{n-1} accumulation inequality, exact rational finite envelope, particular remainder n(n+1)s*u^2/(1-nu), or arbitrary-filter formulation. Those additional conclusions therefore are not supplied by the paper statement.

## Findings

- **note / task-scope:** Intermediate page-2317 inequalities provide supporting context but are not all mandatory conclusions of P14-T1.
- **minor / intermediate-weighted-bounds:** The target must not be described as reproducing every intermediate bound, although this does not affect faithfulness to equation (3.3).
- **note / printed-missing-u:** The omission is treated as a typographical defect; no literal-equivalence claim for that malformed line is accepted.
- **note / explicit-remainder-strength:** This is substantive, nonvacuous extra strength and makes the converse implication fail.

## Semantic checklist

| Check | Direct | Round-trip |
|---|---|---|
| `S01` | `pass` | `pass` |
| `S02` | `pass` | `pass` |
| `S03` | `pass` | `pass` |
| `S04` | `pass` | `pass` |
| `S05` | `fail` | `fail` |
| `S06` | `pass` | `pass` |
| `S07` | `pass` | `pass` |
| `S08` | `pass` | `pass` |
| `S09` | `pass` | `pass` |
| `S10` | `fail` | `fail` |
| `S11` | `pass` | `pass` |
| `S12` | `pass` | `pass` |
| `S13` | `pass` | `pass` |
| `S14` | `unclear` | `pass` |
| `S15` | `pass` | `pass` |
| `S16` | `pass` | `pass` |

## Dependency coverage

- Blind translator covered `86` dependencies (`0` hash-reused meanings); unclear: `none`.
- Direct judge covered `86` dependencies (`0` hash-reused interpretations); failing or unclear: `D002`.

## Remaining uncertainties

- Equation (3.1) reuses an unindexed delta_1, so the PDF does not explicitly decide between one common error and separate local errors. The target's per-index bounded errors match the conventional componentwise reading and include the common-error case.
- The paper gives no constant, parameter dependence, or finite-u range for its O(u^2) term. The target's explicit remainder is therefore a valid witness for equation (3.3), but it cannot be identified as the paper's uniquely intended remainder.

## Audit artifacts

- `paper_bencmark/highambench/tasks/P14/T1/faithfulness/agent_outputs/adjudicator.json` (`e71eab69f333eac3e50347596451be1ed2a39b46dc9ebfb84e438b58fa6f2089`)
- `paper_bencmark/highambench/tasks/P14/T1/faithfulness/agent_outputs/blind_translation.json` (`7d14990007d6bf0ae173d069b823230bfbc5ac1264f39769503ba2f8323f334f`)
- `paper_bencmark/highambench/tasks/P14/T1/faithfulness/agent_outputs/direct_judge.json` (`cbdbe9a41d2a25e9798f9abc2e14887c0077891be18b720f173800eede6c5d7b`)
- `paper_bencmark/highambench/tasks/P14/T1/faithfulness/agent_outputs/roundtrip_judge.json` (`409555ee332d022bf8fc28f254ec29081b0490d5ad968eb0e5cbbe77f1462b20`)
- `paper_bencmark/highambench/tasks/P14/T1/faithfulness/agent_outputs/source_contract.json` (`df7f58e8125087431760dbafff80f1f458e3e8400a4cd133ce41a956e8119884`)
- `paper_bencmark/highambench/tasks/P14/T1/faithfulness/decision.json` (`eff8f5d905b404183dc65ad48bf35f665d840f62830c4f741bc92a6aae29e8f5`)
- `paper_bencmark/highambench/tasks/P14/T1/faithfulness/history/20260820T075347Z/agent_outputs/blind_translation.json` (`d5a0ef51c7edd0b0d65f37202c4f3789bd28545c13157dfbe555336fe96e879c`)
- `paper_bencmark/highambench/tasks/P14/T1/faithfulness/history/20260820T075347Z/agent_outputs/direct_judge.json` (`355484fc173f1bc14654e92ce769be4b79c78b32ce7b280f191fac1d678e56af`)
- `paper_bencmark/highambench/tasks/P14/T1/faithfulness/history/20260820T075347Z/agent_outputs/paper_source_contract.json` (`b9f05c969428f95fef40bddc0aa0b2a7c1d291ecdd7ba0ca0f5fb748131f1562`)
- `paper_bencmark/highambench/tasks/P14/T1/faithfulness/history/20260820T075347Z/agent_outputs/roundtrip_judge.json` (`ebc2c77f6cd66f4abe564e6b702c9e7bdb0ff38be46ca6f56d6d0c7fa14d9218`)
- `paper_bencmark/highambench/tasks/P14/T1/faithfulness/history/20260820T075347Z/agent_outputs/source_contract.json` (`a6db6f8060b77e3de1227a8f25b86e2bfa59e60a708c7100f5588e01477a1da9`)
- `paper_bencmark/highambench/tasks/P14/T1/faithfulness/history/20260820T075347Z/decision.json` (`ec36bf88dbe3c4d427995f08c94abb6bba03baad93e1d587f7c9bf26ece67be4`)
- `paper_bencmark/highambench/tasks/P14/T1/faithfulness/history/20260820T075347Z/inputs/blind_dependency_inventory.json` (`232958a14ed1b329a02aabddcff2ff787e1d87fcc6d16e9e5c30c155a29d2ef5`)
- `paper_bencmark/highambench/tasks/P14/T1/faithfulness/history/20260820T075347Z/inputs/blind_dossier.md` (`608e35f75ad860de70c845e29b159ef50c94cd3ed1ee1efb8c497c00e3e0da68`)
- `paper_bencmark/highambench/tasks/P14/T1/faithfulness/history/20260820T075347Z/inputs/blind_review_packet.md` (`608e35f75ad860de70c845e29b159ef50c94cd3ed1ee1efb8c497c00e3e0da68`)
- `paper_bencmark/highambench/tasks/P14/T1/faithfulness/history/20260820T075347Z/inputs/declaration_dossier.md` (`9b346ffa1c471f654fcdcc6f94608e9dbceb7d3f7b974fc706e6051a35b10673`)
- `paper_bencmark/highambench/tasks/P14/T1/faithfulness/history/20260820T075347Z/inputs/dependency_inventory.json` (`d8089db76b9ece948720014e5ad61ba2734e696ec20690d958cb41bcf1b1d272`)
- `paper_bencmark/highambench/tasks/P14/T1/faithfulness/history/20260820T075347Z/inputs/direct_review_packet.md` (`7ce3cae8d9eb21a1b6bbee129b6084f539e1cc46ff00963209359049ff00868c`)
- `paper_bencmark/highambench/tasks/P14/T1/faithfulness/history/20260820T075347Z/inputs/paper_source_locator.json` (`8627ed196c1c7742168563780358efbf3ebaee357ded297978c4d9199a86318c`)
- `paper_bencmark/highambench/tasks/P14/T1/faithfulness/history/20260820T075347Z/inputs/source_locator.json` (`0743d6c88f70fe6e0d2d4ba6647096a4162697a6774b21cfea6b247ac705bbb5`)
- `paper_bencmark/highambench/tasks/P14/T1/faithfulness/inputs/blind_dependency_inventory.json` (`85a2c6594a9537aa39ab9905bd2e6b0c5f43a676fbd9ccdbf5a638d8a6afb3d6`)
- `paper_bencmark/highambench/tasks/P14/T1/faithfulness/inputs/blind_dossier.md` (`41849ca34a1df2e38f65fa08815642eba40999c97af38874aba921bf8c5299db`)
- `paper_bencmark/highambench/tasks/P14/T1/faithfulness/inputs/blind_review_packet.md` (`41849ca34a1df2e38f65fa08815642eba40999c97af38874aba921bf8c5299db`)
- `paper_bencmark/highambench/tasks/P14/T1/faithfulness/inputs/declaration_dossier.md` (`9ec4c1f5f1ed4223c1b07d448d97a8176514d544b6de064751b8be35371d742b`)
- `paper_bencmark/highambench/tasks/P14/T1/faithfulness/inputs/dependency_inventory.json` (`71990e44ea02ccbf0914ecfe6f8abfa99b933c1216f5fe5374296fae59cc1326`)
- `paper_bencmark/highambench/tasks/P14/T1/faithfulness/inputs/direct_review_packet.md` (`7dd332fc22dfebcb320353385d53a94aca659986ae9539aa6398d0a161dad3e5`)
- `paper_bencmark/highambench/tasks/P14/T1/faithfulness/inputs/source_locator.json` (`505dde6b3a8ee6b868c041ebf02116617d09996efd729a1bf2ba501a300ca5c4`)
