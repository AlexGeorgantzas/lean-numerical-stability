# Faithfulness audit: P10-T1

- Classification: `faithful-equivalent`
- Accepted as paper-faithful: `true`
- Adjudicated: `true`
- Target SHA-256: `5b81bbeed4d7ea8c07958b66a8195484a8a2ef6f4ac4c81c6deb3ad1e99368e1`
- Paper SHA-256: `0ee818d060542baefdd85cbb7c7f2fd948efcb927101da84c37e418713f87269`

## Decision

Primary PDF evidence identifies P10-T1 as the middle first-order contribution ||A|| err(B,n) and its additive placement in equation (8). The declaration realizes that contribution as A*dB, links it to the complete three-matrix first-order expansion, and proves the corresponding coefficient-one norm amplification using an abstract submultiplicative norm. The round-trip objections concerning polynomial mu, machine-level execution, recursive inversion, total forward error, and O(epsilon^2) concern broader paper results that are separable from the selected subclaim. The exact matrix identity is not classified as a genuine stronger numerical theorem: it is a conditional algebraic realization under the run's explicit decomposition, while the real square domain is restricted applicability rather than strength. Within that correctly delimited instance, both implication directions hold and the declaration is faithful-equivalent.

## Implications

- **Lean implies paper:** `yes`. For the selected first-order subclaim, the Lean identity places the matrix A*dB additively between the fresh and left-inherited contributions, and the second conjunct gives ||A*dB|| <= ||A|| errB. Together with the run's local and left-perturbation bounds and the norm axioms, the complete corresponding first-order norm upper bound can also be derived. This entails equation (8)'s inherited-right contribution in the real square instance, without entailing the paper's broader algorithmic stability claims.
- **Paper implies lean:** `yes`. In the selected real square instance, represent inherited operand errors by perturbation matrices dA and dB and fresh multiplication error by E, collecting the cross term and suppressed effects in the explicitly removed terms. Expanding (A+dA)(B+dB) gives the Lean residual identity, while submultiplicativity and ||dB|| <= err(B,n) give ||A*dB|| <= ||A|| err(B,n). Thus the paper's selected first-order mechanism yields the declaration under its explicit run representation.

## Findings

- **note / selected-subclaim-scope:** The declaration captures the located P10-T1 claim even though it is not a complete formalization of equation (1), equation (8)'s entire numerical model, or recursive inversion.
- **note / higher-order-scope:** The declaration cannot certify that the full computed-product remainder is O(epsilon^2), but it does not misidentify that full error with the selected first-order component.
- **note / algorithm-linkage:** Absence of the later recursion is not a defect for this selected generic product subclaim; the theorem must not be cited as proving the recursive algorithm's stability.
- **note / nonvacuity:** The right-inherited contribution can be nonzero and can attain its bound, so acceptance does not rest on vacuity or an all-zero model.

## Semantic checklist

| Check | Direct | Round-trip |
|---|---|---|
| `S01` | `pass` | `pass` |
| `S02` | `pass` | `fail` |
| `S03` | `pass` | `unclear` |
| `S04` | `pass` | `fail` |
| `S05` | `pass` | `fail` |
| `S06` | `pass` | `pass` |
| `S07` | `pass` | `pass` |
| `S08` | `pass` | `fail` |
| `S09` | `pass` | `pass` |
| `S10` | `pass` | `fail` |
| `S11` | `pass` | `fail` |
| `S12` | `pass` | `fail` |
| `S13` | `pass` | `fail` |
| `S14` | `pass` | `fail` |
| `S15` | `pass` | `unclear` |
| `S16` | `pass` | `fail` |

## Dependency coverage

- Blind translator covered `62` dependencies (`0` hash-reused meanings); unclear: `none`.
- Direct judge covered `62` dependencies (`0` hash-reused interpretations); failing or unclear: `none`.

## Remaining uncertainties

- Equation (8) does not formally define err(B,n) as an attained norm rather than an upper bound. The following recurrence discussion supports the upper-bound reading used by the declaration, but the standalone notation remains informal.
- The cited passages do not state a maximal scalar field or rectangular domain. Acceptance is limited to the real square instance represented by the declaration and does not establish coverage of complex or rectangular products.

## Audit artifacts

- `paper_bencmark/highambench/tasks/P10/T1/faithfulness/agent_outputs/adjudicator.json` (`ea2144684ce59b98b55d35f7611c7f766161c7cf92b5b5cc453c6ab03c857a07`)
- `paper_bencmark/highambench/tasks/P10/T1/faithfulness/agent_outputs/blind_translation.json` (`0f505b3a7f62e5637f8067430d911047d5b87c0739f5142482ff25dd9ebd0499`)
- `paper_bencmark/highambench/tasks/P10/T1/faithfulness/agent_outputs/direct_judge.json` (`53353881f558fece65ac234d6309fcc6d3671f092676d5f080e8cf8549899d5d`)
- `paper_bencmark/highambench/tasks/P10/T1/faithfulness/agent_outputs/roundtrip_judge.json` (`2b0a0bd8b9fbf88f655d3757ea5e1f05dc82eb3f623fd264010543e7da755396`)
- `paper_bencmark/highambench/tasks/P10/T1/faithfulness/agent_outputs/source_contract.json` (`0551a84e4ed8684100212083ec66ba6d67bc2b9fba4a959ab89bde166bee1c73`)
- `paper_bencmark/highambench/tasks/P10/T1/faithfulness/decision.json` (`7aabee518ac5975eeb2d9405f8ed1a7bb97bdd193a7e5e065d15fae90177b4e0`)
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
- `paper_bencmark/highambench/tasks/P10/T1/faithfulness/history/20260821T193942Z/agent_outputs/adjudicator.json` (`1bc811edc48f1ddc9445a04242cd6bf0830c94ef5be45438f15d043a6f6f93b2`)
- `paper_bencmark/highambench/tasks/P10/T1/faithfulness/history/20260821T193942Z/agent_outputs/blind_translation.json` (`2149442f1888f0661cb4c9c5de8e033b66574adbd96375f7301a639466bcbd73`)
- `paper_bencmark/highambench/tasks/P10/T1/faithfulness/history/20260821T193942Z/agent_outputs/direct_judge.json` (`ca25bd6b7f065425badd8549b226656af73eacbddcd0a87410c524b9cf833660`)
- `paper_bencmark/highambench/tasks/P10/T1/faithfulness/history/20260821T193942Z/agent_outputs/roundtrip_judge.json` (`a16d77916ace64469f5e8eb7b85518f10e6b3b2a2509fb8359d6439915b95bc1`)
- `paper_bencmark/highambench/tasks/P10/T1/faithfulness/history/20260821T193942Z/agent_outputs/source_contract.json` (`78af795e5b4eb407effe9e95b33a8c1fd6258e1fbfda6d3ebd05a4d373998dc4`)
- `paper_bencmark/highambench/tasks/P10/T1/faithfulness/history/20260821T193942Z/decision.json` (`d9d0e21059297ed0bc51e0a34888170a78748d31534e2ad4e9811fca9003d858`)
- `paper_bencmark/highambench/tasks/P10/T1/faithfulness/history/20260821T193942Z/inputs/blind_dependency_inventory.json` (`41fd69351066c3bf3e2955c78439f177b4bc9eafa8139aa84c37e5dd0bb07c25`)
- `paper_bencmark/highambench/tasks/P10/T1/faithfulness/history/20260821T193942Z/inputs/blind_dossier.md` (`6449e625e49a3f065eed082644fb5555b5d3b216764294552ae5d40f53009a1a`)
- `paper_bencmark/highambench/tasks/P10/T1/faithfulness/history/20260821T193942Z/inputs/blind_review_packet.md` (`6449e625e49a3f065eed082644fb5555b5d3b216764294552ae5d40f53009a1a`)
- `paper_bencmark/highambench/tasks/P10/T1/faithfulness/history/20260821T193942Z/inputs/declaration_dossier.md` (`82a2633f16ae52fa058ae8fd11582542e8d14c6f6245114409bec7de2125ebc5`)
- `paper_bencmark/highambench/tasks/P10/T1/faithfulness/history/20260821T193942Z/inputs/dependency_inventory.json` (`8f280aa54e7755db10827abd8ad4643d67e8378b1727150dbc18c5ed06348c66`)
- `paper_bencmark/highambench/tasks/P10/T1/faithfulness/history/20260821T193942Z/inputs/direct_review_packet.md` (`135e6810027ec5423b8d1eb848842d4949a47414e52a6491d9eeb12e17f15b95`)
- `paper_bencmark/highambench/tasks/P10/T1/faithfulness/history/20260821T193942Z/inputs/source_locator.json` (`d8322c6fdbb9ff0df044f34a53d4c16c9d77770889baccf186ed83c90647815c`)
- `paper_bencmark/highambench/tasks/P10/T1/faithfulness/inputs/blind_dependency_inventory.json` (`da8d85e78c1f986699a314398cc646e47cb8ced36594b6d29bb80c93b21e33b7`)
- `paper_bencmark/highambench/tasks/P10/T1/faithfulness/inputs/blind_dossier.md` (`381b5d7219b3abe9cdabfe4cca9e53a6d255cfcac1bb45bf613276888f2811c3`)
- `paper_bencmark/highambench/tasks/P10/T1/faithfulness/inputs/blind_review_packet.md` (`381b5d7219b3abe9cdabfe4cca9e53a6d255cfcac1bb45bf613276888f2811c3`)
- `paper_bencmark/highambench/tasks/P10/T1/faithfulness/inputs/declaration_dossier.md` (`1dc4263d09048ab379c35e856807e12215b061f3220a0b22675a3b6b6ed42cba`)
- `paper_bencmark/highambench/tasks/P10/T1/faithfulness/inputs/dependency_inventory.json` (`e657d96e936187529f9e77cbc8c27b64760f3f9228e5e5f12d6e5c9947f01d19`)
- `paper_bencmark/highambench/tasks/P10/T1/faithfulness/inputs/direct_review_packet.md` (`76cc12c63b6dc5129717d867b72a9d9d0e48e3d2e02ace947ca85948259752da`)
- `paper_bencmark/highambench/tasks/P10/T1/faithfulness/inputs/source_locator.json` (`d8322c6fdbb9ff0df044f34a53d4c16c9d77770889baccf186ed83c90647815c`)
