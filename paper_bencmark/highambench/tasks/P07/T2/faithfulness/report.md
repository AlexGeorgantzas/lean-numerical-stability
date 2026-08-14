# Faithfulness audit: P07-T2

- Classification: `not-faithful-weaker`
- Accepted as paper-faithful: `false`
- Adjudicated: `true`
- Target SHA-256: `6c74a35b9ccd229e305dde38e11b1e247bee8bef50a42a127e0a5bd8f977371a`
- Paper SHA-256: `4c4d638b359719f47e2c4664a50e9fa8e4704e8b6b39923d73c41883a97c5790`

## Decision

P07-T2 selects the local construction beginning with equation (3.9) and ending with the immediate product-error budget on printed page 920. The declaration faithfully preserves the dimensions, algorithm linkage, exact four-term DeltaA, cross term, gamma_n denominator, inverse-pseudoinverse composition, and immediate spectral bound; it need not include the later 6.04/2.01 specialization. D022 also correctly formalizes the paper's general exact-minimizer backward-error notion. Nevertheless, the selected passage explicitly claims stronger perturbed-solution relations. Neither original full rank nor triangular-factor invertibility supplies perturbed full rank, and equation (3.9) supplies no range condition or smallness bound. Thus the paper passage implies the Lean declaration, but the Lean declaration does not imply either explicit paper formulation. The result is not-faithful-weaker.

## Implications

- **Lean implies paper:** `no`. The Lean conclusions ensure exact least-squares minimization but do not ensure b_tilde lies in range(A_tilde) or that A_tilde has full column rank. Consequently they imply neither A_tilde xHat=b_tilde nor xHat=A_tilde^dagger b_tilde. This gap can occur in satisfiable runs because DeltaYHat is unrestricted and may destroy rank.
- **Paper implies lean:** `yes`. Either explicit paper solution relation implies the normal equation. The page-920 proof also supplies the inverse-pseudoinverse composition, the exact four-term DeltaA expansion yielding A_tilde=Y_tilde R_tilde, and exactly the immediate operator-norm budget asserted by Lean.

## Findings

- **major / perturbed-solution-relation:** Lean preserves exact minimization but loses genuine solution strength, making Lean-implies-paper false.
- **note / selected-result-scope:** The missing specialized bound and global conditioning thresholds are outside P07-T2's selected local result and do not contribute to the negative classification.
- **note / least-squares-error-notion:** The declaration uses the correct least-squares error notion; its defect is conclusion strength rather than use of an incorrect norm or error concept.
- **note / ideal-arithmetic-model:** The absence of overflow, underflow, subnormal, NaN, and infinity behavior is an inherited modeling convention, not a task-specific mismatch.

## Semantic checklist

| Check | Direct | Round-trip |
|---|---|---|
| `S01` | `pass` | `pass` |
| `S02` | `pass` | `pass` |
| `S03` | `pass` | `pass` |
| `S04` | `pass` | `pass` |
| `S05` | `unclear` | `unclear` |
| `S06` | `pass` | `pass` |
| `S07` | `pass` | `pass` |
| `S08` | `pass` | `pass` |
| `S09` | `pass` | `pass` |
| `S10` | `pass` | `pass` |
| `S11` | `pass` | `unclear` |
| `S12` | `unclear` | `unclear` |
| `S13` | `pass` | `unclear` |
| `S14` | `pass` | `pass` |
| `S15` | `pass` | `pass` |
| `S16` | `pass` | `pass` |

## Dependency coverage

- Blind translator covered `137` dependencies (`0` hash-reused meanings); unclear: `none`.
- Direct judge covered `137` dependencies (`0` hash-reused interpretations); failing or unclear: `D022`.

## Remaining uncertainties

- The PDF does not resolve whether the theorem-text residual-zero equation or the proof's Moore-Penrose identity was authorially intended. This uncertainty does not affect the classification because both strictly imply the Lean normal equation, while the stated assumptions make neither recoverable from it.

## Audit artifacts

- `paper_bencmark/highambench/tasks/P07/T2/faithfulness/agent_outputs/adjudicator.json` (`7dc0f29faa369015014a6eacd7dfcdf08333b3edb0f2494a6e1470e8f9054dd8`)
- `paper_bencmark/highambench/tasks/P07/T2/faithfulness/agent_outputs/blind_translation.json` (`16f52a2f0f6effb92e75a0278f4f0a6dbd3d816cbe175544c5eb325203aa751c`)
- `paper_bencmark/highambench/tasks/P07/T2/faithfulness/agent_outputs/direct_judge.json` (`6ab36fc5502c95dec570a8f365c76f07cc4333694006678e1be7b5e4ffd5802d`)
- `paper_bencmark/highambench/tasks/P07/T2/faithfulness/agent_outputs/roundtrip_judge.json` (`e024fe7c9b43713e3ac6859f9a0379a1d6073cbc2ff9866d3276c97771c1909c`)
- `paper_bencmark/highambench/tasks/P07/T2/faithfulness/agent_outputs/source_contract.json` (`4a8e492b18b6cc12db7516ce8b94c15ca1a7ed05bffbae23f585fa3e5d9f8864`)
- `paper_bencmark/highambench/tasks/P07/T2/faithfulness/decision.json` (`94c1d8c95bf7a2d44d1f268ec437d813b27f650293e90028e8c28e2bbd1cf7cb`)
- `paper_bencmark/highambench/tasks/P07/T2/faithfulness/history/20260814T224133Z/agent_outputs/blind_translation.json` (`4419a27f0023ea41a685df98c525098c60d3ff4bb9a5df0ba7488f915d7e6023`)
- `paper_bencmark/highambench/tasks/P07/T2/faithfulness/history/20260814T224133Z/agent_outputs/direct_judge.json` (`ea43746423de16117c76f3ec68fecad35f259ce984cd1e1ed78218d11c4543c1`)
- `paper_bencmark/highambench/tasks/P07/T2/faithfulness/history/20260814T224133Z/agent_outputs/paper_source_contract.json` (`822fe7aa06960deeaa078b8ac855714c9b957ac1656f37de3dcbbaa9f707f076`)
- `paper_bencmark/highambench/tasks/P07/T2/faithfulness/history/20260814T224133Z/agent_outputs/roundtrip_judge.json` (`d3c11bdc6a32f3108b2d311ebbb6ecc006d88ac6d8402359bbfeef9d238e8bba`)
- `paper_bencmark/highambench/tasks/P07/T2/faithfulness/history/20260814T224133Z/agent_outputs/source_contract.json` (`1bcc5e94a23bb69e728ff4e577c93cd4130d27f5755ece1f9345b02ca4a72304`)
- `paper_bencmark/highambench/tasks/P07/T2/faithfulness/history/20260814T224133Z/decision.json` (`28091ab0f44cd379da5456e27fa6385f9cf0f19f0538ad5acdc8c92b2805b41f`)
- `paper_bencmark/highambench/tasks/P07/T2/faithfulness/history/20260814T224133Z/inputs/blind_dependency_inventory.json` (`8e59316251b3a76a0e84968517286166c62607b9dfa189779e28e465989a4351`)
- `paper_bencmark/highambench/tasks/P07/T2/faithfulness/history/20260814T224133Z/inputs/blind_dossier.md` (`0eca6fe917dec5f3c7d8bbd77124abb1d9d9dbaa468e2da59011882beb385de6`)
- `paper_bencmark/highambench/tasks/P07/T2/faithfulness/history/20260814T224133Z/inputs/blind_review_packet.md` (`0eca6fe917dec5f3c7d8bbd77124abb1d9d9dbaa468e2da59011882beb385de6`)
- `paper_bencmark/highambench/tasks/P07/T2/faithfulness/history/20260814T224133Z/inputs/declaration_dossier.md` (`c372a4c8a39bcc551628bc454b9a23bebed16051daaf4734ceaf00f3392720b4`)
- `paper_bencmark/highambench/tasks/P07/T2/faithfulness/history/20260814T224133Z/inputs/dependency_inventory.json` (`9e47a454e718b829e8be3fc71b3f5dfcf0c85ad788c9d8a821c187443f07abbc`)
- `paper_bencmark/highambench/tasks/P07/T2/faithfulness/history/20260814T224133Z/inputs/dependency_reuse_direct.json` (`6830f809f9f25d4db4cafdb4180648c188b97338a0f35362b6d78cc7c250eb22`)
- `paper_bencmark/highambench/tasks/P07/T2/faithfulness/history/20260814T224133Z/inputs/direct_review_packet.md` (`483fd7812562ba6afecb548b0204d376788c3b9986e115aced1ad936fb2a3737`)
- `paper_bencmark/highambench/tasks/P07/T2/faithfulness/history/20260814T224133Z/inputs/paper_source_locator.json` (`7d16e3f6a7585561fffc335fcd99a77aec72a33a336198eca2c59fb9113440a2`)
- `paper_bencmark/highambench/tasks/P07/T2/faithfulness/history/20260814T224133Z/inputs/source_locator.json` (`734421773b0a7d87f3085855d3716d0ee0bad2446623b069f04e21cd2e82d17b`)
- `paper_bencmark/highambench/tasks/P07/T2/faithfulness/inputs/blind_dependency_inventory.json` (`091701614bb759a76a16d9734b35c224e2ecadaeb5f64e258d3ed33b39a4728d`)
- `paper_bencmark/highambench/tasks/P07/T2/faithfulness/inputs/blind_dossier.md` (`ad1b9bcf26c22644b67e0f4967e8ef7473f25840b43f4cd1dc2d16935c5e28bd`)
- `paper_bencmark/highambench/tasks/P07/T2/faithfulness/inputs/blind_review_packet.md` (`ad1b9bcf26c22644b67e0f4967e8ef7473f25840b43f4cd1dc2d16935c5e28bd`)
- `paper_bencmark/highambench/tasks/P07/T2/faithfulness/inputs/declaration_dossier.md` (`84c49c0a2e2ce35cfe5ebd90299bb5f925777ecefbd07a1d5960cbe9d52ca7b8`)
- `paper_bencmark/highambench/tasks/P07/T2/faithfulness/inputs/dependency_inventory.json` (`ccb7ef546cc9543fe80e91e57c40177117fffec683bc2807149f837b68228530`)
- `paper_bencmark/highambench/tasks/P07/T2/faithfulness/inputs/direct_review_packet.md` (`f299fb575eb664dc2797125be847814abc7ff6b2ca351e0e8ff28a1ace1b3df1`)
- `paper_bencmark/highambench/tasks/P07/T2/faithfulness/inputs/source_locator.json` (`fb570ee3206baef8b00a06d25f75f028684da29b8079808e62530dc266200b30`)
