# Faithfulness audit: P09-T3

- Classification: `not-faithful-weaker`
- Accepted as paper-faithful: `false`
- Adjudicated: `true`
- Target SHA-256: `5b5fcb7203bb05b41b1270924ef4803f5f7e18396775dbe27b10d8f4943b0f4b`
- Paper SHA-256: `9076fe377cc64878a4a10f8a47ff49245bc5acaf116ffbd8e2ccca57033da758`

## Decision

The Lean declaration faithfully preserves the product-indexed complex transform, positive unnormalized Fourier phase, nested coordinate order, relative RMS forward-error notion, factorization-dependent K constants, and a standard quantified form of the O(epsilon^2) remainder. The decisive mismatch is axisBounds: it assumes the propagated local asymptotic estimates that the paper derives from Theorem 1 and equations (4.3)-(4.4). Consequently the paper result entails the restricted Lean conclusion, but the Lean theorem does not establish the paper result from its stated primitive hypotheses, so the declaration is not-faithful-weaker.

## Implications

- **Lean implies paper:** `no`. The Lean statement supplies no construction of axisBounds from the primitive arithmetic, trigonometric, algorithmic, and exact-input assumptions. It therefore proves the global bound only for already-certified families and cannot entail the paper's broader Theorem 2(a).
- **Paper implies lean:** `yes`. For each fixed Lean plan and family in the source domain, the paper's Theorem 2(a), under its standard fixed-instance O(epsilon^2) meaning, gives the same relative RMS conclusion. The positive phase matches, while axisBounds, the positive denominator, and the plan-domain conditions only restrict the cases to which the Lean proposition applies.

## Findings

- **major / added-theorem-derived-premise:** A substantive portion of the selected theorem's analysis is assumed rather than derived, so the Lean theorem has strictly reduced applicability.
- **minor / degenerate-domain-restriction:** Potential degenerate source cases are excluded; this reinforces the weaker classification but does not alter the numerical conclusion.
- **note / ratio-domain-explication:** This makes the relative expression well-defined and is not nonvacuous mathematical strengthening of the paper's bound.

## Semantic checklist

| Check | Direct | Round-trip |
|---|---|---|
| `S01` | `pass` | `pass` |
| `S02` | `pass` | `pass` |
| `S03` | `pass` | `unclear` |
| `S04` | `fail` | `fail` |
| `S05` | `pass` | `pass` |
| `S06` | `pass` | `unclear` |
| `S07` | `pass` | `pass` |
| `S08` | `pass` | `pass` |
| `S09` | `pass` | `pass` |
| `S10` | `pass` | `pass` |
| `S11` | `pass` | `pass` |
| `S12` | `pass` | `fail` |
| `S13` | `pass` | `pass` |
| `S14` | `pass` | `unclear` |
| `S15` | `pass` | `unclear` |
| `S16` | `pass` | `pass` |

## Dependency coverage

- Blind translator covered `264` dependencies (`0` hash-reused meanings); unclear: `none`.
- Direct judge covered `264` dependencies (`0` hash-reused interpretations); failing or unclear: `D005, D019`.

## Remaining uncertainties

- The paper does not expressly settle whether a coordinate of length one or a radix factor one is admissible. Lean's nonempty stages with radices at least two exclude such cases, but this uncertainty cannot reverse the implication directions because it only concerns cases outside the Lean domain.

## Audit artifacts

- `paper_bencmark/highambench/tasks/P09/T3/faithfulness/agent_outputs/adjudicator.json` (`922b522249158ad2189acac29e18772259d6bc28acdecc7d683b88fcf485077e`)
- `paper_bencmark/highambench/tasks/P09/T3/faithfulness/agent_outputs/blind_translation.json` (`6a2c37055a5fd9cfb4e0009c1850f47891f85c8c004bdfaf53fa71cfe34fd7c8`)
- `paper_bencmark/highambench/tasks/P09/T3/faithfulness/agent_outputs/direct_judge.json` (`fbbeaa87919aeb85d1e5c781c4d0c7aa912f14b8c1f863f597a61dd827de853f`)
- `paper_bencmark/highambench/tasks/P09/T3/faithfulness/agent_outputs/roundtrip_judge.json` (`83ae9fbc62ba54d1b1b849d7f24046fad12e9b3dbf014eda2e9774fbafcd2f6b`)
- `paper_bencmark/highambench/tasks/P09/T3/faithfulness/agent_outputs/source_contract.json` (`93b78c9ecbec460b9e11d9ecd068529a0b9d74650e6013151036d4ce9ad5985e`)
- `paper_bencmark/highambench/tasks/P09/T3/faithfulness/decision.json` (`e7b346630d11bff50a6b697da1812d1cd0558d95698e34b6b7391682edf2d4d0`)
- `paper_bencmark/highambench/tasks/P09/T3/faithfulness/history/20260815T052751Z/agent_outputs/blind_translation.json` (`a13dee089b0902650277ab595f3dd6019deccc8ca22efc166fd9b39b66d749ce`)
- `paper_bencmark/highambench/tasks/P09/T3/faithfulness/history/20260815T052751Z/agent_outputs/direct_judge.json` (`a351fdf7f66a9e58b4e57f33f50a761bf0fb8ccc797816aba2a4fdbc11103929`)
- `paper_bencmark/highambench/tasks/P09/T3/faithfulness/history/20260815T052751Z/agent_outputs/paper_source_contract.json` (`348db3c4cffe4770d8510e9fec47ccdab62bf40c19935e431854786ba7f44db4`)
- `paper_bencmark/highambench/tasks/P09/T3/faithfulness/history/20260815T052751Z/agent_outputs/roundtrip_judge.json` (`de224336dcae540e54f98bd8b38ea3c19daa2d23dc9384c7534f80afbcdb2bc3`)
- `paper_bencmark/highambench/tasks/P09/T3/faithfulness/history/20260815T052751Z/agent_outputs/source_contract.json` (`a0842a6fb4aa1e4a05e65a879405b31185241d2fdf518de57717b6c71f4059d9`)
- `paper_bencmark/highambench/tasks/P09/T3/faithfulness/history/20260815T052751Z/decision.json` (`b10edff420dba69191a1207e72c5e464cccb337889770d6a5cbdb1a3a0e44d0d`)
- `paper_bencmark/highambench/tasks/P09/T3/faithfulness/history/20260815T052751Z/inputs/blind_dependency_inventory.json` (`607c72b3224eedc6e3d6155183b494a1a4ba8ec5f9e6e3c1bf06b7d692ead238`)
- `paper_bencmark/highambench/tasks/P09/T3/faithfulness/history/20260815T052751Z/inputs/blind_dossier.md` (`b9d6488561612d8cca4deb16990f43df2e0e89cd953a16403a63fa1bbc736dbc`)
- `paper_bencmark/highambench/tasks/P09/T3/faithfulness/history/20260815T052751Z/inputs/blind_review_packet.md` (`b9d6488561612d8cca4deb16990f43df2e0e89cd953a16403a63fa1bbc736dbc`)
- `paper_bencmark/highambench/tasks/P09/T3/faithfulness/history/20260815T052751Z/inputs/declaration_dossier.md` (`d9cbe66545e0f96392762a57802bb786c6d02214b9b31140ea5c7570abb1c90b`)
- `paper_bencmark/highambench/tasks/P09/T3/faithfulness/history/20260815T052751Z/inputs/dependency_inventory.json` (`854f820cb042f0e08f49796f454492cd74109c201aaa57f896420a4bf49c979f`)
- `paper_bencmark/highambench/tasks/P09/T3/faithfulness/history/20260815T052751Z/inputs/dependency_reuse_direct.json` (`d0fffa09c078ca35b0b7c80cca730983bd4e235ceeb4f871bf7e930ee8ff0ca6`)
- `paper_bencmark/highambench/tasks/P09/T3/faithfulness/history/20260815T052751Z/inputs/direct_review_packet.md` (`2862d383d371da3e648a939a508f25d0b4ae69015a9a91d488f5b5a413811d64`)
- `paper_bencmark/highambench/tasks/P09/T3/faithfulness/history/20260815T052751Z/inputs/paper_source_locator.json` (`f236078d56116000664fec27c570812daeb11eb5024aaf78838800ecc07f8a13`)
- `paper_bencmark/highambench/tasks/P09/T3/faithfulness/history/20260815T052751Z/inputs/source_locator.json` (`b9c0b17cf2754d89c505af7c2ab51f4d30c7df14ab3f31a6fad0861ce6d98bcb`)
- `paper_bencmark/highambench/tasks/P09/T3/faithfulness/history/20260821T185434Z/agent_outputs/adjudicator.json` (`8cc5bd9c424f7bce62b1b97d3e404a5ed362d71063ad449088b62fcb1d5c75cf`)
- `paper_bencmark/highambench/tasks/P09/T3/faithfulness/history/20260821T185434Z/agent_outputs/blind_translation.json` (`ec70416b1f970279730b3b611c82f884512c14833fd254d3545a15d8bc23db03`)
- `paper_bencmark/highambench/tasks/P09/T3/faithfulness/history/20260821T185434Z/agent_outputs/direct_judge.json` (`7e757fcdf7fb33314421856562247d5c490211081066293aee958e8922cd3a04`)
- `paper_bencmark/highambench/tasks/P09/T3/faithfulness/history/20260821T185434Z/agent_outputs/roundtrip_judge.json` (`c58ab517eb5313d2ab65d0411230e566652840219a28b22919a61587da6bd653`)
- `paper_bencmark/highambench/tasks/P09/T3/faithfulness/history/20260821T185434Z/agent_outputs/source_contract.json` (`05bbe4302da98c31949f76b1e7c51bf44c0fcec6a9f1b593b694be7837443245`)
- `paper_bencmark/highambench/tasks/P09/T3/faithfulness/history/20260821T185434Z/decision.json` (`15d1c62953fc7d9e31025daca4cdbe59a43155a76b041747740f89747657a584`)
- `paper_bencmark/highambench/tasks/P09/T3/faithfulness/history/20260821T185434Z/inputs/blind_dependency_inventory.json` (`3d6047c608bbb86a109e10234ba0d1a654fa5a2233f054a62e556db2489f916a`)
- `paper_bencmark/highambench/tasks/P09/T3/faithfulness/history/20260821T185434Z/inputs/blind_dossier.md` (`15d0cd71a0097d60fa76b2554f222bec69acf82a3999c573a6e57058972c737f`)
- `paper_bencmark/highambench/tasks/P09/T3/faithfulness/history/20260821T185434Z/inputs/blind_review_packet.md` (`15d0cd71a0097d60fa76b2554f222bec69acf82a3999c573a6e57058972c737f`)
- `paper_bencmark/highambench/tasks/P09/T3/faithfulness/history/20260821T185434Z/inputs/declaration_dossier.md` (`27c786f4e984daafd9075621be641f4189bbc3f2c4f965571909a8e1aaee0851`)
- `paper_bencmark/highambench/tasks/P09/T3/faithfulness/history/20260821T185434Z/inputs/dependency_inventory.json` (`c72f2a9cac1ac3941cbfe494ebdc8b49a8641401eda8d8ef27a8b316518c09ff`)
- `paper_bencmark/highambench/tasks/P09/T3/faithfulness/history/20260821T185434Z/inputs/direct_review_packet.md` (`6d31d39c3e3459977d1c995625d0cf70178ac5810d4e29eb2562265b1a33b323`)
- `paper_bencmark/highambench/tasks/P09/T3/faithfulness/history/20260821T185434Z/inputs/source_locator.json` (`c6220ad13dc28740adfe1b8026a25df6ba99b548d6f3d38a9c1784932f6e0c5f`)
- `paper_bencmark/highambench/tasks/P09/T3/faithfulness/history/20260823T133306Z/agent_outputs/adjudicator.json` (`b3bab96445a56dda5bee6f2242f58d60544caa61c6fed1ba91c75348d9dc856d`)
- `paper_bencmark/highambench/tasks/P09/T3/faithfulness/history/20260823T133306Z/agent_outputs/blind_translation.json` (`39493d3d2c8bb17add5a1d27f82cc9771a65f658250886a14fe308f271422519`)
- `paper_bencmark/highambench/tasks/P09/T3/faithfulness/history/20260823T133306Z/agent_outputs/direct_judge.json` (`e43eae8d6c96a9257313913c299059580bc86db006b29b0615eb117196417229`)
- `paper_bencmark/highambench/tasks/P09/T3/faithfulness/history/20260823T133306Z/agent_outputs/roundtrip_judge.json` (`9282b7194a94922d98419ec3002e6400e2992d10fcf1a657906af123341b74c4`)
- `paper_bencmark/highambench/tasks/P09/T3/faithfulness/history/20260823T133306Z/agent_outputs/source_contract.json` (`5bfea8004a7b989685f888792130630a57ca050cb456cfb5d265d0eb7cf2791e`)
- `paper_bencmark/highambench/tasks/P09/T3/faithfulness/history/20260823T133306Z/decision.json` (`2ac0accac6d88b2eb8739bb531f3c524b5027128256b8c3d52b81ccf025a6cdc`)
- `paper_bencmark/highambench/tasks/P09/T3/faithfulness/history/20260823T133306Z/inputs/blind_dependency_inventory.json` (`efe6d80046477eaf2748d878158652f55f1dd6c5d31474fb21eec3ef750c4a3d`)
- `paper_bencmark/highambench/tasks/P09/T3/faithfulness/history/20260823T133306Z/inputs/blind_dossier.md` (`48ba4312d3310150301d58a9d1deaf872185ac7c8b02d4430e061d3a8116502e`)
- `paper_bencmark/highambench/tasks/P09/T3/faithfulness/history/20260823T133306Z/inputs/blind_review_packet.md` (`48ba4312d3310150301d58a9d1deaf872185ac7c8b02d4430e061d3a8116502e`)
- `paper_bencmark/highambench/tasks/P09/T3/faithfulness/history/20260823T133306Z/inputs/declaration_dossier.md` (`e49281007710aee3d04ac5ab65b33cc25aa0a3415832bf0acec8155f32ea6132`)
- `paper_bencmark/highambench/tasks/P09/T3/faithfulness/history/20260823T133306Z/inputs/dependency_inventory.json` (`8b0a121d2072a5f4bfa42592395e43f95671334fd55020714a48c4e157333a6c`)
- `paper_bencmark/highambench/tasks/P09/T3/faithfulness/history/20260823T133306Z/inputs/direct_review_packet.md` (`fa8b80cb98aa8f91f3b9d3217dd2cbd649eda6d6de2a64941dc5390f859f5857`)
- `paper_bencmark/highambench/tasks/P09/T3/faithfulness/history/20260823T133306Z/inputs/source_locator.json` (`6e0d56fffef27dc86e192c0ea7448d5a6816983611231c18e94c5ab8aaf6818e`)
- `paper_bencmark/highambench/tasks/P09/T3/faithfulness/inputs/blind_dependency_inventory.json` (`9f729f4b4f649e32f19c31be302f776036eea4beec7f1ed7a7b8dd5109842418`)
- `paper_bencmark/highambench/tasks/P09/T3/faithfulness/inputs/blind_dossier.md` (`4db03e7519d0ab43c22e0dd226f0fe9869216d8e9784daec3e5e9fd71d4d38c3`)
- `paper_bencmark/highambench/tasks/P09/T3/faithfulness/inputs/blind_review_packet.md` (`4db03e7519d0ab43c22e0dd226f0fe9869216d8e9784daec3e5e9fd71d4d38c3`)
- `paper_bencmark/highambench/tasks/P09/T3/faithfulness/inputs/declaration_dossier.md` (`c38f3286b459199c4b1369a5be0e90b5b343cf16c5f484a443f3b83d57590693`)
- `paper_bencmark/highambench/tasks/P09/T3/faithfulness/inputs/dependency_inventory.json` (`4112a4d349d3643b22395e39b804a333a2a19f5ee2bc9f66ac9c94fe0836858e`)
- `paper_bencmark/highambench/tasks/P09/T3/faithfulness/inputs/direct_review_packet.md` (`cbe5462518fc7fd203cd4d4cae40fdab8b1e8146ddea8af3ff73c752d089ac33`)
- `paper_bencmark/highambench/tasks/P09/T3/faithfulness/inputs/source_locator.json` (`6e0d56fffef27dc86e192c0ea7448d5a6816983611231c18e94c5ab8aaf6818e`)
