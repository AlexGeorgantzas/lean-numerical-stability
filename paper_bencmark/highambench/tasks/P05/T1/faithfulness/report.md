# Faithfulness audit: P05-T1

- Classification: `faithful-stronger`
- Accepted as paper-faithful: `true`
- Adjudicated: `true`
- Target SHA-256: `7d141c775e8cb9b8d52eb75c7b96b3aa91647bd2b151af9326866be74731eb2b`
- Paper SHA-256: `dd8b525c0eabc509a68b325ee5008cf6f1d4ef262bef8ba54e1947fe3cdb3db6`

## Decision

All paper executions are represented with the same algorithm, identities, constants, exceptional-value assumptions, and k=m+1 indexing. The protected trace and inherited fields are derivable for those executions, so the declaration loses no source applicability. However, D011 is not merely a presentation of standard formats: its one-way representability law and abstract safeRange admit inhabited inexact runs violating a rounding property explicitly asserted by the PDF. The Lean claim therefore properly extends the paper theorem, giving Lean-implies-paper yes, paper-implies-Lean no, and classification faithful-stronger.

## Implications

- **Lean implies paper:** `yes`. For every paper execution, set m=k-1, instantiate D011 with its standard format, encode its permutation and binary summation tree, and construct the protected trace from equation (2.4) along the c-to-root path. D010 then records the same numerator and final division, and the target yields exactly the paper's ku and (k-1)u conclusions.
- **Paper implies lean:** `no`. The paper quantifies only over its standard IEEE-like formats. D011 also admits certified formats such as the inhabited radix-2 example above, whose safe rounding 3/2 to 2 violates the paper's equation (2.1a) and cannot occur in the corresponding standard precision-2 format. The paper therefore does not establish the full universal declaration.

## Findings

- **note / format-domain-generalization:** The declaration has genuine additional applicability, so equivalence would understate its strength.
- **note / protected-trace-certificate:** The certificate is source-derivable and noncircular; it does not reduce coverage of paper executions.
- **note / edge-indexing:** Allowing m=0 introduces no unintended case.

## Semantic checklist

| Check | Direct | Round-trip |
|---|---|---|
| `S01` | `pass` | `pass` |
| `S02` | `pass` | `pass` |
| `S03` | `pass` | `pass` |
| `S04` | `pass` | `pass` |
| `S05` | `pass` | `pass` |
| `S06` | `pass` | `pass` |
| `S07` | `pass` | `pass` |
| `S08` | `pass` | `pass` |
| `S09` | `pass` | `pass` |
| `S10` | `pass` | `pass` |
| `S11` | `pass` | `fail` |
| `S12` | `pass` | `pass` |
| `S13` | `pass` | `pass` |
| `S14` | `pass` | `pass` |
| `S15` | `pass` | `pass` |
| `S16` | `pass` | `pass` |

## Dependency coverage

- Blind translator covered `118` dependencies (`0` hash-reused meanings); unclear: `none`.
- Direct judge covered `118` dependencies (`0` hash-reused interpretations); failing or unclear: `none`.

## Remaining uncertainties

No remaining uncertainties were recorded.

## Audit artifacts

- `paper_bencmark/highambench/tasks/P05/T1/faithfulness/agent_outputs/adjudicator.json` (`87f03538c676975f517899198277dcdad137b2d341c07a140317d3ad791e6c11`)
- `paper_bencmark/highambench/tasks/P05/T1/faithfulness/agent_outputs/blind_translation.json` (`79231c0ca28f69e20dd920bc364f2542653634c7a9d4624114c16bd247ef6ab0`)
- `paper_bencmark/highambench/tasks/P05/T1/faithfulness/agent_outputs/direct_judge.json` (`0c80ce737ed9bd71f4e9b0353a6caa2e1ca6cb8c29ce94b45a7bc18907953aa7`)
- `paper_bencmark/highambench/tasks/P05/T1/faithfulness/agent_outputs/roundtrip_judge.json` (`77629a5c0114805d7bc0032a00b1c10fcf6b6e542ba9c9aca70535c88a5297cb`)
- `paper_bencmark/highambench/tasks/P05/T1/faithfulness/agent_outputs/source_contract.json` (`e716ea67eb0de9ed93ef7afcfbbeae1ebea9ac652dd26b0541eca3c799244569`)
- `paper_bencmark/highambench/tasks/P05/T1/faithfulness/decision.json` (`f17c484fc85c992206cd3af562c50c9a1a4072d009f322580d4ac0d655d1ff59`)
- `paper_bencmark/highambench/tasks/P05/T1/faithfulness/history/20260814T162125Z/agent_outputs/blind_translation.json` (`05208189ac745fdf59e4d42742f60e3f4913ce4828338550052100f796b62497`)
- `paper_bencmark/highambench/tasks/P05/T1/faithfulness/history/20260814T162125Z/agent_outputs/direct_judge.json` (`1c8317016360b1946ba18ad934401e2e4c55467ce8ab4b21c62c04dd07e39349`)
- `paper_bencmark/highambench/tasks/P05/T1/faithfulness/history/20260814T162125Z/agent_outputs/paper_source_contract.json` (`90bcb3f32112e46567a1fde6c0c742ef1d157d1829c1eb2b2cb5ebb4d58d4c1d`)
- `paper_bencmark/highambench/tasks/P05/T1/faithfulness/history/20260814T162125Z/agent_outputs/roundtrip_judge.json` (`87d28a54fc8428f376f6acfc8ead1ef77140b9a65e4d5366b01fd69d90b86278`)
- `paper_bencmark/highambench/tasks/P05/T1/faithfulness/history/20260814T162125Z/agent_outputs/source_contract.json` (`11d8619c966e9dfddf63c80cb311da3c474db4e245ea5b25e17b3d9d1e62250d`)
- `paper_bencmark/highambench/tasks/P05/T1/faithfulness/history/20260814T162125Z/decision.json` (`21329756740e0fd7b2c750dc3b54d3151815dffbf815e124da600b35f75c31b1`)
- `paper_bencmark/highambench/tasks/P05/T1/faithfulness/history/20260814T162125Z/inputs/blind_dependency_inventory.json` (`a82223c2956ced080c44d63e602bf5bcc97ac72d70aba51d9adc0bce549d5868`)
- `paper_bencmark/highambench/tasks/P05/T1/faithfulness/history/20260814T162125Z/inputs/blind_dossier.md` (`dea1dfb802bb0ac29df718b16a78b07401973d3b517d6dc07ebf6424dd085528`)
- `paper_bencmark/highambench/tasks/P05/T1/faithfulness/history/20260814T162125Z/inputs/blind_review_packet.md` (`dea1dfb802bb0ac29df718b16a78b07401973d3b517d6dc07ebf6424dd085528`)
- `paper_bencmark/highambench/tasks/P05/T1/faithfulness/history/20260814T162125Z/inputs/declaration_dossier.md` (`f6a4a88b553ed06db46519962fcf2f7638d72b34ed60a71f6c78c473d69747ea`)
- `paper_bencmark/highambench/tasks/P05/T1/faithfulness/history/20260814T162125Z/inputs/dependency_inventory.json` (`d1341023c6aed372538f3140646341eb085bd7d641a2f587758efc94fe58951f`)
- `paper_bencmark/highambench/tasks/P05/T1/faithfulness/history/20260814T162125Z/inputs/direct_review_packet.md` (`2655aad3e60f6016b0d840eca3eaae82ec8e1c4a74c4b3c3f73356a7aa940ded`)
- `paper_bencmark/highambench/tasks/P05/T1/faithfulness/history/20260814T162125Z/inputs/paper_source_locator.json` (`417f8e6a6ff934c35d3c2379d9faefe1c21d44b1f14a69f7674c0ef303123327`)
- `paper_bencmark/highambench/tasks/P05/T1/faithfulness/history/20260814T162125Z/inputs/source_locator.json` (`ec02206ad77a57f53e7301f350edb6fef3d9312f97956e4bb423c0001dfe8219`)
- `paper_bencmark/highambench/tasks/P05/T1/faithfulness/history/20260814T164732Z/agent_outputs/adjudicator.json` (`35a55c96398ffec57029701a7d5c7c9705a6c69d62f2780b1381ddbe66326ce6`)
- `paper_bencmark/highambench/tasks/P05/T1/faithfulness/history/20260814T164732Z/agent_outputs/blind_translation.json` (`e2055e56c0ecfcdd7c59b2d7dcbd28290eddcdd6b718aa40c3b3f18a90297da8`)
- `paper_bencmark/highambench/tasks/P05/T1/faithfulness/history/20260814T164732Z/agent_outputs/direct_judge.json` (`ff283e5d6978d52d6e3f8207dbba88697fd112bfdf684ce99bf29435303cc42e`)
- `paper_bencmark/highambench/tasks/P05/T1/faithfulness/history/20260814T164732Z/agent_outputs/roundtrip_judge.json` (`29faff768105309670eba51ba3d90de02cbf68144cf8d65148822b9802142ee6`)
- `paper_bencmark/highambench/tasks/P05/T1/faithfulness/history/20260814T164732Z/agent_outputs/source_contract.json` (`307d78f0c768d1ab183ba9cda9583649e53c58f62f1ca1599724bda9d2b2e707`)
- `paper_bencmark/highambench/tasks/P05/T1/faithfulness/history/20260814T164732Z/decision.json` (`350965c331ce4235b30a4c5a3a1bcd26100fe9a455eb1d4713c44da545037c84`)
- `paper_bencmark/highambench/tasks/P05/T1/faithfulness/history/20260814T164732Z/inputs/blind_dependency_inventory.json` (`c4b8e4cbcea5756ce4393cbcc5d5c54dce079c71deb65d99a77062f30b3decb9`)
- `paper_bencmark/highambench/tasks/P05/T1/faithfulness/history/20260814T164732Z/inputs/blind_dossier.md` (`36054541a44c03f74e8f20185d744fea0cd15b74cb0df6ee9bcae1b1745263cc`)
- `paper_bencmark/highambench/tasks/P05/T1/faithfulness/history/20260814T164732Z/inputs/blind_review_packet.md` (`36054541a44c03f74e8f20185d744fea0cd15b74cb0df6ee9bcae1b1745263cc`)
- `paper_bencmark/highambench/tasks/P05/T1/faithfulness/history/20260814T164732Z/inputs/declaration_dossier.md` (`40cd4b82f349f01de5370d46c1281bc75826cdf2f677aee2ce7c53b8890fb539`)
- `paper_bencmark/highambench/tasks/P05/T1/faithfulness/history/20260814T164732Z/inputs/dependency_inventory.json` (`115272009c83978c8abf225328e61e5c4235575365e7695854292155bb5e306f`)
- `paper_bencmark/highambench/tasks/P05/T1/faithfulness/history/20260814T164732Z/inputs/direct_review_packet.md` (`5f2086bfc273a469f7fb5b69073af359b442890abd54020bc3941216a743b3d2`)
- `paper_bencmark/highambench/tasks/P05/T1/faithfulness/history/20260814T164732Z/inputs/source_locator.json` (`5fc435baaab8e18bc83731da27d1c75611cbc602e54e49e702b619356e2aca6e`)
- `paper_bencmark/highambench/tasks/P05/T1/faithfulness/history/20260821T143253Z/agent_outputs/adjudicator.json` (`35a55c96398ffec57029701a7d5c7c9705a6c69d62f2780b1381ddbe66326ce6`)
- `paper_bencmark/highambench/tasks/P05/T1/faithfulness/history/20260821T143253Z/agent_outputs/blind_translation.json` (`e2055e56c0ecfcdd7c59b2d7dcbd28290eddcdd6b718aa40c3b3f18a90297da8`)
- `paper_bencmark/highambench/tasks/P05/T1/faithfulness/history/20260821T143253Z/agent_outputs/direct_judge.json` (`ff283e5d6978d52d6e3f8207dbba88697fd112bfdf684ce99bf29435303cc42e`)
- `paper_bencmark/highambench/tasks/P05/T1/faithfulness/history/20260821T143253Z/agent_outputs/roundtrip_judge.json` (`29faff768105309670eba51ba3d90de02cbf68144cf8d65148822b9802142ee6`)
- `paper_bencmark/highambench/tasks/P05/T1/faithfulness/history/20260821T143253Z/agent_outputs/source_contract.json` (`307d78f0c768d1ab183ba9cda9583649e53c58f62f1ca1599724bda9d2b2e707`)
- `paper_bencmark/highambench/tasks/P05/T1/faithfulness/history/20260821T143253Z/decision.json` (`c9fe08a1c79ad26b0d0431e9da4e9ab66dd2803c699dfee3c6195a579c0a5fcf`)
- `paper_bencmark/highambench/tasks/P05/T1/faithfulness/history/20260821T143253Z/inputs/blind_dependency_inventory.json` (`c4b8e4cbcea5756ce4393cbcc5d5c54dce079c71deb65d99a77062f30b3decb9`)
- `paper_bencmark/highambench/tasks/P05/T1/faithfulness/history/20260821T143253Z/inputs/blind_dossier.md` (`36054541a44c03f74e8f20185d744fea0cd15b74cb0df6ee9bcae1b1745263cc`)
- `paper_bencmark/highambench/tasks/P05/T1/faithfulness/history/20260821T143253Z/inputs/blind_review_packet.md` (`36054541a44c03f74e8f20185d744fea0cd15b74cb0df6ee9bcae1b1745263cc`)
- `paper_bencmark/highambench/tasks/P05/T1/faithfulness/history/20260821T143253Z/inputs/declaration_dossier.md` (`13edcf44d3625c4bb7a22ea5b36a39b6cc9650fc152c67ef4b02d14026296038`)
- `paper_bencmark/highambench/tasks/P05/T1/faithfulness/history/20260821T143253Z/inputs/dependency_inventory.json` (`115272009c83978c8abf225328e61e5c4235575365e7695854292155bb5e306f`)
- `paper_bencmark/highambench/tasks/P05/T1/faithfulness/history/20260821T143253Z/inputs/direct_review_packet.md` (`5f2086bfc273a469f7fb5b69073af359b442890abd54020bc3941216a743b3d2`)
- `paper_bencmark/highambench/tasks/P05/T1/faithfulness/history/20260821T143253Z/inputs/source_locator.json` (`5fc435baaab8e18bc83731da27d1c75611cbc602e54e49e702b619356e2aca6e`)
- `paper_bencmark/highambench/tasks/P05/T1/faithfulness/inputs/blind_dependency_inventory.json` (`1e819471c3b745260d8b979b525dee65bf941743e0f70f466f422aa6ea340831`)
- `paper_bencmark/highambench/tasks/P05/T1/faithfulness/inputs/blind_dossier.md` (`5b765926ff292b7bd6c4a5fe8dca402fde970c81aed62e068244f8db87ccc9e5`)
- `paper_bencmark/highambench/tasks/P05/T1/faithfulness/inputs/blind_review_packet.md` (`5b765926ff292b7bd6c4a5fe8dca402fde970c81aed62e068244f8db87ccc9e5`)
- `paper_bencmark/highambench/tasks/P05/T1/faithfulness/inputs/declaration_dossier.md` (`336d6fc2db214c05211dc7ec1ae177cbe45cdcbf5b43d7185a58d82cb440b13c`)
- `paper_bencmark/highambench/tasks/P05/T1/faithfulness/inputs/dependency_inventory.json` (`f27351e08ecf54bc2b2aed4492a108ba3473ec06523697fa7769f72aacea5b9b`)
- `paper_bencmark/highambench/tasks/P05/T1/faithfulness/inputs/direct_review_packet.md` (`7a9871f8b454e1dc21393ff5ed4ebef1bf86cad7eb18fa94954b0884ab390a05`)
- `paper_bencmark/highambench/tasks/P05/T1/faithfulness/inputs/source_locator.json` (`5fc435baaab8e18bc83731da27d1c75611cbc602e54e49e702b619356e2aca6e`)
