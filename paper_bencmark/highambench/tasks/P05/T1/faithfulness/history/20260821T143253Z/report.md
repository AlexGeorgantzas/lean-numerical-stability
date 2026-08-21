# Faithfulness audit: P05-T1

- Classification: `not-faithful-different`
- Accepted as paper-faithful: `false`
- Adjudicated: `true`
- Target SHA-256: `7d141c775e8cb9b8d52eb75c7b96b3aa91647bd2b151af9326866be74731eb2b`
- Paper SHA-256: `dd8b525c0eabc509a68b325ee5008cf6f1d4ef262bef8ba54e1947fe3cdb3db6`

## Decision

The displayed Lean conclusions faithfully reproduce Lemma 4.1 under k=m+1. The proposition as a whole does not. It assumes the weighted residual estimates that the paper derives from the floating-point execution, so it cannot by itself recover the paper theorem. Conversely, it ranges over abstract non-paper formats, so the selected paper result does not cover every Lean run. The residual premises make those extra cases algebraically provable but do not constitute a source-backed generalization of Lemma 4.1. Therefore both implications are no and the final classification is not-faithful-different.

## Implications

- **Lean implies paper:** `no`. A paper-admissible execution is not sufficient to apply the Lean theorem until the two residual estimates have been proved and inserted into P05Lemma41Run. Those estimates are precisely the substantive consequences of Theorem 3.1 and Corollary 3.2 omitted from the target, so the Lean proposition alone does not establish Lemma 4.1 for every paper execution.
- **Paper implies lean:** `no`. Lemma 4.1 covers the paper's concrete floating-point systems, whereas the Lean proposition quantifies over additional abstract formats and runs admitted by D011. The paper gives no universal theorem for those non-paper instances. That their residual premises independently imply the target by real algebra does not make the selected paper statement imply this broader algebraic theorem.

## Findings

- **critical / core-residual-result-assumed:** The target formalizes only the algebraic conversion of already-established residual bounds, not the paper's error theorem for the modeled computation.
- **major / mixed-quantifier-domain:** The opposing domain changes prevent implication in either direction and require not-faithful-different rather than not-faithful-weaker.
- **major / floating-point-model:** Some Lean runs have no corresponding paper execution, so the paper cannot establish the complete universally quantified Lean proposition.
- **note / conclusion-shape-and-nonvacuity:** The conclusion is accurately transcribed and the theorem is nonvacuous, but its analytical obligation has been replaced by an essentially equivalent premise.

## Semantic checklist

| Check | Direct | Round-trip |
|---|---|---|
| `S01` | `pass` | `pass` |
| `S02` | `pass` | `pass` |
| `S03` | `fail` | `fail` |
| `S04` | `fail` | `fail` |
| `S05` | `pass` | `fail` |
| `S06` | `fail` | `pass` |
| `S07` | `pass` | `pass` |
| `S08` | `fail` | `fail` |
| `S09` | `pass` | `pass` |
| `S10` | `pass` | `pass` |
| `S11` | `fail` | `fail` |
| `S12` | `fail` | `fail` |
| `S13` | `fail` | `pass` |
| `S14` | `pass` | `pass` |
| `S15` | `fail` | `fail` |
| `S16` | `fail` | `fail` |

## Dependency coverage

- Blind translator covered `104` dependencies (`0` hash-reused meanings); unclear: `none`.
- Direct judge covered `104` dependencies (`0` hash-reused interpretations); failing or unclear: `D002, D009, D010, D011, D012, D014, D018`.

## Remaining uncertainties

- The PDF does not define sign(0), so its intermediate assertion that every constructed coefficient has exactly |epsilon| is notation-dependent for zero-weight terms. This does not affect the required upper bounds, identities, implication decisions, or classification.

## Audit artifacts

- `paper_bencmark/highambench/tasks/P05/T1/faithfulness/agent_outputs/adjudicator.json` (`35a55c96398ffec57029701a7d5c7c9705a6c69d62f2780b1381ddbe66326ce6`)
- `paper_bencmark/highambench/tasks/P05/T1/faithfulness/agent_outputs/blind_translation.json` (`e2055e56c0ecfcdd7c59b2d7dcbd28290eddcdd6b718aa40c3b3f18a90297da8`)
- `paper_bencmark/highambench/tasks/P05/T1/faithfulness/agent_outputs/direct_judge.json` (`ff283e5d6978d52d6e3f8207dbba88697fd112bfdf684ce99bf29435303cc42e`)
- `paper_bencmark/highambench/tasks/P05/T1/faithfulness/agent_outputs/roundtrip_judge.json` (`29faff768105309670eba51ba3d90de02cbf68144cf8d65148822b9802142ee6`)
- `paper_bencmark/highambench/tasks/P05/T1/faithfulness/agent_outputs/source_contract.json` (`307d78f0c768d1ab183ba9cda9583649e53c58f62f1ca1599724bda9d2b2e707`)
- `paper_bencmark/highambench/tasks/P05/T1/faithfulness/decision.json` (`c9fe08a1c79ad26b0d0431e9da4e9ab66dd2803c699dfee3c6195a579c0a5fcf`)
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
- `paper_bencmark/highambench/tasks/P05/T1/faithfulness/inputs/blind_dependency_inventory.json` (`c4b8e4cbcea5756ce4393cbcc5d5c54dce079c71deb65d99a77062f30b3decb9`)
- `paper_bencmark/highambench/tasks/P05/T1/faithfulness/inputs/blind_dossier.md` (`36054541a44c03f74e8f20185d744fea0cd15b74cb0df6ee9bcae1b1745263cc`)
- `paper_bencmark/highambench/tasks/P05/T1/faithfulness/inputs/blind_review_packet.md` (`36054541a44c03f74e8f20185d744fea0cd15b74cb0df6ee9bcae1b1745263cc`)
- `paper_bencmark/highambench/tasks/P05/T1/faithfulness/inputs/declaration_dossier.md` (`13edcf44d3625c4bb7a22ea5b36a39b6cc9650fc152c67ef4b02d14026296038`)
- `paper_bencmark/highambench/tasks/P05/T1/faithfulness/inputs/dependency_inventory.json` (`115272009c83978c8abf225328e61e5c4235575365e7695854292155bb5e306f`)
- `paper_bencmark/highambench/tasks/P05/T1/faithfulness/inputs/direct_review_packet.md` (`5f2086bfc273a469f7fb5b69073af359b442890abd54020bc3941216a743b3d2`)
- `paper_bencmark/highambench/tasks/P05/T1/faithfulness/inputs/source_locator.json` (`5fc435baaab8e18bc83731da27d1c75611cbc602e54e49e702b619356e2aca6e`)
