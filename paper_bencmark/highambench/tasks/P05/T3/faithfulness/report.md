# Faithfulness audit: P05-T3

- Classification: `faithful-stronger`
- Accepted as paper-faithful: `true`
- Adjudicated: `true`
- Target SHA-256: `26d07cef8ee5e1c3b00db72e8c109eeb65f1438eb85304e6d038a679908e094e`
- Paper SHA-256: `dd8b525c0eabc509a68b325ee5008cf6f1d4ef262bef8ba54e1947fe3cdb3db6`

## Decision

The PDF SHA-256 matches the required digest. The exact declarations preserve the conventional upper-triangular column algorithm, arbitrary ordering only within its sums, every index endpoint and coefficient, computed-versus-exact distinctions, both local estimates, the exact backward identity, and both global componentwise bounds. The operation certificates add only source-derived lower-level facts and range evidence, and every RHat entry remains linked to a rounded output. All paper executions embed, while an explicit non-paper format and nonzero-residual run show strict, nonvacuous additional coverage. Thus Lean implies the selected paper result, the paper result does not cover every Lean instance, and faithful-stronger is the implication-consistent accepted classification.

## Implications

- **Lean implies paper:** `yes`. Every standard paper format and successful no-underflow/no-overflow conventional Cholesky execution instantiates P05FiniteRoundToNearestFormat and P05CholeskyRun. Equation (2.4) supplies the protected-trace sibling bounds, equation (3.7) supplies the square-root field, and rounded outputs supply representability. The target then gives exactly equations (4.5a)-(4.5b) and both parts of (4.4), with the correct zero-based offsets.
- **Paper implies lean:** `no`. The paper theorem ranges over standard finite floating-point systems. D018 additionally admits inhabited sparse radix formats and certified runs not belonging to that source domain, including the nonzero-residual example above. The paper result alone therefore does not establish the proposition for every Lean format and run.

## Findings

- **note / source-licensed lower-level assumptions:** Neither dependency assumes Lemma 4.1, Lemma 4.3, equation (4.5), or the final matrix result.
- **note / computed-factor representability:** The first target conjunct is derived. Redundant operand-representability fields for already computed entries exclude no valid paper execution.
- **note / strict nonvacuous format generalization:** The additional domain is real mathematical coverage, so the yes/no implication pair warrants faithful-stronger rather than faithful-equivalent or a reduced-applicability classification.

## Semantic checklist

| Check | Direct | Round-trip |
|---|---|---|
| `S01` | `pass` | `pass` |
| `S02` | `pass` | `pass` |
| `S03` | `pass` | `pass` |
| `S04` | `pass` | `unclear` |
| `S05` | `pass` | `pass` |
| `S06` | `pass` | `unclear` |
| `S07` | `pass` | `pass` |
| `S08` | `pass` | `pass` |
| `S09` | `pass` | `pass` |
| `S10` | `pass` | `pass` |
| `S11` | `pass` | `unclear` |
| `S12` | `pass` | `pass` |
| `S13` | `pass` | `pass` |
| `S14` | `pass` | `pass` |
| `S15` | `pass` | `unclear` |
| `S16` | `pass` | `unclear` |

## Dependency coverage

- Blind translator covered `146` dependencies (`0` hash-reused meanings); unclear: `none`.
- Direct judge covered `146` dependencies (`0` hash-reused interpretations); failing or unclear: `none`.

## Remaining uncertainties

No remaining uncertainties were recorded.

## Audit artifacts

- `paper_bencmark/highambench/tasks/P05/T3/faithfulness/agent_outputs/adjudicator.json` (`d2338fdb24ca98bb07cfdc41b7721b718026c942cb758b6b165254218dee01b7`)
- `paper_bencmark/highambench/tasks/P05/T3/faithfulness/agent_outputs/blind_translation.json` (`c670b84538952b6485ddbfd4564517fb540b9119407c458ab781bb169deabe40`)
- `paper_bencmark/highambench/tasks/P05/T3/faithfulness/agent_outputs/direct_judge.json` (`deca1d03f97e9d25ee4351ceadc758108494872e100ad3a61a93a22657bc99a3`)
- `paper_bencmark/highambench/tasks/P05/T3/faithfulness/agent_outputs/roundtrip_judge.json` (`12b34594773ae83956a3a964094031a517d361e77718fabe96dfc3e6902c58df`)
- `paper_bencmark/highambench/tasks/P05/T3/faithfulness/agent_outputs/source_contract.json` (`44175a6153d506b81c3d81e96c30f4ef299d75a0e408b20be26e7cb6616d6ab0`)
- `paper_bencmark/highambench/tasks/P05/T3/faithfulness/decision.json` (`b445aa99ac997b7009f31801c4aa524c0dca21b1ac4609518a618e57a0d12d25`)
- `paper_bencmark/highambench/tasks/P05/T3/faithfulness/history/20260814T203348Z/agent_outputs/blind_translation.json` (`cdc53949f20209460810b6aa91be140d279befb6c32d7f9151d394703bc0979a`)
- `paper_bencmark/highambench/tasks/P05/T3/faithfulness/history/20260814T203348Z/agent_outputs/direct_judge.json` (`46e490112fdfb2957b85ba525c40a7a5e7c4f9d5f9e70e678f9755a9eb5af43d`)
- `paper_bencmark/highambench/tasks/P05/T3/faithfulness/history/20260814T203348Z/agent_outputs/paper_source_contract.json` (`90bcb3f32112e46567a1fde6c0c742ef1d157d1829c1eb2b2cb5ebb4d58d4c1d`)
- `paper_bencmark/highambench/tasks/P05/T3/faithfulness/history/20260814T203348Z/agent_outputs/roundtrip_judge.json` (`a9c106c7bf4879ef0f85cb589b3378cf208246afe75fff6eb20a15899071d4c0`)
- `paper_bencmark/highambench/tasks/P05/T3/faithfulness/history/20260814T203348Z/agent_outputs/source_contract.json` (`383f9b21985e279369d4c14212bb70109146c948c8e3013af05eef6c69781b11`)
- `paper_bencmark/highambench/tasks/P05/T3/faithfulness/history/20260814T203348Z/decision.json` (`25b9b204f5ba5c77aea814ca96ddd4abc589a5008896a1a5f00675bff904cf6e`)
- `paper_bencmark/highambench/tasks/P05/T3/faithfulness/history/20260814T203348Z/inputs/blind_dependency_inventory.json` (`12bf0cd0f6f079664df24f38b8eb4a2637a07e24db008460622b072ef62e3744`)
- `paper_bencmark/highambench/tasks/P05/T3/faithfulness/history/20260814T203348Z/inputs/blind_dossier.md` (`8740a5009980963200c72465c2c36a8d3c670689db7ea8e8a7ae7b8da369ccd8`)
- `paper_bencmark/highambench/tasks/P05/T3/faithfulness/history/20260814T203348Z/inputs/blind_review_packet.md` (`8740a5009980963200c72465c2c36a8d3c670689db7ea8e8a7ae7b8da369ccd8`)
- `paper_bencmark/highambench/tasks/P05/T3/faithfulness/history/20260814T203348Z/inputs/declaration_dossier.md` (`2deecf940f270dcc15e90e0e80eb3330f30d813342c5ca792ff28f3fa85710dd`)
- `paper_bencmark/highambench/tasks/P05/T3/faithfulness/history/20260814T203348Z/inputs/dependency_inventory.json` (`9cce9ce2eb6ff22fbc5b06987ba96e0137ddcb05f4b7e2ff92c360b7bcb906eb`)
- `paper_bencmark/highambench/tasks/P05/T3/faithfulness/history/20260814T203348Z/inputs/dependency_reuse_direct.json` (`80f198548bad495db52ce5b9d42a75abdd6bfc3e24d439720fb000cc6551f73b`)
- `paper_bencmark/highambench/tasks/P05/T3/faithfulness/history/20260814T203348Z/inputs/direct_review_packet.md` (`6fc5702fd4006c8c0e8af8fbc28c745ee3c5a8516f4381145a0d2c1ae575126b`)
- `paper_bencmark/highambench/tasks/P05/T3/faithfulness/history/20260814T203348Z/inputs/paper_source_locator.json` (`417f8e6a6ff934c35d3c2379d9faefe1c21d44b1f14a69f7674c0ef303123327`)
- `paper_bencmark/highambench/tasks/P05/T3/faithfulness/history/20260814T203348Z/inputs/source_locator.json` (`9ec305a0bba44c4c7bb843aa8558ea4136ceb4e622b5321d0ee3125a78b54220`)
- `paper_bencmark/highambench/tasks/P05/T3/faithfulness/history/20260821T162254Z/agent_outputs/blind_translation.json` (`83a54d292e4d04488d76917919332bcf81cb4aed5bcf7025d847afd18d33492c`)
- `paper_bencmark/highambench/tasks/P05/T3/faithfulness/history/20260821T162254Z/agent_outputs/direct_judge.json` (`fa76688609ff3649c0101f899497076893f1cabd7239d6c265a9d606301a3c79`)
- `paper_bencmark/highambench/tasks/P05/T3/faithfulness/history/20260821T162254Z/agent_outputs/roundtrip_judge.json` (`d80baeb786597fdd7e8cc8d53a0e6b2b75fd6e87c54f7a603668b4905ccefa3d`)
- `paper_bencmark/highambench/tasks/P05/T3/faithfulness/history/20260821T162254Z/agent_outputs/source_contract.json` (`aad6136357e36a8a65b665a451ce13d5196383b2dc3d67df4643b81b8f8e3044`)
- `paper_bencmark/highambench/tasks/P05/T3/faithfulness/history/20260821T162254Z/decision.json` (`eec7b6d442f7d41a1aa549dda2f4558e7cc2db83df9b0c92dcddbed7f263d3c8`)
- `paper_bencmark/highambench/tasks/P05/T3/faithfulness/history/20260821T162254Z/inputs/blind_dependency_inventory.json` (`11c07aed679b7e50931f22d05b7eb901de5caa92d891c09d86787e68c2471b86`)
- `paper_bencmark/highambench/tasks/P05/T3/faithfulness/history/20260821T162254Z/inputs/blind_dossier.md` (`5b06b60af50c75fb79a0d21aac665e334b1268de000b5a465add8c3ad5318d3c`)
- `paper_bencmark/highambench/tasks/P05/T3/faithfulness/history/20260821T162254Z/inputs/blind_review_packet.md` (`5b06b60af50c75fb79a0d21aac665e334b1268de000b5a465add8c3ad5318d3c`)
- `paper_bencmark/highambench/tasks/P05/T3/faithfulness/history/20260821T162254Z/inputs/declaration_dossier.md` (`2ca273f2a5d4bb6eee040e7db3978a9630da96fca7f66aa8e182b0ebd45dd11b`)
- `paper_bencmark/highambench/tasks/P05/T3/faithfulness/history/20260821T162254Z/inputs/dependency_inventory.json` (`06b765dc4722b1d1a20d209148773248b8b69627cbeac277c83a86fbaf8f69c1`)
- `paper_bencmark/highambench/tasks/P05/T3/faithfulness/history/20260821T162254Z/inputs/direct_review_packet.md` (`f6d77cb073eebc3122095999c6e365637260ff576cb77f32ae36a79ed7c8d87f`)
- `paper_bencmark/highambench/tasks/P05/T3/faithfulness/history/20260821T162254Z/inputs/source_locator.json` (`1b1d519dd36c7dac40113a1e7117b8f515e4e097997ec55c5462fb911b3e1959`)
- `paper_bencmark/highambench/tasks/P05/T3/faithfulness/inputs/blind_dependency_inventory.json` (`031fdc6c7367a94c3ed0722aaad5fcac03211c3f817504228ce62eda6d9dfbbc`)
- `paper_bencmark/highambench/tasks/P05/T3/faithfulness/inputs/blind_dossier.md` (`609475a1e016b64a5a377b97a732b0cc3f945bc8a86aad4f53594bb6c5e3ad5e`)
- `paper_bencmark/highambench/tasks/P05/T3/faithfulness/inputs/blind_review_packet.md` (`609475a1e016b64a5a377b97a732b0cc3f945bc8a86aad4f53594bb6c5e3ad5e`)
- `paper_bencmark/highambench/tasks/P05/T3/faithfulness/inputs/declaration_dossier.md` (`9bbebc258f31d2c1c77d50914529c53970c14e87f3e57d7bf073d97d031b6232`)
- `paper_bencmark/highambench/tasks/P05/T3/faithfulness/inputs/dependency_inventory.json` (`79760e952a56cb03ceb107974cfc51fb203f63c3f0e0225a348f2b90edb2fb13`)
- `paper_bencmark/highambench/tasks/P05/T3/faithfulness/inputs/direct_review_packet.md` (`5f3e9c86a6e1cab2757097c440564d4ba9e68ab5a990e2797032505e186f13c6`)
- `paper_bencmark/highambench/tasks/P05/T3/faithfulness/inputs/source_locator.json` (`1b1d519dd36c7dac40113a1e7117b8f515e4e097997ec55c5462fb911b3e1959`)
