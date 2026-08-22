# Faithfulness audit: P10-T3

- Classification: `faithful-equivalent`
- Accepted as paper-faithful: `true`
- Adjudicated: `true`
- Target SHA-256: `00375cfea3c0ff4c537b0924b76c44b015eabd79eb3f4b338aa54abd6f34aaef`
- Paper SHA-256: `0ee818d060542baefdd85cbb7c7f2fd948efcb927101da84c37e418713f87269`

## Decision

The corrected controlled packets confirm the proposition previously analyzed. Primary PDF evidence supports treating the selected object as the finite unnumbered block-inverse identity and its exact product-block consequence, not as the whole asymptotic converse of Theorem 3.3. The source contract and judges accurately described that surrounding theorem but overextended it into the benchmark selection. Lean reproduces the input and inverse blocks, signs, indices, ordered product, two-sided inverse semantics, and extraction exactly. Fixing Real and requiring positive dimension are acceptable nonvacuous specializations, and defining the displayed candidate with A * B is a faithful definitional presentation. Both implication directions are therefore yes, yielding faithful-equivalent and accepted.

## Implications

- **Lean implies paper:** `yes`. For every positive dimension and real A and B, Lean proves that the paper's displayed right-hand matrix is a two-sided inverse of the displayed left-hand matrix and that its top-right block is exactly A * B. This entails the selected finite inverse identity and extraction fact.
- **Paper implies lean:** `yes`. Specializing the paper's finite display to positive-dimensional real matrices gives exactly D006 and D007. Standard inverse notation entails both product equalities in D002, and the displayed top-right block entails the extraction equality.

## Findings

- **note / source-selection:** Omitting omega, eta, operation counts, and an inversion-routine interface is not a conclusion omission for this selected finite result.
- **note / specialization:** The specialization is acceptable and nonvacuous; it neither supplies artificial strength nor removes the benchmark's selected content.
- **note / definitional-reformulation:** The definitional extraction conjunct does not weaken the substantive inverse identity or make the complete proposition vacuous.

## Semantic checklist

| Check | Direct | Round-trip |
|---|---|---|
| `S01` | `pass` | `pass` |
| `S02` | `pass` | `fail` |
| `S03` | `fail` | `fail` |
| `S04` | `fail` | `fail` |
| `S05` | `fail` | `fail` |
| `S06` | `pass` | `pass` |
| `S07` | `pass` | `pass` |
| `S08` | `fail` | `fail` |
| `S09` | `not-applicable` | `not-applicable` |
| `S10` | `pass` | `pass` |
| `S11` | `not-applicable` | `not-applicable` |
| `S12` | `fail` | `fail` |
| `S13` | `not-applicable` | `pass` |
| `S14` | `fail` | `fail` |
| `S15` | `pass` | `unclear` |
| `S16` | `pass` | `pass` |

## Dependency coverage

- Blind translator covered `49` dependencies (`0` hash-reused meanings); unclear: `none`.
- Direct judge covered `49` dependencies (`0` hash-reused interpretations); failing or unclear: `D002`.

## Remaining uncertainties

No remaining uncertainties were recorded.

## Audit artifacts

- `paper_bencmark/highambench/tasks/P10/T3/faithfulness/agent_outputs/adjudicator.json` (`10fc4b4bf9765a3d9563cc3ccb13dded990a6a811e321ae4be54285b75a2b2e1`)
- `paper_bencmark/highambench/tasks/P10/T3/faithfulness/agent_outputs/blind_translation.json` (`87f7f40b032817264e86a5a255f93bbe23842e63dfc632693f2b0c04986fa0ae`)
- `paper_bencmark/highambench/tasks/P10/T3/faithfulness/agent_outputs/direct_judge.json` (`3e0c54b0b9d13072130799f077ef727c509d9e9fa87b023401f8f3a1fe0933cc`)
- `paper_bencmark/highambench/tasks/P10/T3/faithfulness/agent_outputs/roundtrip_judge.json` (`bcc23e0570e01d92ea96d343c2f34ab2ea84853dbbfb184f442a147d7b216bff`)
- `paper_bencmark/highambench/tasks/P10/T3/faithfulness/agent_outputs/source_contract.json` (`363929163f4ec67a1e1557c35fdf11c4c0ff1e4cca0469912c9d71428fbb1765`)
- `paper_bencmark/highambench/tasks/P10/T3/faithfulness/decision.json` (`b1bc40462361e66ba0f5160c4486d17d5e674ce86c4270ba2c41c8dc4f74d552`)
- `paper_bencmark/highambench/tasks/P10/T3/faithfulness/history/20260815T062559Z/agent_outputs/adjudicator.json` (`6e1622cefd63b1ac0a8fa7a956911832ed3317a6b7a62561bb9abb56c2424226`)
- `paper_bencmark/highambench/tasks/P10/T3/faithfulness/history/20260815T062559Z/agent_outputs/blind_translation.json` (`13fe8c3784c3e21150701b15fdf6a77d19bc30a6bcc6b5c7517c0bb6ec2657ff`)
- `paper_bencmark/highambench/tasks/P10/T3/faithfulness/history/20260815T062559Z/agent_outputs/direct_judge.json` (`2cfc5b96b26e914acc7842f8dee5be9327497487b1266d22783c6c48548a9c8a`)
- `paper_bencmark/highambench/tasks/P10/T3/faithfulness/history/20260815T062559Z/agent_outputs/paper_source_contract.json` (`a730fdcbbc543ec8712373b135d8a67dd310f31f635dedabf0ed548f9316414a`)
- `paper_bencmark/highambench/tasks/P10/T3/faithfulness/history/20260815T062559Z/agent_outputs/roundtrip_judge.json` (`72bf1e6126a74c3a3de86a69aa8f6cba4911244cbe2aadfbb7836b856d9ac318`)
- `paper_bencmark/highambench/tasks/P10/T3/faithfulness/history/20260815T062559Z/agent_outputs/source_contract.json` (`8efac3e47a1bc50618231ce1fc451cbe8d17d2a680e7d0f83e953c44ae888184`)
- `paper_bencmark/highambench/tasks/P10/T3/faithfulness/history/20260815T062559Z/decision.json` (`7557b95cb0ea441d32eca1215aff2955243da00cbe9b27859395ce379610d0e3`)
- `paper_bencmark/highambench/tasks/P10/T3/faithfulness/history/20260815T062559Z/inputs/blind_dependency_inventory.json` (`e6e1e63de5c03181ea762421b4af0ff3f227cd32578d2286f77f8d578a12b3a0`)
- `paper_bencmark/highambench/tasks/P10/T3/faithfulness/history/20260815T062559Z/inputs/blind_dossier.md` (`719b4d67c6e21357302ebc4493123dea7fceffde1c58ed9091101dc88280126f`)
- `paper_bencmark/highambench/tasks/P10/T3/faithfulness/history/20260815T062559Z/inputs/blind_review_packet.md` (`719b4d67c6e21357302ebc4493123dea7fceffde1c58ed9091101dc88280126f`)
- `paper_bencmark/highambench/tasks/P10/T3/faithfulness/history/20260815T062559Z/inputs/declaration_dossier.md` (`a748607e03908e6f1837a9cd6a747d55e2744eb26ee73d3d8acccabe4d66a47d`)
- `paper_bencmark/highambench/tasks/P10/T3/faithfulness/history/20260815T062559Z/inputs/dependency_inventory.json` (`e896a8536f096464d33672f122968a460409d83ce8eb9dc38864668fa1dad48c`)
- `paper_bencmark/highambench/tasks/P10/T3/faithfulness/history/20260815T062559Z/inputs/dependency_reuse_direct.json` (`6d40017070ef9b09a33230c3d2de7549a8eec696e7b08b74611a9fe586c59bf0`)
- `paper_bencmark/highambench/tasks/P10/T3/faithfulness/history/20260815T062559Z/inputs/direct_review_packet.md` (`70a35c142f16e4806a68726f7a0ea0453d8534d87d4a940a194029c235dce993`)
- `paper_bencmark/highambench/tasks/P10/T3/faithfulness/history/20260815T062559Z/inputs/paper_source_locator.json` (`91f77a26c65c7ca024e216f6cc35327e6521963eee50d0bda4fd50b72060a4dc`)
- `paper_bencmark/highambench/tasks/P10/T3/faithfulness/history/20260815T062559Z/inputs/source_locator.json` (`c42d916d212b72c2dd5775fe26ed54385d4194a33841d840176614d9adebb304`)
- `paper_bencmark/highambench/tasks/P10/T3/faithfulness/history/20260822T073938Z/agent_outputs/adjudicator.json` (`4dc28e153403db67fb858ccd41d6c4f023c8675b4bb2c500e40ae93d4ece1c3e`)
- `paper_bencmark/highambench/tasks/P10/T3/faithfulness/history/20260822T073938Z/agent_outputs/blind_translation.json` (`dca565d427a0de5c30d17f12cd7dbd73afd746d961f6a2b7a756e87fc337c7fe`)
- `paper_bencmark/highambench/tasks/P10/T3/faithfulness/history/20260822T073938Z/agent_outputs/direct_judge.json` (`f8268b9ed67f0e56ee783f5e081768a99c4110b90aec16b2b3bc99039879fd36`)
- `paper_bencmark/highambench/tasks/P10/T3/faithfulness/history/20260822T073938Z/agent_outputs/roundtrip_judge.json` (`b8121815f8aa28e79b0d2053833045ad377cbc14f560783f24f9ce0cf0125e38`)
- `paper_bencmark/highambench/tasks/P10/T3/faithfulness/history/20260822T073938Z/agent_outputs/source_contract.json` (`fe4a0df76d2d452148d0e8d12ddb63c23cde0bc8907abe6459b074d1fec50bf9`)
- `paper_bencmark/highambench/tasks/P10/T3/faithfulness/history/20260822T073938Z/decision.json` (`d300862badca4e4ee728c1602ce7a02e88ff2bd8a387e1e4f498d7a4dee991a9`)
- `paper_bencmark/highambench/tasks/P10/T3/faithfulness/history/20260822T073938Z/inputs/blind_dependency_inventory.json` (`8dd27e2de13bd10025dfdc7514a79098906d9a58b7d2d30fe54af3d3b4743cc7`)
- `paper_bencmark/highambench/tasks/P10/T3/faithfulness/history/20260822T073938Z/inputs/blind_dossier.md` (`f40408bd1390d2dd9aed9d6702462e2a0904e56c3db426937898f208ef3fb3dd`)
- `paper_bencmark/highambench/tasks/P10/T3/faithfulness/history/20260822T073938Z/inputs/blind_review_packet.md` (`f40408bd1390d2dd9aed9d6702462e2a0904e56c3db426937898f208ef3fb3dd`)
- `paper_bencmark/highambench/tasks/P10/T3/faithfulness/history/20260822T073938Z/inputs/declaration_dossier.md` (`3a81ed4c9b642b06535db4d5a873b953b90d70c2dc4b2283666f60103adbdcf3`)
- `paper_bencmark/highambench/tasks/P10/T3/faithfulness/history/20260822T073938Z/inputs/dependency_inventory.json` (`a788530927e1cd6457f16fadf363e94421c0169fda73137c49f37e6450a808e4`)
- `paper_bencmark/highambench/tasks/P10/T3/faithfulness/history/20260822T073938Z/inputs/direct_review_packet.md` (`c598d64ddd65430d3c827d45f6358b554e4ba391e004bda891114761ec119254`)
- `paper_bencmark/highambench/tasks/P10/T3/faithfulness/history/20260822T073938Z/inputs/source_locator.json` (`51ddf47f7a0f039198b66da3de9a8132d8241bfda767ea69b2530ea2e4cafb4f`)
- `paper_bencmark/highambench/tasks/P10/T3/faithfulness/inputs/blind_dependency_inventory.json` (`a74dbdbb96afbfe2d336f4555499ff1657dabeae2f6eecc93804ff4ce00c9f73`)
- `paper_bencmark/highambench/tasks/P10/T3/faithfulness/inputs/blind_dossier.md` (`e7b04979e15ab5161bdc24c17bdb9741dd80da2648ea7d05d983858611ee6d59`)
- `paper_bencmark/highambench/tasks/P10/T3/faithfulness/inputs/blind_review_packet.md` (`e7b04979e15ab5161bdc24c17bdb9741dd80da2648ea7d05d983858611ee6d59`)
- `paper_bencmark/highambench/tasks/P10/T3/faithfulness/inputs/declaration_dossier.md` (`62a20eae46dccd969595ab3a89332837b4806874071da83d18db781a90623326`)
- `paper_bencmark/highambench/tasks/P10/T3/faithfulness/inputs/dependency_inventory.json` (`93f17a149266e0243bb676a04a4882361c52a14039db58c6877997a9f0d66adb`)
- `paper_bencmark/highambench/tasks/P10/T3/faithfulness/inputs/direct_review_packet.md` (`4192dce65a12619939b6d1feeb7780830339cdb9e206768ef30d06b958a3c667`)
- `paper_bencmark/highambench/tasks/P10/T3/faithfulness/inputs/source_locator.json` (`1a64883e901acc8920beb1bbd2b108217bcc4869cd480dcb75bfcc5a4ca13e4e`)
