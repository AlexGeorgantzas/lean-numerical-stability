# Faithfulness audit: P04-T1

- Classification: `faithful-stronger`
- Accepted as paper-faithful: `true`
- Adjudicated: `true`
- Target SHA-256: `2bfaa12fb4acbadd9866984cdd81a4622d5360dbb1e29b0af7a5c2d7df82cf73`
- Paper SHA-256: `7ad9ebb7eef9864c58e9a3760ee308be48060647286f8e16cdc740ed4be5b862`

## Decision

The central mathematical content matches the paper exactly: blocked dimensions, effective precision priority, exact perturbation factorization, gamma constants, componentwise scale, full mixed product term, all-orders baseline, and right-to-left refinement. The run fields are sufficient execution certificates rather than the final theorem itself, and every paper execution can supply them. They nevertheless abstract away exact local operation sharing and allow conservative maximum-length paths, while the target also records a same-witness right-to-left refinement. Therefore the Lean declaration covers the full paper result and a nonvacuous broader certificate class: Lean implies the paper result, the converse does not hold at the declared domains, and faithful-stronger is the consistent classification.

## Implications

- **Lean implies paper:** `yes`. Every paper execution supplies a D018 certificate: its q states and local theta and delta factors satisfy state_step, and its elementary internal errors along each term-to-root path populate the n-factor arrays, with zero padding where the printed path is shorter. Right-to-left execution similarly supplies q+b-1 factors. Applying the Lean conclusion then yields the paper's compact representation and equation (3.4), so no paper case is lost.
- **Paper implies lean:** `no`. The paper quantifies over evaluations of Algorithm 3.1 with the printed operation paths; it does not assert the result for every abstract certificate admitted by D018. D018 permits uniform maximum-length, independently certified paths and does not force unused factors to be zero or enforce every position-specific theta count. The target also states the shorter bound for the same beta witness. These are genuine extensions beyond the paper's stated execution domain.

## Findings

- **note / certificate-scope-generalization:** Exact equivalence is too strong a classification, but this does not reduce applicability because every paper path embeds by zero padding.
- **note / right-to-left-witness-strengthening:** For q,b>1 and positive valid uBar, q+b-1<qb=n, so the added componentwise witness bound is strictly stronger. Its antecedent is satisfiable, so the strength is nonvacuous.

## Semantic checklist

| Check | Direct | Round-trip |
|---|---|---|
| `S01` | `pass` | `pass` |
| `S02` | `pass` | `pass` |
| `S03` | `pass` | `fail` |
| `S04` | `pass` | `fail` |
| `S05` | `pass` | `fail` |
| `S06` | `pass` | `pass` |
| `S07` | `pass` | `pass` |
| `S08` | `pass` | `unclear` |
| `S09` | `pass` | `pass` |
| `S10` | `pass` | `fail` |
| `S11` | `pass` | `fail` |
| `S12` | `pass` | `unclear` |
| `S13` | `pass` | `pass` |
| `S14` | `pass` | `pass` |
| `S15` | `pass` | `unclear` |
| `S16` | `pass` | `pass` |

## Dependency coverage

- Blind translator covered `78` dependencies (`0` hash-reused meanings); unclear: `none`.
- Direct judge covered `78` dependencies (`0` hash-reused interpretations); failing or unclear: `none`.

## Remaining uncertainties

- The paper does not formally enumerate its phrase "all orders of evaluation," and the constructor other(code) is only a tag. The baseline comparison is therefore made at the path-certificate level enforced by D018, not through a bijection with concrete parenthesization trees.

## Audit artifacts

- `paper_bencmark/highambench/tasks/P04/T1/faithfulness/agent_outputs/adjudicator.json` (`ab1f590ec2ef389135c51123de2a0d2e7b0f30e1c6dc27fc52c816d5801e8153`)
- `paper_bencmark/highambench/tasks/P04/T1/faithfulness/agent_outputs/blind_translation.json` (`9e255a8059e7037e85e8a75ba0ea16e9df310cf18cdedb156a0a680fa0e360ae`)
- `paper_bencmark/highambench/tasks/P04/T1/faithfulness/agent_outputs/direct_judge.json` (`51c34b217d66ececd842963e9465088bfd5d3e8f16b1e29704eeb93a62c8acca`)
- `paper_bencmark/highambench/tasks/P04/T1/faithfulness/agent_outputs/roundtrip_judge.json` (`60f089aed1e7c586623870a502169b72574187c1d34d92828c93e8cfb39e2501`)
- `paper_bencmark/highambench/tasks/P04/T1/faithfulness/agent_outputs/source_contract.json` (`77539c4fc1699e531f132b6bc3693779789d35401dd92d17a991212c4e862b1e`)
- `paper_bencmark/highambench/tasks/P04/T1/faithfulness/decision.json` (`96f66534de4cc215489ea9a351d64c1b73032e3d7d2fec0348caea216ab458ef`)
- `paper_bencmark/highambench/tasks/P04/T1/faithfulness/history/20260814T150947Z/agent_outputs/blind_translation.json` (`24c95edf957661904e999746b54ab92381f5891b09f10c972e36be32033626cd`)
- `paper_bencmark/highambench/tasks/P04/T1/faithfulness/history/20260814T150947Z/agent_outputs/direct_judge.json` (`59100ca117811f24a484738f4503848d51ffbec7c1723a2108ace018cc584ea5`)
- `paper_bencmark/highambench/tasks/P04/T1/faithfulness/history/20260814T150947Z/agent_outputs/paper_source_contract.json` (`f23d1d2864ab683fc44d7b4dd917ebb13c36417400d3ee09d7d5a642c3a0d785`)
- `paper_bencmark/highambench/tasks/P04/T1/faithfulness/history/20260814T150947Z/agent_outputs/roundtrip_judge.json` (`dfff72ac4aec4a9429a1da416cff0da40254fc2295cd8fdc55de1ce7042e8544`)
- `paper_bencmark/highambench/tasks/P04/T1/faithfulness/history/20260814T150947Z/agent_outputs/source_contract.json` (`51fe3191c0c33dceff9c2249c82e47cbcef4076ad8eb29f3f1edae94f3ac1d99`)
- `paper_bencmark/highambench/tasks/P04/T1/faithfulness/history/20260814T150947Z/decision.json` (`70281eebae8eed0b8a0bc77057f21c35ff5bfdeca26c6feaf415cfb6455f4ff1`)
- `paper_bencmark/highambench/tasks/P04/T1/faithfulness/history/20260814T150947Z/inputs/blind_dependency_inventory.json` (`b1f20dc3160c39e673d3cc76c27d435e473a5386864d2b4e019ab63d4fbd5580`)
- `paper_bencmark/highambench/tasks/P04/T1/faithfulness/history/20260814T150947Z/inputs/blind_dossier.md` (`93ef79dd73803cb2fa496bfe95bf92844648367ad706b4fb9f886fe42e61165e`)
- `paper_bencmark/highambench/tasks/P04/T1/faithfulness/history/20260814T150947Z/inputs/blind_review_packet.md` (`93ef79dd73803cb2fa496bfe95bf92844648367ad706b4fb9f886fe42e61165e`)
- `paper_bencmark/highambench/tasks/P04/T1/faithfulness/history/20260814T150947Z/inputs/declaration_dossier.md` (`81a55beeecdcdfde5ac3b5c0ef548e422f014d8c2d253775fe815d60b2f90ff3`)
- `paper_bencmark/highambench/tasks/P04/T1/faithfulness/history/20260814T150947Z/inputs/dependency_inventory.json` (`33840bb7404d27918dcc8ecf6f82434a24bfbd1c8bc65951ebe952717b0ef08c`)
- `paper_bencmark/highambench/tasks/P04/T1/faithfulness/history/20260814T150947Z/inputs/direct_review_packet.md` (`b86392f54544415bf8073873faa53f4baa70a6737c64eb414aa667507b29af05`)
- `paper_bencmark/highambench/tasks/P04/T1/faithfulness/history/20260814T150947Z/inputs/paper_source_locator.json` (`609fbccbf417b9661d911f32e2ac6e1c09c3fa4c980c82c53b5c0edd480437f7`)
- `paper_bencmark/highambench/tasks/P04/T1/faithfulness/history/20260814T150947Z/inputs/source_locator.json` (`86c3ca31f4fd3bf29dc0f84a7428bd2ee8d0bbf49781a00e741c683be03bb76e`)
- `paper_bencmark/highambench/tasks/P04/T1/faithfulness/history/20260821T133453Z/agent_outputs/blind_translation.json` (`f08349945ee815496c28671988169b1c2ff0e5dfe71b1438fd3133e21011fc07`)
- `paper_bencmark/highambench/tasks/P04/T1/faithfulness/history/20260821T133453Z/agent_outputs/direct_judge.json` (`df3209df94d2c6968625ed30bdd8ef3c4d5b1f0df3841a52e036bdbd73f2143e`)
- `paper_bencmark/highambench/tasks/P04/T1/faithfulness/history/20260821T133453Z/agent_outputs/roundtrip_judge.json` (`299e5b19045a89136bd7850b121f02e3f40b0d9f13a0865bc0eff62e10aef826`)
- `paper_bencmark/highambench/tasks/P04/T1/faithfulness/history/20260821T133453Z/agent_outputs/source_contract.json` (`1bfffcb1cdaf60a9db4a7b2a12e17f3e2e16e061312bdc71a5c931e8bfddb162`)
- `paper_bencmark/highambench/tasks/P04/T1/faithfulness/history/20260821T133453Z/decision.json` (`f534933fd280fe45e94b09aa044a8ba7cc5126c6a060ccf16356ff383221d697`)
- `paper_bencmark/highambench/tasks/P04/T1/faithfulness/history/20260821T133453Z/inputs/blind_dependency_inventory.json` (`da0101c0cf622ab7b095ec1b9aef3ec8a7e9499edbe265fea288e4ee5fdc6fc4`)
- `paper_bencmark/highambench/tasks/P04/T1/faithfulness/history/20260821T133453Z/inputs/blind_dossier.md` (`b19dd66051f23e6a3a30305118713ac3d0a3b40feb547573f79d63ec32ab9aa2`)
- `paper_bencmark/highambench/tasks/P04/T1/faithfulness/history/20260821T133453Z/inputs/blind_review_packet.md` (`b19dd66051f23e6a3a30305118713ac3d0a3b40feb547573f79d63ec32ab9aa2`)
- `paper_bencmark/highambench/tasks/P04/T1/faithfulness/history/20260821T133453Z/inputs/declaration_dossier.md` (`8bc51563a680ab2d2e93ed9b241cc775b89ce60c63c786f7c53d7ede1e8dcbe1`)
- `paper_bencmark/highambench/tasks/P04/T1/faithfulness/history/20260821T133453Z/inputs/dependency_inventory.json` (`87702bfac5a2483131afc425641408ac65186f08f8d6be2f7a1256f7e7b5494a`)
- `paper_bencmark/highambench/tasks/P04/T1/faithfulness/history/20260821T133453Z/inputs/direct_review_packet.md` (`e86eb6dd51eaec87d3ea99722efbd73014248d1795ffa568ec03d162cc7c0969`)
- `paper_bencmark/highambench/tasks/P04/T1/faithfulness/history/20260821T133453Z/inputs/source_locator.json` (`7ee5eb4b54f5e0aae61d41f000b69cf34b5282e338cde7be62973d1621087058`)
- `paper_bencmark/highambench/tasks/P04/T1/faithfulness/inputs/blind_dependency_inventory.json` (`567480f6d5b4d76e5f5d4dcafa6b2eeaf8c678b42c88d7288f9696425572b4dc`)
- `paper_bencmark/highambench/tasks/P04/T1/faithfulness/inputs/blind_dossier.md` (`ebd41cb5febdd308a8e26959738b84765e6d5c2194aafe90b3c3cab54b28f381`)
- `paper_bencmark/highambench/tasks/P04/T1/faithfulness/inputs/blind_review_packet.md` (`ebd41cb5febdd308a8e26959738b84765e6d5c2194aafe90b3c3cab54b28f381`)
- `paper_bencmark/highambench/tasks/P04/T1/faithfulness/inputs/declaration_dossier.md` (`37e7fe5b1e11e4a5f1b979a06df6ae2b3a720b6dc958a8493b720d8839b60e27`)
- `paper_bencmark/highambench/tasks/P04/T1/faithfulness/inputs/dependency_inventory.json` (`5e6ae1716ea7992f652e53b6b40e1e2a37b9c7050d45c47dee0f360d0a0fbe4e`)
- `paper_bencmark/highambench/tasks/P04/T1/faithfulness/inputs/direct_review_packet.md` (`5427a7f98257fcb6d38c81fd6bc87e8a106803e7e3b10a524a6f4792e6ad3342`)
- `paper_bencmark/highambench/tasks/P04/T1/faithfulness/inputs/source_locator.json` (`7ee5eb4b54f5e0aae61d41f000b69cf34b5282e338cde7be62973d1621087058`)
