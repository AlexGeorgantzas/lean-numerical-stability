# Faithfulness audit: P04-T1

- Classification: `not-faithful-weaker`
- Accepted as paper-faithful: `false`
- Adjudicated: `false`
- Target SHA-256: `c26a9e4cde7e60be6bea67cf5b21aac6ed89138b78973be26394f9e75175c552`
- Paper SHA-256: `7ad9ebb7eef9864c58e9a3760ee308be48060647286f8e16cdc740ed4be5b862`

## Decision

The final factorization, gamma definitions, effective-roundoff branches, forward-error coefficient, componentwise scale, and right-to-left offset are algebraically accurate. However, P04BlockFmaDotRun is not a block-FMA execution: its constructor requires the perturbation witnesses, factorization, and bounds that the paper derives. The target consequently proves only a weaker certificate-extraction lemma, with no recurrence or floating-point model, so it is not a faithful benchmark statement of the paper result.

## Implications

- **Lean implies paper:** `no`. The Lean proposition cannot establish that an output of recurrence (3.1) satisfies the factorization or error bound, because constructing its run input already requires those facts. It therefore does not imply the paper's algorithmic result.
- **Paper implies lean:** `yes`. For a genuine paper execution, the paper supplies alpha and beta and all generic or right-to-left bounds needed to construct the Lean certificate. The extra zero-effective-roundoff clause follows from gamma(0,q)=0 and the same factorization. Synthetic Lean runs satisfy these premises by construction, so the target is no stronger than the source result.

## Findings

- **critical / circular-certification:** The target re-extracts assumed conclusions instead of formalizing the error analysis the benchmark claims to measure.
- **major / missing-algorithm-model:** The theorem cannot be applied to an implementation or modeled execution without first proving the omitted paper result externally.
- **major / missing-floating-point-hypotheses:** The formal statement does not identify which numerical behaviors justify its perturbation certificate.
- **major / incomplete-source-conclusion:** Important execution and indexing content of the selected result is absent.
- **note / matching-final-algebra:** Once the perturbation certificate is assumed, the target's final algebraic consequences faithfully reproduce the paper's constants and error notion.
- **critical / assumed-principal-conclusion:** The theorem repackages an assumed error representation instead of proving it from the paper's numerical hypotheses.
- **critical / missing-algorithm-and-numerical-model:** The translation applies to synthetic packages unrelated to the block-FMA algorithm and cannot imply the paper result.
- **major / incomplete-source-conclusion:** Material parts of the source result, including its execution-level interpretation, are lost.
- **major / altered-quantifier-scope:** Witness existence is shifted from the theorem's conclusion into its domain, weakening the claimed result.
- **note / preserved-algebraic-bound:** The algebraic corollary is accurately encoded once the missing perturbation facts are assumed.

## Semantic checklist

| Check | Direct | Round-trip |
|---|---|---|
| `S01` | `pass` | `pass` |
| `S02` | `fail` | `fail` |
| `S03` | `fail` | `fail` |
| `S04` | `fail` | `fail` |
| `S05` | `fail` | `fail` |
| `S06` | `fail` | `pass` |
| `S07` | `fail` | `fail` |
| `S08` | `fail` | `fail` |
| `S09` | `pass` | `pass` |
| `S10` | `fail` | `fail` |
| `S11` | `fail` | `fail` |
| `S12` | `fail` | `fail` |
| `S13` | `pass` | `pass` |
| `S14` | `pass` | `pass` |
| `S15` | `fail` | `fail` |
| `S16` | `fail` | `fail` |

## Dependency coverage

- Blind translator covered `60` dependencies (`0` hash-reused meanings); unclear: `none`.
- Direct judge covered `60` dependencies (`0` hash-reused interpretations); failing or unclear: `D001, D002, D003, D014`.

## Remaining uncertainties

No remaining uncertainties were recorded.

## Audit artifacts

- `paper_bencmark/highambench/tasks/P04/T1/faithfulness/agent_outputs/blind_translation.json` (`f08349945ee815496c28671988169b1c2ff0e5dfe71b1438fd3133e21011fc07`)
- `paper_bencmark/highambench/tasks/P04/T1/faithfulness/agent_outputs/direct_judge.json` (`df3209df94d2c6968625ed30bdd8ef3c4d5b1f0df3841a52e036bdbd73f2143e`)
- `paper_bencmark/highambench/tasks/P04/T1/faithfulness/agent_outputs/roundtrip_judge.json` (`299e5b19045a89136bd7850b121f02e3f40b0d9f13a0865bc0eff62e10aef826`)
- `paper_bencmark/highambench/tasks/P04/T1/faithfulness/agent_outputs/source_contract.json` (`1bfffcb1cdaf60a9db4a7b2a12e17f3e2e16e061312bdc71a5c931e8bfddb162`)
- `paper_bencmark/highambench/tasks/P04/T1/faithfulness/decision.json` (`f534933fd280fe45e94b09aa044a8ba7cc5126c6a060ccf16356ff383221d697`)
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
- `paper_bencmark/highambench/tasks/P04/T1/faithfulness/inputs/blind_dependency_inventory.json` (`da0101c0cf622ab7b095ec1b9aef3ec8a7e9499edbe265fea288e4ee5fdc6fc4`)
- `paper_bencmark/highambench/tasks/P04/T1/faithfulness/inputs/blind_dossier.md` (`b19dd66051f23e6a3a30305118713ac3d0a3b40feb547573f79d63ec32ab9aa2`)
- `paper_bencmark/highambench/tasks/P04/T1/faithfulness/inputs/blind_review_packet.md` (`b19dd66051f23e6a3a30305118713ac3d0a3b40feb547573f79d63ec32ab9aa2`)
- `paper_bencmark/highambench/tasks/P04/T1/faithfulness/inputs/declaration_dossier.md` (`8bc51563a680ab2d2e93ed9b241cc775b89ce60c63c786f7c53d7ede1e8dcbe1`)
- `paper_bencmark/highambench/tasks/P04/T1/faithfulness/inputs/dependency_inventory.json` (`87702bfac5a2483131afc425641408ac65186f08f8d6be2f7a1256f7e7b5494a`)
- `paper_bencmark/highambench/tasks/P04/T1/faithfulness/inputs/direct_review_packet.md` (`e86eb6dd51eaec87d3ea99722efbd73014248d1795ffa568ec03d162cc7c0969`)
- `paper_bencmark/highambench/tasks/P04/T1/faithfulness/inputs/source_locator.json` (`7ee5eb4b54f5e0aae61d41f000b69cf34b5282e338cde7be62973d1621087058`)
