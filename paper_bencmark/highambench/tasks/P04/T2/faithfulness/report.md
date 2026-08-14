# Faithfulness audit: P04-T2

- Classification: `not-faithful-different`
- Accepted as paper-faithful: `false`
- Adjudicated: `true`
- Target SHA-256: `deb0f26432dfea38fe73fc819a18b6a5d879b13481f4f21eedf99ee14d3942c7`
- Paper SHA-256: `7ad9ebb7eef9864c58e9a3760ee308be48060647286f8e16cdc740ed4be5b862`

## Decision

Primary PDF evidence distinguishes the operational algorithm from the factorization derived during its analysis: C128 defines the conversion and chained block-FMA execution, C129 derives the alpha/beta representation, and C130 states the bound for the result of that algorithm. The Lean record assumes the derived representation and bounds without encoding or connecting to the execution. Although the resulting algebraic lemma is exact and nonvacuous and ranges over additional certificates, that wider certificate domain does not supply the missing algorithm guarantee. The paper likewise does not prove the lemma for all such certificates. Therefore neither implication holds and the declaration is not-faithful-different.

## Implications

- **Lean implies paper:** `no`. The declaration proves the bound only after a P04MixedInputMatMulRun containing the derived conversion and alpha/beta certificates has been supplied. It contains no execution semantics or theorem mapping an Algorithm 3.1 output to such a record, so it does not by itself establish Theorem 3.2 for the algorithm.
- **Paper implies lean:** `no`. Theorem 3.2 covers actual Algorithm 3.1 outputs under the paper's floating-point model. It does not quantify over every arbitrary real-valued certificate, perturbation choice, computed matrix, or precision tuple satisfying only D013's extensional postconditions.

## Findings

- **critical / algorithm-linkage:** The declaration does not formalize the paper's guarantee that Algorithm 3.1 produces an output satisfying equation (3.6).
- **major / reduced-proof-obligation:** The target proves only the final algebraic propagation step and cannot be counted as genuinely stronger merely because its certificate domain contains nonalgorithm objects.
- **major / floating-point-model:** The formal premise describes a different extensional numerical model and permits configurations outside the source theorem.
- **note / formula-fidelity:** The defect is the theorem's subject and hypotheses, not an error in the displayed bound.

## Semantic checklist

| Check | Direct | Round-trip |
|---|---|---|
| `S01` | `pass` | `pass` |
| `S02` | `pass` | `pass` |
| `S03` | `pass` | `pass` |
| `S04` | `pass` | `fail` |
| `S05` | `pass` | `pass` |
| `S06` | `pass` | `pass` |
| `S07` | `pass` | `pass` |
| `S08` | `pass` | `fail` |
| `S09` | `pass` | `pass` |
| `S10` | `pass` | `pass` |
| `S11` | `pass` | `fail` |
| `S12` | `pass` | `fail` |
| `S13` | `pass` | `pass` |
| `S14` | `pass` | `pass` |
| `S15` | `pass` | `fail` |
| `S16` | `pass` | `pass` |

## Dependency coverage

- Blind translator covered `63` dependencies (`0` hash-reused meanings); unclear: `none`.
- Direct judge covered `63` dependencies (`0` hash-reused interpretations); failing or unclear: `none`.

## Remaining uncertainties

No remaining uncertainties were recorded.

## Audit artifacts

- `paper_bencmark/highambench/tasks/P04/T2/faithfulness/agent_outputs/adjudicator.json` (`1dc2e89e4ddaee0e5945b74d29f9661def3def3529fbb1102c0d24b62ed08af9`)
- `paper_bencmark/highambench/tasks/P04/T2/faithfulness/agent_outputs/blind_translation.json` (`0864f3b2a58a95e353041fbad8db5e8cb9111fb725da2fb9d4e46df9c5667936`)
- `paper_bencmark/highambench/tasks/P04/T2/faithfulness/agent_outputs/direct_judge.json` (`436e83475d4746df8fdf7708ce78ff4cdeb4463070023f82e0c7b233d499b178`)
- `paper_bencmark/highambench/tasks/P04/T2/faithfulness/agent_outputs/roundtrip_judge.json` (`1677c6d4ee5a461d9acb092277b1ab8048699b3365e0fc74ced8b36d0a58629f`)
- `paper_bencmark/highambench/tasks/P04/T2/faithfulness/agent_outputs/source_contract.json` (`152fbe2a3c2c5cc867f5835cd15808f82524547ee43b09d2c89fc6f1419dace5`)
- `paper_bencmark/highambench/tasks/P04/T2/faithfulness/decision.json` (`54d4735b9279e0e0be987304f5479bfe8da04f4d8cb0fff88a5f3ade74eed3f7`)
- `paper_bencmark/highambench/tasks/P04/T2/faithfulness/history/20260814T152738Z/agent_outputs/blind_translation.json` (`4d71a7009e4cb29d27a134339ecf7b18c5220d2507c972f2cd793f26b9d8fbf8`)
- `paper_bencmark/highambench/tasks/P04/T2/faithfulness/history/20260814T152738Z/agent_outputs/direct_judge.json` (`c8550401e7f9caa5c9bbf71dad5391d07dcd6eba65821665baffbe8e0209771b`)
- `paper_bencmark/highambench/tasks/P04/T2/faithfulness/history/20260814T152738Z/agent_outputs/paper_source_contract.json` (`f23d1d2864ab683fc44d7b4dd917ebb13c36417400d3ee09d7d5a642c3a0d785`)
- `paper_bencmark/highambench/tasks/P04/T2/faithfulness/history/20260814T152738Z/agent_outputs/roundtrip_judge.json` (`01403dc737c6f8c804399734fccc14badb310c8df096ee83e4f7f0708e9e25d3`)
- `paper_bencmark/highambench/tasks/P04/T2/faithfulness/history/20260814T152738Z/agent_outputs/source_contract.json` (`f91ab8283eea97a3263327b17be4b438564672ac842266b86621054c130df589`)
- `paper_bencmark/highambench/tasks/P04/T2/faithfulness/history/20260814T152738Z/decision.json` (`bf585cec6a7195053b93f6fd066a68369c59615714a743e5921b141fbaef45fc`)
- `paper_bencmark/highambench/tasks/P04/T2/faithfulness/history/20260814T152738Z/inputs/blind_dependency_inventory.json` (`62f92733f1d6bd164114aabb88151cf1bfff522262475a1a60228bd73020c5b0`)
- `paper_bencmark/highambench/tasks/P04/T2/faithfulness/history/20260814T152738Z/inputs/blind_dossier.md` (`96abb59a7a2442174b606f193289f5d5c707fc22ba390a60dd00ae71a96c4955`)
- `paper_bencmark/highambench/tasks/P04/T2/faithfulness/history/20260814T152738Z/inputs/blind_review_packet.md` (`96abb59a7a2442174b606f193289f5d5c707fc22ba390a60dd00ae71a96c4955`)
- `paper_bencmark/highambench/tasks/P04/T2/faithfulness/history/20260814T152738Z/inputs/declaration_dossier.md` (`f5c48f188222a2480238b2c40d27f75ef228c4b2d7c6217d68ebe1fc49508119`)
- `paper_bencmark/highambench/tasks/P04/T2/faithfulness/history/20260814T152738Z/inputs/dependency_inventory.json` (`edb46564cba8406b42c6d333c68e9518d67704cf7da44fe676ccf5f6f989e7af`)
- `paper_bencmark/highambench/tasks/P04/T2/faithfulness/history/20260814T152738Z/inputs/dependency_reuse_direct.json` (`f69ef14afab568cfc4bcce54833be6807beba992d2a39b6f51af29e604fa6a7c`)
- `paper_bencmark/highambench/tasks/P04/T2/faithfulness/history/20260814T152738Z/inputs/direct_review_packet.md` (`89ea80907b3d9155fd60c79a2d5db9e0ae3b17f16e1514dd17f5ff2cf20b716e`)
- `paper_bencmark/highambench/tasks/P04/T2/faithfulness/history/20260814T152738Z/inputs/paper_source_locator.json` (`609fbccbf417b9661d911f32e2ac6e1c09c3fa4c980c82c53b5c0edd480437f7`)
- `paper_bencmark/highambench/tasks/P04/T2/faithfulness/history/20260814T152738Z/inputs/source_locator.json` (`8bf362e8f7f6f69a831e5593e1218ef3d7a2b716196afed0f070400ab36bf4b1`)
- `paper_bencmark/highambench/tasks/P04/T2/faithfulness/inputs/blind_dependency_inventory.json` (`d6a132052a35dfd240d1b71075b8fb6810e281bc9a9f75d4fb16d27a88a35c51`)
- `paper_bencmark/highambench/tasks/P04/T2/faithfulness/inputs/blind_dossier.md` (`213f7205321b63196e02a0778bbc31c8fc5576cbb4ed850163345bc3fed85df3`)
- `paper_bencmark/highambench/tasks/P04/T2/faithfulness/inputs/blind_review_packet.md` (`213f7205321b63196e02a0778bbc31c8fc5576cbb4ed850163345bc3fed85df3`)
- `paper_bencmark/highambench/tasks/P04/T2/faithfulness/inputs/declaration_dossier.md` (`3527b5c8664f6a6ad1c778d4195f384b081639e9c6053dd2e45607524f06472e`)
- `paper_bencmark/highambench/tasks/P04/T2/faithfulness/inputs/dependency_inventory.json` (`5b00364951e70e2edc52f1f143cc15eedc6dcb8dbc2c5e7aa1ef62e2c89cca68`)
- `paper_bencmark/highambench/tasks/P04/T2/faithfulness/inputs/direct_review_packet.md` (`3b0a564479bea029c245241173fc00c4777d2dce721cc9a7bba453f72a52932d`)
- `paper_bencmark/highambench/tasks/P04/T2/faithfulness/inputs/source_locator.json` (`e714f534dcc931ee4d94fdf815cba6d3e12fea743ec32896003bfe143cd8d351`)
