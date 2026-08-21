# Faithfulness audit: P08-T3

- Classification: `not-faithful-different`
- Accepted as paper-faithful: `false`
- Adjudicated: `true`
- Target SHA-256: `3e2146203b4b72c536a5f0354845ccd4c8d1113eedeb5765186e57631c052057`
- Paper SHA-256: `f520066b46331dcbf25e51345c5ff5ffffe8fcad573d7f46e68834f83b3a2c54`

## Decision

The floating-point-model dispute is resolved in favor of faithfulness: the Lean total relative-error operations and left-associated sum instantiate assumptions the PDF deliberately leaves abstract. The decisive defects lie elsewhere. The source result remains tied to column-pivoted Gaussian elimination, uses preceding lemmas as established results, and gives anonymous constants uniform dimension-only meaning. The Lean proposition instead uses generic behavioral solve certificates, takes the preceding estimates as an explicit proof-valued premise, and omits uniform constant dependence. Since it combines broader solver scope with reduced applicability and quantitative content, neither implication holds and the correct classification is not-faithful-different.

## Implications

- **Lean implies paper:** `no`. The Lean theorem establishes the matching inequality only after constants and prior estimates are supplied. It neither establishes their existence for every paper execution nor proves that the constants are bounded solely as functions of n. Its solve certificates also do not establish column-pivoted Gaussian-elimination provenance. Therefore it does not entail the complete paper result.
- **Paper implies lean:** `no`. The paper proves Lemma 4.3 for its column-pivoted iterative-refinement execution. It does not assert the Lean theorem's universal rule for arbitrary behavioral solve certificates and arbitrary supplied prior packages. The acceptable floating-point specialization does not bridge that broader algorithmic domain.

## Findings

- **major / constant-parameter-dependence:** The target proves a potentially data- or execution-dependent bound and therefore loses the uniform quantitative assertion central to the paper.
- **major / dependency-as-hypothesis:** The proposition does not establish Lemma 4.3 from the paper's standing hypotheses alone.
- **major / algorithm-linkage:** The theorem applies to a different behavioral solver class and cannot certify that its solves came from the paper's algorithm.
- **note / floating-point-model:** This is an acceptable implementation specialization and is not a reason for rejection.
- **note / core-formula:** The central finite componentwise inequality, precision dependence, and indexing are faithfully represented.

## Semantic checklist

| Check | Direct | Round-trip |
|---|---|---|
| `S01` | `pass` | `pass` |
| `S02` | `pass` | `pass` |
| `S03` | `fail` | `fail` |
| `S04` | `fail` | `fail` |
| `S05` | `fail` | `pass` |
| `S06` | `pass` | `pass` |
| `S07` | `pass` | `pass` |
| `S08` | `fail` | `fail` |
| `S09` | `pass` | `pass` |
| `S10` | `fail` | `fail` |
| `S11` | `pass` | `unclear` |
| `S12` | `fail` | `fail` |
| `S13` | `pass` | `pass` |
| `S14` | `pass` | `pass` |
| `S15` | `fail` | `fail` |
| `S16` | `pass` | `pass` |

## Dependency coverage

- Blind translator covered `140` dependencies (`0` hash-reused meanings); unclear: `none`.
- Direct judge covered `140` dependencies (`0` hash-reused interpretations); failing or unclear: `D002, D004, D006, D017, D018, D019, D029, D031, D060`.

## Remaining uncertainties

- The PDF does not formalize whether a matrix-valued anonymous quantity being 'bounded above by functions of n only' means entrywise domination or a norm bound. Either interpretation imposes dimension-only uniformity absent from the Lean proposition, so this ambiguity does not affect the classification.

## Audit artifacts

- `paper_bencmark/highambench/tasks/P08/T3/faithfulness/agent_outputs/adjudicator.json` (`d57519457a3decbbad2e0423ae97cf551b87e54c39c9f8098fe3c7e1590a1b4f`)
- `paper_bencmark/highambench/tasks/P08/T3/faithfulness/agent_outputs/blind_translation.json` (`331084f1500a2fcdb1ffc8e5566870fe4d78a3f61728d4d6cc70501b16bd3a57`)
- `paper_bencmark/highambench/tasks/P08/T3/faithfulness/agent_outputs/direct_judge.json` (`839fdaac258bcd751e2e9bc7c025374512f929241d1cda300ce63d41765a5fe9`)
- `paper_bencmark/highambench/tasks/P08/T3/faithfulness/agent_outputs/roundtrip_judge.json` (`26fc5feeac5e482bedc8ec6400508390804f64264ea240a33124d29988f7bf40`)
- `paper_bencmark/highambench/tasks/P08/T3/faithfulness/agent_outputs/source_contract.json` (`d43479623be815d3b81b22ed1a371799b4747b437850ac06861d4445fb1a140a`)
- `paper_bencmark/highambench/tasks/P08/T3/faithfulness/decision.json` (`74951898138eeaf4b46d0cd512f481f6f4bddf21b6fa52b60d5215405c42b597`)
- `paper_bencmark/highambench/tasks/P08/T3/faithfulness/history/20260814T231158Z/agent_outputs/blind_translation.json` (`57036ede799569e746ad9ff7cdbe97849072ae9921428d222a4078901216e34a`)
- `paper_bencmark/highambench/tasks/P08/T3/faithfulness/history/20260814T231158Z/agent_outputs/direct_judge.json` (`7aa60f2f689e9561a41a1b075028e35166d175776e9acf0f707fa7544526c125`)
- `paper_bencmark/highambench/tasks/P08/T3/faithfulness/history/20260814T231158Z/agent_outputs/paper_source_contract.json` (`a163817fa5c88f26c8ba3e26089da7681e1ce417d954cec7742e812dbcc3f006`)
- `paper_bencmark/highambench/tasks/P08/T3/faithfulness/history/20260814T231158Z/agent_outputs/roundtrip_judge.json` (`9d37bb14cedba41acb75423298b9bcfe713a1a69f7afaea5de6e54ca069e6527`)
- `paper_bencmark/highambench/tasks/P08/T3/faithfulness/history/20260814T231158Z/agent_outputs/source_contract.json` (`842da5765045626400bf3765e50ba5b417bc64160627ea4f349d36c71254b6d3`)
- `paper_bencmark/highambench/tasks/P08/T3/faithfulness/history/20260814T231158Z/decision.json` (`90eaefef6f7d3bedfd656050fc0cec00e612efd3a91e7f53c45e4b73f05675ca`)
- `paper_bencmark/highambench/tasks/P08/T3/faithfulness/history/20260814T231158Z/inputs/blind_dependency_inventory.json` (`b133b7c6b9fd52c0a28c6a545ebffa23a0dc649280adb9e269a4c708b6569982`)
- `paper_bencmark/highambench/tasks/P08/T3/faithfulness/history/20260814T231158Z/inputs/blind_dossier.md` (`ff29c3f51276b219aba1a6012871be09ad25566633ab9c8ac77970a265d943d2`)
- `paper_bencmark/highambench/tasks/P08/T3/faithfulness/history/20260814T231158Z/inputs/blind_review_packet.md` (`ff29c3f51276b219aba1a6012871be09ad25566633ab9c8ac77970a265d943d2`)
- `paper_bencmark/highambench/tasks/P08/T3/faithfulness/history/20260814T231158Z/inputs/declaration_dossier.md` (`80b376bf40cc842bcde0cf55df76ee3bf1cf0bce14b26dc1ae3ca26a59060501`)
- `paper_bencmark/highambench/tasks/P08/T3/faithfulness/history/20260814T231158Z/inputs/dependency_inventory.json` (`a62a1ef7e45e10f8a3e1e87d3f180b22d1137fae465996104706bb100cde9d2d`)
- `paper_bencmark/highambench/tasks/P08/T3/faithfulness/history/20260814T231158Z/inputs/dependency_reuse_direct.json` (`d5a4ed06ca753323f783656e77058e1329698ef31b33a09749d9a304a7e8de8e`)
- `paper_bencmark/highambench/tasks/P08/T3/faithfulness/history/20260814T231158Z/inputs/direct_review_packet.md` (`b4334fc81066015a6dd45f92082aa02961f73a807ad01a2a94cdcce29027d507`)
- `paper_bencmark/highambench/tasks/P08/T3/faithfulness/history/20260814T231158Z/inputs/paper_source_locator.json` (`3242b63a529acc04514175dadb3f98deebf67f847a6bf33be0b5bb7850f84391`)
- `paper_bencmark/highambench/tasks/P08/T3/faithfulness/history/20260814T231158Z/inputs/source_locator.json` (`72d2ab219970ae0b0c6623e8f884275995b11ab5fd34e9d16952319ccb1a68b5`)
- `paper_bencmark/highambench/tasks/P08/T3/faithfulness/inputs/blind_dependency_inventory.json` (`2db81bd7429744339aee1f03d1f45498e4d93aa49d4694c7dea87aa918f02b45`)
- `paper_bencmark/highambench/tasks/P08/T3/faithfulness/inputs/blind_dossier.md` (`f48089a5d4b9b9e92462355712e713a034db249b15ab4315392e4564aa8d942d`)
- `paper_bencmark/highambench/tasks/P08/T3/faithfulness/inputs/blind_review_packet.md` (`f48089a5d4b9b9e92462355712e713a034db249b15ab4315392e4564aa8d942d`)
- `paper_bencmark/highambench/tasks/P08/T3/faithfulness/inputs/declaration_dossier.md` (`240fd8846a6e8431c8810e4c6a3c8bf6e6d2149e385af14a4099e02607ee6ee4`)
- `paper_bencmark/highambench/tasks/P08/T3/faithfulness/inputs/dependency_inventory.json` (`4cdeca65c93377e296a946befc6e7b3ebf18b17c4bae9382d6a93148b78d4e08`)
- `paper_bencmark/highambench/tasks/P08/T3/faithfulness/inputs/direct_review_packet.md` (`38c87221fa8c220de3326c72a138763a34713d5ec0150278f7be1d329b6bcc09`)
- `paper_bencmark/highambench/tasks/P08/T3/faithfulness/inputs/source_locator.json` (`a79927b5a093b5bf626b61761e908f4ff3a7fa5bdd4b2d9fefcac24871317d58`)
