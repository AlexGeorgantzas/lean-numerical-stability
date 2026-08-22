# Faithfulness audit: P08-T3

- Classification: `faithful-stronger`
- Accepted as paper-faithful: `true`
- Adjudicated: `false`
- Target SHA-256: `2e0ed250d2dc54230f8aaf3da4399ba60c88847d15786c10b7a3d0bfc389cd97`
- Paper SHA-256: `f520066b46331dcbf25e51345c5ff5ffffe8fcad573d7f46e68834f83b3a2c54`

## Decision

Direct inspection of printed pages 818-827 confirms that the Lean residual, nonstandard kappa, smallness condition, precision split, constants, indexing, componentwise relation, and all four finite terms match Lemma 4.3. Every paper computation is covered and the target is nonvacuous. Because the formal run is characterized by extensional numerical certificates rather than literal column-pivoting and floating-operation traces, its quantified domain is broader than the paper's stated algorithmic domain; the appropriate classification is faithful-stronger.

## Implications

- **Lean implies paper:** `yes`. Restrict the formal run to the paper's actual column-pivoted computation. Equations (3.1) and (4.1), the residual-precision analysis, the update model, and the displayed constant definitions instantiate the records, after which the Lean conclusion is exactly Lemma 4.3 component by component.
- **Paper implies lean:** `no`. The paper states Lemma 4.3 for the specified column-pivoted floating-point algorithm. The Lean proposition quantifies over every real-valued run satisfying the extensional solve, residual, correction, and update certificates; those records do not require an actual pivot-selection or floating-operation trace. The paper's stated proposition therefore does not by itself quantify over the whole broader Lean domain.

## Findings

- **note / conservative-algorithm-generalization:** The formal theorem covers every paper execution and additionally covers arbitrary certificate-bearing executions. This makes it faithfully stronger rather than propositionally equivalent.
- **note / dimension-bound-packaging:** The core Lemma 4.3 inequality and exact constants are unaffected, but uniform n-only boundedness is packaged as contextual evidence rather than established as a conclusion of this theorem.
- **note / algorithm-contract generalization:** The source algorithm remains a valid specialization, but the translated theorem also covers other solvers satisfying the same certificate; this makes the translation strictly stronger.
- **note / floating-point abstraction:** The numerical inequalities needed by the paper are preserved, but additional abstract real executions are admitted, reinforcing failure of the reverse implication.
- **note / constant-bound packaging:** The proposition does not itself construct these packages, but a paper instance supplies them from the displayed definitions and notes. No target coefficient or parameter dependence is lost.

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
| `S11` | `pass` | `pass` |
| `S12` | `pass` | `pass` |
| `S13` | `pass` | `pass` |
| `S14` | `pass` | `pass` |
| `S15` | `pass` | `pass` |
| `S16` | `pass` | `pass` |

## Dependency coverage

- Blind translator covered `122` dependencies (`0` hash-reused meanings); unclear: `none`.
- Direct judge covered `122` dependencies (`0` hash-reused interpretations); failing or unclear: `none`.

## Remaining uncertainties

No remaining uncertainties were recorded.

## Audit artifacts

- `paper_bencmark/highambench/tasks/P08/T3/faithfulness/agent_outputs/blind_translation.json` (`5e200d343efd3cb053368a30ca826103f7bd855c9e0dbd8bbc16cde0d8217796`)
- `paper_bencmark/highambench/tasks/P08/T3/faithfulness/agent_outputs/direct_judge.json` (`6eaa4107ab040d366c8158911c06d47303c3fe51e09a6e86e01539c52031666f`)
- `paper_bencmark/highambench/tasks/P08/T3/faithfulness/agent_outputs/roundtrip_judge.json` (`ce115cf2e5ae81a5e8bae2a86ac5ed57de3a3a19c1270d4edb10293afdf0baad`)
- `paper_bencmark/highambench/tasks/P08/T3/faithfulness/agent_outputs/source_contract.json` (`7ce46ffd5a9444cc79bc4ccf61faba80dd9493e3195a71b1a3b305e7417df98d`)
- `paper_bencmark/highambench/tasks/P08/T3/faithfulness/decision.json` (`fbf2f0eca5df46b85ff15fe97fcf59b3ea3b1ed5a2b2d19432be4cc4e098bdc0`)
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
- `paper_bencmark/highambench/tasks/P08/T3/faithfulness/history/20260821T172945Z/agent_outputs/adjudicator.json` (`d57519457a3decbbad2e0423ae97cf551b87e54c39c9f8098fe3c7e1590a1b4f`)
- `paper_bencmark/highambench/tasks/P08/T3/faithfulness/history/20260821T172945Z/agent_outputs/blind_translation.json` (`331084f1500a2fcdb1ffc8e5566870fe4d78a3f61728d4d6cc70501b16bd3a57`)
- `paper_bencmark/highambench/tasks/P08/T3/faithfulness/history/20260821T172945Z/agent_outputs/direct_judge.json` (`839fdaac258bcd751e2e9bc7c025374512f929241d1cda300ce63d41765a5fe9`)
- `paper_bencmark/highambench/tasks/P08/T3/faithfulness/history/20260821T172945Z/agent_outputs/roundtrip_judge.json` (`26fc5feeac5e482bedc8ec6400508390804f64264ea240a33124d29988f7bf40`)
- `paper_bencmark/highambench/tasks/P08/T3/faithfulness/history/20260821T172945Z/agent_outputs/source_contract.json` (`d43479623be815d3b81b22ed1a371799b4747b437850ac06861d4445fb1a140a`)
- `paper_bencmark/highambench/tasks/P08/T3/faithfulness/history/20260821T172945Z/decision.json` (`74951898138eeaf4b46d0cd512f481f6f4bddf21b6fa52b60d5215405c42b597`)
- `paper_bencmark/highambench/tasks/P08/T3/faithfulness/history/20260821T172945Z/inputs/blind_dependency_inventory.json` (`2db81bd7429744339aee1f03d1f45498e4d93aa49d4694c7dea87aa918f02b45`)
- `paper_bencmark/highambench/tasks/P08/T3/faithfulness/history/20260821T172945Z/inputs/blind_dossier.md` (`f48089a5d4b9b9e92462355712e713a034db249b15ab4315392e4564aa8d942d`)
- `paper_bencmark/highambench/tasks/P08/T3/faithfulness/history/20260821T172945Z/inputs/blind_review_packet.md` (`f48089a5d4b9b9e92462355712e713a034db249b15ab4315392e4564aa8d942d`)
- `paper_bencmark/highambench/tasks/P08/T3/faithfulness/history/20260821T172945Z/inputs/declaration_dossier.md` (`240fd8846a6e8431c8810e4c6a3c8bf6e6d2149e385af14a4099e02607ee6ee4`)
- `paper_bencmark/highambench/tasks/P08/T3/faithfulness/history/20260821T172945Z/inputs/dependency_inventory.json` (`4cdeca65c93377e296a946befc6e7b3ebf18b17c4bae9382d6a93148b78d4e08`)
- `paper_bencmark/highambench/tasks/P08/T3/faithfulness/history/20260821T172945Z/inputs/direct_review_packet.md` (`38c87221fa8c220de3326c72a138763a34713d5ec0150278f7be1d329b6bcc09`)
- `paper_bencmark/highambench/tasks/P08/T3/faithfulness/history/20260821T172945Z/inputs/source_locator.json` (`a79927b5a093b5bf626b61761e908f4ff3a7fa5bdd4b2d9fefcac24871317d58`)
- `paper_bencmark/highambench/tasks/P08/T3/faithfulness/history/20260822T095334Z/agent_outputs/adjudicator.json` (`973eda5beca3830d93e134b24368ae41ce90a1308f7fac7279437acfc754c27e`)
- `paper_bencmark/highambench/tasks/P08/T3/faithfulness/history/20260822T095334Z/agent_outputs/blind_translation.json` (`4ea3e0ad9e1e2dafe235128a4cb0b1f679e4c3695f159eff77e049dbf236313c`)
- `paper_bencmark/highambench/tasks/P08/T3/faithfulness/history/20260822T095334Z/agent_outputs/direct_judge.json` (`82860f8f7a44d3f63c404709365ae6954686cd3bb4f2849c91f9bb8319bae793`)
- `paper_bencmark/highambench/tasks/P08/T3/faithfulness/history/20260822T095334Z/agent_outputs/roundtrip_judge.json` (`25c92f92a9e0bdad4a97c98144a7c7999de4dac512e43d9749f50ee52fd9e4f6`)
- `paper_bencmark/highambench/tasks/P08/T3/faithfulness/history/20260822T095334Z/agent_outputs/source_contract.json` (`9f43526a96137e80f2db89f7780080d7bc0065560c100456abb2aa01e48d6d97`)
- `paper_bencmark/highambench/tasks/P08/T3/faithfulness/history/20260822T095334Z/decision.json` (`652503074741a699ca24065ce57442037a953bd8b8170448321e58b70a8d2f91`)
- `paper_bencmark/highambench/tasks/P08/T3/faithfulness/history/20260822T095334Z/inputs/blind_dependency_inventory.json` (`7f9b0159e87b807f95bfc410e9a56053f635585ea4714380ed745bc973615065`)
- `paper_bencmark/highambench/tasks/P08/T3/faithfulness/history/20260822T095334Z/inputs/blind_dossier.md` (`cdb0eac04ce01005e363ce48548ea336183f04d5f626f23fe0b7440d675f82fb`)
- `paper_bencmark/highambench/tasks/P08/T3/faithfulness/history/20260822T095334Z/inputs/blind_review_packet.md` (`cdb0eac04ce01005e363ce48548ea336183f04d5f626f23fe0b7440d675f82fb`)
- `paper_bencmark/highambench/tasks/P08/T3/faithfulness/history/20260822T095334Z/inputs/declaration_dossier.md` (`6395389f349c8bcf7e6f15d6145584b53c26777ee8d375f9417128eb5991ec31`)
- `paper_bencmark/highambench/tasks/P08/T3/faithfulness/history/20260822T095334Z/inputs/dependency_inventory.json` (`0c6dae466b77fc7b3c712e100f8fac46260efdcd0f0a447e29e4bb0935ea3950`)
- `paper_bencmark/highambench/tasks/P08/T3/faithfulness/history/20260822T095334Z/inputs/direct_review_packet.md` (`8c678f4d53b147e4d2cef2f291e0fbf53482055b27a0766258663943e03aeb1d`)
- `paper_bencmark/highambench/tasks/P08/T3/faithfulness/history/20260822T095334Z/inputs/source_locator.json` (`a79927b5a093b5bf626b61761e908f4ff3a7fa5bdd4b2d9fefcac24871317d58`)
- `paper_bencmark/highambench/tasks/P08/T3/faithfulness/inputs/blind_dependency_inventory.json` (`1d565a153d1cb512eeaa4c18ce369336a88c9879c1b96b3c877d7620d8d60b21`)
- `paper_bencmark/highambench/tasks/P08/T3/faithfulness/inputs/blind_dossier.md` (`ca18bf6cc5f065141ec0b899f8f59e38af48b4fd4965f98ba571c7efb44e9a0b`)
- `paper_bencmark/highambench/tasks/P08/T3/faithfulness/inputs/blind_review_packet.md` (`ca18bf6cc5f065141ec0b899f8f59e38af48b4fd4965f98ba571c7efb44e9a0b`)
- `paper_bencmark/highambench/tasks/P08/T3/faithfulness/inputs/declaration_dossier.md` (`8b210451db86414cf7537d8ef1716438089e4de2d4ee8cdf63c91fe44c32101f`)
- `paper_bencmark/highambench/tasks/P08/T3/faithfulness/inputs/dependency_inventory.json` (`b7d6ec64489144077c635fd09c92bb2d8764cd051d5d0c0e7523ca227bf672d7`)
- `paper_bencmark/highambench/tasks/P08/T3/faithfulness/inputs/direct_review_packet.md` (`970c5515f535301e3907d20c3964fa6bb9e66ea5a4b6c6b546564d76b4fda114`)
- `paper_bencmark/highambench/tasks/P08/T3/faithfulness/inputs/source_locator.json` (`a79927b5a093b5bf626b61761e908f4ff3a7fa5bdd4b2d9fefcac24871317d58`)
