# Faithfulness audit: P10-T3

- Classification: `not-faithful-different`
- Accepted as paper-faithful: `false`
- Adjudicated: `true`
- Target SHA-256: `3768d2f5a743618038ff91cf8dbe7e3882be20611078b6235b6a4abc7a6137f3`
- Paper SHA-256: `0ee818d060542baefdd85cbb7c7f2fd948efcb927101da84c37e418713f87269`

## Decision

The declaration preserves the ordinary equation, block signs, solve dependencies, dyadic dimensions, variational separation, recurrence coefficients, and equation-(20) exponent shape. Frobenius norms are a defensible specialization, and certified runs are globally inhabited. Nevertheless, the theorem applies only after the central local error analysis and a source-absent base bound have been packaged as assumptions, does not connect those records to every SylR execution, and replaces a first-order big-O result with an exact constant-2 inequality. The real-only scope may also be narrower. These facts make both implication directions fail, so the result is not-faithful-different rather than faithful-stronger or merely weaker.

## Implications

- **Lean implies paper:** `no`. The Lean theorem covers only pre-certified run records and supplies no representation theorem for every admissible SylR input or floating-point execution. Global nonvacuity of that record type does not recover the paper's algorithm-wide logarithmic-stability claim.
- **Paper implies lean:** `no`. The paper gives first-order big-O bounds with no fixed constant, no displayed scalar base estimate, and no envelope-attainment or certificate-record obligations. It therefore does not imply the exact constant-2 Lean bound or the additional run requirements.

## Findings

- **critical / assumed-local-analysis:** The declaration changes the proof boundary and does not derive the selected numerical result from the paper's stable-arithmetic model.
- **major / restricted-algorithm-coverage:** The formal result cannot establish the paper's claim for all intended inputs or executions.
- **major / asymptotic-to-exact-bound:** The paper does not imply the formal conclusion, even after accepting the Frobenius and dyadic specializations.
- **major / unsupported-base-and-first-order-model:** The finite bound depends on assumptions absent from the source and is not linked to actual floating-point behavior.
- **minor / scalar-domain-specialization:** Potentially omitted complex cases represent narrower applicability and cannot support a faithful-stronger classification.
- **note / resolved-norm-and-nonvacuity:** S09's norm choice and global emptiness are not decisive failures; the remaining failure is coverage and the altered hypothesis/conclusion boundary.

## Semantic checklist

| Check | Direct | Round-trip |
|---|---|---|
| `S01` | `pass` | `pass` |
| `S02` | `fail` | `fail` |
| `S03` | `fail` | `fail` |
| `S04` | `fail` | `fail` |
| `S05` | `fail` | `fail` |
| `S06` | `fail` | `pass` |
| `S07` | `pass` | `fail` |
| `S08` | `fail` | `fail` |
| `S09` | `fail` | `unclear` |
| `S10` | `fail` | `fail` |
| `S11` | `fail` | `fail` |
| `S12` | `fail` | `fail` |
| `S13` | `fail` | `fail` |
| `S14` | `fail` | `fail` |
| `S15` | `fail` | `unclear` |
| `S16` | `pass` | `unclear` |

## Dependency coverage

- Blind translator covered `136` dependencies (`0` hash-reused meanings); unclear: `none`.
- Direct judge covered `136` dependencies (`0` hash-reused interpretations); failing or unclear: `D001, D002, D003, D004, D005, D006, D007, D009, D017, D030, D033, D035, D066, D088`.

## Remaining uncertainties

- The selected passage never states whether its scalar domain is real, complex, or both.
- The page-86 norms remain textually unsubscripted; context strongly supports the Frobenius specialization for the asymptotic argument, but supplies no exact norm-conversion constants.
- Whether every intended finite SylR execution can be equipped with the formal certificates is not established by the paper or declarations.

## Audit artifacts

- `paper_bencmark/highambench/tasks/P10/T3/faithfulness/agent_outputs/adjudicator.json` (`4dc28e153403db67fb858ccd41d6c4f023c8675b4bb2c500e40ae93d4ece1c3e`)
- `paper_bencmark/highambench/tasks/P10/T3/faithfulness/agent_outputs/blind_translation.json` (`dca565d427a0de5c30d17f12cd7dbd73afd746d961f6a2b7a756e87fc337c7fe`)
- `paper_bencmark/highambench/tasks/P10/T3/faithfulness/agent_outputs/direct_judge.json` (`f8268b9ed67f0e56ee783f5e081768a99c4110b90aec16b2b3bc99039879fd36`)
- `paper_bencmark/highambench/tasks/P10/T3/faithfulness/agent_outputs/roundtrip_judge.json` (`b8121815f8aa28e79b0d2053833045ad377cbc14f560783f24f9ce0cf0125e38`)
- `paper_bencmark/highambench/tasks/P10/T3/faithfulness/agent_outputs/source_contract.json` (`fe4a0df76d2d452148d0e8d12ddb63c23cde0bc8907abe6459b074d1fec50bf9`)
- `paper_bencmark/highambench/tasks/P10/T3/faithfulness/decision.json` (`d300862badca4e4ee728c1602ce7a02e88ff2bd8a387e1e4f498d7a4dee991a9`)
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
- `paper_bencmark/highambench/tasks/P10/T3/faithfulness/inputs/blind_dependency_inventory.json` (`8dd27e2de13bd10025dfdc7514a79098906d9a58b7d2d30fe54af3d3b4743cc7`)
- `paper_bencmark/highambench/tasks/P10/T3/faithfulness/inputs/blind_dossier.md` (`f40408bd1390d2dd9aed9d6702462e2a0904e56c3db426937898f208ef3fb3dd`)
- `paper_bencmark/highambench/tasks/P10/T3/faithfulness/inputs/blind_review_packet.md` (`f40408bd1390d2dd9aed9d6702462e2a0904e56c3db426937898f208ef3fb3dd`)
- `paper_bencmark/highambench/tasks/P10/T3/faithfulness/inputs/declaration_dossier.md` (`3a81ed4c9b642b06535db4d5a873b953b90d70c2dc4b2283666f60103adbdcf3`)
- `paper_bencmark/highambench/tasks/P10/T3/faithfulness/inputs/dependency_inventory.json` (`a788530927e1cd6457f16fadf363e94421c0169fda73137c49f37e6450a808e4`)
- `paper_bencmark/highambench/tasks/P10/T3/faithfulness/inputs/direct_review_packet.md` (`c598d64ddd65430d3c827d45f6358b554e4ba391e004bda891114761ec119254`)
- `paper_bencmark/highambench/tasks/P10/T3/faithfulness/inputs/source_locator.json` (`51ddf47f7a0f039198b66da3de9a8132d8241bfda767ea69b2530ea2e4cafb4f`)
