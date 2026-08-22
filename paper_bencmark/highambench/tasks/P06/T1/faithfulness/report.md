# Faithfulness audit: P06-T1

- Classification: `faithful-stronger`
- Accepted as paper-faithful: `true`
- Adjudicated: `true`
- Target SHA-256: `dd81e6e8eb963b0f9eea3e51aab80ef2dce770b6168c042a976d2d4ef4dc7722`
- Paper SHA-256: `c02a20e9ffa8039a5ad3db9261fba19929de84bf0bff7654547541dffe496a79`

## Decision

The authoritative PDF hash matches the supplied locator. The mandated boundary selects the deterministic sentence taking (4.17) to (4.20), so omissions concerning Householder execution, Q, R-hat, backward-error provenance, Model 1.5, and probability are not defects in this declaration. The declaration exactly preserves simultaneity across columns, Euclidean and Frobenius norms, inequality direction, gamma_tilde, lambda positivity, the coefficient c6 lambda sqrt(n) gamma_tilde_m(lambda), and additive second-order terms. It is strictly broader because it proves the same conditional implication for positive wide matrices and every positive natural c6. Those extensions have nontrivial instances, while the added zero-dimensional cases are merely trivial. Therefore Lean implies the selected paper result, the paper does not imply the full Lean generalization, and the accepted classification is faithful-stronger.

## Implications

- **Lean implies paper:** `yes`. Restrict the Lean theorem to the paper's m >= n dimensions and fixed positive integer c6, and instantiate the explicit remainder functions with representatives of the printed O(u^2) terms. The simultaneous premise then yields (4.20) with the exact Euclidean and Frobenius norms, exact gamma_tilde formula, identical coefficient, and no additional sqrt(n).
- **Paper implies lean:** `no`. The selected paper statement is made in the standing m >= n QR domain and uses its fixed symbolic c6. It does not assert the universal conditional theorem for positive-dimensional m < n matrices or for every positive natural c6. The failure of this direction is genuine broader applicability, not reduced applicability or reliance on zero-dimensional vacuity.

## Findings

- **note / scope-boundary:** The declaration is faithful as the selected columnwise-to-Frobenius implication but must not be represented as a formalization of all of Theorem 4.4.
- **note / genuine-generalization:** Positive m < n instances and additional c6 values provide nonvacuous broader applicability, supporting faithful-stronger rather than faithful-equivalent.
- **note / higher-order-formalization:** The higher-order terms are preserved coherently, but their exact source-side uniformity remains unspecified.

## Semantic checklist

| Check | Direct | Round-trip |
|---|---|---|
| `S01` | `pass` | `pass` |
| `S02` | `pass` | `fail` |
| `S03` | `pass` | `unclear` |
| `S04` | `pass` | `fail` |
| `S05` | `pass` | `unclear` |
| `S06` | `pass` | `pass` |
| `S07` | `not-applicable` | `fail` |
| `S08` | `not-applicable` | `fail` |
| `S09` | `pass` | `pass` |
| `S10` | `pass` | `fail` |
| `S11` | `not-applicable` | `fail` |
| `S12` | `pass` | `pass` |
| `S13` | `pass` | `fail` |
| `S14` | `pass` | `unclear` |
| `S15` | `pass` | `fail` |
| `S16` | `pass` | `unclear` |

## Dependency coverage

- Blind translator covered `58` dependencies (`0` hash-reused meanings); unclear: `none`.
- Direct judge covered `58` dependencies (`0` hash-reused interpretations); failing or unclear: `none`.

## Remaining uncertainties

- The PDF does not specify the hidden constants, parameter dependence, or uniformity convention of its O(u^2) terms. The Lean right-sided witness interpretation is faithful but not uniquely forced by the source.
- The PDF does not explicitly say whether zero-dimensional matrices are admissible. This does not affect the classification because the Lean zero-dimensional cases are trivial and are not used as evidence of genuine strength.

## Audit artifacts

- `paper_bencmark/highambench/tasks/P06/T1/faithfulness/agent_outputs/adjudicator.json` (`5e4a3fbfc28b76a17e2c5991ea1be160f9751130f2a33886bb3c1c20a3538c07`)
- `paper_bencmark/highambench/tasks/P06/T1/faithfulness/agent_outputs/blind_translation.json` (`27b4c1d5ec410bc85d25c5ae73d45f0ece798cf16a9bd1adc5abd2ec34e33e67`)
- `paper_bencmark/highambench/tasks/P06/T1/faithfulness/agent_outputs/direct_judge.json` (`075720a408116a9a32caedf3b35358fd6c85d10b92e2b0ffc590642d23dbc824`)
- `paper_bencmark/highambench/tasks/P06/T1/faithfulness/agent_outputs/roundtrip_judge.json` (`7f844567b5a17435565e90d498dff50b7750613e089dca55b9efb401a511b935`)
- `paper_bencmark/highambench/tasks/P06/T1/faithfulness/agent_outputs/source_contract.json` (`d4ab8b93dd1e84b603c30230ba85c8c19f39bd90cb2722b77ec81670d3d06f9b`)
- `paper_bencmark/highambench/tasks/P06/T1/faithfulness/decision.json` (`d54acf65c14443c9d609942b76440d9c64e8a80f16f045f295c7fdf5a03292e2`)
- `paper_bencmark/highambench/tasks/P06/T1/faithfulness/history/20260814T205659Z/agent_outputs/blind_translation.json` (`78d6a16e2e4969e1ccd4ef2d4b9da9e95db6193fd1b3f0143192da3eaac4b1ab`)
- `paper_bencmark/highambench/tasks/P06/T1/faithfulness/history/20260814T205659Z/agent_outputs/direct_judge.json` (`bfb4556277b4c9b57738fe02f72286e1ae29ae0a9f36179266066b6a6c8224e3`)
- `paper_bencmark/highambench/tasks/P06/T1/faithfulness/history/20260814T205659Z/agent_outputs/paper_source_contract.json` (`5fc79f8dcb892e5e54a0e6404abfb754e2c8f1233e5e586f0036f135448517d2`)
- `paper_bencmark/highambench/tasks/P06/T1/faithfulness/history/20260814T205659Z/agent_outputs/roundtrip_judge.json` (`846f94bbb1149d106cf26cab12191653d0b9e44a246a56223b01fef46a373273`)
- `paper_bencmark/highambench/tasks/P06/T1/faithfulness/history/20260814T205659Z/agent_outputs/source_contract.json` (`8e53e0f8269939e3d98772fe34c53a586fe75c258d270e8cea278f2e988f0534`)
- `paper_bencmark/highambench/tasks/P06/T1/faithfulness/history/20260814T205659Z/decision.json` (`e8fa8a338bdca0d306c5fde261870b0c6eeeffbd3ac60994b18cb4834e50f724`)
- `paper_bencmark/highambench/tasks/P06/T1/faithfulness/history/20260814T205659Z/inputs/blind_dependency_inventory.json` (`9799d69d3509de7a0728aa479be82d3114810aa563336ff9b6a848da2bb37c69`)
- `paper_bencmark/highambench/tasks/P06/T1/faithfulness/history/20260814T205659Z/inputs/blind_dossier.md` (`5c0b359341957a9a846813c29b78c4d35b52235beb62b4d080d22e4a7ae1105e`)
- `paper_bencmark/highambench/tasks/P06/T1/faithfulness/history/20260814T205659Z/inputs/blind_review_packet.md` (`5c0b359341957a9a846813c29b78c4d35b52235beb62b4d080d22e4a7ae1105e`)
- `paper_bencmark/highambench/tasks/P06/T1/faithfulness/history/20260814T205659Z/inputs/declaration_dossier.md` (`abd2e0cce35b6cb05ae4945594c10f97eba9690e1b86140618736bf3a45b960f`)
- `paper_bencmark/highambench/tasks/P06/T1/faithfulness/history/20260814T205659Z/inputs/dependency_inventory.json` (`59f70fa079aafa059c53853182266e2b8c52aa8ca55244059579166953a2c30d`)
- `paper_bencmark/highambench/tasks/P06/T1/faithfulness/history/20260814T205659Z/inputs/direct_review_packet.md` (`8bb9d553f484d386159b95aab961709edfb9b567d03d89fea23e010fc6c33fcd`)
- `paper_bencmark/highambench/tasks/P06/T1/faithfulness/history/20260814T205659Z/inputs/paper_source_locator.json` (`d42b3fea8b0a859f7675a27adf15eef5a9d1a4d454377d2374aa02bdd01476fe`)
- `paper_bencmark/highambench/tasks/P06/T1/faithfulness/history/20260814T205659Z/inputs/source_locator.json` (`d6efa51b03cf5945c37b778053c05ddf456c4c9285a5ca6a0456f0fa32cef2d5`)
- `paper_bencmark/highambench/tasks/P06/T1/faithfulness/history/20260821T170105Z/agent_outputs/adjudicator.json` (`3170161fe5ce1788f775179369277f4360ea374af1cf4092f5260b0429adeb82`)
- `paper_bencmark/highambench/tasks/P06/T1/faithfulness/history/20260821T170105Z/agent_outputs/blind_translation.json` (`6951444f423cc38534ecada43139dc1a8bfd8b789e7b53ae702a2dfca95143cb`)
- `paper_bencmark/highambench/tasks/P06/T1/faithfulness/history/20260821T170105Z/agent_outputs/direct_judge.json` (`f6b3c3c919f0a8485d7b85ab4634d17a5189826e46308bb11048969fb0d8a397`)
- `paper_bencmark/highambench/tasks/P06/T1/faithfulness/history/20260821T170105Z/agent_outputs/roundtrip_judge.json` (`b5a7e136241163b20a4f36e02eb4c7d648aea879b8934323e6b869a2aa1a6a8a`)
- `paper_bencmark/highambench/tasks/P06/T1/faithfulness/history/20260821T170105Z/agent_outputs/source_contract.json` (`e335f0c3c6306afbf8da38581eabe3bfb90cbc5756e29b1cf4cc26628c7edfc6`)
- `paper_bencmark/highambench/tasks/P06/T1/faithfulness/history/20260821T170105Z/decision.json` (`f91bcca42197de83572f7ee0b59fad1b6969c6ef4713341bffa87ee906bc6f46`)
- `paper_bencmark/highambench/tasks/P06/T1/faithfulness/history/20260821T170105Z/inputs/blind_dependency_inventory.json` (`8cacdaeffe3b9bdc23e902acc504a7cf4a875e53cc8656116409404f532284f7`)
- `paper_bencmark/highambench/tasks/P06/T1/faithfulness/history/20260821T170105Z/inputs/blind_dossier.md` (`c831f0a8ecb9d8f82d2688aa95507ae629a992991730fa7c338c0420396eddab`)
- `paper_bencmark/highambench/tasks/P06/T1/faithfulness/history/20260821T170105Z/inputs/blind_review_packet.md` (`c831f0a8ecb9d8f82d2688aa95507ae629a992991730fa7c338c0420396eddab`)
- `paper_bencmark/highambench/tasks/P06/T1/faithfulness/history/20260821T170105Z/inputs/declaration_dossier.md` (`e46a4e0a73b127058bae7a1fd041843486a682f185676b20284784050e920435`)
- `paper_bencmark/highambench/tasks/P06/T1/faithfulness/history/20260821T170105Z/inputs/dependency_inventory.json` (`9c8726e4a74182bfcd243cf489d6c3beb76b1cc9e4e4e10e8c91485af93cbfea`)
- `paper_bencmark/highambench/tasks/P06/T1/faithfulness/history/20260821T170105Z/inputs/direct_review_packet.md` (`ca6a823c1734eda672f0906894d761fe2578c9bc93864b24137cdb3b5417f110`)
- `paper_bencmark/highambench/tasks/P06/T1/faithfulness/history/20260821T170105Z/inputs/source_locator.json` (`45ef01b373210cb2cb62694656a1c11adba586bbbe8a9e63961cdea3f1984ede`)
- `paper_bencmark/highambench/tasks/P06/T1/faithfulness/history/20260822T141015Z/agent_outputs/blind_translation.json` (`544a5bd20d19168c238fe0f9bd31dd521f494430bd0a172b1b3ff0e4dcf3ea84`)
- `paper_bencmark/highambench/tasks/P06/T1/faithfulness/history/20260822T141015Z/agent_outputs/direct_judge.json` (`6ddedae899da9d1e0d8b33f4de07a8f56f9d78f36e33cb971af48499e0de9e86`)
- `paper_bencmark/highambench/tasks/P06/T1/faithfulness/history/20260822T141015Z/agent_outputs/roundtrip_judge.json` (`5374b9c2599be660d5d40f46eded483b31fc5eed5d53695952df74ec9cab9cd6`)
- `paper_bencmark/highambench/tasks/P06/T1/faithfulness/history/20260822T141015Z/agent_outputs/source_contract.json` (`a42312a0cb9e2210d1f1cd958123df156db69198f781a7ea8bf70394366360f8`)
- `paper_bencmark/highambench/tasks/P06/T1/faithfulness/history/20260822T141015Z/decision.json` (`acfb27f15b3582f1c310e7891f20b7a61d74aa7582164fe21cb6371c92149d7a`)
- `paper_bencmark/highambench/tasks/P06/T1/faithfulness/history/20260822T141015Z/inputs/blind_dependency_inventory.json` (`68fbaeb5dd4f8a3444df64da276a8346b78b7c49bf4dd239b1291967b6ca4201`)
- `paper_bencmark/highambench/tasks/P06/T1/faithfulness/history/20260822T141015Z/inputs/blind_dossier.md` (`cb51f7e3034b8fffea782c42ab82768365c02d6fe74d8f8a80134d7369f3ee13`)
- `paper_bencmark/highambench/tasks/P06/T1/faithfulness/history/20260822T141015Z/inputs/blind_review_packet.md` (`cb51f7e3034b8fffea782c42ab82768365c02d6fe74d8f8a80134d7369f3ee13`)
- `paper_bencmark/highambench/tasks/P06/T1/faithfulness/history/20260822T141015Z/inputs/declaration_dossier.md` (`726eb5d56a20ff887d9909f63af472bb71a3ebe9b6edc9c399b3941bee479948`)
- `paper_bencmark/highambench/tasks/P06/T1/faithfulness/history/20260822T141015Z/inputs/dependency_inventory.json` (`27c2363eea841c7d092acef6c75e6d90a57f82a1c48e3e53613a8e5dcecac0c5`)
- `paper_bencmark/highambench/tasks/P06/T1/faithfulness/history/20260822T141015Z/inputs/direct_review_packet.md` (`c1cd201b5edfa3b4e2c2a0b4b39f347fdcb910fde5fac0d9b829417ef3bda35d`)
- `paper_bencmark/highambench/tasks/P06/T1/faithfulness/history/20260822T141015Z/inputs/source_locator.json` (`45ef01b373210cb2cb62694656a1c11adba586bbbe8a9e63961cdea3f1984ede`)
- `paper_bencmark/highambench/tasks/P06/T1/faithfulness/inputs/blind_dependency_inventory.json` (`43885d9113e6011e223ff64fa5c82ff0e4601c114cc0c0928e56aef367ea80e4`)
- `paper_bencmark/highambench/tasks/P06/T1/faithfulness/inputs/blind_dossier.md` (`0c8f1005a3d207c85a0df4edb71e832fc912f95a36810f090cc22fdd6c697d27`)
- `paper_bencmark/highambench/tasks/P06/T1/faithfulness/inputs/blind_review_packet.md` (`0c8f1005a3d207c85a0df4edb71e832fc912f95a36810f090cc22fdd6c697d27`)
- `paper_bencmark/highambench/tasks/P06/T1/faithfulness/inputs/declaration_dossier.md` (`f66b875bb7ed37f17c8b1fba3ffe6fe4950d2f0db092ab1ab6ce06f01c053a22`)
- `paper_bencmark/highambench/tasks/P06/T1/faithfulness/inputs/dependency_inventory.json` (`0f1ce8e7ace67edf7ee60e11f03c85c2de7674de1ffe5f1d63d6a81514a12120`)
- `paper_bencmark/highambench/tasks/P06/T1/faithfulness/inputs/direct_review_packet.md` (`3725f3cdc6ba7c2a9cd7f6ebbc17534834566657ced2350e5ea16c8b83dd1056`)
- `paper_bencmark/highambench/tasks/P06/T1/faithfulness/inputs/source_locator.json` (`359e37a6f0cbacea02687766ae892b53ae1b8f4e779c2fd0f10ca68a4cc13118`)
