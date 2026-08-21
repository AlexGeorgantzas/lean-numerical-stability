# Faithfulness audit: P06-T1

- Classification: `not-faithful-weaker`
- Accepted as paper-faithful: `false`
- Adjudicated: `false`
- Target SHA-256: `582a7ed4a7777f6cdc9f2b8ec85c39fc2ef74e8aa17d2d5a6d6c7c2c8968df40`
- Paper SHA-256: `c02a20e9ffa8039a5ad3db9261fba19929de84bf0bff7654547541dffe496a79`

## Decision

The target reproduces the source's dimensions, factorization orientation, exact Q versus computed RHat distinction at the surface, simultaneous event shape, norms, gamma-tilde, coefficient, and probability formula. It is nevertheless not faithful: it assumes per-column certificates containing nearly the Lemma 4.2 conclusion, does not couple the QR run to the Model 1.5 operation/error trace, and uses post-unit-roundoff pointwise O(u^2) witnesses that make the numerical bounds vacuous for positive u. The paper result can instantiate this weaker target, but the target cannot recover the paper theorem from the paper's hypotheses.

## Implications

- **Lean implies paper:** `no`. The Lean proposition requires per-column certificates that the paper derives, permits runs whose perturbations are unrelated to Model 1.5 errors, and permits arbitrary pointwise actual-u O(u^2) slack. It therefore does not establish Theorem 4.4 from the paper's hypotheses.
- **Paper implies lean:** `yes`. For a source-conforming QR execution, Lemma 4.2 supplies the per-column facts, Lemma 4.3 supplies the simultaneous event and p4 coefficient, and Theorem 4.4 plus (4.20) supplies the exact relation and meaningful O(u^2) bounds, which instantiate the weaker formal conclusion.

## Findings

- **critical / hypotheses-and-quantifier-scope:** A substantial part of the selected theorem is assumed, so Lean does not imply the paper theorem.
- **critical / higher-order-terms-and-nonvacuity:** The column and Frobenius inequalities admit arbitrarily large slack and do not assert the paper's nontrivial backward-error bound.
- **major / algorithm-linkage:** Model 1.5 may describe a different error sequence from the packaged QR run.
- **major / constant-provenance:** The target does not establish the paper's universal coefficient, despite reproducing its displayed formula.
- **critical / conclusion-as-hypothesis:** The translated proposition is primarily a certificate-gluing lemma and can hold vacuously where the paper must establish the numerical result.
- **major / algorithm-linkage:** The stochastic execution represented by the formal assumptions is not demonstrably the execution analyzed in the paper.
- **major / constants-and-quantifiers:** The theorem's constant claim is replaced by a conditional parameterization that is vacuous for unsupported constants.
- **major / higher-order-terms:** The formal remainder conditions can fit a single finite-u discrepancy without representing the paper's asymptotic execution family.
- **note / preserved-core-content:** The algebraic surface of the selected result is recognizable despite the material hypothesis and quantifier defects.

## Semantic checklist

| Check | Direct | Round-trip |
|---|---|---|
| `S01` | `pass` | `pass` |
| `S02` | `pass` | `fail` |
| `S03` | `fail` | `fail` |
| `S04` | `fail` | `fail` |
| `S05` | `pass` | `pass` |
| `S06` | `fail` | `pass` |
| `S07` | `fail` | `pass` |
| `S08` | `fail` | `fail` |
| `S09` | `pass` | `pass` |
| `S10` | `fail` | `fail` |
| `S11` | `pass` | `pass` |
| `S12` | `fail` | `fail` |
| `S13` | `pass` | `pass` |
| `S14` | `fail` | `fail` |
| `S15` | `pass` | `pass` |
| `S16` | `fail` | `fail` |

## Dependency coverage

- Blind translator covered `145` dependencies (`0` hash-reused meanings); unclear: `none`.
- Direct judge covered `145` dependencies (`0` hash-reused interpretations); failing or unclear: `D001, D002, D004, D008, D016, D018, D025`.

## Remaining uncertainties

No remaining uncertainties were recorded.

## Audit artifacts

- `paper_bencmark/highambench/tasks/P06/T1/faithfulness/agent_outputs/blind_translation.json` (`544a5bd20d19168c238fe0f9bd31dd521f494430bd0a172b1b3ff0e4dcf3ea84`)
- `paper_bencmark/highambench/tasks/P06/T1/faithfulness/agent_outputs/direct_judge.json` (`6ddedae899da9d1e0d8b33f4de07a8f56f9d78f36e33cb971af48499e0de9e86`)
- `paper_bencmark/highambench/tasks/P06/T1/faithfulness/agent_outputs/roundtrip_judge.json` (`5374b9c2599be660d5d40f46eded483b31fc5eed5d53695952df74ec9cab9cd6`)
- `paper_bencmark/highambench/tasks/P06/T1/faithfulness/agent_outputs/source_contract.json` (`a42312a0cb9e2210d1f1cd958123df156db69198f781a7ea8bf70394366360f8`)
- `paper_bencmark/highambench/tasks/P06/T1/faithfulness/decision.json` (`acfb27f15b3582f1c310e7891f20b7a61d74aa7582164fe21cb6371c92149d7a`)
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
- `paper_bencmark/highambench/tasks/P06/T1/faithfulness/inputs/blind_dependency_inventory.json` (`68fbaeb5dd4f8a3444df64da276a8346b78b7c49bf4dd239b1291967b6ca4201`)
- `paper_bencmark/highambench/tasks/P06/T1/faithfulness/inputs/blind_dossier.md` (`cb51f7e3034b8fffea782c42ab82768365c02d6fe74d8f8a80134d7369f3ee13`)
- `paper_bencmark/highambench/tasks/P06/T1/faithfulness/inputs/blind_review_packet.md` (`cb51f7e3034b8fffea782c42ab82768365c02d6fe74d8f8a80134d7369f3ee13`)
- `paper_bencmark/highambench/tasks/P06/T1/faithfulness/inputs/declaration_dossier.md` (`726eb5d56a20ff887d9909f63af472bb71a3ebe9b6edc9c399b3941bee479948`)
- `paper_bencmark/highambench/tasks/P06/T1/faithfulness/inputs/dependency_inventory.json` (`27c2363eea841c7d092acef6c75e6d90a57f82a1c48e3e53613a8e5dcecac0c5`)
- `paper_bencmark/highambench/tasks/P06/T1/faithfulness/inputs/direct_review_packet.md` (`c1cd201b5edfa3b4e2c2a0b4b39f347fdcb910fde5fac0d9b829417ef3bda35d`)
- `paper_bencmark/highambench/tasks/P06/T1/faithfulness/inputs/source_locator.json` (`45ef01b373210cb2cb62694656a1c11adba586bbbe8a9e63961cdea3f1984ede`)
