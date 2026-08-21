# Faithfulness audit: P06-T1

- Classification: `not-faithful-weaker`
- Accepted as paper-faithful: `false`
- Adjudicated: `true`
- Target SHA-256: `58b5668acafdbd9fc628fcd1a6ca85f8ff956a51cf02b0e5b2c1f0c1fda3895d`
- Paper SHA-256: `c02a20e9ffa8039a5ad3db9261fba19929de84bf0bff7654547541dffe496a79`

## Decision

Primary paper evidence confirms the exact coefficient, probability, norms, tall real dimensions, local probability-one assumption, backward relation, simultaneous column bounds, and Frobenius consequence. The declaration nevertheless assumes the complete columnwise theorem, proves only its aggregation, under-specifies the source algorithm, and encodes the higher-order remainder so that the asserted bound can be trivial at a fixed positive unit roundoff. Its apparently broader run and constant quantification therefore do not constitute genuine nonvacuous strength. The paper result yields the Lean consequence, but the Lean proposition does not yield the paper result, so the directionally consistent classification is not-faithful-weaker.

## Implications

- **Lean implies paper:** `no`. The Lean proposition does not derive Theorem 4.4's simultaneous columnwise result from Model 1.5 and the local probability-one assumption. It assumes that result in a certificate, omits the column bounds from its conclusion, admits executions not linked to Householder QR, and allows a fixed-unit-roundoff remainder spike to trivialize its quantitative bound.
- **Paper implies lean:** `yes`. For a corresponding genuine Householder QR execution, Theorem 4.4 supplies the event, orthogonal witness, exact factorization, and simultaneous column bounds required by the certificate. The paper explicitly states that (4.17) implies the Frobenius bound (4.20), which is at least as strong as the Lean conclusion.

## Findings

- **critical / conclusion-as-hypothesis:** The declaration proves only a consequence after assuming the selected theorem's main conclusion.
- **critical / higher-order-vacuity:** For any positive fixed unit roundoff, an isolated positive spike can make the Frobenius inequality automatic without representing an O(u^2) computational error.
- **major / algorithm-linkage:** The formal execution class includes processes not established to be executions of the source algorithm.
- **major / incomplete-conclusion:** The declaration cannot recover the complete selected theorem-and-consequence result.
- **minor / constant-quantification:** The declaration does not assert existence of the paper's constants, although its displayed coefficient is otherwise correct.
- **note / event-witness-scope:** This textual scope differs, but it is not an independent logical weakening here because nonmeasurable existential witnesses can be extended outside goodEvent.

## Semantic checklist

| Check | Direct | Round-trip |
|---|---|---|
| `S01` | `pass` | `pass` |
| `S02` | `pass` | `fail` |
| `S03` | `unclear` | `fail` |
| `S04` | `fail` | `fail` |
| `S05` | `fail` | `fail` |
| `S06` | `fail` | `pass` |
| `S07` | `pass` | `pass` |
| `S08` | `fail` | `fail` |
| `S09` | `pass` | `pass` |
| `S10` | `pass` | `fail` |
| `S11` | `pass` | `pass` |
| `S12` | `fail` | `fail` |
| `S13` | `pass` | `pass` |
| `S14` | `fail` | `fail` |
| `S15` | `fail` | `pass` |
| `S16` | `fail` | `fail` |

## Dependency coverage

- Blind translator covered `134` dependencies (`0` hash-reused meanings); unclear: `none`.
- Direct judge covered `134` dependencies (`0` hash-reused interpretations); failing or unclear: `D001, D007, D013, D015, D018, D064, D091`.

## Remaining uncertainties

- The PDF does not quantify the coefficient, dimension dependence, input-norm scaling, or uniformity hidden in its additive O(u^2) terms.
- The numerical values of c5 and c6 are not supplied; they are only described as integer constants of modest size.
- The paper does not formalize measurability or canonical Skolemization of Q and DeltaA as random functions. This does not alter the classification because the Lean declaration also imposes no measurability on those witnesses.

## Audit artifacts

- `paper_bencmark/highambench/tasks/P06/T1/faithfulness/agent_outputs/adjudicator.json` (`3170161fe5ce1788f775179369277f4360ea374af1cf4092f5260b0429adeb82`)
- `paper_bencmark/highambench/tasks/P06/T1/faithfulness/agent_outputs/blind_translation.json` (`6951444f423cc38534ecada43139dc1a8bfd8b789e7b53ae702a2dfca95143cb`)
- `paper_bencmark/highambench/tasks/P06/T1/faithfulness/agent_outputs/direct_judge.json` (`f6b3c3c919f0a8485d7b85ab4634d17a5189826e46308bb11048969fb0d8a397`)
- `paper_bencmark/highambench/tasks/P06/T1/faithfulness/agent_outputs/roundtrip_judge.json` (`b5a7e136241163b20a4f36e02eb4c7d648aea879b8934323e6b869a2aa1a6a8a`)
- `paper_bencmark/highambench/tasks/P06/T1/faithfulness/agent_outputs/source_contract.json` (`e335f0c3c6306afbf8da38581eabe3bfb90cbc5756e29b1cf4cc26628c7edfc6`)
- `paper_bencmark/highambench/tasks/P06/T1/faithfulness/decision.json` (`f91bcca42197de83572f7ee0b59fad1b6969c6ef4713341bffa87ee906bc6f46`)
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
- `paper_bencmark/highambench/tasks/P06/T1/faithfulness/inputs/blind_dependency_inventory.json` (`8cacdaeffe3b9bdc23e902acc504a7cf4a875e53cc8656116409404f532284f7`)
- `paper_bencmark/highambench/tasks/P06/T1/faithfulness/inputs/blind_dossier.md` (`c831f0a8ecb9d8f82d2688aa95507ae629a992991730fa7c338c0420396eddab`)
- `paper_bencmark/highambench/tasks/P06/T1/faithfulness/inputs/blind_review_packet.md` (`c831f0a8ecb9d8f82d2688aa95507ae629a992991730fa7c338c0420396eddab`)
- `paper_bencmark/highambench/tasks/P06/T1/faithfulness/inputs/declaration_dossier.md` (`e46a4e0a73b127058bae7a1fd041843486a682f185676b20284784050e920435`)
- `paper_bencmark/highambench/tasks/P06/T1/faithfulness/inputs/dependency_inventory.json` (`9c8726e4a74182bfcd243cf489d6c3beb76b1cc9e4e4e10e8c91485af93cbfea`)
- `paper_bencmark/highambench/tasks/P06/T1/faithfulness/inputs/direct_review_packet.md` (`ca6a823c1734eda672f0906894d761fe2578c9bc93864b24137cdb3b5417f110`)
- `paper_bencmark/highambench/tasks/P06/T1/faithfulness/inputs/source_locator.json` (`45ef01b373210cb2cb62694656a1c11adba586bbbe8a9e63961cdea3f1984ede`)
