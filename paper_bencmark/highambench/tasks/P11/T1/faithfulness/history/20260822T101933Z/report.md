# Faithfulness audit: P11-T1

- Classification: `not-faithful-weaker`
- Accepted as paper-faithful: `false`
- Adjudicated: `true`
- Target SHA-256: `d288077fb1730fbea2cf9f145a2df64efb854f87b8e1a42b31558025b230a7e4`
- Paper SHA-256: `72b7521848be07971a6721ea0356bb898c63e21b8ad3aa109fee8f41517284a5`

## Decision

The substantive k=1 witness, residual identity, norm meanings, signs, and full equation-(16) chain match the source. The arithmetic interface, first-column execution record, and localized second-order coefficient faithfully isolate the hypotheses actually used by that base-case argument. The sole classification-changing defect is the incorrectly grouped c1 formula used in the inherited all-k condition. Because it is strictly larger for every relevant k>=2, it narrows applicability without strengthening the conclusion, yielding not-faithful-weaker.

## Implications

- **Lean implies paper:** `no`. Lean's malformed larger c4 excludes some executions satisfying the paper's condition (3), so the Lean theorem does not recover the source result over its full stated domain.
- **Paper implies lean:** `yes`. After the faithful identification of the abstract first-column operations with the source's normalized norm and division laws, restricting the paper result to Lean's stronger condition yields every Lean conclusion. The first-column prefix and explicit remainder coefficient introduce no conflicting conclusion.

## Findings

- **major / constant-and-applicability-mismatch:** For n>=2, the formal theorem applies to a proper subset of the paper-admissible executions.
- **note / faithful-local-arithmetic-abstraction:** The abstraction broadens implementation representation without changing the selected mathematical claim.
- **note / faithful-algorithm-prefix:** Omitting irrelevant later execution traces is not an algorithm-linkage defect for P11-T1.
- **note / higher-order-separation:** The selected residual result retains the source's exact first-column form.

## Semantic checklist

| Check | Direct | Round-trip |
|---|---|---|
| `S01` | `pass` | `pass` |
| `S02` | `pass` | `pass` |
| `S03` | `pass` | `fail` |
| `S04` | `fail` | `fail` |
| `S05` | `pass` | `pass` |
| `S06` | `fail` | `pass` |
| `S07` | `pass` | `pass` |
| `S08` | `pass` | `fail` |
| `S09` | `pass` | `pass` |
| `S10` | `fail` | `fail` |
| `S11` | `pass` | `fail` |
| `S12` | `fail` | `pass` |
| `S13` | `pass` | `pass` |
| `S14` | `pass` | `fail` |
| `S15` | `fail` | `fail` |
| `S16` | `pass` | `pass` |

## Dependency coverage

- Blind translator covered `122` dependencies (`0` hash-reused meanings); unclear: `none`.
- Direct judge covered `122` dependencies (`0` hash-reused interpretations); failing or unclear: `D001, D003, D012, D026`.

## Remaining uncertainties

No remaining uncertainties were recorded.

## Audit artifacts

- `paper_bencmark/highambench/tasks/P11/T1/faithfulness/agent_outputs/adjudicator.json` (`bd21e56406d824642767efaf284d6fc4365bdc38d3a449477b8e669974e70431`)
- `paper_bencmark/highambench/tasks/P11/T1/faithfulness/agent_outputs/blind_translation.json` (`ac4812748bd6d69800930fa077c4c5d30289190bbfe47e22472fc08e2fc3c62a`)
- `paper_bencmark/highambench/tasks/P11/T1/faithfulness/agent_outputs/direct_judge.json` (`f341011ecf13911405ecb3ce250728d244d45163bb03dfcd698b0444126142bc`)
- `paper_bencmark/highambench/tasks/P11/T1/faithfulness/agent_outputs/roundtrip_judge.json` (`9e54f02b92655f900357f4063fec3232b43e9c0161fb7d71fedd5bbca65997d8`)
- `paper_bencmark/highambench/tasks/P11/T1/faithfulness/agent_outputs/source_contract.json` (`f74ae09ffbf17709ed5e974f6125bc63240c3d603a9fedbfb61aa87437955442`)
- `paper_bencmark/highambench/tasks/P11/T1/faithfulness/decision.json` (`d69aab0cd0e89acdadb46357cb3b153e6c6ca75645343f619a7e6a8fc7c86fa3`)
- `paper_bencmark/highambench/tasks/P11/T1/faithfulness/history/20260815T065726Z/agent_outputs/adjudicator.json` (`6dd477313776e9b16971fc243e4725e56a9cede70fa53b11d4d961f767dd50a7`)
- `paper_bencmark/highambench/tasks/P11/T1/faithfulness/history/20260815T065726Z/agent_outputs/blind_translation.json` (`33d631145d9171c5a10d906e00f5f2e935108c805144e36cfec487b50b447365`)
- `paper_bencmark/highambench/tasks/P11/T1/faithfulness/history/20260815T065726Z/agent_outputs/direct_judge.json` (`8fb8d336e29a399b7e6d914ceeef9f05405de6a11d229888e240f8ee6e6b2d2f`)
- `paper_bencmark/highambench/tasks/P11/T1/faithfulness/history/20260815T065726Z/agent_outputs/roundtrip_judge.json` (`1a723fb7ea84b892619076684ca6192e360e13c40472b643678643bd76409bdd`)
- `paper_bencmark/highambench/tasks/P11/T1/faithfulness/history/20260815T065726Z/agent_outputs/source_contract.json` (`b6b205e2131601bc1e987c77ba6a94a5fe0519814e45a8898036c7da6d23f3ba`)
- `paper_bencmark/highambench/tasks/P11/T1/faithfulness/history/20260815T065726Z/decision.json` (`4f63dd898137c097064ef7cbfdcbc1d0d426207f0ecff9b9038045ea2c7d3c0f`)
- `paper_bencmark/highambench/tasks/P11/T1/faithfulness/history/20260815T065726Z/inputs/blind_dossier.md` (`1b49b7fd0dbd315f2767a43f76cab9d60a7d713a1084e882569d4f887bb4d682`)
- `paper_bencmark/highambench/tasks/P11/T1/faithfulness/history/20260815T065726Z/inputs/declaration_dossier.md` (`781435c9386bfcdaf7fc38e1b9355f040381a48b6da9929294395c2565203738`)
- `paper_bencmark/highambench/tasks/P11/T1/faithfulness/history/20260815T065726Z/inputs/source_locator.json` (`e19ebf9ab8fdeca1573b78753863b04c548b278b0ff6e3071e560bcd5dd72c70`)
- `paper_bencmark/highambench/tasks/P11/T1/faithfulness/history/20260821T203110Z/agent_outputs/adjudicator.json` (`8233ccb0a2983781a46de413462be4f4c70f8cef8f7a7a8c904e020329aaf167`)
- `paper_bencmark/highambench/tasks/P11/T1/faithfulness/history/20260821T203110Z/agent_outputs/blind_translation.json` (`db2ff34dcab7539a5fcebc5b66fb7dd8dd6bd05654f0a0424d6b82136e483660`)
- `paper_bencmark/highambench/tasks/P11/T1/faithfulness/history/20260821T203110Z/agent_outputs/direct_judge.json` (`633594670c1d2dbcd4d1353050e57e609f175acf43241bd9b9b25040436653da`)
- `paper_bencmark/highambench/tasks/P11/T1/faithfulness/history/20260821T203110Z/agent_outputs/roundtrip_judge.json` (`2113f0945eec0c068e6a07e16b05a70d185c7b4b449ef09c0a26f9f149881384`)
- `paper_bencmark/highambench/tasks/P11/T1/faithfulness/history/20260821T203110Z/agent_outputs/source_contract.json` (`2c59d1f3ff107aa5feec5ec56164800f60ba3d18227f4bfa8be6c9507b0763d7`)
- `paper_bencmark/highambench/tasks/P11/T1/faithfulness/history/20260821T203110Z/decision.json` (`94f427b287ab9686c06cdf1f9f12e0a8f8a7b9fa746912d8e0bb3a84c5a9be5c`)
- `paper_bencmark/highambench/tasks/P11/T1/faithfulness/history/20260821T203110Z/inputs/blind_dependency_inventory.json` (`5c72bfc5d963a6b802d4751dc530493e3b2f034fdff87a0175a52ff84f81981e`)
- `paper_bencmark/highambench/tasks/P11/T1/faithfulness/history/20260821T203110Z/inputs/blind_dossier.md` (`46b0d3e1cd0684aaade6805383722507fcb566370117112877cc9c6b08555b96`)
- `paper_bencmark/highambench/tasks/P11/T1/faithfulness/history/20260821T203110Z/inputs/blind_review_packet.md` (`46b0d3e1cd0684aaade6805383722507fcb566370117112877cc9c6b08555b96`)
- `paper_bencmark/highambench/tasks/P11/T1/faithfulness/history/20260821T203110Z/inputs/declaration_dossier.md` (`b4d9d7368a5ecccc39630c0586dbc9958721a694a56758ebf4a339a4fe391bf4`)
- `paper_bencmark/highambench/tasks/P11/T1/faithfulness/history/20260821T203110Z/inputs/dependency_inventory.json` (`fbd36d1780038547e39db84aebc387e08a3735c4ad76360f836f1aba50e4341a`)
- `paper_bencmark/highambench/tasks/P11/T1/faithfulness/history/20260821T203110Z/inputs/direct_review_packet.md` (`83767df91e32f72c64b72c3f9d795b28d894de45506fb1cfe13be59996f03fc7`)
- `paper_bencmark/highambench/tasks/P11/T1/faithfulness/history/20260821T203110Z/inputs/source_locator.json` (`81f5fd3ae92d710d611ec7c586273c53619da4de4bd509461ea9e16aba10298e`)
- `paper_bencmark/highambench/tasks/P11/T1/faithfulness/inputs/blind_dependency_inventory.json` (`b39a4adb71fba7b5e873a7fc4bf008788a9e8721ae1764657d533b5b6e004de8`)
- `paper_bencmark/highambench/tasks/P11/T1/faithfulness/inputs/blind_dossier.md` (`e8b28cf7409e94f48257adbf68902d2cc8fbd2527471df3b61deb746b78d2909`)
- `paper_bencmark/highambench/tasks/P11/T1/faithfulness/inputs/blind_review_packet.md` (`e8b28cf7409e94f48257adbf68902d2cc8fbd2527471df3b61deb746b78d2909`)
- `paper_bencmark/highambench/tasks/P11/T1/faithfulness/inputs/declaration_dossier.md` (`a25e178247aca01038b60b0d7a793ecbb158f57802a56564b80251444e933ab0`)
- `paper_bencmark/highambench/tasks/P11/T1/faithfulness/inputs/dependency_inventory.json` (`51813b51de12a1ec8064775031368d0c7e108b48f29139a34ea3feccfd5da636`)
- `paper_bencmark/highambench/tasks/P11/T1/faithfulness/inputs/direct_review_packet.md` (`5567c0573de3987bd054b0cd193deb6fe45a3306ade997598eaee3d9dc50f666`)
- `paper_bencmark/highambench/tasks/P11/T1/faithfulness/inputs/source_locator.json` (`81f5fd3ae92d710d611ec7c586273c53619da4de4bd509461ea9e16aba10298e`)
