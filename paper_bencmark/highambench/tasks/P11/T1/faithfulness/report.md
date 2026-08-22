# Faithfulness audit: P11-T1

- Classification: `faithful-stronger`
- Accepted as paper-faithful: `true`
- Adjudicated: `true`
- Target SHA-256: `d288077fb1730fbea2cf9f145a2df64efb854f87b8e1a42b31558025b230a7e4`
- Paper SHA-256: `72b7521848be07971a6721ea0356bb898c63e21b8ad3aa109fee8f41517284a5`

## Decision

The authoritative PDF hash matches the supplied SHA-256. Its Algorithm 2 linkage is explicit, but its k=1 proof uses only the first computed norm, componentwise normalization error, positivity, and ordinary norm algebra. The declaration isolates those sufficient hypotheses and reproduces every equation (16) identity, sign, norm, inequality direction, and coefficient. Because it also applies to inhabited records that are not complete Algorithm 2 executions, it is strictly and nonvacuously stronger rather than equivalent. The abstract IEEE and higher-order encodings leave documented modeling uncertainty but do not alter the selected first-column residual theorem.

## Implications

- **Lean implies paper:** `yes`. Every normalized-range Algorithm 2 first-column execution satisfying the PDF's standing hypotheses supplies the local norm and division facts packaged by D003. D006 then yields exactly q1=(I+G1)a1/r11, ||G1||2<=epsilonM, A1-Q1R1=a1-q1r11=-G1a1, and the equation (16) norm chain. Omitting irrelevant later-column trace does not prevent application to the paper case.
- **Paper implies lean:** `no`. The PDF quantifies only over factors resulting from Algorithm 2. D003 admits additional records whose later Q entries are arbitrary while all first-column, invertibility, and conditioning fields hold. The paper theorem therefore does not, as a source-statement implication, establish the declaration for every Lean run.

## Findings

- **note / algorithm-domain-strengthening:** This rules out faithful-equivalent but creates genuine broader applicability because admissible non-Algorithm-2 records exist and receive the same first-column conclusion.
- **minor / floating-point-model-reconstruction:** The declaration is not a literal operational IEEE model, although its task-specific normalized-division effect is sufficient for and consistent with the printed first-column derivation.
- **minor / higher-order-terms:** Uniform asymptotic meaning is not preserved for that auxiliary norm estimate; equation (16) itself remains exactly remainder-free in both sources.

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
| `S12` | `pass` | `pass` |
| `S13` | `pass` | `pass` |
| `S14` | `pass` | `fail` |
| `S15` | `pass` | `pass` |
| `S16` | `pass` | `pass` |

## Dependency coverage

- Blind translator covered `122` dependencies (`0` hash-reused meanings); unclear: `none`.
- Direct judge covered `122` dependencies (`0` hash-reused interpretations); failing or unclear: `none`.

## Remaining uncertainties

- The PDF does not explicitly declare G1's dimension, structure, or existential quantifier, nor does it spell out the componentwise division-error rule; the m-by-m operator and abstract division interface remain dimensionally and numerically standard reconstructions.
- D024's coefficient times epsilonM squared is attached to one fixed-epsilon arithmetic model and does not encode uniform asymptotic big-O semantics. This affects the auxiliary Lemma 2 relation, not the remainder-free equation (16) conclusion.

## Audit artifacts

- `paper_bencmark/highambench/tasks/P11/T1/faithfulness/agent_outputs/adjudicator.json` (`bfe2c91b24b8d614cfe516164e2895d0b806308ae3e1b3b8f64fa874785f4a71`)
- `paper_bencmark/highambench/tasks/P11/T1/faithfulness/agent_outputs/blind_translation.json` (`5bf3e6185b63b4a215345536d39d255a3fb5f07ed6b339db7fa62b01cc121ace`)
- `paper_bencmark/highambench/tasks/P11/T1/faithfulness/agent_outputs/direct_judge.json` (`5eaba206419e0879b8aa011a1a68cd41166d5db872279b21fd8542fbb2e37d55`)
- `paper_bencmark/highambench/tasks/P11/T1/faithfulness/agent_outputs/roundtrip_judge.json` (`1dd29ffb9689cc3587f28201526650aa6587e2eb61058fb08f7ee811ff3f7596`)
- `paper_bencmark/highambench/tasks/P11/T1/faithfulness/agent_outputs/source_contract.json` (`63d53f6f35361be27691616239582a6ebf6ac67cdbe8aeeca87c1957afbfba8b`)
- `paper_bencmark/highambench/tasks/P11/T1/faithfulness/decision.json` (`d975544b4cdde8053088be2c404e3a5f239f0de267cdac9fe07a4f1ccc99d31e`)
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
- `paper_bencmark/highambench/tasks/P11/T1/faithfulness/history/20260822T101933Z/agent_outputs/adjudicator.json` (`bd21e56406d824642767efaf284d6fc4365bdc38d3a449477b8e669974e70431`)
- `paper_bencmark/highambench/tasks/P11/T1/faithfulness/history/20260822T101933Z/agent_outputs/blind_translation.json` (`ac4812748bd6d69800930fa077c4c5d30289190bbfe47e22472fc08e2fc3c62a`)
- `paper_bencmark/highambench/tasks/P11/T1/faithfulness/history/20260822T101933Z/agent_outputs/direct_judge.json` (`f341011ecf13911405ecb3ce250728d244d45163bb03dfcd698b0444126142bc`)
- `paper_bencmark/highambench/tasks/P11/T1/faithfulness/history/20260822T101933Z/agent_outputs/roundtrip_judge.json` (`9e54f02b92655f900357f4063fec3232b43e9c0161fb7d71fedd5bbca65997d8`)
- `paper_bencmark/highambench/tasks/P11/T1/faithfulness/history/20260822T101933Z/agent_outputs/source_contract.json` (`f74ae09ffbf17709ed5e974f6125bc63240c3d603a9fedbfb61aa87437955442`)
- `paper_bencmark/highambench/tasks/P11/T1/faithfulness/history/20260822T101933Z/decision.json` (`d69aab0cd0e89acdadb46357cb3b153e6c6ca75645343f619a7e6a8fc7c86fa3`)
- `paper_bencmark/highambench/tasks/P11/T1/faithfulness/history/20260822T101933Z/inputs/blind_dependency_inventory.json` (`b39a4adb71fba7b5e873a7fc4bf008788a9e8721ae1764657d533b5b6e004de8`)
- `paper_bencmark/highambench/tasks/P11/T1/faithfulness/history/20260822T101933Z/inputs/blind_dossier.md` (`e8b28cf7409e94f48257adbf68902d2cc8fbd2527471df3b61deb746b78d2909`)
- `paper_bencmark/highambench/tasks/P11/T1/faithfulness/history/20260822T101933Z/inputs/blind_review_packet.md` (`e8b28cf7409e94f48257adbf68902d2cc8fbd2527471df3b61deb746b78d2909`)
- `paper_bencmark/highambench/tasks/P11/T1/faithfulness/history/20260822T101933Z/inputs/declaration_dossier.md` (`a25e178247aca01038b60b0d7a793ecbb158f57802a56564b80251444e933ab0`)
- `paper_bencmark/highambench/tasks/P11/T1/faithfulness/history/20260822T101933Z/inputs/dependency_inventory.json` (`51813b51de12a1ec8064775031368d0c7e108b48f29139a34ea3feccfd5da636`)
- `paper_bencmark/highambench/tasks/P11/T1/faithfulness/history/20260822T101933Z/inputs/direct_review_packet.md` (`5567c0573de3987bd054b0cd193deb6fe45a3306ade997598eaee3d9dc50f666`)
- `paper_bencmark/highambench/tasks/P11/T1/faithfulness/history/20260822T101933Z/inputs/source_locator.json` (`81f5fd3ae92d710d611ec7c586273c53619da4de4bd509461ea9e16aba10298e`)
- `paper_bencmark/highambench/tasks/P11/T1/faithfulness/inputs/blind_dependency_inventory.json` (`2ff4982c62a54ec66d674662daa90fce3e317bdfbc8648574dec313ef9736396`)
- `paper_bencmark/highambench/tasks/P11/T1/faithfulness/inputs/blind_dossier.md` (`8d38580de8f174482a53c4d77159619de5d88503b403d7858d320659f1f5ba29`)
- `paper_bencmark/highambench/tasks/P11/T1/faithfulness/inputs/blind_review_packet.md` (`8d38580de8f174482a53c4d77159619de5d88503b403d7858d320659f1f5ba29`)
- `paper_bencmark/highambench/tasks/P11/T1/faithfulness/inputs/declaration_dossier.md` (`3e57471d445712b9eaf9e6a83ba85e97910b32dffbb5fcf21e5f924e62117c31`)
- `paper_bencmark/highambench/tasks/P11/T1/faithfulness/inputs/dependency_inventory.json` (`9c3d269620d574d6e16026d36cf73448c172a9bddff4f1fcf7204f72e3ff8830`)
- `paper_bencmark/highambench/tasks/P11/T1/faithfulness/inputs/direct_review_packet.md` (`90c67c8f8b48d3cd9f3e16d1a9c51078b2f267cb21fa8d9ba298ee574b93a385`)
- `paper_bencmark/highambench/tasks/P11/T1/faithfulness/inputs/source_locator.json` (`81f5fd3ae92d710d611ec7c586273c53619da4de4bd509461ea9e16aba10298e`)
