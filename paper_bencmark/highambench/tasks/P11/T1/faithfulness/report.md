# Faithfulness audit: P11-T1

- Classification: `not-faithful-weaker`
- Accepted as paper-faithful: `false`
- Adjudicated: `true`
- Target SHA-256: `cce293127384ae51b7929f9bc9e0c80139057f1c877763204b151e172e362fc3`
- Paper SHA-256: `72b7521848be07971a6721ea0356bb898c63e21b8ad3aa109fee8f41517284a5`

## Decision

Primary evidence resolves the norm ambiguity: the target uses Mathlib's induced L2 operator norm, not the separately defined Frobenius norm, so S06 and S09 pass. D105 and D107 are closed elaboration infrastructure. The decisive mismatch is logical and numerical: the paper produces G1 for computed Algorithm 2 data, whereas the Lean theorem quantifies only over runs already containing G1, its representation, and its bound, without an independent algorithm or IEEE model. The paper can use its produced witness and surrounding hypotheses to build such a run and derive the Lean certificate, but the Lean theorem cannot establish witness existence for pre-certificate Algorithm 2 outputs. Thus paper_implies_lean is yes, lean_implies_paper is no, and the theorem is not-faithful-weaker rather than genuinely stronger or merely vacuous.

## Implications

- **Lean implies paper:** `no`. For an existing Lean run, its stored G1 does witness the same local algebraic representation. However, the paper claim is witness-producing for every admissible Algorithm 2 computation. The Lean theorem supplies no coverage theorem converting a pre-G1 Algorithm 2 output into a run, and constructing the run already requires G1, its representation, and its bound. It also lacks Algorithm 2, normalized-range IEEE, and computed-r11 provenance. Therefore it cannot recover the paper claim.
- **Paper implies lean:** `yes`. For an admissible paper execution, the standing setting supplies positive dimensions, n<=m, full column rank, and Algorithm 2 matrices Q and upper-triangular R. Condition (3) and its nonsingularity consequence permit choosing the required two-sided leading-block inverses and give r11>0. The standard-error assertion on printed page 308 supplies G1, its representation, and its spectral-norm bound, thereby constructing first_normalization. The exact residual identity, induced-norm action bound, and equation (16) then supply every P11Equation16 field.

## Findings

- **critical / assumed-central-witness:** The theorem applies only after the central selected witness claim has been supplied, so it does not prove that claim for Algorithm 2 outputs.
- **major / algorithm-and-numerical-provenance:** Synthetic exact-real packages qualify as runs without being established as CGS-P computations, and the reverse implication to the paper fails.
- **major / reduced-applicability-not-strength:** Nonempty premises do not make the theorem genuinely stronger; moving the witness-producing burden into the domain reduces applicability and yields a weaker selected claim.
- **note / norm-and-residual-algebra:** Once the prepackaged witness is accepted, the dimensions, signs, norm notions, and equation (16) algebra faithfully match the source.

## Semantic checklist

| Check | Direct | Round-trip |
|---|---|---|
| `S01` | `pass` | `pass` |
| `S02` | `pass` | `pass` |
| `S03` | `fail` | `fail` |
| `S04` | `fail` | `fail` |
| `S05` | `fail` | `fail` |
| `S06` | `pass` | `unclear` |
| `S07` | `fail` | `fail` |
| `S08` | `fail` | `fail` |
| `S09` | `pass` | `unclear` |
| `S10` | `pass` | `pass` |
| `S11` | `fail` | `fail` |
| `S12` | `pass` | `fail` |
| `S13` | `pass` | `pass` |
| `S14` | `fail` | `fail` |
| `S15` | `pass` | `pass` |
| `S16` | `fail` | `fail` |

## Dependency coverage

- Blind translator covered `110` dependencies (`0` hash-reused meanings); unclear: `D091, D105, D107`.
- Direct judge covered `110` dependencies (`0` hash-reused interpretations); failing or unclear: `D001, D002, D003, D010, D012, D013, D027`.

## Remaining uncertainties

- The PDF introduces G1 without an explicit quantifier or dimension. Compatibility with (I+G1)a1 supports the minimally structured m-by-m existential interpretation used here, but the source does not assert uniqueness, diagonality, or componentwise structure.
- The paper globally invokes a first-order O(epsilonM^2) convention while printing the local G1 relation, exact residual identity, and equation (16) without a remainder. No explicit constant or threshold reconciles those presentations; this adjudication follows the selected remainder-free displays while retaining the first-order context as a modeling omission.

## Audit artifacts

- `paper_bencmark/highambench/tasks/P11/T1/faithfulness/agent_outputs/adjudicator.json` (`8233ccb0a2983781a46de413462be4f4c70f8cef8f7a7a8c904e020329aaf167`)
- `paper_bencmark/highambench/tasks/P11/T1/faithfulness/agent_outputs/blind_translation.json` (`db2ff34dcab7539a5fcebc5b66fb7dd8dd6bd05654f0a0424d6b82136e483660`)
- `paper_bencmark/highambench/tasks/P11/T1/faithfulness/agent_outputs/direct_judge.json` (`633594670c1d2dbcd4d1353050e57e609f175acf43241bd9b9b25040436653da`)
- `paper_bencmark/highambench/tasks/P11/T1/faithfulness/agent_outputs/roundtrip_judge.json` (`2113f0945eec0c068e6a07e16b05a70d185c7b4b449ef09c0a26f9f149881384`)
- `paper_bencmark/highambench/tasks/P11/T1/faithfulness/agent_outputs/source_contract.json` (`2c59d1f3ff107aa5feec5ec56164800f60ba3d18227f4bfa8be6c9507b0763d7`)
- `paper_bencmark/highambench/tasks/P11/T1/faithfulness/decision.json` (`94f427b287ab9686c06cdf1f9f12e0a8f8a7b9fa746912d8e0bb3a84c5a9be5c`)
- `paper_bencmark/highambench/tasks/P11/T1/faithfulness/history/20260815T065726Z/agent_outputs/adjudicator.json` (`6dd477313776e9b16971fc243e4725e56a9cede70fa53b11d4d961f767dd50a7`)
- `paper_bencmark/highambench/tasks/P11/T1/faithfulness/history/20260815T065726Z/agent_outputs/blind_translation.json` (`33d631145d9171c5a10d906e00f5f2e935108c805144e36cfec487b50b447365`)
- `paper_bencmark/highambench/tasks/P11/T1/faithfulness/history/20260815T065726Z/agent_outputs/direct_judge.json` (`8fb8d336e29a399b7e6d914ceeef9f05405de6a11d229888e240f8ee6e6b2d2f`)
- `paper_bencmark/highambench/tasks/P11/T1/faithfulness/history/20260815T065726Z/agent_outputs/roundtrip_judge.json` (`1a723fb7ea84b892619076684ca6192e360e13c40472b643678643bd76409bdd`)
- `paper_bencmark/highambench/tasks/P11/T1/faithfulness/history/20260815T065726Z/agent_outputs/source_contract.json` (`b6b205e2131601bc1e987c77ba6a94a5fe0519814e45a8898036c7da6d23f3ba`)
- `paper_bencmark/highambench/tasks/P11/T1/faithfulness/history/20260815T065726Z/decision.json` (`4f63dd898137c097064ef7cbfdcbc1d0d426207f0ecff9b9038045ea2c7d3c0f`)
- `paper_bencmark/highambench/tasks/P11/T1/faithfulness/history/20260815T065726Z/inputs/blind_dossier.md` (`1b49b7fd0dbd315f2767a43f76cab9d60a7d713a1084e882569d4f887bb4d682`)
- `paper_bencmark/highambench/tasks/P11/T1/faithfulness/history/20260815T065726Z/inputs/declaration_dossier.md` (`781435c9386bfcdaf7fc38e1b9355f040381a48b6da9929294395c2565203738`)
- `paper_bencmark/highambench/tasks/P11/T1/faithfulness/history/20260815T065726Z/inputs/source_locator.json` (`e19ebf9ab8fdeca1573b78753863b04c548b278b0ff6e3071e560bcd5dd72c70`)
- `paper_bencmark/highambench/tasks/P11/T1/faithfulness/inputs/blind_dependency_inventory.json` (`5c72bfc5d963a6b802d4751dc530493e3b2f034fdff87a0175a52ff84f81981e`)
- `paper_bencmark/highambench/tasks/P11/T1/faithfulness/inputs/blind_dossier.md` (`46b0d3e1cd0684aaade6805383722507fcb566370117112877cc9c6b08555b96`)
- `paper_bencmark/highambench/tasks/P11/T1/faithfulness/inputs/blind_review_packet.md` (`46b0d3e1cd0684aaade6805383722507fcb566370117112877cc9c6b08555b96`)
- `paper_bencmark/highambench/tasks/P11/T1/faithfulness/inputs/declaration_dossier.md` (`b4d9d7368a5ecccc39630c0586dbc9958721a694a56758ebf4a339a4fe391bf4`)
- `paper_bencmark/highambench/tasks/P11/T1/faithfulness/inputs/dependency_inventory.json` (`fbd36d1780038547e39db84aebc387e08a3735c4ad76360f836f1aba50e4341a`)
- `paper_bencmark/highambench/tasks/P11/T1/faithfulness/inputs/direct_review_packet.md` (`83767df91e32f72c64b72c3f9d795b28d894de45506fb1cfe13be59996f03fc7`)
- `paper_bencmark/highambench/tasks/P11/T1/faithfulness/inputs/source_locator.json` (`81f5fd3ae92d710d611ec7c586273c53619da4de4bd509461ea9e16aba10298e`)
