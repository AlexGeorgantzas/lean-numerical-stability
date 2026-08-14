# Faithfulness audit: P07-T1

- Classification: `not-faithful-different`
- Accepted as paper-faithful: `false`
- Adjudicated: `false`
- Target SHA-256: `a2c42582fa017f4bc27749ec721ce360de2774ec999b15e3c18f9c54dd10b3a4`
- Paper SHA-256: `4c4d638b359719f47e2c4664a50e9fa8e4704e8b6b39923d73c41883a97c5790`

## Decision

The Lean target is a valid and nonvacuous generic perturbation theorem: its Euclidean lower-gain and operator-norm certificates imply injectivity of Y + DeltaY, and suitable exact choices recover the qualitative full-rank conjunct of Lemma 3.2. However, it does not encode the computed forward-substitution matrix, the exact epsilon_2 definition, the inherited algorithmic setup, or the lemma's condition-number bound. Because the Lean statement cannot imply the complete paper result and the algorithm-specific paper statement does not imply the target's universal generalization, the correct classification is not-faithful-different.

## Implications

- **Lean implies paper:** `no`. The Lean proposition can recover the paper's full-rank conclusion after externally identifying Y with A R_hat^{-1}, choosing exact norm certificates, and identifying Y + DeltaY with Y_hat. It cannot supply the condition-number bound or establish the required algorithmic finite-precision identities, so it does not imply Lemma 3.2 as stated.
- **Paper implies lean:** `no`. Lemma 3.2 concerns the particular R_hat and Y_hat produced by the paper's algorithm and does not state the target's universally quantified perturbation theorem for arbitrary dimensions, matrices, and lower/upper norm certificates. The generic proof idea may extend, but the cited paper result itself does not imply that broader proposition.

## Findings

- **critical / conclusion-completeness:** The formal proposition omits the paper result's entire quantitative condition-number guarantee.
- **major / algorithm-linkage:** The target proves a generic perturbation fact without formalizing that it applies to the matrix produced by the analyzed algorithm.
- **major / perturbation-parameter-semantics:** The certificates form a valid sufficient rank-preservation condition, but the exact paper error measure and its pseudoinverse scaling are absent and require external reconstruction.
- **major / scope-and-dimensions:** The target is broader in domain while weaker in conclusion, making the two statements incomparable rather than a faithful strengthening or weakening.
- **critical / conclusion-completeness:** One of the paper lemma's two principal conclusions is entirely absent.
- **major / algorithm-and-error-provenance:** The proposition no longer describes the algorithmic quantity or numerical error analyzed by the paper.
- **major / constants-and-hypotheses:** The translation proves a related sufficient rank-preservation principle rather than the paper's stated perturbation theorem.
- **major / binders-and-dimensions:** The changed scope prevents implication in either direction and introduces trivial or vacuous dimension cases.
- **note / dependency-ledger:** The dependency ledger is internally adequate for the reduced generic proposition, but cannot compensate for the paper concepts omitted from that proposition.

## Semantic checklist

| Check | Direct | Round-trip |
|---|---|---|
| `S01` | `pass` | `pass` |
| `S02` | `fail` | `fail` |
| `S03` | `fail` | `fail` |
| `S04` | `fail` | `fail` |
| `S05` | `fail` | `fail` |
| `S06` | `fail` | `fail` |
| `S07` | `fail` | `fail` |
| `S08` | `fail` | `fail` |
| `S09` | `pass` | `fail` |
| `S10` | `fail` | `fail` |
| `S11` | `fail` | `fail` |
| `S12` | `fail` | `fail` |
| `S13` | `fail` | `fail` |
| `S14` | `pass` | `pass` |
| `S15` | `fail` | `fail` |
| `S16` | `pass` | `fail` |

## Dependency coverage

- Blind translator covered `29` dependencies (`0` hash-reused meanings); unclear: `none`.
- Direct judge covered `29` dependencies (`0` hash-reused interpretations); failing or unclear: `D002, D003, D006, D008, D009`.

## Remaining uncertainties

No remaining uncertainties were recorded.

## Audit artifacts

- `paper_bencmark/highambench/tasks/P07/T1/faithfulness/agent_outputs/blind_translation.json` (`1a5f913a72fcc01f18ff98be99f154fe2bb7cc1f2b08e559ebf2c942dccd1c8e`)
- `paper_bencmark/highambench/tasks/P07/T1/faithfulness/agent_outputs/direct_judge.json` (`fcf96b7d6b6aebe33e6de12f564adff3ddd93e6d63fc418819080a48e548fdee`)
- `paper_bencmark/highambench/tasks/P07/T1/faithfulness/agent_outputs/paper_source_contract.json` (`822fe7aa06960deeaa078b8ac855714c9b957ac1656f37de3dcbbaa9f707f076`)
- `paper_bencmark/highambench/tasks/P07/T1/faithfulness/agent_outputs/roundtrip_judge.json` (`6ee5b1803086fd09285849ce73ea89ae0e2656ea1ea454c7d49196c0f059c932`)
- `paper_bencmark/highambench/tasks/P07/T1/faithfulness/agent_outputs/source_contract.json` (`3ccaa2fec9cc5d00324aeb0ad914b60da416204b515a212a7c107e149e5e8a29`)
- `paper_bencmark/highambench/tasks/P07/T1/faithfulness/decision.json` (`57db9aa1bb8458ae591140a5b459ca938fc6efb2f14c9e74bfe6896541021579`)
- `paper_bencmark/highambench/tasks/P07/T1/faithfulness/inputs/blind_dependency_inventory.json` (`6cf2e01bbd85b41359eba7e0190c47febaeb3c25eb343d3615dc72cb9aad4ded`)
- `paper_bencmark/highambench/tasks/P07/T1/faithfulness/inputs/blind_dossier.md` (`7db258cd5b9d617d6b05e073fc3c93436c8e83d7adf962c05bedd42855fb5d1f`)
- `paper_bencmark/highambench/tasks/P07/T1/faithfulness/inputs/blind_review_packet.md` (`7db258cd5b9d617d6b05e073fc3c93436c8e83d7adf962c05bedd42855fb5d1f`)
- `paper_bencmark/highambench/tasks/P07/T1/faithfulness/inputs/declaration_dossier.md` (`0a81c8e6eb8b69f084e1e2c1ee64c6caff4af385b9ffcb2daf66f50207b4e3a2`)
- `paper_bencmark/highambench/tasks/P07/T1/faithfulness/inputs/dependency_inventory.json` (`a3899633a2105b32f1466bbea0c7b41bb07b7a0643ee8d049441d05b346a2712`)
- `paper_bencmark/highambench/tasks/P07/T1/faithfulness/inputs/direct_review_packet.md` (`d2a3bb80810c1a942d56dbd0a2d95edc6c6d69fd249001206836a19b576e8a54`)
- `paper_bencmark/highambench/tasks/P07/T1/faithfulness/inputs/paper_source_locator.json` (`7d16e3f6a7585561fffc335fcd99a77aec72a33a336198eca2c59fb9113440a2`)
- `paper_bencmark/highambench/tasks/P07/T1/faithfulness/inputs/source_locator.json` (`c37af6b87cad9f4d467cde52ff0d31f545a33c3f4a92ce201b205180cfb3c6b7`)
