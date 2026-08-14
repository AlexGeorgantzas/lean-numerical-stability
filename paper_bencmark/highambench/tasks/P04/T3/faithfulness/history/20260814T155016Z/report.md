# Faithfulness audit: P04-T3

- Classification: `not-faithful-different`
- Accepted as paper-faithful: `false`
- Adjudicated: `false`
- Target SHA-256: `8d92998de2588ca675b513db902c36f7ca1d8689c81ad8d8b886c9b5371b4b7e`
- Paper SHA-256: `7ad9ebb7eef9864c58e9a3760ee308be48060647286f8e16cdc740ed4be5b862`

## Decision

The declaration preserves the algebraic perturbation-composition identity, componentwise inequality form, and all displayed second-order coefficient terms. It nevertheless replaces Theorem 4.4's algorithm-generated quantities and hypotheses with strong arbitrary algebraic premises, leaves the required scale as an unconstrained M, disconnects matrix dimension N from n, and omits or conflates the floating-point model. These changes prevent implication in either direction. The result is nonvacuous but is a different generic lemma rather than a faithful formalization of the cited paper theorem.

## Implications

- **Lean implies paper:** `no`. The Lean proposition alone cannot recover Theorem 4.4: algorithm completion does not appear, the preliminary perturbation premises are not derived, M is not the paper scale, dimensions are unlinked, and the precision model is restricted or conflated.
- **Paper implies lean:** `no`. The paper theorem concerns outputs of one specified algorithm with a fixed componentwise scale and floating-point model. It does not establish the Lean proposition's universal conditional claim for arbitrary matrices, decompositions, M, unrelated dimensions, or unrestricted real parameters.

## Findings

- **critical / algorithm-and-quantifier-linkage:** The formal theorem proves only an algebraic composition step and does not establish the paper's algorithmic backward-stability result.
- **critical / missing-componentwise-scale:** The stated Lean conclusion is not the paper's error bound and requires an external premise to recover it.
- **major / dimensions-and-indexing:** The target covers parameter combinations with no paper interpretation and fails to encode the intended matrix/block geometry.
- **major / floating-point-model:** Even the otherwise recognizable coefficient is faithful only under unstated precision identifications and domain restrictions.
- **critical / dimension-and-index-parameter mismatch:** Coefficient indices can be unrelated to the represented matrices, and the statement no longer describes a block LU factorization of the paper's dimensions.
- **critical / mixed-precision coefficient mismatch:** The exact paper coefficient cannot be represented when internal block-FMA precision differs from working precision, so the claimed error bound is a different bound.
- **critical / bound-scale replacement:** The translation neither states nor entails the paper's quantitative perturbation bound.
- **major / algorithm-and-computed-semantics removed:** The translation is a generic perturbation-composition lemma rather than the paper's backward-stability theorem for block LU.
- **major / missing-model-assumptions-and-vacuity:** The statement includes unintended vacuous cases and lacks the hypotheses needed to interpret its constants as floating-point error bounds.
- **note / preserved-semantic-core:** These matching features identify the intended theorem, but they do not repair the dimensional, algorithmic, scale, or numerical-model discrepancies.

## Semantic checklist

| Check | Direct | Round-trip |
|---|---|---|
| `S01` | `pass` | `pass` |
| `S02` | `fail` | `fail` |
| `S03` | `fail` | `fail` |
| `S04` | `fail` | `fail` |
| `S05` | `fail` | `fail` |
| `S06` | `pass` | `fail` |
| `S07` | `fail` | `fail` |
| `S08` | `fail` | `fail` |
| `S09` | `pass` | `pass` |
| `S10` | `fail` | `fail` |
| `S11` | `fail` | `fail` |
| `S12` | `fail` | `fail` |
| `S13` | `pass` | `pass` |
| `S14` | `pass` | `pass` |
| `S15` | `fail` | `fail` |
| `S16` | `pass` | `fail` |

## Dependency coverage

- Blind translator covered `52` dependencies (`0` hash-reused meanings); unclear: `none`.
- Direct judge covered `52` dependencies (`25` hash-reused interpretations); failing or unclear: `D001, D002, D009, D015, D051`.

## Remaining uncertainties

No remaining uncertainties were recorded.

## Audit artifacts

- `paper_bencmark/highambench/tasks/P04/T3/faithfulness/agent_outputs/blind_translation.json` (`30e59264b489cd97d3b85308b5345ca89ca297b2d3d103b345c6f96df813a5ee`)
- `paper_bencmark/highambench/tasks/P04/T3/faithfulness/agent_outputs/direct_judge.json` (`8532745b82324ef46395f892209783f309a8c3eb4b58665ab2f32e276b6f8a69`)
- `paper_bencmark/highambench/tasks/P04/T3/faithfulness/agent_outputs/paper_source_contract.json` (`f23d1d2864ab683fc44d7b4dd917ebb13c36417400d3ee09d7d5a642c3a0d785`)
- `paper_bencmark/highambench/tasks/P04/T3/faithfulness/agent_outputs/roundtrip_judge.json` (`854a2cacf6df1f471885171b29aa604b403e2da488b28a295a9d1db0d10229cd`)
- `paper_bencmark/highambench/tasks/P04/T3/faithfulness/agent_outputs/source_contract.json` (`0014aa4e845579171263aaeb595c2072db8a0d34e6d3ac7b10b022af11ff1bd3`)
- `paper_bencmark/highambench/tasks/P04/T3/faithfulness/decision.json` (`41c992758dd02a47292939852b304c852267dc3502c425e661fd3e80b21541bb`)
- `paper_bencmark/highambench/tasks/P04/T3/faithfulness/inputs/blind_dependency_inventory.json` (`4b94cfee5317878982f957321191b6c3d81d6ddee69428439e3413052fdd68c4`)
- `paper_bencmark/highambench/tasks/P04/T3/faithfulness/inputs/blind_dossier.md` (`f1ab8ee76b928333543348e584f5e460ff81101249dc133bdfaa977fd78c6d3e`)
- `paper_bencmark/highambench/tasks/P04/T3/faithfulness/inputs/blind_review_packet.md` (`f1ab8ee76b928333543348e584f5e460ff81101249dc133bdfaa977fd78c6d3e`)
- `paper_bencmark/highambench/tasks/P04/T3/faithfulness/inputs/declaration_dossier.md` (`d5b7181c0887bed4460f8e3f547f18c6c48f94a5de1fd051fbdbc3162063dc10`)
- `paper_bencmark/highambench/tasks/P04/T3/faithfulness/inputs/dependency_inventory.json` (`a5d04076ab452b00cc1417fad14fcf58d923ffc5e914a0146ab17d2141fc06b5`)
- `paper_bencmark/highambench/tasks/P04/T3/faithfulness/inputs/dependency_reuse_direct.json` (`5dfec669146d909b31a5953df4213ce08063af744286ed5043aa8f1643d98e46`)
- `paper_bencmark/highambench/tasks/P04/T3/faithfulness/inputs/direct_review_packet.md` (`fbeb16df8ad4b21006181f6f1eb103b56f73acf21a7260d75860286a8feba576`)
- `paper_bencmark/highambench/tasks/P04/T3/faithfulness/inputs/paper_source_locator.json` (`609fbccbf417b9661d911f32e2ac6e1c09c3fa4c980c82c53b5c0edd480437f7`)
- `paper_bencmark/highambench/tasks/P04/T3/faithfulness/inputs/source_locator.json` (`146919f1f2e368a94705a639e983d0247830330d80fc4e7582bbb63327a29738`)
