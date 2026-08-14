# Faithfulness audit: P08-T3

- Classification: `not-faithful-different`
- Accepted as paper-faithful: `false`
- Adjudicated: `false`
- Target SHA-256: `1af1bf1c6a340c6b5b01e2b2b060fdb129105cc115e7865a9ba0d9634fab3d20`
- Paper SHA-256: `f520066b46331dcbf25e51345c5ff5ffffe8fcad573d7f46e68834f83b3a2c54`

## Decision

The dependency meanings are clear and the target is a valid, nonvacuous finite-dimensional affine-recurrence bound. Direct comparison with the verified Lemma 4.3 passage shows that it replaces the paper's algorithmic exact-residual theorem by a different abstract proposition: the source's one-sided magnitude recurrence cannot supply hStep, the q_1 base and power m become q_0 and power m+1, the C10/C11/C12 four-term bound is replaced by a generic finite sum, and all numerical-model and conditioning hypotheses disappear. Neither proposition represents or entails the other in the required paper-to-Lean sense, so the result is not-faithful-different.

## Implications

- **Lean implies paper:** `no`. The Lean theorem requires an exact signed affine recurrence with a uniformly bounded additive disturbance, which the paper's one-sided recurrence for residual magnitudes does not supply. It also yields B^(m+1)|q_0| plus a finite sum, not Lemma 4.3's q_1-based B_p^m term and explicit C10/C11/C12 four-term formula, and it contains no algorithmic or floating-point premises from which those quantities could be recovered.
- **Paper implies lean:** `no`. Lemma 4.3 concerns one source-defined residual sequence and one propagation matrix under its numerical-algorithm hypotheses. It neither quantifies arbitrary nonnegative B, arbitrary affine sequences q,d, and arbitrary majorants s nor proves the target's universal exact-recurrence unrolling statement.

## Findings

- **critical / selected-result-substitution:** The Lean proposition does not state the selected paper result; it states a generic recurrence-unrolling fact that could at most be one auxiliary ingredient in a different reconstruction.
- **major / recurrence-semantics:** The paper recurrence does not establish the Lean hypotheses, so the abstract theorem cannot be directly instantiated with the paper residuals.
- **major / constants-and-indexing:** The selected finite-m formula, base case, coefficient identities, and precision-sensitive orders are absent.
- **major / algorithm-and-model-omission:** The theorem is disconnected from the execution model and conditioning regime that give the paper claim its numerical meaning.
- **major / error-notion:** The formal statement does not measure the paper's residual or preserve the exact/computed distinction.
- **critical / statement-substitution:** The two propositions have different mathematical subjects, and neither semantically implies the other.
- **major / algorithm-and-numerical-model:** The theorem is disconnected from the algorithm and numerical model whose error is being bounded.
- **major / bound-shape-and-indexing:** The conclusion cannot be identified with the paper bound by a harmless notation change.
- **major / hypotheses-norms-and-constants:** Applicability and parameter dependence differ from the paper.
- **minor / zero-dimensional-vacuity:** The translation includes an unintended trivial specialization.

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
| `S09` | `fail` | `fail` |
| `S10` | `fail` | `fail` |
| `S11` | `fail` | `fail` |
| `S12` | `fail` | `fail` |
| `S13` | `fail` | `fail` |
| `S14` | `fail` | `fail` |
| `S15` | `fail` | `fail` |
| `S16` | `pass` | `fail` |

## Dependency coverage

- Blind translator covered `40` dependencies (`0` hash-reused meanings); unclear: `none`.
- Direct judge covered `40` dependencies (`25` hash-reused interpretations); failing or unclear: `D001, D006, D008, D009, D012, D023`.

## Remaining uncertainties

No remaining uncertainties were recorded.

## Audit artifacts

- `paper_bencmark/highambench/tasks/P08/T3/faithfulness/agent_outputs/blind_translation.json` (`57036ede799569e746ad9ff7cdbe97849072ae9921428d222a4078901216e34a`)
- `paper_bencmark/highambench/tasks/P08/T3/faithfulness/agent_outputs/direct_judge.json` (`7aa60f2f689e9561a41a1b075028e35166d175776e9acf0f707fa7544526c125`)
- `paper_bencmark/highambench/tasks/P08/T3/faithfulness/agent_outputs/paper_source_contract.json` (`a163817fa5c88f26c8ba3e26089da7681e1ce417d954cec7742e812dbcc3f006`)
- `paper_bencmark/highambench/tasks/P08/T3/faithfulness/agent_outputs/roundtrip_judge.json` (`9d37bb14cedba41acb75423298b9bcfe713a1a69f7afaea5de6e54ca069e6527`)
- `paper_bencmark/highambench/tasks/P08/T3/faithfulness/agent_outputs/source_contract.json` (`842da5765045626400bf3765e50ba5b417bc64160627ea4f349d36c71254b6d3`)
- `paper_bencmark/highambench/tasks/P08/T3/faithfulness/decision.json` (`90eaefef6f7d3bedfd656050fc0cec00e612efd3a91e7f53c45e4b73f05675ca`)
- `paper_bencmark/highambench/tasks/P08/T3/faithfulness/inputs/blind_dependency_inventory.json` (`b133b7c6b9fd52c0a28c6a545ebffa23a0dc649280adb9e269a4c708b6569982`)
- `paper_bencmark/highambench/tasks/P08/T3/faithfulness/inputs/blind_dossier.md` (`ff29c3f51276b219aba1a6012871be09ad25566633ab9c8ac77970a265d943d2`)
- `paper_bencmark/highambench/tasks/P08/T3/faithfulness/inputs/blind_review_packet.md` (`ff29c3f51276b219aba1a6012871be09ad25566633ab9c8ac77970a265d943d2`)
- `paper_bencmark/highambench/tasks/P08/T3/faithfulness/inputs/declaration_dossier.md` (`80b376bf40cc842bcde0cf55df76ee3bf1cf0bce14b26dc1ae3ca26a59060501`)
- `paper_bencmark/highambench/tasks/P08/T3/faithfulness/inputs/dependency_inventory.json` (`a62a1ef7e45e10f8a3e1e87d3f180b22d1137fae465996104706bb100cde9d2d`)
- `paper_bencmark/highambench/tasks/P08/T3/faithfulness/inputs/dependency_reuse_direct.json` (`d5a4ed06ca753323f783656e77058e1329698ef31b33a09749d9a304a7e8de8e`)
- `paper_bencmark/highambench/tasks/P08/T3/faithfulness/inputs/direct_review_packet.md` (`b4334fc81066015a6dd45f92082aa02961f73a807ad01a2a94cdcce29027d507`)
- `paper_bencmark/highambench/tasks/P08/T3/faithfulness/inputs/paper_source_locator.json` (`3242b63a529acc04514175dadb3f98deebf67f847a6bf33be0b5bb7850f84391`)
- `paper_bencmark/highambench/tasks/P08/T3/faithfulness/inputs/source_locator.json` (`72d2ab219970ae0b0c6623e8f884275995b11ab5fd34e9d16952319ccb1a68b5`)
