# Faithfulness audit: P11-T3

- Classification: `not-faithful-different`
- Accepted as paper-faithful: `false`
- Adjudicated: `false`
- Target SHA-256: `b6ecd17c207880a5b97422a423981ad79c542ee4f29eddfd1b4b5c460e1cf48a`
- Paper SHA-256: `72b7521848be07971a6721ea0356bb898c63e21b8ad3aa109fee8f41517284a5`

## Decision

The matrix dimensions, prefix indexing, orthogonality defect, spectral norm, inverse-based condition number, and residual signs are represented correctly, and the run type is nonempty. Nevertheless, the formal c1 formula is wrong, so c4 is wrong; the numerical execution model is not IEEE semantics; selected conclusions of Theorem 1 are assumed through certificates; the target omits four explicit conclusions; and the source's O(epsilonM^2) qualification is replaced by a witness-dependent exact term. These are decisive semantic differences, not an acceptable stronger theorem or a harmless specialization. :codex-file-citation{path="/tmp/lean-fp-analysis-p11t3-audit/paper_bencmark/reference_papers/P11_A note on the error analysis of classical Gram–Schmidt.pdf" purpose="source"}

## Implications

- **Lean implies paper:** `no`. The Lean theorem applies only after supplying permissive traces and certificates containing selected residual estimates, uses a different c1 and c4, and concludes only equation (7). It therefore cannot establish the paper's theorem from the paper's stated assumptions.
- **Paper implies lean:** `no`. The paper's first-order result does not provide the Lean certificate fields or their exact witness-dependent remainder coefficient, and its larger source c4 bound cannot imply the Lean bound using the incorrectly smaller c4 with only an O(epsilonM^2) adjustment.

## Findings

- **critical / incorrect-constant:** Both condition (3) and the principal coefficient in equation (7) are changed for m>1, preventing either claimed implication.
- **critical / derived-results-assumed:** The target formalizes an algebraic consequence for pre-certified prefixes rather than the paper's floating-point theorem.
- **major / floating-point-model:** The run type admits executions not justified by the paper's numerical model.
- **major / conclusion-incompleteness:** The declaration does not represent the complete cited theorem.
- **major / higher-order-semantics:** The formal statement has different uniformity and witness dependence from the paper's first-order claim.
- **critical / conclusion completeness and role reversal:** The translated proposition does not express the complete paper result and changes conclusions into hypotheses.
- **critical / constant mismatch:** The main first-order constant and smallness condition are numerically different whenever m is generally greater than one.
- **major / algorithm and floating-point provenance:** The proposition applies to an abstract certificate class rather than precisely to the paper's computed CGS-P outputs.
- **major / higher-order treatment:** The translated remainder is neither the same asymptotic assertion nor a uniformly justified strengthening of it.
- **major / quantifier and domain mismatch:** Witness dependence and admissible inputs differ enough that neither complete statement implies the other.

## Semantic checklist

| Check | Direct | Round-trip |
|---|---|---|
| `S01` | `pass` | `pass` |
| `S02` | `pass` | `fail` |
| `S03` | `fail` | `fail` |
| `S04` | `fail` | `fail` |
| `S05` | `fail` | `fail` |
| `S06` | `fail` | `pass` |
| `S07` | `pass` | `fail` |
| `S08` | `fail` | `fail` |
| `S09` | `pass` | `pass` |
| `S10` | `fail` | `fail` |
| `S11` | `fail` | `fail` |
| `S12` | `fail` | `fail` |
| `S13` | `pass` | `pass` |
| `S14` | `fail` | `fail` |
| `S15` | `fail` | `fail` |
| `S16` | `pass` | `fail` |

## Dependency coverage

- Blind translator covered `115` dependencies (`0` hash-reused meanings); unclear: `none`.
- Direct judge covered `115` dependencies (`0` hash-reused interpretations); failing or unclear: `D001, D006, D012, D014, D015, D018, D019, D020, D021, D022, D031, D032, D037`.

## Remaining uncertainties

No remaining uncertainties were recorded.

## Audit artifacts

- `paper_bencmark/highambench/tasks/P11/T3/faithfulness/agent_outputs/blind_translation.json` (`d394f63263058025e9cee598f5579d034e6c71021cd79baa353d920bfcbdca49`)
- `paper_bencmark/highambench/tasks/P11/T3/faithfulness/agent_outputs/direct_judge.json` (`a31fbb6dc1dd588fc79fac87f1d7dde429088ee6580df9390fb4dff8d7dacca9`)
- `paper_bencmark/highambench/tasks/P11/T3/faithfulness/agent_outputs/roundtrip_judge.json` (`953165a95ea6bb4309976bee92d0f1433642008d7b7bce0d1bdde3f99d9a5a8c`)
- `paper_bencmark/highambench/tasks/P11/T3/faithfulness/agent_outputs/source_contract.json` (`47e65a65f2c17dd755dbc441bc82dbfdca1fdb2de79b21ff21ea5971edd8516b`)
- `paper_bencmark/highambench/tasks/P11/T3/faithfulness/decision.json` (`921f6a7a0e8e580f7e53e755321f690fa2d82932dadb47f27a9643df39eaf1d2`)
- `paper_bencmark/highambench/tasks/P11/T3/faithfulness/history/20260815T081207Z/agent_outputs/adjudicator.json` (`f5e3c756e8e7b98057f8beed5b509c462ac564d8db18fecf6a1b0b02c05ba79c`)
- `paper_bencmark/highambench/tasks/P11/T3/faithfulness/history/20260815T081207Z/agent_outputs/blind_translation.json` (`8c6a3b0d929496a8d39edc63dea1b0fc258b291d951c5917f916013cc7ccafa0`)
- `paper_bencmark/highambench/tasks/P11/T3/faithfulness/history/20260815T081207Z/agent_outputs/direct_judge.json` (`a9e043560225a247eb60eb11df7b668eea45bc5d4923976ea9b07cf4bfdc13c8`)
- `paper_bencmark/highambench/tasks/P11/T3/faithfulness/history/20260815T081207Z/agent_outputs/roundtrip_judge.json` (`56e4467deaf61d214633ea7a6f4f293a7428c07bc78f7bc456219a2002a2f826`)
- `paper_bencmark/highambench/tasks/P11/T3/faithfulness/history/20260815T081207Z/agent_outputs/source_contract.json` (`194111c880ac26678dbfdb7b61d1e11b2b3bff2fac14b933d761ec649f8f5452`)
- `paper_bencmark/highambench/tasks/P11/T3/faithfulness/history/20260815T081207Z/decision.json` (`3187a62a92ae74923194e5c4bfee972f15229d302f8858805f8ce521a576c0a9`)
- `paper_bencmark/highambench/tasks/P11/T3/faithfulness/history/20260815T081207Z/inputs/blind_dossier.md` (`659d69cfdf03fdb38dde10997ba8ab55d5fa1b7f24ee649e3248597c04417b67`)
- `paper_bencmark/highambench/tasks/P11/T3/faithfulness/history/20260815T081207Z/inputs/declaration_dossier.md` (`e9b1a1ae64a6e5396574b5b2009bb11d9338b209b1b8e60de0e1eae9b6bab8ae`)
- `paper_bencmark/highambench/tasks/P11/T3/faithfulness/history/20260815T081207Z/inputs/source_locator.json` (`d24934d1efaca21f42feeb65395e13f8827a6f1ddca53a9e5b45136a330a11f4`)
- `paper_bencmark/highambench/tasks/P11/T3/faithfulness/inputs/blind_dependency_inventory.json` (`a68c90ccbc94fb63ddf2908f73babd5a653b0b512c6d64433a266eb0d3ad6c2e`)
- `paper_bencmark/highambench/tasks/P11/T3/faithfulness/inputs/blind_dossier.md` (`661c9a60c9ec4ac226429c7ee2182b7e389710f9134ab271c657dcb698978ccc`)
- `paper_bencmark/highambench/tasks/P11/T3/faithfulness/inputs/blind_review_packet.md` (`661c9a60c9ec4ac226429c7ee2182b7e389710f9134ab271c657dcb698978ccc`)
- `paper_bencmark/highambench/tasks/P11/T3/faithfulness/inputs/declaration_dossier.md` (`2e5897fdfeb98a5173677a84f05f628aca74356c2ecdd5012003470fd7bdba19`)
- `paper_bencmark/highambench/tasks/P11/T3/faithfulness/inputs/dependency_inventory.json` (`bb4a46bccc95e435c421e057bc927a0cb18320deaf6a2245de9c0bde34c8d288`)
- `paper_bencmark/highambench/tasks/P11/T3/faithfulness/inputs/direct_review_packet.md` (`215ca35c06a41ff1a2dc709c845314979a20b099ee638826967dfa273e064074`)
- `paper_bencmark/highambench/tasks/P11/T3/faithfulness/inputs/source_locator.json` (`462bb0ce8a8f57893759800327728a43d0213f88c39ae9c5db657ef92813e402`)
