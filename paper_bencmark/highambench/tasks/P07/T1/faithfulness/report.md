# Faithfulness audit: P07-T1

- Classification: `faithful-stronger`
- Accepted as paper-faithful: `true`
- Adjudicated: `true`
- Target SHA-256: `0685cd4d49fff279a72a0c648c291de38652a15a0970ed79ea7bdc60c027e7f4`
- Paper SHA-256: `4c4d638b359719f47e2c4664a50e9fa8e4704e8b6b39923d73c41883a97c5790`

## Decision

Primary PDF evidence confirms exact agreement on the reference matrix, DeltaY, epsilon_2, strict threshold, full-column-rank conclusion, spectral norms, pseudoinverse, and condition-number bound. Constructor inspection confirms that the formal preprocessing record does not prove actual HHQR provenance or epsilon_1<1; instead it directly assumes the algebraic consequences needed by Lemma 3.2. That substitution strictly enlarges the domain, and an explicit epsilon_1-failing exact-run instance establishes nonvacuity. The concrete summation order and ideal relative-error model are compatible refinements whose unspecified details are absorbed into DeltaY for this selected result. Thus Lean implies the paper claim, the reverse implication fails, and the appropriate accepted classification is faithful-stronger.

## Implications

- **Lean implies paper:** `yes`. Restricting the formal theorem to the paper's Lemma 3.1 setup supplies D017's algebraic fields, while D027 is the row-wise forward-substitution recurrence and D018 identifies DeltaY exactly. The spectral records then make epsilon_2 and both condition numbers identical to the paper's quantities, so the formal conjunction yields both conclusions of Lemma 3.2.
- **Paper implies lean:** `no`. The paper statement assumes the inherited computed-HHQR setting and epsilon_1<1 route. D017 instead permits additional invertible factors with arbitrary sketch and QR residuals, and D025 permits any nonnegative u. The explicit epsilon_1=2, DeltaY=0 instance demonstrates a substantive formal case not covered by the stated paper theorem.

## Findings

- **note / genuine strengthening:** The theorem has strictly broader, nonvacuous applicability while preserving the selected conclusion.
- **note / forward-substitution order:** This is an implementation refinement; because Lemma 3.2 uses only the realized DeltaY, it does not change the perturbation statement.
- **note / floating-point abstraction:** The formal numerical-model domain is broader in u and should not be read as hardware-level IEEE coverage; neither point invalidates the selected algebraic lemma.

## Semantic checklist

| Check | Direct | Round-trip |
|---|---|---|
| `S01` | `pass` | `pass` |
| `S02` | `pass` | `pass` |
| `S03` | `pass` | `pass` |
| `S04` | `pass` | `pass` |
| `S05` | `pass` | `pass` |
| `S06` | `pass` | `pass` |
| `S07` | `pass` | `pass` |
| `S08` | `pass` | `fail` |
| `S09` | `pass` | `pass` |
| `S10` | `pass` | `unclear` |
| `S11` | `pass` | `fail` |
| `S12` | `pass` | `pass` |
| `S13` | `pass` | `pass` |
| `S14` | `pass` | `pass` |
| `S15` | `pass` | `fail` |
| `S16` | `pass` | `pass` |

## Dependency coverage

- Blind translator covered `112` dependencies (`0` hash-reused meanings); unclear: `none`.
- Direct judge covered `112` dependencies (`0` hash-reused interpretations); failing or unclear: `none`.

## Remaining uncertainties

- The PDF does not determine the primitive accumulation association or singleton behavior of forward substitution; the declaration's increasing-index left fold is a defensible concretization but is not source-confirmed operation detail.
- The PDF does not specify a rounding mode or exceptional-value policy, so the declaration's real relative-error operations cannot be identified with a particular IEEE implementation.

## Audit artifacts

- `paper_bencmark/highambench/tasks/P07/T1/faithfulness/agent_outputs/adjudicator.json` (`3b372fef84dba287ebb1e300e34988de1c938ebb2c2b5a552593b602fb36ed42`)
- `paper_bencmark/highambench/tasks/P07/T1/faithfulness/agent_outputs/blind_translation.json` (`96f8509f803c4715f0d50c519e43ad5824dcfabbe42059b37e14766120a4758f`)
- `paper_bencmark/highambench/tasks/P07/T1/faithfulness/agent_outputs/direct_judge.json` (`73b105afccbc681aeb7b93a5e9d08bd39ffd736a22b5aeccc6c5a195e2db23e6`)
- `paper_bencmark/highambench/tasks/P07/T1/faithfulness/agent_outputs/roundtrip_judge.json` (`14ebeafb2e068e1e202e9eda09706aba36bda502014cfc4e355991bc7d13867c`)
- `paper_bencmark/highambench/tasks/P07/T1/faithfulness/agent_outputs/source_contract.json` (`bc773c9582bf36afc2f337c666d0218ec9530ea388ff83d04cf52d5cfd324ad9`)
- `paper_bencmark/highambench/tasks/P07/T1/faithfulness/decision.json` (`a8a42d56ad254a95ecaab9d6e77242f8544db6152fcf96deeacef7a24bbf72a9`)
- `paper_bencmark/highambench/tasks/P07/T1/faithfulness/history/20260814T220439Z/agent_outputs/blind_translation.json` (`1a5f913a72fcc01f18ff98be99f154fe2bb7cc1f2b08e559ebf2c942dccd1c8e`)
- `paper_bencmark/highambench/tasks/P07/T1/faithfulness/history/20260814T220439Z/agent_outputs/direct_judge.json` (`fcf96b7d6b6aebe33e6de12f564adff3ddd93e6d63fc418819080a48e548fdee`)
- `paper_bencmark/highambench/tasks/P07/T1/faithfulness/history/20260814T220439Z/agent_outputs/paper_source_contract.json` (`822fe7aa06960deeaa078b8ac855714c9b957ac1656f37de3dcbbaa9f707f076`)
- `paper_bencmark/highambench/tasks/P07/T1/faithfulness/history/20260814T220439Z/agent_outputs/roundtrip_judge.json` (`6ee5b1803086fd09285849ce73ea89ae0e2656ea1ea454c7d49196c0f059c932`)
- `paper_bencmark/highambench/tasks/P07/T1/faithfulness/history/20260814T220439Z/agent_outputs/source_contract.json` (`3ccaa2fec9cc5d00324aeb0ad914b60da416204b515a212a7c107e149e5e8a29`)
- `paper_bencmark/highambench/tasks/P07/T1/faithfulness/history/20260814T220439Z/decision.json` (`57db9aa1bb8458ae591140a5b459ca938fc6efb2f14c9e74bfe6896541021579`)
- `paper_bencmark/highambench/tasks/P07/T1/faithfulness/history/20260814T220439Z/inputs/blind_dependency_inventory.json` (`6cf2e01bbd85b41359eba7e0190c47febaeb3c25eb343d3615dc72cb9aad4ded`)
- `paper_bencmark/highambench/tasks/P07/T1/faithfulness/history/20260814T220439Z/inputs/blind_dossier.md` (`7db258cd5b9d617d6b05e073fc3c93436c8e83d7adf962c05bedd42855fb5d1f`)
- `paper_bencmark/highambench/tasks/P07/T1/faithfulness/history/20260814T220439Z/inputs/blind_review_packet.md` (`7db258cd5b9d617d6b05e073fc3c93436c8e83d7adf962c05bedd42855fb5d1f`)
- `paper_bencmark/highambench/tasks/P07/T1/faithfulness/history/20260814T220439Z/inputs/declaration_dossier.md` (`0a81c8e6eb8b69f084e1e2c1ee64c6caff4af385b9ffcb2daf66f50207b4e3a2`)
- `paper_bencmark/highambench/tasks/P07/T1/faithfulness/history/20260814T220439Z/inputs/dependency_inventory.json` (`a3899633a2105b32f1466bbea0c7b41bb07b7a0643ee8d049441d05b346a2712`)
- `paper_bencmark/highambench/tasks/P07/T1/faithfulness/history/20260814T220439Z/inputs/direct_review_packet.md` (`d2a3bb80810c1a942d56dbd0a2d95edc6c6d69fd249001206836a19b576e8a54`)
- `paper_bencmark/highambench/tasks/P07/T1/faithfulness/history/20260814T220439Z/inputs/paper_source_locator.json` (`7d16e3f6a7585561fffc335fcd99a77aec72a33a336198eca2c59fb9113440a2`)
- `paper_bencmark/highambench/tasks/P07/T1/faithfulness/history/20260814T220439Z/inputs/source_locator.json` (`c37af6b87cad9f4d467cde52ff0d31f545a33c3f4a92ce201b205180cfb3c6b7`)
- `paper_bencmark/highambench/tasks/P07/T1/faithfulness/inputs/blind_dependency_inventory.json` (`765e6dea00daa95ff009eb3de593b7f6e263294e08e36b5af140b7ff4432ca18`)
- `paper_bencmark/highambench/tasks/P07/T1/faithfulness/inputs/blind_dossier.md` (`1f5081881ebda37c43c038c177afeb3cc38a0d1d0a015f8efe9776b7c7ed0c08`)
- `paper_bencmark/highambench/tasks/P07/T1/faithfulness/inputs/blind_review_packet.md` (`1f5081881ebda37c43c038c177afeb3cc38a0d1d0a015f8efe9776b7c7ed0c08`)
- `paper_bencmark/highambench/tasks/P07/T1/faithfulness/inputs/declaration_dossier.md` (`6a84321e5c68a3391000a8d3705f1d9e6040b8f9e6895522e531c562e45ad0ad`)
- `paper_bencmark/highambench/tasks/P07/T1/faithfulness/inputs/dependency_inventory.json` (`97f5de78462722e04a28561252a7c2000eed23398352de681980e3f73697335d`)
- `paper_bencmark/highambench/tasks/P07/T1/faithfulness/inputs/direct_review_packet.md` (`534fc7bde3b41dfd68af113d1087d1c4460819e011b8f3be163574d188694e6e`)
- `paper_bencmark/highambench/tasks/P07/T1/faithfulness/inputs/source_locator.json` (`8ea5ad8f6a1f882ec26e9335fab8b93097ddfaf71f70ca4eb39640c0bbde0f85`)
