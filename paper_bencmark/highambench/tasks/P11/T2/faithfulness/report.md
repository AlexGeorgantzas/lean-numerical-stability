# Faithfulness audit: P11-T2

- Classification: `not-faithful-different`
- Accepted as paper-faithful: `false`
- Adjudicated: `true`
- Target SHA-256: `0841de2615bd65b411edf5fd3aef97f97877d931fe8963f505b2f668abea4c2e`
- Paper SHA-256: `72b7521848be07971a6721ea0356bb898c63e21b8ad3aa109fee8f41517284a5`

## Decision

Primary evidence resolves the selected object as the exact supporting identity used to derive bound (7), not the complete numerical theorem. Lean faithfully reproduces that identity on square real matrices and validly generalizes away unnecessary algorithmic and rounding hypotheses. It nevertheless replaces the paper's m-by-k geometry with a single square dimension and adds arbitrary non-algorithmic data and n = 0. Consequently Lean does not retain every source instance, while the paper does not assert Lean's broader square scope. Both implication directions are therefore no, so the consistent classification is not-faithful-different and the declaration is not accepted.

## Implications

- **Lean implies paper:** `no`. The source identity has genuine m-by-k instances with m > k, whereas every Lean binder is n-by-n. No binder or declared correspondence represents those tall factors. Generalizing away algorithmic hypotheses does not restore the omitted dimensional instances.
- **Paper implies lean:** `no`. The paper states the identity for positive-index leading factors computed in the Theorem 1 CGS-P context. It does not state the universal claim for every arbitrary square tuple satisfying only hQR and hInv, nor the n = 0 case. The fact that this broader square claim is independently derivable algebraically does not make it a consequence of the paper's stated scope.

## Findings

- **major / dimension-specialization:** Lean does not directly retain the paper's tall-matrix instances and therefore cannot be classified as faithful-stronger.
- **major / mixed-statement-scope:** Lean broadens admissible algebraic data while narrowing dimensions, making the complete scopes incomparable.
- **minor / index-domain:** Lean adds a degenerate empty-dimensional instance absent from the source, although its theorem also has nontrivial positive-dimensional instances.
- **note / algebraic-core:** Within the square specialization, the exact formula, signs, residual convention, conjugation order, and quadratic term are faithful.
- **note / exact-supporting-identity:** The absence of floating-point and norm machinery from Lean is appropriate for the selected exact identity and should not independently count as a formula-level failure.

## Semantic checklist

| Check | Direct | Round-trip |
|---|---|---|
| `S01` | `pass` | `pass` |
| `S02` | `fail` | `fail` |
| `S03` | `fail` | `fail` |
| `S04` | `fail` | `fail` |
| `S05` | `pass` | `pass` |
| `S06` | `pass` | `pass` |
| `S07` | `pass` | `pass` |
| `S08` | `fail` | `fail` |
| `S09` | `not-applicable` | `not-applicable` |
| `S10` | `fail` | `fail` |
| `S11` | `not-applicable` | `fail` |
| `S12` | `pass` | `pass` |
| `S13` | `pass` | `pass` |
| `S14` | `pass` | `pass` |
| `S15` | `fail` | `fail` |
| `S16` | `pass` | `pass` |

## Dependency coverage

- Blind translator covered `32` dependencies; unclear: `none`.
- Direct judge covered `32` dependencies; failing or unclear: `D001, D012`.

## Remaining uncertainties

- The paper never states the page-312 identity as a separately quantified lemma, so its maximal intended generality beyond the enclosing computed CGS-P factors is not textually fixed. This does not affect the classification because Lean still omits the explicit m > k source instances.
- The paper defines kappa_2(R_k) using R_k^{-1} before saying condition (3) assures nonsingularity, without stating an extended condition-number convention for singular matrices. This presentation issue is immaterial once the selected identity's inverse is assumed.
- The paper displays only an addition rounding relation although Algorithm 2 also uses products, norms, division, and square roots. No fuller operation model can be inferred from the cited pages, but none is needed inside the selected exact identity.

## Audit artifacts

- `paper_bencmark/highambench/tasks/P11/T2/faithfulness/agent_outputs/adjudicator.json` (`58027bc895e31027cd9223258fb7f5324c820f4e2491299358f3697631188772`)
- `paper_bencmark/highambench/tasks/P11/T2/faithfulness/agent_outputs/blind_translation.json` (`ccbd9b3259835e43f8344955168694cb89770144127cdabfed421d2ab605642d`)
- `paper_bencmark/highambench/tasks/P11/T2/faithfulness/agent_outputs/direct_judge.json` (`40e1193f056d775ab0c8245c13c5dcd4af7590b9fd0e7f0014eb75e64798efc8`)
- `paper_bencmark/highambench/tasks/P11/T2/faithfulness/agent_outputs/roundtrip_judge.json` (`d1babda4520b70266e7bf79fa4d6448bea29e83d56c4fffdbe9ca87b311b5772`)
- `paper_bencmark/highambench/tasks/P11/T2/faithfulness/agent_outputs/source_contract.json` (`3eb4845c275c93ac76ad1216225513ce38b2edb9a1fc467dcab505544414fc20`)
- `paper_bencmark/highambench/tasks/P11/T2/faithfulness/decision.json` (`271595e9996c98e396b28bbb4ba637a51c3483b929bc95a2fb932e5aa3e1c712`)
- `paper_bencmark/highambench/tasks/P11/T2/faithfulness/inputs/blind_dossier.md` (`8caf1fe2aa2c0287b9c6c1380aa53b2b3af6e367a3fd1f06dc44d39befd6bd20`)
- `paper_bencmark/highambench/tasks/P11/T2/faithfulness/inputs/declaration_dossier.md` (`9cf6428bd30c41300100c8cd58bda8d4b2c9c49a42fc1c8130f8cdf2dc80b21f`)
- `paper_bencmark/highambench/tasks/P11/T2/faithfulness/inputs/source_locator.json` (`d852b170574fb224f1934e9143f7623c0f0ed210cd7cc6730b4373e98cdf97e7`)
