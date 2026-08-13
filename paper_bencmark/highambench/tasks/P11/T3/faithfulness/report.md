# Faithfulness audit: P11-T3

- Classification: `not-faithful-different`
- Accepted as paper-faithful: `false`
- Adjudicated: `true`
- Target SHA-256: `4dff54d443d74f80beb55e2a83baae6aa601d4d6d0be9b0e16c5c4914d692205`
- Paper SHA-256: `72b7521848be07971a6721ea0356bb898c63e21b8ad3aa109fee8f41517284a5`

## Decision

Primary evidence establishes that the selected claim is Theorem 1(7): a prefixwise spectral-norm loss-of-orthogonality bound for matrices computed by CGS-P, under standing rectangular full-rank assumptions, strict condition (3), explicit constants, and first-order floating-point semantics. The Lean declaration instead proves an exact Frobenius-norm budget for arbitrary square matrix certificates. Its algebraic core is genuine and nonvacuous, but it omits essential source hypotheses and conclusions and excludes general rectangular paper instances. Neither complete statement implies the other, so the consistent classification is not-faithful-different and the declaration is not accepted.

## Implications

- **Lean implies paper:** `no`. The Lean theorem cannot cover general m-by-k paper prefixes because all its matrices are square. It supplies neither CGS-P provenance nor the spectral c4(m,k)kappa_2(R_k)^2 epsilon_M bound. Substituting paper-style residual estimates would still encounter Frobenius-versus-spectral dimension factors and would not reproduce the selected theorem.
- **Paper implies lean:** `no`. The paper proves a first-order spectral-norm result only for prefixes computed by CGS-P under its standing setup and strict condition. It does not assert the declaration's exact Frobenius inequality for every arbitrary square matrix certificate and every collection of scalar majorants. The appendix identity explains the declaration's origin but does not universalize the paper theorem to that target.

## Findings

- **critical / complete-result-linkage:** The selected numerical-analysis theorem is replaced by a supporting algebraic lemma.
- **major / norm-and-dimension-mismatch:** The declaration omits paper instances and cannot recover the stated quantitative bound with its exact constant.
- **major / constants-model-and-remainder:** The numerical content, applicability condition, and approximation order of inequality (7) are absent.
- **note / retained-algebraic-core:** The target has a genuine and nonvacuous relationship to the proof, but matching that proof fragment is insufficient for statement faithfulness.
- **note / source-formalization-gaps:** A faithful mechanization must make additional conventions explicit, but none of these ambiguities reconciles the declaration with the selected theorem.

## Semantic checklist

| Check | Direct | Round-trip |
|---|---|---|
| `S01` | `pass` | `pass` |
| `S02` | `fail` | `fail` |
| `S03` | `fail` | `fail` |
| `S04` | `fail` | `fail` |
| `S05` | `fail` | `fail` |
| `S06` | `fail` | `pass` |
| `S07` | `fail` | `fail` |
| `S08` | `fail` | `fail` |
| `S09` | `fail` | `fail` |
| `S10` | `fail` | `fail` |
| `S11` | `fail` | `fail` |
| `S12` | `fail` | `fail` |
| `S13` | `pass` | `pass` |
| `S14` | `fail` | `fail` |
| `S15` | `fail` | `fail` |
| `S16` | `pass` | `pass` |

## Dependency coverage

- Blind translator covered `48` dependencies; unclear: `none`.
- Direct judge covered `48` dependencies; failing or unclear: `D001, D002, D016`.

## Remaining uncertainties

- The paper does not specify whether condition (3) uses an extended condition number for singular R_k or implicitly assumes invertibility before the condition is formed.
- No coefficient, sign, threshold, or parameter dependence is supplied for the O(epsilon_M^2) remainder, so no exact all-orders version of inequality (7) is determined.
- The paper does not provide complete primitive rounding rules, evaluation orders, or a specific IEEE rounding mode for every operation used by Algorithm 2.
- Behavior for subnormals, overflow, infinities, NaNs, signed zero, and input conversion is not specified beyond the normalized-range restriction and the discussed square-root breakdown.

## Audit artifacts

- `paper_bencmark/highambench/tasks/P11/T3/faithfulness/agent_outputs/adjudicator.json` (`f5e3c756e8e7b98057f8beed5b509c462ac564d8db18fecf6a1b0b02c05ba79c`)
- `paper_bencmark/highambench/tasks/P11/T3/faithfulness/agent_outputs/blind_translation.json` (`8c6a3b0d929496a8d39edc63dea1b0fc258b291d951c5917f916013cc7ccafa0`)
- `paper_bencmark/highambench/tasks/P11/T3/faithfulness/agent_outputs/direct_judge.json` (`a9e043560225a247eb60eb11df7b668eea45bc5d4923976ea9b07cf4bfdc13c8`)
- `paper_bencmark/highambench/tasks/P11/T3/faithfulness/agent_outputs/roundtrip_judge.json` (`56e4467deaf61d214633ea7a6f4f293a7428c07bc78f7bc456219a2002a2f826`)
- `paper_bencmark/highambench/tasks/P11/T3/faithfulness/agent_outputs/source_contract.json` (`194111c880ac26678dbfdb7b61d1e11b2b3bff2fac14b933d761ec649f8f5452`)
- `paper_bencmark/highambench/tasks/P11/T3/faithfulness/decision.json` (`3187a62a92ae74923194e5c4bfee972f15229d302f8858805f8ce521a576c0a9`)
- `paper_bencmark/highambench/tasks/P11/T3/faithfulness/inputs/blind_dossier.md` (`659d69cfdf03fdb38dde10997ba8ab55d5fa1b7f24ee649e3248597c04417b67`)
- `paper_bencmark/highambench/tasks/P11/T3/faithfulness/inputs/declaration_dossier.md` (`e9b1a1ae64a6e5396574b5b2009bb11d9338b209b1b8e60de0e1eae9b6bab8ae`)
- `paper_bencmark/highambench/tasks/P11/T3/faithfulness/inputs/source_locator.json` (`d24934d1efaca21f42feeb65395e13f8827a6f1ddca53a9e5b45136a330a11f4`)
