# Faithfulness audit: P01-T1

- Classification: `faithful-equivalent`
- Accepted as paper-faithful: `true`
- Adjudicated: `true`
- Target SHA-256: `ee6bd516f8c592936e1f9b0b9d54049579ba7aee7714cdb871b230332e0f1d19`
- Paper SHA-256: `d5ad99fac5022da54dbe02721ea57116df3cec15badddd7c96c344328718fea7`

## Decision

Primary inspection resolves the disagreement in favor of equivalence to the selected P01-T1 proposition. The source packet deliberately combines the power-of-two pairwise bound with the nonnegative-input simplification. Lean has exactly 2^r real inputs, the same balanced adjacent-pair tree, the same per-operation relative-error model, a separate exact real sum, scalar absolute forward error, and the exact gamma_r coefficient. Its explicit gamma-validity premise supplies a condition required by the paper's displayed denominator. The preceding pathwise representation and the separate relative-error quotient are not omitted conjuncts of the selected absolute bound. Both implications are therefore yes, while the declaration remains narrower than and must not be advertised as the full signed-input equation (3.6).

## Implications

- **Lean implies paper:** `yes`. Unfolding GammaValid, gamma, pairwiseSum, and the exact Finset sum gives the paper's power-of-two balanced pairwise computation and gamma_r absolute bound on nonnegative inputs. This implication is to the selected nonnegative specialization and does not assert unrestricted equation (3.6) for signed inputs.
- **Paper implies lean:** `yes`. Apply equation (3.6) with n=2^r to the tree defined by pairwiseSum. StandardAddModel supplies the per-addition relative-error witnesses, GammaValid supplies the mathematically necessary positive denominator, and hv gives sum_i |v i|=sum_i v i. This yields the Lean inequality, including the all-zero case.

## Findings

- **note / selected-specialization:** The declaration is equivalent to the selected nonnegative result but cannot replace the unrestricted signed-input equation (3.6).
- **note / gamma-domain:** Lean states the validity condition required for the displayed coefficient to be a finite positive bound.
- **note / absolute-versus-relative:** The all-zero input is valid for the Lean theorem, and no nonzero exact-sum hypothesis is missing.
- **note / model-abstraction:** The theorem concerns model-valid real-valued operations and proves nothing about concrete executions that violate the relative-error law.

## Semantic checklist

| Check | Direct | Round-trip |
|---|---|---|
| `S01` | `pass` | `pass` |
| `S02` | `pass` | `pass` |
| `S03` | `pass` | `pass` |
| `S04` | `pass` | `fail` |
| `S05` | `pass` | `fail` |
| `S06` | `pass` | `pass` |
| `S07` | `pass` | `pass` |
| `S08` | `pass` | `pass` |
| `S09` | `pass` | `pass` |
| `S10` | `pass` | `pass` |
| `S11` | `pass` | `fail` |
| `S12` | `pass` | `pass` |
| `S13` | `pass` | `pass` |
| `S14` | `pass` | `pass` |
| `S15` | `pass` | `fail` |
| `S16` | `pass` | `pass` |

## Dependency coverage

- Blind translator covered `67` dependencies; unclear: `none`.
- Direct judge covered `67` dependencies; failing or unclear: `none`.

## Remaining uncertainties

- The PDF does not print the usual condition m*u<1 beside the finite-product estimate; its intended necessity is inferred from the denominator and from the inequality's mathematical validity.
- The paper does not formalize initial representability, overflow, infinities, or NaNs. This adjudication is therefore limited to the real-valued standard relative-error model used in the cited analysis.

## Audit artifacts

- `paper_bencmark/highambench/tasks/P01/T1/faithfulness/agent_outputs/adjudicator.json` (`8522a7c5b79dba309864ad604e5a816c307959e73705c0de815e21e6ab1b931f`)
- `paper_bencmark/highambench/tasks/P01/T1/faithfulness/agent_outputs/blind_translation.json` (`e6a4d5a8f3817aec0a35f72459357be5f44d47b0378c55dac638422a5126ebe5`)
- `paper_bencmark/highambench/tasks/P01/T1/faithfulness/agent_outputs/direct_judge.json` (`643e155c7e8c3ec1e10e8338e883196d01261bb5a273a014c8d7384284643595`)
- `paper_bencmark/highambench/tasks/P01/T1/faithfulness/agent_outputs/roundtrip_judge.json` (`1c3136a88a5649fd36bed32a5c85be32551d8361edf9efb3f2d2bd8a990c96ad`)
- `paper_bencmark/highambench/tasks/P01/T1/faithfulness/agent_outputs/source_contract.json` (`4c05f96918c368ebe7d5edf6e5a14800d425ca5337689b4e58b8134ff4bca88b`)
- `paper_bencmark/highambench/tasks/P01/T1/faithfulness/decision.json` (`886c5978e0738f19d576cac56d5212f74c7bf0b7d6ec80d2da6c46514377426b`)
- `paper_bencmark/highambench/tasks/P01/T1/faithfulness/inputs/blind_dossier.md` (`4659b42677386eee7280f4f4953cbcfa0ade0bfc4db73469da452ada592e434e`)
- `paper_bencmark/highambench/tasks/P01/T1/faithfulness/inputs/declaration_dossier.md` (`7636b7ef5783bc428eb7524f81acb7d4f7d66946204ecc2f9f8f40b7bb2c0f25`)
- `paper_bencmark/highambench/tasks/P01/T1/faithfulness/inputs/source_locator.json` (`62d30c6046bc477078905cca96055116c3c86067ccd58ff833cd5598064f5f81`)
