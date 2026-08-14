# Faithfulness audit: P06-T1

- Classification: `not-faithful-different`
- Accepted as paper-faithful: `false`
- Adjudicated: `false`
- Target SHA-256: `2527b886559c2b572f9d6f1939cec64202ffcbc6b4e32b59015e41e5fedeed34`
- Paper SHA-256: `c02a20e9ffa8039a5ad3db9261fba19929de84bf0bff7654547541dffe496a79`

## Decision

The declaration faithfully formalizes a nonvacuous deterministic norm-aggregation lemma with the correct finite-dimensional Euclidean and Frobenius norms. It does not formalize P06-T1's Householder QR backward-error theorem: the computed factor, orthogonal witness, exact backward relation, rounding and probability hypotheses, inherited probability, exact leading expression, dimension restrictions, and additive O(u^2) remainder are absent. The stronger exact hcol premise also prevents direct instantiation from equation (4.17). Consequently neither statement implies the other at the claimed semantic scope, so the result is not-faithful-different and does not require adjudication.

## Implications

- **Lean implies paper:** `no`. The Lean theorem cannot produce the computed R_hat, an orthogonal Q, the exact backward relation, the algorithm-generated ΔA, Model 1.5 assumptions, the probability guarantee, or the concrete first-order coefficient. Moreover, the paper's columnwise estimate contains O(u^2), so it does not directly supply Lean's exact hcol premise.
- **Paper implies lean:** `no`. The paper establishes an algorithm-specific high-probability result for particular computed quantities, not the universally quantified deterministic implication for every A, ΔA, and η. Its additive O(u^2) terms also do not imply the target's exact pure multiplicative premise and conclusion.

## Findings

- **critical / missing-backward-error-certificate:** The proposition does not state that Householder QR is backward stable; it only bounds one arbitrary matrix from assumed column bounds.
- **critical / missing-probabilistic-numerical-model:** The defining probabilistic rounding-error content of the selected paper result is not formalized.
- **major / higher-order-term-deletion:** The target cannot be instantiated from the paper's displayed columnwise estimate without an unjustified treatment of the remainder.
- **major / coefficient-and-domain-abstraction:** The theorem does not preserve the paper's dimension dependence, constants, parameters, or QR domain.
- **note / valid-aggregation-sublemma:** The declaration is mathematically relevant as a supporting lemma, but it is not the selected paper result.
- **critical / algorithm-and-conclusion-omission:** The translated proposition is not a backward-stability result for the paper's algorithm.
- **critical / higher-order-term-deletion:** The translation converts a first-order asymptotic estimate into a different all-orders claim.
- **major / numerical-model-and-probability:** The main conditions under which the paper establishes its estimate are lost.
- **major / quantifiers-and-parameters:** Neither direction of semantic implication holds between the two statements.
- **note / norm-aggregation:** This preserves one mathematical step used by the paper but not the P06-T1 result as a whole.

## Semantic checklist

| Check | Direct | Round-trip |
|---|---|---|
| `S01` | `pass` | `fail` |
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
| `S13` | `fail` | `fail` |
| `S14` | `fail` | `fail` |
| `S15` | `fail` | `fail` |
| `S16` | `pass` | `pass` |

## Dependency coverage

- Blind translator covered `23` dependencies (`0` hash-reused meanings); unclear: `none`.
- Direct judge covered `23` dependencies (`0` hash-reused interpretations); failing or unclear: `none`.

## Remaining uncertainties

No remaining uncertainties were recorded.

## Audit artifacts

- `paper_bencmark/highambench/tasks/P06/T1/faithfulness/agent_outputs/blind_translation.json` (`78d6a16e2e4969e1ccd4ef2d4b9da9e95db6193fd1b3f0143192da3eaac4b1ab`)
- `paper_bencmark/highambench/tasks/P06/T1/faithfulness/agent_outputs/direct_judge.json` (`bfb4556277b4c9b57738fe02f72286e1ae29ae0a9f36179266066b6a6c8224e3`)
- `paper_bencmark/highambench/tasks/P06/T1/faithfulness/agent_outputs/paper_source_contract.json` (`5fc79f8dcb892e5e54a0e6404abfb754e2c8f1233e5e586f0036f135448517d2`)
- `paper_bencmark/highambench/tasks/P06/T1/faithfulness/agent_outputs/roundtrip_judge.json` (`846f94bbb1149d106cf26cab12191653d0b9e44a246a56223b01fef46a373273`)
- `paper_bencmark/highambench/tasks/P06/T1/faithfulness/agent_outputs/source_contract.json` (`8e53e0f8269939e3d98772fe34c53a586fe75c258d270e8cea278f2e988f0534`)
- `paper_bencmark/highambench/tasks/P06/T1/faithfulness/decision.json` (`e8fa8a338bdca0d306c5fde261870b0c6eeeffbd3ac60994b18cb4834e50f724`)
- `paper_bencmark/highambench/tasks/P06/T1/faithfulness/inputs/blind_dependency_inventory.json` (`9799d69d3509de7a0728aa479be82d3114810aa563336ff9b6a848da2bb37c69`)
- `paper_bencmark/highambench/tasks/P06/T1/faithfulness/inputs/blind_dossier.md` (`5c0b359341957a9a846813c29b78c4d35b52235beb62b4d080d22e4a7ae1105e`)
- `paper_bencmark/highambench/tasks/P06/T1/faithfulness/inputs/blind_review_packet.md` (`5c0b359341957a9a846813c29b78c4d35b52235beb62b4d080d22e4a7ae1105e`)
- `paper_bencmark/highambench/tasks/P06/T1/faithfulness/inputs/declaration_dossier.md` (`abd2e0cce35b6cb05ae4945594c10f97eba9690e1b86140618736bf3a45b960f`)
- `paper_bencmark/highambench/tasks/P06/T1/faithfulness/inputs/dependency_inventory.json` (`59f70fa079aafa059c53853182266e2b8c52aa8ca55244059579166953a2c30d`)
- `paper_bencmark/highambench/tasks/P06/T1/faithfulness/inputs/direct_review_packet.md` (`8bb9d553f484d386159b95aab961709edfb9b567d03d89fea23e010fc6c33fcd`)
- `paper_bencmark/highambench/tasks/P06/T1/faithfulness/inputs/paper_source_locator.json` (`d42b3fea8b0a859f7675a27adf15eef5a9d1a4d454377d2374aa02bdd01476fe`)
- `paper_bencmark/highambench/tasks/P06/T1/faithfulness/inputs/source_locator.json` (`d6efa51b03cf5945c37b778053c05ddf456c4c9285a5ca6a0456f0fa32cef2d5`)
