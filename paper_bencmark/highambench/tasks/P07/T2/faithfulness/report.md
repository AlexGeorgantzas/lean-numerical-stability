# Faithfulness audit: P07-T2

- Classification: `not-faithful-different`
- Accepted as paper-faithful: `false`
- Adjudicated: `false`
- Target SHA-256: `66cf9586215f93594421bb978c14317dd27fdc49556a45c3d13be036d45045ee`
- Paper SHA-256: `4c4d638b359719f47e2c4664a50e9fa8e4704e8b6b39923d73c41883a97c5790`

## Decision

The declaration faithfully formalizes the algebraic four-term perturbation expansion and a general induced-2-norm product budget. It can be instantiated to the paper's immediate displayed inequality once the paper-specific rowwise and triangular-solve bounds are supplied. However, the proposition neither derives those bounds nor represents the LSQR assumption, algorithm execution, computed solution, deltab, or the relation that makes the matrix a backward error. Conversely, the paper's algorithm-specific result does not imply the universal Lean budget theorem. The paper's literal-equation versus pseudoinverse ambiguity does not require adjudication here because Lean states neither relation. The implications are therefore both negative and the result is not-faithful-different.

## Implications

- **Lean implies paper:** `no`. The generic budget can reproduce the paper's immediate inequality after externally supplying e0 = n gamma_n ||R-hat||_2 ||Y-hat||_2, eR = sqrt(n) gamma_n ||R-hat||_2, and exact norm budgets. Those source-specific bounds, the LSQR hypothesis, and the relation making DeltaA a backward perturbation are not consequences of the Lean proposition, so it does not imply the selected paper result.
- **Paper implies lean:** `no`. The paper establishes the estimate for matrices and perturbations arising from SAA Blendenpik under its numerical assumptions. It does not assert the Lean theorem's universal product-budget statement for arbitrary finite real matrices and arbitrary admissible scalar bounds.

## Findings

- **critical / backward-error-linkage-omitted:** The bounded matrix is not established to be a backward perturbation for the computed least-squares solution.
- **major / numerical-analysis-assumed-away:** The proposition bypasses the source-specific reasoning that creates the displayed compositional estimate.
- **major / algorithm-linkage-missing:** It cannot support claims about the numerical stability of SAA Blendenpik.
- **major / exact-coefficients-not-stated:** Recovering the paper formula requires additional substitutions and hypotheses not present in the target.
- **note / correct-nonvacuous-algebraic-core:** The target is a meaningful and nonvacuous supporting lemma, but that does not make it equivalent to or stronger than the full selected paper result.
- **critical / backward-error-conclusion-omitted:** The translation does not express the paper's backward-error result, irrespective of the source's equation-versus-pseudoinverse ambiguity.
- **major / algorithm-and-model-omitted:** The computed, rounded, and algorithm-dependent meaning of every perturbation is lost.
- **major / paper-specific-bound-omitted:** The paper estimate cannot be recovered from the translated statement alone.
- **minor / unintended-vacuity:** The formal proposition covers trivial cases that do not represent the paper setting.
- **note / four-term-algebraic-core-retained:** The translation faithfully captures the elementary submultiplicative estimate underlying one step of the proof, but not the complete result.

## Semantic checklist

| Check | Direct | Round-trip |
|---|---|---|
| `S01` | `pass` | `pass` |
| `S02` | `fail` | `fail` |
| `S03` | `fail` | `fail` |
| `S04` | `fail` | `fail` |
| `S05` | `fail` | `fail` |
| `S06` | `pass` | `fail` |
| `S07` | `pass` | `fail` |
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

- Blind translator covered `32` dependencies (`0` hash-reused meanings); unclear: `none`.
- Direct judge covered `32` dependencies (`23` hash-reused interpretations); failing or unclear: `none`.

## Remaining uncertainties

No remaining uncertainties were recorded.

## Audit artifacts

- `paper_bencmark/highambench/tasks/P07/T2/faithfulness/agent_outputs/blind_translation.json` (`4419a27f0023ea41a685df98c525098c60d3ff4bb9a5df0ba7488f915d7e6023`)
- `paper_bencmark/highambench/tasks/P07/T2/faithfulness/agent_outputs/direct_judge.json` (`ea43746423de16117c76f3ec68fecad35f259ce984cd1e1ed78218d11c4543c1`)
- `paper_bencmark/highambench/tasks/P07/T2/faithfulness/agent_outputs/paper_source_contract.json` (`822fe7aa06960deeaa078b8ac855714c9b957ac1656f37de3dcbbaa9f707f076`)
- `paper_bencmark/highambench/tasks/P07/T2/faithfulness/agent_outputs/roundtrip_judge.json` (`d3c11bdc6a32f3108b2d311ebbb6ecc006d88ac6d8402359bbfeef9d238e8bba`)
- `paper_bencmark/highambench/tasks/P07/T2/faithfulness/agent_outputs/source_contract.json` (`1bcc5e94a23bb69e728ff4e577c93cd4130d27f5755ece1f9345b02ca4a72304`)
- `paper_bencmark/highambench/tasks/P07/T2/faithfulness/decision.json` (`28091ab0f44cd379da5456e27fa6385f9cf0f19f0538ad5acdc8c92b2805b41f`)
- `paper_bencmark/highambench/tasks/P07/T2/faithfulness/inputs/blind_dependency_inventory.json` (`8e59316251b3a76a0e84968517286166c62607b9dfa189779e28e465989a4351`)
- `paper_bencmark/highambench/tasks/P07/T2/faithfulness/inputs/blind_dossier.md` (`0eca6fe917dec5f3c7d8bbd77124abb1d9d9dbaa468e2da59011882beb385de6`)
- `paper_bencmark/highambench/tasks/P07/T2/faithfulness/inputs/blind_review_packet.md` (`0eca6fe917dec5f3c7d8bbd77124abb1d9d9dbaa468e2da59011882beb385de6`)
- `paper_bencmark/highambench/tasks/P07/T2/faithfulness/inputs/declaration_dossier.md` (`c372a4c8a39bcc551628bc454b9a23bebed16051daaf4734ceaf00f3392720b4`)
- `paper_bencmark/highambench/tasks/P07/T2/faithfulness/inputs/dependency_inventory.json` (`9e47a454e718b829e8be3fc71b3f5dfcf0c85ad788c9d8a821c187443f07abbc`)
- `paper_bencmark/highambench/tasks/P07/T2/faithfulness/inputs/dependency_reuse_direct.json` (`6830f809f9f25d4db4cafdb4180648c188b97338a0f35362b6d78cc7c250eb22`)
- `paper_bencmark/highambench/tasks/P07/T2/faithfulness/inputs/direct_review_packet.md` (`483fd7812562ba6afecb548b0204d376788c3b9986e115aced1ad936fb2a3737`)
- `paper_bencmark/highambench/tasks/P07/T2/faithfulness/inputs/paper_source_locator.json` (`7d16e3f6a7585561fffc335fcd99a77aec72a33a336198eca2c59fb9113440a2`)
- `paper_bencmark/highambench/tasks/P07/T2/faithfulness/inputs/source_locator.json` (`734421773b0a7d87f3085855d3716d0ee0bad2446623b069f04e21cd2e82d17b`)
