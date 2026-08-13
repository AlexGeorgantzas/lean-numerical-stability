# Faithfulness audit: P01-T3

- Classification: `faithful-equivalent`
- Accepted as paper-faithful: `true`
- Adjudicated: `true`
- Target SHA-256: `e5badc1d71efe1d99f4d211edb7eff96ceb893628641ed140494f380de284cda`
- Paper SHA-256: `d5ad99fac5022da54dbe02721ea57116df3cec15badddd7c96c344328718fea7`

## Decision

Primary inspection of printed pages 784 and 793 and the definitions of NoGuardAddModel, recursiveSum, and noGuardRecursiveRunningBudget resolves the round-trip concerns. The theorem uses the same per-operation two-perturbation model, exact sum, computed prefixes, absolute forward error, coefficient u, and k=2,...,n indexing as equation (5.3). No-underflow is abstracted into direct satisfaction of the model law, the exact singleton is explicitly the paper's S_hat_1=x_1 convention, and the arbitrary-real scalar domain is stated in Section 2. Both implications hold. The n=0 extension is tautological, so there is no genuine nonvacuous basis for faithful-stronger. The surviving x_i ambiguity belongs to printed equation (5.2) and does not make the selected bound uncertain.

## Implications

- **Lean implies paper:** `yes`. Map v(j) to x_{j+1}. recursiveSum is S_hat_n, the Finset sum is the exact S_n, and the unfolded budget is sum_{k=2}^n (|S_hat_{k-1}| + |x_k|). The target therefore specializes exactly to equation (5.3) under the paper's componentwise no-guard model.
- **Paper implies lean:** `yes`. For n>=2, NoGuardAddModel supplies the bounded alpha_k and beta_k witnesses from (5.1) at each recursive call; telescoping computed-minus-exact local errors and applying the triangle inequality gives the Lean budget exactly. The n=1 and n=0 statements are definitional zero-error cases. The paper's no-underflow condition has no independent algebraic role once the model law is assumed directly.

## Findings

- **note / source-typography:** The target faithfully formalizes the closed bound (5.3) but should not be described as a literal formalization of the printed identity (5.2).
- **note / model-abstraction:** This is an algebraic packaging of the hypothesis used by (5.3), not an omission that permits model-violating executions.
- **note / edge-domain-and-initialization:** The initialization matches the analyzed algorithm, and the additional empty case is trivial rather than genuine stronger content.

## Semantic checklist

| Check | Direct | Round-trip |
|---|---|---|
| `S01` | `pass` | `pass` |
| `S02` | `pass` | `unclear` |
| `S03` | `pass` | `pass` |
| `S04` | `pass` | `fail` |
| `S05` | `pass` | `pass` |
| `S06` | `pass` | `pass` |
| `S07` | `pass` | `pass` |
| `S08` | `pass` | `unclear` |
| `S09` | `pass` | `pass` |
| `S10` | `pass` | `pass` |
| `S11` | `pass` | `fail` |
| `S12` | `pass` | `pass` |
| `S13` | `pass` | `pass` |
| `S14` | `pass` | `pass` |
| `S15` | `pass` | `unclear` |
| `S16` | `pass` | `pass` |

## Dependency coverage

- Blind translator covered `55` dependencies; unclear: `none`.
- Direct judge covered `55` dependencies; failing or unclear: `none`.

## Remaining uncertainties

- Equation (5.2) literally contains the unbound symbol x_i. The likely correction to x_k is supported by the recurrence and (5.3), but this adjudication does not attribute that correction to the printed identity.
- The paper does not explicitly state an n=0 convention or a representability predicate. These source omissions do not affect the selected (5.3) classification because Lean's n=0 case is tautological and Section 2 formulates the data as real numbers.

## Audit artifacts

- `paper_bencmark/highambench/tasks/P01/T3/faithfulness/agent_outputs/adjudicator.json` (`f7981d1863a640e4bbc780198ea16d93677bf7f51dac7dd3ec83355ece8cb6e8`)
- `paper_bencmark/highambench/tasks/P01/T3/faithfulness/agent_outputs/blind_translation.json` (`6a33475a9fefe667dfc4b8c6cec3be805796190da39e3aa7d28ca72009166959`)
- `paper_bencmark/highambench/tasks/P01/T3/faithfulness/agent_outputs/direct_judge.json` (`d34ada47dc2b3e13abd78250289f55586d92a53cdcbad7722b40f79073f41892`)
- `paper_bencmark/highambench/tasks/P01/T3/faithfulness/agent_outputs/roundtrip_judge.json` (`11f3ead087f80969b65a18559645059b3c04dc4cba5228073a17cc33418ddb4d`)
- `paper_bencmark/highambench/tasks/P01/T3/faithfulness/agent_outputs/source_contract.json` (`1936ce744d3326849e367aa5905875c482922efc4d3baf948bb45285b3f9f33a`)
- `paper_bencmark/highambench/tasks/P01/T3/faithfulness/decision.json` (`17f8a8c8f3e11d77bdd27d90df571cd7ab5fa3e8d194f2f2fb52193527cc2555`)
- `paper_bencmark/highambench/tasks/P01/T3/faithfulness/inputs/blind_dossier.md` (`559b96bd39201e5cc4c34fc5666b5e90d18c9bb8ea542a84ef425922597fed60`)
- `paper_bencmark/highambench/tasks/P01/T3/faithfulness/inputs/declaration_dossier.md` (`19a98f94f5be8dd2cd76b1cff945a144b18634ddca491524444f0f7dd07a86f1`)
- `paper_bencmark/highambench/tasks/P01/T3/faithfulness/inputs/source_locator.json` (`215dc3e3ec3df9272eaa20c0707cc0a2654b88a28e3cbc77150e75ef0700be87`)
