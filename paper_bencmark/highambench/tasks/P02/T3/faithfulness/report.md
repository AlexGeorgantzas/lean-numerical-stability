# Faithfulness audit: P02-T3

- Classification: `faithful-stronger`
- Accepted as paper-faithful: `true`
- Adjudicated: `true`
- Target SHA-256: `4da16107e718b289c13ed7398a2af4b9f4b5fca48c09eaa6ec7aa5a9563e3452`
- Paper SHA-256: `e7b8523c793ad7345dfc76f681c44d1afbbc3a810fb948912451432ae616512d`

## Decision

Primary inspection of PDF pp. 5-8, 11, 15-16, 20, and 23-24 and declarations D001-D102 resolves the disagreement. N=n+1 is an exact positive-dimension reindexing; the transformed vector, SumK parameter, exact reference value, magnitude, gamma index, coefficients, powers, and non-strict absolute inequality match. A finite reached-operation extension embeds every selected no-underflow paper run into the global Lean model. The apparent VecSum operand reversal is observationally identical for the paper's TwoSum, and the K=3 boundary follows from the paper's Sum2 estimate even though the local derivation cites Proposition 4.10 too broadly. Lean retains all paper cases and has satisfiable extra real-domain and abstract-model cases, so the final classification is faithful-stronger.

## Implications

- **Lean implies paper:** `yes`. For paper dimension N set Lean n=N-1 and u=eps. Extend each concrete no-underflow execution's reached operations to an ErrorFreeDotModel using exact off-run behavior. The paper's equations (2.1)-(2.3) and Theorem 3.4 discharge every model field, and operand-order symmetry makes Lean's VecSum numerically identical on the paper specialization. Unfolding D005-D013 then reproduces Algorithm 5.10, its SumK(r,K-1) call, exact dot product, magnitude, gamma index, and selected inequality, including K=3 via Proposition 4.5.
- **Paper implies lean:** `no`. The paper result is restricted to working-precision vectors and its concrete arithmetic execution. It does not assert the bound for arbitrary real vectors or every total abstract model satisfying D010, D014, and D017, including exact and order-sensitive non-IEEE models admitted by Lean.

## Findings

- **note / execution-preserving-model-embedding:** The global axioms do not remove any selected paper execution, resolving the round-trip judge's main applicability concern.
- **minor / K=3-source-derivation-gap:** The PDF omits the boundary-case argument at that point, but the omission does not create a statement mismatch or remaining semantic uncertainty.
- **note / TwoSum-operand-order:** Paper executions are unchanged; Lean additionally covers order-sensitive abstract variants.
- **note / genuine-model-and-domain-generalization:** This is nonvacuous additional scope, supporting faithful-stronger rather than faithful-equivalent.

## Semantic checklist

| Check | Direct | Round-trip |
|---|---|---|
| `S01` | `pass` | `pass` |
| `S02` | `pass` | `fail` |
| `S03` | `pass` | `fail` |
| `S04` | `pass` | `fail` |
| `S05` | `pass` | `pass` |
| `S06` | `pass` | `pass` |
| `S07` | `pass` | `pass` |
| `S08` | `pass` | `fail` |
| `S09` | `pass` | `pass` |
| `S10` | `pass` | `pass` |
| `S11` | `pass` | `fail` |
| `S12` | `pass` | `unclear` |
| `S13` | `pass` | `pass` |
| `S14` | `pass` | `pass` |
| `S15` | `pass` | `unclear` |
| `S16` | `pass` | `pass` |

## Dependency coverage

- Blind translator covered `102` dependencies; unclear: `none`.
- Direct judge covered `102` dependencies; failing or unclear: `none`.

## Remaining uncertainties

No remaining uncertainties were recorded.

## Audit artifacts

- `paper_bencmark/highambench/tasks/P02/T3/faithfulness/agent_outputs/adjudicator.json` (`4c3ea7a13cd6769176c9610ee0ed7c9a130cfd013ac24eb6af9903f24c1fd7c9`)
- `paper_bencmark/highambench/tasks/P02/T3/faithfulness/agent_outputs/blind_translation.json` (`5b12e87c2c3855fb543c8d3e91bad8ad07a8570e6c5db46785f0a6532d138dad`)
- `paper_bencmark/highambench/tasks/P02/T3/faithfulness/agent_outputs/direct_judge.json` (`f46805a2d3a08dccb12de4a7d4597c3c1f45e82033ec0b361398c513e1aeec38`)
- `paper_bencmark/highambench/tasks/P02/T3/faithfulness/agent_outputs/roundtrip_judge.json` (`f9bcba1686119487b61ab8cd16504d03e176bdaa144900bafd93ef2b39f4be8f`)
- `paper_bencmark/highambench/tasks/P02/T3/faithfulness/agent_outputs/source_contract.json` (`a4e3eeab50c0489fa1122813f2115e69b541c2edb0d387276e663a568468cff8`)
- `paper_bencmark/highambench/tasks/P02/T3/faithfulness/decision.json` (`aa8ad0e509d1a4a8c45452eb75dc14ddd2d3c0ba0e55d32af7ba790a407e221e`)
- `paper_bencmark/highambench/tasks/P02/T3/faithfulness/inputs/blind_dossier.md` (`41af23b70658c554b14df4f6b4005f03158d03df51261a0624874e24b894c729`)
- `paper_bencmark/highambench/tasks/P02/T3/faithfulness/inputs/declaration_dossier.md` (`aca11da1add3034c6fd09e2e3c0ed85763203f5a5146681dcf712f29761a6a5e`)
- `paper_bencmark/highambench/tasks/P02/T3/faithfulness/inputs/source_locator.json` (`15d7f4ac82749eaef5aab7ec453cf0084bc4b81497ee33efdbd4accd98a3d185`)
