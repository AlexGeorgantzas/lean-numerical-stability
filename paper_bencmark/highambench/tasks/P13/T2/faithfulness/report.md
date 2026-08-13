# Faithfulness audit: P13-T2

- Classification: `faithful-equivalent`
- Accepted as paper-faithful: `true`
- Adjudicated: `true`
- Target SHA-256: `6e8f701d5a9c6f43185460c0cee389d922fa54f47f33a382a91929c56398ee6d`
- Paper SHA-256: `9ebf8adb699f96c82ccbb153dd6ca592c64475a8bc3e0703a50cb659b012c520`

## Decision

After direct dependency unfolding, Lean states precisely the exact finite weighted-sum inequality of Lemma 2.2, with the same componentwise perturbation model, relative output error, coefficient one, nonzero denominator, and no remainder term. The source context supports Lean's real scalars. Although Lean omits nodes and allows arbitrary weights, this is not strict theorem strength: because the paper permits arbitrary data, any weight vector can be transferred into rescaled data for a fixed nonzero Lagrange vector. The converse is immediate by specializing Lean to the paper's Lagrange values. Both implications therefore hold, making the declaration faithful-equivalent and accepted.

## Implications

- **Lean implies paper:** `yes`. For a paper degree n, instantiate Lean at Fin (n+1), set ell_i to the fixed Lagrange basis values ell_i(x), and retain the paper's f and Delta f. D002 becomes p_f(x), D001 becomes equation (2.2), and absolute-value symmetry removes the reversed subtraction.
- **Paper implies lean:** `yes`. For Lean dimension m>0, choose m distinct real nodes and an evaluation point different from every node, giving nonzero Lagrange values lambda_i. Define paper data F_i=(ell_i/lambda_i)f_i and perturbations Delta F_i=(ell_i/lambda_i)deltaF_i. Then lambda_i F_i=ell_i f_i and lambda_i Delta F_i=ell_i deltaF_i, so the paper hypothesis, output ratio, and condition number become exactly Lean's. The Lean hypotheses force epsilon>=0, validating the componentwise rescaling. For m=0 the Lean nonzero hypothesis is impossible.

## Findings

- **note / coefficient abstraction:** The broader binder is not genuine additional logical strength, so it does not justify faithful-stronger.
- **note / nonvacuous generalized instances:** The generalized presentation has real instances outside the literal coefficient family, but those instances remain consequences of the paper theorem.
- **note / scalar-domain wording:** The textual omission does not create a task-level domain mismatch or block either implication.
- **note / index reparameterization:** The bijective substitution n_Lean=n_paper+1 preserves all nonvacuous cases.

## Semantic checklist

| Check | Direct | Round-trip |
|---|---|---|
| `S01` | `pass` | `pass` |
| `S02` | `pass` | `fail` |
| `S03` | `pass` | `pass` |
| `S04` | `fail` | `fail` |
| `S05` | `pass` | `pass` |
| `S06` | `pass` | `pass` |
| `S07` | `pass` | `pass` |
| `S08` | `pass` | `fail` |
| `S09` | `pass` | `pass` |
| `S10` | `pass` | `fail` |
| `S11` | `pass` | `pass` |
| `S12` | `pass` | `pass` |
| `S13` | `pass` | `pass` |
| `S14` | `pass` | `pass` |
| `S15` | `pass` | `unclear` |
| `S16` | `pass` | `pass` |

## Dependency coverage

- Blind translator covered `31` dependencies (`0` hash-reused meanings); unclear: `none`.
- Direct judge covered `31` dependencies (`20` hash-reused interpretations); failing or unclear: `none`.

## Remaining uncertainties

No remaining uncertainties were recorded.

## Audit artifacts

- `paper_bencmark/highambench/tasks/P13/T2/faithfulness/agent_outputs/adjudicator.json` (`8c3aebd177b8c19078c7579d7e0870505a839ebadf76cefee3c27ba1dd4ff488`)
- `paper_bencmark/highambench/tasks/P13/T2/faithfulness/agent_outputs/blind_translation.json` (`30e5c90d3af02f5a3ab9fd4c7a2b9f311ce7428bd8bf6ac144225cf082d54743`)
- `paper_bencmark/highambench/tasks/P13/T2/faithfulness/agent_outputs/direct_judge.json` (`bb64b7a4a0b60e3b81e1f085692140a526b2dc4a5030dd0af6953709902f6b2b`)
- `paper_bencmark/highambench/tasks/P13/T2/faithfulness/agent_outputs/paper_source_contract.json` (`0b665a5c91e976eec5d015b1b58ea8cec5aa3023d351689e493b8b019f9b8393`)
- `paper_bencmark/highambench/tasks/P13/T2/faithfulness/agent_outputs/roundtrip_judge.json` (`ae2bb562e71000f8f595677c3f6bda2dd69b5b6ba6d2a392490cda370dfa8543`)
- `paper_bencmark/highambench/tasks/P13/T2/faithfulness/agent_outputs/source_contract.json` (`dfd2b9d6d1b73a49933f16ace2d4811fbf62cd1f61543f71990992ad13d43659`)
- `paper_bencmark/highambench/tasks/P13/T2/faithfulness/decision.json` (`ceb1af1880cf3d579a07995d8e162de71d8470d2f52a371fbca1a3691c2efb35`)
- `paper_bencmark/highambench/tasks/P13/T2/faithfulness/inputs/blind_dependency_inventory.json` (`0b1519482f45535fd3e2269d6c82fb6d6d3ec01d0c36ece21d08381434b67e95`)
- `paper_bencmark/highambench/tasks/P13/T2/faithfulness/inputs/blind_dossier.md` (`5321d6c6dd13dcb4c56fdaa5c7c79bb8b59ee5527c1a34d9d61652882c4f19b2`)
- `paper_bencmark/highambench/tasks/P13/T2/faithfulness/inputs/blind_review_packet.md` (`5321d6c6dd13dcb4c56fdaa5c7c79bb8b59ee5527c1a34d9d61652882c4f19b2`)
- `paper_bencmark/highambench/tasks/P13/T2/faithfulness/inputs/declaration_dossier.md` (`865048f82afd7f768423c433c109e87b7f3f40ca36e3ede44142fb1db90f3729`)
- `paper_bencmark/highambench/tasks/P13/T2/faithfulness/inputs/dependency_inventory.json` (`8e7dbf04b74ba84d4b1ac9ad8be45436a03162d57f1c42750fba4f9f6288b4d8`)
- `paper_bencmark/highambench/tasks/P13/T2/faithfulness/inputs/dependency_reuse_direct.json` (`5736ee22e7d94191d519c6a43a01a8fac976e9646896da12a2e266f251ccef29`)
- `paper_bencmark/highambench/tasks/P13/T2/faithfulness/inputs/direct_review_packet.md` (`99d5429aad39ffbd6da3acd68d2bba946c9ff380e95284731cbd1bfa49248053`)
- `paper_bencmark/highambench/tasks/P13/T2/faithfulness/inputs/paper_source_locator.json` (`ec1d43325cb06b3c0839afb1c4848208a4c9dfd1b54b19aa5048fb5de3fa9f0f`)
- `paper_bencmark/highambench/tasks/P13/T2/faithfulness/inputs/source_locator.json` (`4f3b737bccc4b68487d9e6081b5ddb81ab195923ec4b4f3aa4d3d92a2b2052cf`)
