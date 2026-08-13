# Faithfulness audit: P08-T1

- Classification: `faithful-stronger`
- Accepted as paper-faithful: `true`
- Adjudicated: `false`
- Target SHA-256: `afb1f605f02d7de39c0db8ec195b90575040d44055a0fba4db9bef4563038bbb`
- Paper SHA-256: `f520066b46331dcbf25e51345c5ff5ffffe8fcad573d7f46e68834f83b3a2c54`

## Decision

After unfolding every dependency, the target conclusion is exactly the componentwise inequality on printed page 826. The target is not statement-equivalent because it removes the iteration index, inverse and exact-residual constraints, solution provenance, and the surrounding floating-point execution model. Nevertheless, those changes broaden rather than restrict the algebraic theorem: the paper's actual quantities satisfy hUpdate and hRound and therefore instantiate the target for every m>=0. The converse fails because the target also covers arbitrary matrices and unrelated one-step tuples. A concrete one-dimensional equality case establishes nonvacuity. The result is therefore a faithful but strictly stronger algebraic generalization, with the noted limitation that algorithmic provenance is not internalized.

## Implications

- **Lean implies paper:** `yes`. For each paper index m, instantiate Ainv with A^{-1}, q with q_{m+1}, xNext with x_{m+1}, and h with h_{m+1}. The paper's proof supplies x_{m+1}=A^{-1}q_{m+1}+x+h_{m+1} and |h_{m+1}|<=u|A^{-1}q_{m+1}|+u|x|, while positive u supplies hu. The unfolded p08AbsAction is exactly |A^{-1}||q_{m+1}| componentwise, so the Lean conclusion is the selected paper inequality, including m=0.
- **Paper implies lean:** `no`. The paper asserts the bound only for inverses and quantities arising from its iterative-refinement execution. It does not entail the target's universal claim for arbitrary matrices, including singular Ainv, arbitrary vectors, u=0, or tuples unrelated to any refinement process. Establishing those extra cases requires the independent real-algebra argument embodied by the Lean theorem.

## Findings

- **minor / algorithmic-provenance-erasure:** The proposition proves the algebraic core sufficient for the paper bound but does not itself verify that a modeled algorithm supplies those premises.
- **note / genuine-domain-strengthening:** This broader domain is nonvacuous and makes Lean imply the paper specialization while preventing the converse; it is not strength obtained from extra hypotheses or a narrower domain.
- **major / algorithm-and-error-semantics:** The algebraic result covers the paper after specialization but no longer independently states an iterative-refinement forward-error theorem.
- **major / scope-generalization:** This gives a genuine nonvacuous strengthening, so the reverse implication fails.
- **minor / floating-point-model:** The proof-relevant perturbation bound remains, but precision and exceptional-value semantics are absent.
- **minor / iteration-indexing:** The translated theorem must be instantiated externally for each iteration, including the artificial base case.

## Semantic checklist

| Check | Direct | Round-trip |
|---|---|---|
| `S01` | `pass` | `pass` |
| `S02` | `fail` | `fail` |
| `S03` | `fail` | `fail` |
| `S04` | `fail` | `fail` |
| `S05` | `pass` | `pass` |
| `S06` | `pass` | `pass` |
| `S07` | `fail` | `fail` |
| `S08` | `fail` | `fail` |
| `S09` | `pass` | `pass` |
| `S10` | `fail` | `fail` |
| `S11` | `fail` | `fail` |
| `S12` | `pass` | `fail` |
| `S13` | `fail` | `fail` |
| `S14` | `pass` | `pass` |
| `S15` | `pass` | `fail` |
| `S16` | `pass` | `pass` |

## Dependency coverage

- Blind translator covered `29` dependencies (`0` hash-reused meanings); unclear: `none`.
- Direct judge covered `29` dependencies (`0` hash-reused interpretations); failing or unclear: `none`.

## Remaining uncertainties

No remaining uncertainties were recorded.

## Audit artifacts

- `paper_bencmark/highambench/tasks/P08/T1/faithfulness/agent_outputs/blind_translation.json` (`8b35cd3b2d4161d998cf9aeeaa4d43fdbadbf890b706bf19946613e01339b559`)
- `paper_bencmark/highambench/tasks/P08/T1/faithfulness/agent_outputs/direct_judge.json` (`3623b452260f5e7831d445dd8b114c0f7d675794cc9afcd290810abc67555ccf`)
- `paper_bencmark/highambench/tasks/P08/T1/faithfulness/agent_outputs/paper_source_contract.json` (`a163817fa5c88f26c8ba3e26089da7681e1ce417d954cec7742e812dbcc3f006`)
- `paper_bencmark/highambench/tasks/P08/T1/faithfulness/agent_outputs/roundtrip_judge.json` (`b1be83d2b364dfba4e424c9bb337dd750c5dcf6f9410fdddba068d4e87635ff5`)
- `paper_bencmark/highambench/tasks/P08/T1/faithfulness/agent_outputs/source_contract.json` (`ca35bb054c46e68811532b7993edb2d8576399b2fd057cdeefd784bfb7087aad`)
- `paper_bencmark/highambench/tasks/P08/T1/faithfulness/decision.json` (`e95cc0856fa8b280178ca9b3f8c4b32f2a628316cee5884b26ebc4371301d185`)
- `paper_bencmark/highambench/tasks/P08/T1/faithfulness/inputs/blind_dependency_inventory.json` (`6d0d6dd8e70eda526d2edc17e894ebf189d1300613420cb66687ca3f43917fbf`)
- `paper_bencmark/highambench/tasks/P08/T1/faithfulness/inputs/blind_dossier.md` (`9f819939fdd3e31e171f6cc64011ce5473c600426fb26a0b9ffbdf641c65c7d0`)
- `paper_bencmark/highambench/tasks/P08/T1/faithfulness/inputs/blind_review_packet.md` (`9f819939fdd3e31e171f6cc64011ce5473c600426fb26a0b9ffbdf641c65c7d0`)
- `paper_bencmark/highambench/tasks/P08/T1/faithfulness/inputs/declaration_dossier.md` (`ac32306a6986c40c7c0bac1cc142fc7de46b0a3c6321e174ee89c99ceec4b6c4`)
- `paper_bencmark/highambench/tasks/P08/T1/faithfulness/inputs/dependency_inventory.json` (`bf09730d5f647849d3f9dbe214f58354739283e198c7e0b065e380c04cb8f623`)
- `paper_bencmark/highambench/tasks/P08/T1/faithfulness/inputs/direct_review_packet.md` (`81d37877068f45b249570b792ab98a9bf450ffe2ea1b6b3655b71b6af7909637`)
- `paper_bencmark/highambench/tasks/P08/T1/faithfulness/inputs/paper_source_locator.json` (`3242b63a529acc04514175dadb3f98deebf67f847a6bf33be0b5bb7850f84391`)
- `paper_bencmark/highambench/tasks/P08/T1/faithfulness/inputs/source_locator.json` (`2edbe8122db887fbf92d503d86cce70045175566dd5a80ad677e7b1d29e79fee`)
