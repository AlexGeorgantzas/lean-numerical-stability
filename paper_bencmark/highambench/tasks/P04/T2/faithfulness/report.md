# Faithfulness audit: P04-T2

- Classification: `not-faithful-different`
- Accepted as paper-faithful: `false`
- Adjudicated: `false`
- Target SHA-256: `98e82d8b57ec9dc9d93b67c12f18a3c1eb2940b4a9550a0f8e1d342c98341da7`
- Paper SHA-256: `7ad9ebb7eef9864c58e9a3760ee308be48060647286f8e16cdc740ed4be5b862`

## Decision

The target retains the exact higher-order scalar coefficient and proves a nonvacuous scalar perturbation bound, but it is not Theorem 3.2. It replaces matrices and Algorithm 3.1 by arbitrary real variables, assumes the key arithmetic-error estimate, omits q=n/b and the floating-point execution model, and leaves the effective FMA precision undefined. Because neither proposition covers the other's full quantified domain and execution semantics, the appropriate classification is not-faithful-different.

## Implications

- **Lean implies paper:** `no`. The scalar algebraic proposition cannot derive the general componentwise matrix theorem, cannot establish its assumed he from Algorithm 3.1, and contains neither the matrix dimensions nor the block-FMA precision model.
- **Paper implies lean:** `no`. The paper theorem concerns outputs of Algorithm 3.1 with q=n/b and paper-defined precisions. It does not assert the target's universal implication for arbitrary independent scalar perturbations, errors, computed values, q, and n. A 1-by-1 paper specialization overlaps only a restricted subset of Lean instances.

## Findings

- **critical / matrix-domain-collapse:** The target cannot express the general matrix product, its inner summation, or the theorem's componentwise matrix conclusion.
- **critical / algorithmic-result-assumed:** The target formalizes only the final scalar perturbation algebra and omits the main algorithm-to-error guarantee measured by the benchmark task.
- **major / precision-parameter-mismatch:** The exact-looking coefficient is not linked to the paper's actual FMA-output, internal, and final-output precision semantics.
- **major / dimension-and-indexing-omission:** The gamma indices can describe combinations that do not correspond to any execution covered by the paper.
- **major / floating-point-model-omission:** The proposition cannot establish that actual mixed-precision block-FMA computation satisfies its hypotheses.
- **critical / dimension-and-result-domain:** The translated proposition cannot express or entail the paper's matrix-product result.
- **critical / algorithm-and-floating-point-model:** The theorem has been changed from an error analysis of a specified computation into an abstract real-algebra implication.
- **major / index-and-precision-dependence:** The coefficient has the correct shape but no longer has the parameter dependence asserted by the paper.
- **major / quantifier-and-premise-shift:** The central computational claim is moved into a premise and therefore is not formalized.
- **note / preserved-coefficient:** The coefficient-propagation algebra is accurate, but this does not repair the missing matrix, algorithmic, and floating-point semantics.

## Semantic checklist

| Check | Direct | Round-trip |
|---|---|---|
| `S01` | `pass` | `pass` |
| `S02` | `fail` | `fail` |
| `S03` | `fail` | `fail` |
| `S04` | `fail` | `fail` |
| `S05` | `fail` | `fail` |
| `S06` | `fail` | `pass` |
| `S07` | `pass` | `pass` |
| `S08` | `fail` | `fail` |
| `S09` | `fail` | `fail` |
| `S10` | `fail` | `fail` |
| `S11` | `fail` | `fail` |
| `S12` | `fail` | `fail` |
| `S13` | `pass` | `pass` |
| `S14` | `pass` | `pass` |
| `S15` | `fail` | `fail` |
| `S16` | `pass` | `pass` |

## Dependency coverage

- Blind translator covered `41` dependencies (`0` hash-reused meanings); unclear: `none`.
- Direct judge covered `41` dependencies (`28` hash-reused interpretations); failing or unclear: `D002, D016, D021, D030`.

## Remaining uncertainties

No remaining uncertainties were recorded.

## Audit artifacts

- `paper_bencmark/highambench/tasks/P04/T2/faithfulness/agent_outputs/blind_translation.json` (`4d71a7009e4cb29d27a134339ecf7b18c5220d2507c972f2cd793f26b9d8fbf8`)
- `paper_bencmark/highambench/tasks/P04/T2/faithfulness/agent_outputs/direct_judge.json` (`c8550401e7f9caa5c9bbf71dad5391d07dcd6eba65821665baffbe8e0209771b`)
- `paper_bencmark/highambench/tasks/P04/T2/faithfulness/agent_outputs/paper_source_contract.json` (`f23d1d2864ab683fc44d7b4dd917ebb13c36417400d3ee09d7d5a642c3a0d785`)
- `paper_bencmark/highambench/tasks/P04/T2/faithfulness/agent_outputs/roundtrip_judge.json` (`01403dc737c6f8c804399734fccc14badb310c8df096ee83e4f7f0708e9e25d3`)
- `paper_bencmark/highambench/tasks/P04/T2/faithfulness/agent_outputs/source_contract.json` (`f91ab8283eea97a3263327b17be4b438564672ac842266b86621054c130df589`)
- `paper_bencmark/highambench/tasks/P04/T2/faithfulness/decision.json` (`bf585cec6a7195053b93f6fd066a68369c59615714a743e5921b141fbaef45fc`)
- `paper_bencmark/highambench/tasks/P04/T2/faithfulness/inputs/blind_dependency_inventory.json` (`62f92733f1d6bd164114aabb88151cf1bfff522262475a1a60228bd73020c5b0`)
- `paper_bencmark/highambench/tasks/P04/T2/faithfulness/inputs/blind_dossier.md` (`96abb59a7a2442174b606f193289f5d5c707fc22ba390a60dd00ae71a96c4955`)
- `paper_bencmark/highambench/tasks/P04/T2/faithfulness/inputs/blind_review_packet.md` (`96abb59a7a2442174b606f193289f5d5c707fc22ba390a60dd00ae71a96c4955`)
- `paper_bencmark/highambench/tasks/P04/T2/faithfulness/inputs/declaration_dossier.md` (`f5c48f188222a2480238b2c40d27f75ef228c4b2d7c6217d68ebe1fc49508119`)
- `paper_bencmark/highambench/tasks/P04/T2/faithfulness/inputs/dependency_inventory.json` (`edb46564cba8406b42c6d333c68e9518d67704cf7da44fe676ccf5f6f989e7af`)
- `paper_bencmark/highambench/tasks/P04/T2/faithfulness/inputs/dependency_reuse_direct.json` (`f69ef14afab568cfc4bcce54833be6807beba992d2a39b6f51af29e604fa6a7c`)
- `paper_bencmark/highambench/tasks/P04/T2/faithfulness/inputs/direct_review_packet.md` (`89ea80907b3d9155fd60c79a2d5db9e0ae3b17f16e1514dd17f5ff2cf20b716e`)
- `paper_bencmark/highambench/tasks/P04/T2/faithfulness/inputs/paper_source_locator.json` (`609fbccbf417b9661d911f32e2ac6e1c09c3fa4c980c82c53b5c0edd480437f7`)
- `paper_bencmark/highambench/tasks/P04/T2/faithfulness/inputs/source_locator.json` (`8bf362e8f7f6f69a831e5593e1218ef3d7a2b716196afed0f070400ab36bf4b1`)
