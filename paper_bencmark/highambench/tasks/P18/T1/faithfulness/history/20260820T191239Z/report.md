# Faithfulness audit: P18-T1

- Classification: `not-faithful-different`
- Accepted as paper-faithful: `false`
- Adjudicated: `true`
- Target SHA-256: `3858ce5ab8240d8eb5d773798c857db776fbed475a5cfbddb7f4e68b059cb6d9`
- Paper SHA-256: `b18628ffc348d7aeec2da02efb989b6e012f0b0fae09b27fbff735bb8a5877cd`

## Decision

The primary source states a method-specific decomposition of one-step error followed by separate scheme and epsilon-scaled perturbation orders, and it conditions the global envelope on stability. The Lean declaration instead states Minkowski's inequality for arbitrary finite real vectors. The missing paper norm makes Euclidean compatibility genuinely uncertain, so S09 should not be converted into a claim of demonstrated norm contradiction. Nevertheless, assuming the Euclidean norm would not restore the omitted algorithm, hypotheses, asymptotic orders, local/global distinction, or stability qualification. Consequently neither complete statement implies the other under its actual binders, and the decisive classification remains not-faithful-different.

## Implications

- **Lean implies paper:** `no`. The Euclidean triangle inequality for arbitrary finite real vectors does not entail the paper's Runge-Kutta error decomposition, consistency and perturbation conditions, epsilon-scaled asymptotic orders, or stability-conditional global result. Even assuming Euclidean norm compatibility would provide only a generic norm bound, not the paper's complete conclusions.
- **Paper implies lean:** `no`. The paper does not select finite real vectors or the Euclidean norm and does not quantify over every vector pair. Its equality could yield a triangle-inequality bound for its particular errors only after adding an external Euclidean-space interpretation and the general norm theorem; it does not entail the Lean declaration under the preserved binders.

## Findings

- **critical / result-substitution:** The formal declaration does not express or establish the selected paper result.
- **critical / algorithm-and-asymptotic-omission:** The declaration is provable without any mixed-precision Runge-Kutta analysis.
- **major / unsupported-norm-specialization:** The Euclidean choice cannot be attributed to the source, but this ambiguity is not classification-decisive because the principal algorithmic and asymptotic conclusions are absent regardless of norm.
- **major / unintended-generic-truth:** Its broader quantification is not genuine strength over the paper result because it achieves that applicability by replacing the substantive conclusion.
- **note / source-sign-ambiguity:** The ambiguity must be preserved, but it cannot affect this classification because the Lean declaration contains no tau or perturbation coefficients.

## Semantic checklist

| Check | Direct | Round-trip |
|---|---|---|
| `S01` | `pass` | `pass` |
| `S02` | `fail` | `fail` |
| `S03` | `fail` | `fail` |
| `S04` | `fail` | `fail` |
| `S05` | `fail` | `fail` |
| `S06` | `fail` | `fail` |
| `S07` | `fail` | `fail` |
| `S08` | `fail` | `fail` |
| `S09` | `fail` | `unclear` |
| `S10` | `fail` | `fail` |
| `S11` | `fail` | `fail` |
| `S12` | `fail` | `fail` |
| `S13` | `fail` | `fail` |
| `S14` | `fail` | `fail` |
| `S15` | `fail` | `fail` |
| `S16` | `fail` | `fail` |

## Dependency coverage

- Blind translator covered `22` dependencies (`0` hash-reused meanings); unclear: `none`.
- Direct judge covered `22` dependencies (`0` hash-reused interpretations); failing or unclear: `D001, D002, D003, D004, D006, D007, D008, D010, D012, D013, D014, D015, D016, D017, D018, D019, D020, D021, D022`.

## Remaining uncertainties

- Primary evidence does not determine which norm, if any, governs E, E_sch, E_per, Error, or the big-O terms; Euclidean compatibility therefore remains unresolved.
- Equation (2.3) prints tau = (F - F^epsilon)/epsilon, while equations (3.2)-(3.3) print positive epsilon tau contributions. The PDF does not resolve which sign is intended.

## Audit artifacts

- `paper_bencmark/highambench/tasks/P18/T1/faithfulness/agent_outputs/adjudicator.json` (`9d6e50044567d19a045ed13b1d19149d0841ebda2348a922f8d9fc0276a274a7`)
- `paper_bencmark/highambench/tasks/P18/T1/faithfulness/agent_outputs/blind_translation.json` (`38f96c2cd655f4e4e945d1d9c775afd51122bcc97a01535552e7a68c88895502`)
- `paper_bencmark/highambench/tasks/P18/T1/faithfulness/agent_outputs/direct_judge.json` (`a20f7e1ce06baa6306b45344cdebde7880552eb18c5c91f19405fc3aedcccb64`)
- `paper_bencmark/highambench/tasks/P18/T1/faithfulness/agent_outputs/paper_source_contract.json` (`6de2cebc98667558bfb276c01a2286c46a88edff824491fda40799511abf8891`)
- `paper_bencmark/highambench/tasks/P18/T1/faithfulness/agent_outputs/roundtrip_judge.json` (`38a1de58ba090ad2452f129950eb45e6f0b3fed360b6d14c12a61448896a033d`)
- `paper_bencmark/highambench/tasks/P18/T1/faithfulness/agent_outputs/source_contract.json` (`57b0c1c20dcde08249e280f41f66435d9d30987f76fbbd4bb150b63fddb1958f`)
- `paper_bencmark/highambench/tasks/P18/T1/faithfulness/decision.json` (`7f961eac576456856ec563eac9fd40ebbf3baaa139da53b81f78b3f35301325b`)
- `paper_bencmark/highambench/tasks/P18/T1/faithfulness/inputs/blind_dependency_inventory.json` (`400ff3acb28edf83e594394c0aeb93eb922f0232efd70f2294b6f8421f341ceb`)
- `paper_bencmark/highambench/tasks/P18/T1/faithfulness/inputs/blind_dossier.md` (`4dfa2c4305b6ac779d9789bf3321a47c8a2ff215aee951796f59da8c375f0136`)
- `paper_bencmark/highambench/tasks/P18/T1/faithfulness/inputs/blind_review_packet.md` (`4dfa2c4305b6ac779d9789bf3321a47c8a2ff215aee951796f59da8c375f0136`)
- `paper_bencmark/highambench/tasks/P18/T1/faithfulness/inputs/declaration_dossier.md` (`04e8d0bc563c7f0996f39e3da45ad09098b51a2babf27ecd62d997bcdb82c611`)
- `paper_bencmark/highambench/tasks/P18/T1/faithfulness/inputs/dependency_inventory.json` (`8d60643be0c377ee0ec174956f2e13390a23bd5f76297c31b58873385bdc207a`)
- `paper_bencmark/highambench/tasks/P18/T1/faithfulness/inputs/direct_review_packet.md` (`eab56626ce225d4fb7e765fe029bcb5dba52a4cdf6423f488289f548a761d0f3`)
- `paper_bencmark/highambench/tasks/P18/T1/faithfulness/inputs/paper_source_locator.json` (`ba129952837b9f0f76f04aaf15df9d09fbc4e140b4fac00813259e514dd1ea6e`)
- `paper_bencmark/highambench/tasks/P18/T1/faithfulness/inputs/source_locator.json` (`62ab2c3e0fcdd901cc982f262a7f8943edc169124f66e3e2b265ae7d6f63b722`)
