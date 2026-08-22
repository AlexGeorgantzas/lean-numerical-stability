# Faithfulness audit: P18-T1

- Classification: `undetermined`
- Accepted as paper-faithful: `false`
- Adjudicated: `true`
- Target SHA-256: `a9b6807124a1ed5664980f475a52e135fd01dc586defc7a8877ed44e7b8674e6`
- Paper SHA-256: `b18628ffc348d7aeec2da02efb989b6e012f0b0fae09b27fbff735bb8a5877cd`

## Decision

The selected paper result is the exact structural split E = E_sch + E_per; the adjacent asymptotic and global statements are context. Lean supplies a coherent finite-real realization in which the equality telescopes and the Euclidean bound is valid, and its run type is inhabited. Primary evidence nevertheless does not define the paper errors as Lean's concrete signed differences, constrain their baseline, select finite Euclidean state semantics, or resolve the tau sign conflict. Lean also both broadens the operator and baseline scope and specializes the state model. Consequently Lean implying the paper remains unclear, while the paper does not imply the full universal Lean package. The implication pattern requires an undetermined classification rather than faithful-stronger.

## Implications

- **Lean implies paper:** `unclear`. For a finite-real paper execution, if E, E_sch, and E_per are identified respectively with exactNext - perturbedNext, exactNext - schemeNext, and schemeNext - perturbedNext, the first Lean conjunct yields the selected split immediately. The PDF does not define those signed quantities or its state space, so that interpretation cannot be established from primary evidence.
- **Paper implies lean:** `no`. The paper's split is stated in its F^epsilon perturbation framework. It does not establish the complete Lean proposition for every finite-real run with arbitrary tau and arbitrary exactNext, nor does it state that universal concrete Euclidean package. Intended paper instances may satisfy the Lean conclusions, but that is weaker than implication of the full Lean target.

## Findings

- **major / error-correspondence:** The exact Lean equality is plausible but cannot be identified definitively with the paper's B-series error partition.
- **major / mixed-scope:** The Lean and paper applicability domains are not demonstrably nested, so faithful-stronger is not justified.
- **minor / non-genuine-strengthening:** This redundant consequence cannot by itself make the theorem genuinely stronger than the selected decomposition.
- **minor / source-sign-ambiguity:** Literal (3.2) linkage is present, but consistency with the paper's perturbation definition cannot be certified.
- **note / source-scope:** Those statements are surrounding context under the supplied locator and are not missing conclusions of this target.

## Semantic checklist

| Check | Direct | Round-trip |
|---|---|---|
| `S01` | `pass` | `pass` |
| `S02` | `pass` | `fail` |
| `S03` | `pass` | `unclear` |
| `S04` | `pass` | `fail` |
| `S05` | `pass` | `pass` |
| `S06` | `pass` | `fail` |
| `S07` | `pass` | `fail` |
| `S08` | `pass` | `pass` |
| `S09` | `pass` | `unclear` |
| `S10` | `pass` | `unclear` |
| `S11` | `not-applicable` | `fail` |
| `S12` | `pass` | `unclear` |
| `S13` | `pass` | `unclear` |
| `S14` | `pass` | `not-applicable` |
| `S15` | `pass` | `fail` |
| `S16` | `pass` | `unclear` |

## Dependency coverage

- Blind translator covered `45` dependencies (`0` hash-reused meanings); unclear: `none`.
- Direct judge covered `45` dependencies (`0` hash-reused interpretations); failing or unclear: `none`.

## Remaining uncertainties

- The PDF does not define E, E_sch, and E_per as signed differences or identify their exact comparison baseline.
- The PDF does not determine whether its state space is specifically a positive-dimensional finite real vector space or which norm, if any, interprets its errors.
- The intended sign of the perturbed algorithm remains inconsistent between equation (2.3) and equations (3.1)-(3.2).

## Audit artifacts

- `paper_bencmark/highambench/tasks/P18/T1/faithfulness/agent_outputs/adjudicator.json` (`e59b0d0ae12c8e081cfe26190b3d6a986e0abcd458c826826dcbb34a6142ca29`)
- `paper_bencmark/highambench/tasks/P18/T1/faithfulness/agent_outputs/blind_translation.json` (`53cba453663af24b6170d390124ecf374be3a59b817ecb30243dc74b350a7d80`)
- `paper_bencmark/highambench/tasks/P18/T1/faithfulness/agent_outputs/direct_judge.json` (`4dc737d8bfd799fd788b97459fc47c0c64d607717ead041c1aeced1ea7f5dbab`)
- `paper_bencmark/highambench/tasks/P18/T1/faithfulness/agent_outputs/roundtrip_judge.json` (`d8fabe9174bec01b853fe0ddbe52f4e4d04477517e08647e97f3345e17beaecb`)
- `paper_bencmark/highambench/tasks/P18/T1/faithfulness/agent_outputs/source_contract.json` (`309a6c59f8995d01f9917767c3c3aeca2d0605b11661639ebf2559c0279a159a`)
- `paper_bencmark/highambench/tasks/P18/T1/faithfulness/decision.json` (`25a067eab283d7f1d9835e56f54869dea8eccd97ad4bd4a2b6800f671c7ec45c`)
- `paper_bencmark/highambench/tasks/P18/T1/faithfulness/history/20260820T191239Z/agent_outputs/adjudicator.json` (`9d6e50044567d19a045ed13b1d19149d0841ebda2348a922f8d9fc0276a274a7`)
- `paper_bencmark/highambench/tasks/P18/T1/faithfulness/history/20260820T191239Z/agent_outputs/blind_translation.json` (`38f96c2cd655f4e4e945d1d9c775afd51122bcc97a01535552e7a68c88895502`)
- `paper_bencmark/highambench/tasks/P18/T1/faithfulness/history/20260820T191239Z/agent_outputs/direct_judge.json` (`a20f7e1ce06baa6306b45344cdebde7880552eb18c5c91f19405fc3aedcccb64`)
- `paper_bencmark/highambench/tasks/P18/T1/faithfulness/history/20260820T191239Z/agent_outputs/paper_source_contract.json` (`6de2cebc98667558bfb276c01a2286c46a88edff824491fda40799511abf8891`)
- `paper_bencmark/highambench/tasks/P18/T1/faithfulness/history/20260820T191239Z/agent_outputs/roundtrip_judge.json` (`38a1de58ba090ad2452f129950eb45e6f0b3fed360b6d14c12a61448896a033d`)
- `paper_bencmark/highambench/tasks/P18/T1/faithfulness/history/20260820T191239Z/agent_outputs/source_contract.json` (`57b0c1c20dcde08249e280f41f66435d9d30987f76fbbd4bb150b63fddb1958f`)
- `paper_bencmark/highambench/tasks/P18/T1/faithfulness/history/20260820T191239Z/decision.json` (`7f961eac576456856ec563eac9fd40ebbf3baaa139da53b81f78b3f35301325b`)
- `paper_bencmark/highambench/tasks/P18/T1/faithfulness/history/20260820T191239Z/inputs/blind_dependency_inventory.json` (`400ff3acb28edf83e594394c0aeb93eb922f0232efd70f2294b6f8421f341ceb`)
- `paper_bencmark/highambench/tasks/P18/T1/faithfulness/history/20260820T191239Z/inputs/blind_dossier.md` (`4dfa2c4305b6ac779d9789bf3321a47c8a2ff215aee951796f59da8c375f0136`)
- `paper_bencmark/highambench/tasks/P18/T1/faithfulness/history/20260820T191239Z/inputs/blind_review_packet.md` (`4dfa2c4305b6ac779d9789bf3321a47c8a2ff215aee951796f59da8c375f0136`)
- `paper_bencmark/highambench/tasks/P18/T1/faithfulness/history/20260820T191239Z/inputs/declaration_dossier.md` (`04e8d0bc563c7f0996f39e3da45ad09098b51a2babf27ecd62d997bcdb82c611`)
- `paper_bencmark/highambench/tasks/P18/T1/faithfulness/history/20260820T191239Z/inputs/dependency_inventory.json` (`8d60643be0c377ee0ec174956f2e13390a23bd5f76297c31b58873385bdc207a`)
- `paper_bencmark/highambench/tasks/P18/T1/faithfulness/history/20260820T191239Z/inputs/direct_review_packet.md` (`eab56626ce225d4fb7e765fe029bcb5dba52a4cdf6423f488289f548a761d0f3`)
- `paper_bencmark/highambench/tasks/P18/T1/faithfulness/history/20260820T191239Z/inputs/paper_source_locator.json` (`ba129952837b9f0f76f04aaf15df9d09fbc4e140b4fac00813259e514dd1ea6e`)
- `paper_bencmark/highambench/tasks/P18/T1/faithfulness/history/20260820T191239Z/inputs/source_locator.json` (`62ab2c3e0fcdd901cc982f262a7f8943edc169124f66e3e2b265ae7d6f63b722`)
- `paper_bencmark/highambench/tasks/P18/T1/faithfulness/inputs/blind_dependency_inventory.json` (`4687ecf64d54061025a3763d6dea3a6c69589067dba1963fb2e0f05b069f16ec`)
- `paper_bencmark/highambench/tasks/P18/T1/faithfulness/inputs/blind_dossier.md` (`aed47c88b9db8cc106581e87089dea3a60078fb24777699e4f9d382cc879050c`)
- `paper_bencmark/highambench/tasks/P18/T1/faithfulness/inputs/blind_review_packet.md` (`aed47c88b9db8cc106581e87089dea3a60078fb24777699e4f9d382cc879050c`)
- `paper_bencmark/highambench/tasks/P18/T1/faithfulness/inputs/declaration_dossier.md` (`a7f1717d38f6a445f2ab5e97804e4b2c5d95f0143b0cde5617fe593cef1f96f7`)
- `paper_bencmark/highambench/tasks/P18/T1/faithfulness/inputs/dependency_inventory.json` (`cbe748a90f0e4fd6dcc0b7a9cf6b5c86b4e6d0f4351d8703bc5a621e6fdaff12`)
- `paper_bencmark/highambench/tasks/P18/T1/faithfulness/inputs/direct_review_packet.md` (`d357133c5ac91f3c5d8e191fea48ee7b2732fc54cdd1395bbfc793a3f537f15e`)
- `paper_bencmark/highambench/tasks/P18/T1/faithfulness/inputs/source_locator.json` (`60fa7a20a4f51e7f7cf2f67810a0fc488efe36c7c4b0ffce5347161a6d6117a0`)
