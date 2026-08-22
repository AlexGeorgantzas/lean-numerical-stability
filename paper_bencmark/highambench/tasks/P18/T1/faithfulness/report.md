# Faithfulness audit: P18-T1

- Classification: `faithful-stronger`
- Accepted as paper-faithful: `true`
- Adjudicated: `true`
- Target SHA-256: `336718b64b38d02e31778d65ead999145160c1c125f443598fa097581d656598`
- Paper SHA-256: `b18628ffc348d7aeec2da02efb989b6e012f0b0fae09b27fbff735bb8a5877cd`

## Decision

The paper's selected result is only the exact one-step decomposition. Lean realizes it by inserting the all-F comparator between an exact-flow-capable reference and the perturbed output. The signed realization is supported by the explicitly oriented midpoint differences, and the comparator is exactly the method obtained by replacing F^epsilon with F in (3.1). An exact-flow reference is not enforced, but it is an available specialization of a genuinely nonvacuous universal theorem; similarly, dropping the O(epsilon) condition broadens an identity that does not require asymptotic control. The exact output subtraction avoids the paper's tau-sign conflict and makes no claim about the truncated B-series remainder. The observer inequality is a derived auxiliary consequence rather than a source norm definition. Consequently Lean entails the paper instance, the paper does not entail Lean's full generalized statement, and faithful-stronger is the directionally consistent classification.

## Implications

- **Lean implies paper:** `yes`. Specialize State to the paper's state space, use the additive update (3.1), choose schemeNext as the all-F method with combined coefficient families, and choose referenceNext as the exact one-step ODE endpoint. D005, D004, and D002 then represent total, scheme-approximation, and perturbation errors with the full-precision-minus-perturbed orientation supported on printed page 3, and the first conjunct gives exactly E = E_sch + E_per. The paper's O(epsilon) cases are included among Lean's broader runs.
- **Paper implies lean:** `no`. The paper's contextual equality does not assert the result for every real module, every arbitrary shared reference, or runs lacking an O(epsilon) approximation relation, and it does not quantify every additive finite-dimensional observer. Its prose also does not supply D003's exact operational definition. Thus it does not entail the full universal Lean proposition.

## Findings

- **minor / source-error-definitions:** The Lean realization is supported and internally consistent but is not uniquely forced by the selected display.
- **note / reference-generalization:** For non-exact references, the phrase scheme approximation error loses its paper-specific interpretation. Universal quantification nevertheless retains the exact-flow specialization and adds nonvacuous cases, so this is genuine broader strength rather than reduced applicability.
- **note / approximation-scale:** The omission prevents recovery of the surrounding asymptotic estimates but legitimately weakens the hypotheses of the selected exact algebraic identity.
- **note / observer-consequence:** The inequality is relevant and can be nontrivial, but it follows from the first conjunct and Euclidean triangle inequality and should not independently justify the stronger classification.
- **note / higher-order-allocation:** Lean does not silently allocate the displayed remainder, although its exact operational definition goes beyond what the truncated B-series explicitly states.
- **note / paper-sign-inconsistency:** The declaration avoids choosing the inconsistent rewrite and remains linked to the authoritative additive update.

## Semantic checklist

| Check | Direct | Round-trip |
|---|---|---|
| `S01` | `pass` | `pass` |
| `S02` | `pass` | `fail` |
| `S03` | `pass` | `fail` |
| `S04` | `pass` | `fail` |
| `S05` | `pass` | `unclear` |
| `S06` | `pass` | `unclear` |
| `S07` | `pass` | `fail` |
| `S08` | `pass` | `pass` |
| `S09` | `pass` | `unclear` |
| `S10` | `pass` | `pass` |
| `S11` | `pass` | `fail` |
| `S12` | `pass` | `unclear` |
| `S13` | `pass` | `fail` |
| `S14` | `pass` | `unclear` |
| `S15` | `pass` | `fail` |
| `S16` | `pass` | `fail` |

## Dependency coverage

- Blind translator covered `72` dependencies (`0` hash-reused meanings); unclear: `none`.
- Direct judge covered `72` dependencies (`0` hash-reused interpretations); failing or unclear: `none`.

## Remaining uncertainties

- The generic symbols E, E_sch, and E_per on printed page 5 have no explicit subtraction formulas or reference baseline. Printed page 3 supports Lean's orientation but does not make it the uniquely possible interpretation of the later generic notation.
- Equation (3.3) does not allocate its displayed O(Delta t^3) remainder. The exact schemeNext-minus-perturbedNext definition is compatible with the two-source description, but the paper does not explicitly identify every omitted higher-order term with that operational difference.
- Equations (2.3) and (3.2) retain an unresolved sign inconsistency in the paper. Lean avoids it by using (3.1) directly, so this uncertainty does not affect the selected exact split.

## Audit artifacts

- `paper_bencmark/highambench/tasks/P18/T1/faithfulness/agent_outputs/adjudicator.json` (`962d7196b2440f683ebde362279dddc81cd59fd2713005764d980ab0a448ff2c`)
- `paper_bencmark/highambench/tasks/P18/T1/faithfulness/agent_outputs/blind_translation.json` (`7f26cd5660af32669e37225db5ff8c9dd0f8dbe872f9e95f4b84af655ac8b98f`)
- `paper_bencmark/highambench/tasks/P18/T1/faithfulness/agent_outputs/direct_judge.json` (`89c2c058a41511dc1450bd8e81bbafad0796d5dd805e8d80cc51c1498b568468`)
- `paper_bencmark/highambench/tasks/P18/T1/faithfulness/agent_outputs/roundtrip_judge.json` (`59414b41264fe74e34e450b19fd0ac12957c2913abfb72ac8351ed90576941ef`)
- `paper_bencmark/highambench/tasks/P18/T1/faithfulness/agent_outputs/source_contract.json` (`bc20d20a50c024410bb2da572fb43fad030ec329c32faf5e79ba56df07d9af3e`)
- `paper_bencmark/highambench/tasks/P18/T1/faithfulness/decision.json` (`65de340f12b4770b977962fbfeb252cd459f2d6b10d5225b2c2d06f65834c71c`)
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
- `paper_bencmark/highambench/tasks/P18/T1/faithfulness/history/20260822T000034Z/agent_outputs/adjudicator.json` (`e59b0d0ae12c8e081cfe26190b3d6a986e0abcd458c826826dcbb34a6142ca29`)
- `paper_bencmark/highambench/tasks/P18/T1/faithfulness/history/20260822T000034Z/agent_outputs/blind_translation.json` (`53cba453663af24b6170d390124ecf374be3a59b817ecb30243dc74b350a7d80`)
- `paper_bencmark/highambench/tasks/P18/T1/faithfulness/history/20260822T000034Z/agent_outputs/direct_judge.json` (`4dc737d8bfd799fd788b97459fc47c0c64d607717ead041c1aeced1ea7f5dbab`)
- `paper_bencmark/highambench/tasks/P18/T1/faithfulness/history/20260822T000034Z/agent_outputs/roundtrip_judge.json` (`d8fabe9174bec01b853fe0ddbe52f4e4d04477517e08647e97f3345e17beaecb`)
- `paper_bencmark/highambench/tasks/P18/T1/faithfulness/history/20260822T000034Z/agent_outputs/source_contract.json` (`309a6c59f8995d01f9917767c3c3aeca2d0605b11661639ebf2559c0279a159a`)
- `paper_bencmark/highambench/tasks/P18/T1/faithfulness/history/20260822T000034Z/decision.json` (`25a067eab283d7f1d9835e56f54869dea8eccd97ad4bd4a2b6800f671c7ec45c`)
- `paper_bencmark/highambench/tasks/P18/T1/faithfulness/history/20260822T000034Z/inputs/blind_dependency_inventory.json` (`4687ecf64d54061025a3763d6dea3a6c69589067dba1963fb2e0f05b069f16ec`)
- `paper_bencmark/highambench/tasks/P18/T1/faithfulness/history/20260822T000034Z/inputs/blind_dossier.md` (`aed47c88b9db8cc106581e87089dea3a60078fb24777699e4f9d382cc879050c`)
- `paper_bencmark/highambench/tasks/P18/T1/faithfulness/history/20260822T000034Z/inputs/blind_review_packet.md` (`aed47c88b9db8cc106581e87089dea3a60078fb24777699e4f9d382cc879050c`)
- `paper_bencmark/highambench/tasks/P18/T1/faithfulness/history/20260822T000034Z/inputs/declaration_dossier.md` (`a7f1717d38f6a445f2ab5e97804e4b2c5d95f0143b0cde5617fe593cef1f96f7`)
- `paper_bencmark/highambench/tasks/P18/T1/faithfulness/history/20260822T000034Z/inputs/dependency_inventory.json` (`cbe748a90f0e4fd6dcc0b7a9cf6b5c86b4e6d0f4351d8703bc5a621e6fdaff12`)
- `paper_bencmark/highambench/tasks/P18/T1/faithfulness/history/20260822T000034Z/inputs/direct_review_packet.md` (`d357133c5ac91f3c5d8e191fea48ee7b2732fc54cdd1395bbfc793a3f537f15e`)
- `paper_bencmark/highambench/tasks/P18/T1/faithfulness/history/20260822T000034Z/inputs/source_locator.json` (`60fa7a20a4f51e7f7cf2f67810a0fc488efe36c7c4b0ffce5347161a6d6117a0`)
- `paper_bencmark/highambench/tasks/P18/T1/faithfulness/inputs/blind_dependency_inventory.json` (`1bded0dbd7446188ee113166944748d71ca2b3ace454c100c2a227d28486ea81`)
- `paper_bencmark/highambench/tasks/P18/T1/faithfulness/inputs/blind_dossier.md` (`a58bb4f09445fb483813a92c119629223679dd85b8cc77d313810ef5285b83c9`)
- `paper_bencmark/highambench/tasks/P18/T1/faithfulness/inputs/blind_review_packet.md` (`a58bb4f09445fb483813a92c119629223679dd85b8cc77d313810ef5285b83c9`)
- `paper_bencmark/highambench/tasks/P18/T1/faithfulness/inputs/declaration_dossier.md` (`9b2162e6ddcd6bb6df841bd3b6382b475b464bcfe148f99dc3d414821d5cbc20`)
- `paper_bencmark/highambench/tasks/P18/T1/faithfulness/inputs/dependency_inventory.json` (`10e40482bfe3bf7803feff851606803cf2cdcaac1ff255be3bfa5cb000d9e7f2`)
- `paper_bencmark/highambench/tasks/P18/T1/faithfulness/inputs/direct_review_packet.md` (`77bc9f227679e26e8db46128737880b5801612ae5b6cb93fb23b48ea44376643`)
- `paper_bencmark/highambench/tasks/P18/T1/faithfulness/inputs/source_locator.json` (`a6ce4f229e15a4953b473103de116ad2d773bf1ba6382dbb26604874d446a527`)
