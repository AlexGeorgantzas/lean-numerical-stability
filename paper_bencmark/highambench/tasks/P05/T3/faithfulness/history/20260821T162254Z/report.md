# Faithfulness audit: P05-T3

- Classification: `not-faithful-weaker`
- Accepted as paper-faithful: `false`
- Adjudicated: `false`
- Target SHA-256: `aa6e36344de4982006edfc069bd22907e1349339b4ed3e19b5e240693a262f38`
- Paper SHA-256: `dd8b525c0eabc509a68b325ee5008cf6f1d4ef262bef8ba54e1947fe3cdb3db6`

## Decision

The algebraic content of the target is carefully encoded: transpose and matrix multiplication are exact, absolute matrix multiplication is componentwise, the backward identity has the correct orientation, and every zero-based coefficient matches (4.4)-(4.5). The decisive defect is the meaning of run. Its off-diagonal and diagonal execution objects can be constructed only after supplying the same residual inequalities that the target advertises as conclusions. The theorem therefore covers pre-certified runs rather than deriving the paper's error bounds for every successful conventional Cholesky execution. The underconstrained floating-point format creates an additional model mismatch. Consequently the paper result entails the restricted target, but the target does not recover the paper result.

## Implications

- **Lean implies paper:** `no`. The Lean proposition applies only after P05CholeskyRun has been built, and building it requires the Lemma 4.1 and Lemma 4.3 residual inequalities that the paper derives. It therefore cannot establish Theorem 4.4 for an arbitrary paper-valid successful execution without first assuming the core result; its abstract format also does not ensure the paper's floating-point semantics.
- **Paper implies lean:** `yes`. For a paper-valid execution, equations (4.5a)-(4.5b) provide exactly the stored entry estimates after the zero-based index shift, and equation (4.4) provides the target's exact relation and both global bounds. For the additional abstract certified runs, the target obligation already follows from the certificates' supplied residual fields, so the Lean statement imposes no stronger substantive conclusion.

## Findings

- **critical / conclusion-assumed-by-domain:** The Lean theorem does not prove the central local error estimates from the execution model. It quantifies only over runs already certified with them, making the benchmark proposition substantially weaker and partly circular.
- **major / floating-point-model-mismatch:** A P05CholeskyRun need not denote an execution in the paper's numerical model, so the formal domain is not a faithful encoding even apart from the embedded conclusions.
- **major / computed-output-property-assumed:** Representability of the computed factor is shifted from an execution consequence into the theorem's input domain, further narrowing the claim.
- **critical / local-error-bounds-assumed:** The translation does not establish the central rounding-error result from the paper hypotheses; it reduces the proposition to repeating assumed local bounds and assembling them into a matrix bound.
- **major / floating-point-model-mismatch:** The translated run type admits numerical systems outside the paper's model and fails to express a required source hypothesis, so its apparent generality is not the same theorem.

## Semantic checklist

| Check | Direct | Round-trip |
|---|---|---|
| `S01` | `pass` | `pass` |
| `S02` | `fail` | `pass` |
| `S03` | `fail` | `fail` |
| `S04` | `fail` | `fail` |
| `S05` | `pass` | `pass` |
| `S06` | `fail` | `pass` |
| `S07` | `pass` | `pass` |
| `S08` | `pass` | `pass` |
| `S09` | `pass` | `pass` |
| `S10` | `pass` | `pass` |
| `S11` | `fail` | `fail` |
| `S12` | `fail` | `fail` |
| `S13` | `pass` | `pass` |
| `S14` | `pass` | `pass` |
| `S15` | `fail` | `fail` |
| `S16` | `fail` | `fail` |

## Dependency coverage

- Blind translator covered `133` dependencies (`0` hash-reused meanings); unclear: `none`.
- Direct judge covered `133` dependencies (`0` hash-reused interpretations); failing or unclear: `D001, D011, D012, D015, D016, D017, D018, D020, D021, D023, D030, D036, D037, D039`.

## Remaining uncertainties

No remaining uncertainties were recorded.

## Audit artifacts

- `paper_bencmark/highambench/tasks/P05/T3/faithfulness/agent_outputs/blind_translation.json` (`83a54d292e4d04488d76917919332bcf81cb4aed5bcf7025d847afd18d33492c`)
- `paper_bencmark/highambench/tasks/P05/T3/faithfulness/agent_outputs/direct_judge.json` (`fa76688609ff3649c0101f899497076893f1cabd7239d6c265a9d606301a3c79`)
- `paper_bencmark/highambench/tasks/P05/T3/faithfulness/agent_outputs/roundtrip_judge.json` (`d80baeb786597fdd7e8cc8d53a0e6b2b75fd6e87c54f7a603668b4905ccefa3d`)
- `paper_bencmark/highambench/tasks/P05/T3/faithfulness/agent_outputs/source_contract.json` (`aad6136357e36a8a65b665a451ce13d5196383b2dc3d67df4643b81b8f8e3044`)
- `paper_bencmark/highambench/tasks/P05/T3/faithfulness/decision.json` (`eec7b6d442f7d41a1aa549dda2f4558e7cc2db83df9b0c92dcddbed7f263d3c8`)
- `paper_bencmark/highambench/tasks/P05/T3/faithfulness/history/20260814T203348Z/agent_outputs/blind_translation.json` (`cdc53949f20209460810b6aa91be140d279befb6c32d7f9151d394703bc0979a`)
- `paper_bencmark/highambench/tasks/P05/T3/faithfulness/history/20260814T203348Z/agent_outputs/direct_judge.json` (`46e490112fdfb2957b85ba525c40a7a5e7c4f9d5f9e70e678f9755a9eb5af43d`)
- `paper_bencmark/highambench/tasks/P05/T3/faithfulness/history/20260814T203348Z/agent_outputs/paper_source_contract.json` (`90bcb3f32112e46567a1fde6c0c742ef1d157d1829c1eb2b2cb5ebb4d58d4c1d`)
- `paper_bencmark/highambench/tasks/P05/T3/faithfulness/history/20260814T203348Z/agent_outputs/roundtrip_judge.json` (`a9c106c7bf4879ef0f85cb589b3378cf208246afe75fff6eb20a15899071d4c0`)
- `paper_bencmark/highambench/tasks/P05/T3/faithfulness/history/20260814T203348Z/agent_outputs/source_contract.json` (`383f9b21985e279369d4c14212bb70109146c948c8e3013af05eef6c69781b11`)
- `paper_bencmark/highambench/tasks/P05/T3/faithfulness/history/20260814T203348Z/decision.json` (`25b9b204f5ba5c77aea814ca96ddd4abc589a5008896a1a5f00675bff904cf6e`)
- `paper_bencmark/highambench/tasks/P05/T3/faithfulness/history/20260814T203348Z/inputs/blind_dependency_inventory.json` (`12bf0cd0f6f079664df24f38b8eb4a2637a07e24db008460622b072ef62e3744`)
- `paper_bencmark/highambench/tasks/P05/T3/faithfulness/history/20260814T203348Z/inputs/blind_dossier.md` (`8740a5009980963200c72465c2c36a8d3c670689db7ea8e8a7ae7b8da369ccd8`)
- `paper_bencmark/highambench/tasks/P05/T3/faithfulness/history/20260814T203348Z/inputs/blind_review_packet.md` (`8740a5009980963200c72465c2c36a8d3c670689db7ea8e8a7ae7b8da369ccd8`)
- `paper_bencmark/highambench/tasks/P05/T3/faithfulness/history/20260814T203348Z/inputs/declaration_dossier.md` (`2deecf940f270dcc15e90e0e80eb3330f30d813342c5ca792ff28f3fa85710dd`)
- `paper_bencmark/highambench/tasks/P05/T3/faithfulness/history/20260814T203348Z/inputs/dependency_inventory.json` (`9cce9ce2eb6ff22fbc5b06987ba96e0137ddcb05f4b7e2ff92c360b7bcb906eb`)
- `paper_bencmark/highambench/tasks/P05/T3/faithfulness/history/20260814T203348Z/inputs/dependency_reuse_direct.json` (`80f198548bad495db52ce5b9d42a75abdd6bfc3e24d439720fb000cc6551f73b`)
- `paper_bencmark/highambench/tasks/P05/T3/faithfulness/history/20260814T203348Z/inputs/direct_review_packet.md` (`6fc5702fd4006c8c0e8af8fbc28c745ee3c5a8516f4381145a0d2c1ae575126b`)
- `paper_bencmark/highambench/tasks/P05/T3/faithfulness/history/20260814T203348Z/inputs/paper_source_locator.json` (`417f8e6a6ff934c35d3c2379d9faefe1c21d44b1f14a69f7674c0ef303123327`)
- `paper_bencmark/highambench/tasks/P05/T3/faithfulness/history/20260814T203348Z/inputs/source_locator.json` (`9ec305a0bba44c4c7bb843aa8558ea4136ceb4e622b5321d0ee3125a78b54220`)
- `paper_bencmark/highambench/tasks/P05/T3/faithfulness/inputs/blind_dependency_inventory.json` (`11c07aed679b7e50931f22d05b7eb901de5caa92d891c09d86787e68c2471b86`)
- `paper_bencmark/highambench/tasks/P05/T3/faithfulness/inputs/blind_dossier.md` (`5b06b60af50c75fb79a0d21aac665e334b1268de000b5a465add8c3ad5318d3c`)
- `paper_bencmark/highambench/tasks/P05/T3/faithfulness/inputs/blind_review_packet.md` (`5b06b60af50c75fb79a0d21aac665e334b1268de000b5a465add8c3ad5318d3c`)
- `paper_bencmark/highambench/tasks/P05/T3/faithfulness/inputs/declaration_dossier.md` (`2ca273f2a5d4bb6eee040e7db3978a9630da96fca7f66aa8e182b0ebd45dd11b`)
- `paper_bencmark/highambench/tasks/P05/T3/faithfulness/inputs/dependency_inventory.json` (`06b765dc4722b1d1a20d209148773248b8b69627cbeac277c83a86fbaf8f69c1`)
- `paper_bencmark/highambench/tasks/P05/T3/faithfulness/inputs/direct_review_packet.md` (`f6d77cb073eebc3122095999c6e365637260ff576cb77f32ae36a79ed7c8d87f`)
- `paper_bencmark/highambench/tasks/P05/T3/faithfulness/inputs/source_locator.json` (`1b1d519dd36c7dac40113a1e7117b8f515e4e097997ec55c5462fb911b3e1959`)
