# Faithfulness audit: P18-T3

- Classification: `not-faithful-weaker`
- Accepted as paper-faithful: `false`
- Adjudicated: `false`
- Target SHA-256: `c840feeef03171551b63d4517e814fd8d34a9aa6904d6b965f7cebd27fa3dbc0`
- Paper SHA-256: `b18628ffc348d7aeec2da02efb989b6e012f0b0fae09b27fbff735bb8a5877cd`

## Decision

The proposition is a correct, nonvacuous certificate that the literal page-18 coefficient display approximately satisfies all four third-order consistency equations and all nontrivial simplified smooth perturbation equations after b_eps is proved zero. It is nevertheless only a closed coefficient computation. It omits the additive algorithm, approximation and regularity hypotheses, stability, exact order satisfaction, and both smooth and nonsmooth global error conclusions. Thus the paper result entails the certificate, but the certificate does not entail the paper result, giving the classification not-faithful-weaker.

## Implications

- **Lean implies paper:** `no`. The closed arithmetic certificate can hold without any operators F or F_eps, perturbation model, regularity assumption, stable Runge-Kutta execution, or error predicate. Moreover, residual bounds within 2e-15 do not imply the paper's exact order equalities. It therefore cannot entail either page-18 global error statement.
- **Paper implies lean:** `yes`. Using the standard four-stage zero-filled tableau reading of the coefficients printed on PDF p. 18, the target is a direct exact-arithmetic certificate of that display: b_eps is zero; the largest asserted residual is approximately 1.3933e-15, below 2e-15; and the absolute dot product is approximately 0.030846, above 0.01. These facts follow from the displayed data even though the paper does not state the chosen thresholds.

## Findings

- **critical / omitted-error-conclusions:** The Lean theorem does not formalize the central result selected from the paper.
- **major / approximate-certificate-only:** The theorem certifies numerical proximity of rounded data but does not establish exact order conditions or their analytic consequences.
- **major / algorithm-and-hypotheses-omitted:** The certificate remains disconnected from the algorithm and cannot support the claimed smooth or nonsmooth execution behavior.
- **minor / inferred-printed-tableau-model:** The modeling choice is reasonable for a printed-coefficient certificate but is not itself specified by the paper.
- **note / nonvacuous-smooth-cancellation:** This correctly demonstrates a genuine signed cancellation, but it is an auxiliary computed fact and does not recover the missing error theorem.
- **critical / algorithm-and-error-result-omitted:** It cannot imply the principal Method 4s3pC result.
- **major / unsupported-tolerance-and-exactness:** The translation is an approximate certificate rather than the exact order-condition assertion made by the paper.
- **major / perturbation-parameter-conflation:** The numerical-model parameter has been replaced by an unrelated verification tolerance.
- **major / added-nonsmooth-condition-failure-certificate:** This useful noncancellation fact is not the paper's nonsmooth error conclusion and cannot replace that branch.
- **note / coefficient-condition-mapping:** The coefficient-level algebra is substantially and correctly mapped despite the missing theorem context.

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
| `S09` | `pass` | `pass` |
| `S10` | `pass` | `fail` |
| `S11` | `fail` | `fail` |
| `S12` | `fail` | `fail` |
| `S13` | `fail` | `fail` |
| `S14` | `fail` | `fail` |
| `S15` | `fail` | `pass` |
| `S16` | `pass` | `pass` |

## Dependency coverage

- Blind translator covered `78` dependencies (`0` hash-reused meanings); unclear: `none`.
- Direct judge covered `78` dependencies (`0` hash-reused interpretations); failing or unclear: `none`.

## Remaining uncertainties

No remaining uncertainties were recorded.

## Audit artifacts

- `paper_bencmark/highambench/tasks/P18/T3/faithfulness/agent_outputs/blind_translation.json` (`0b899a02f671d265be5b7a79f51c2d73c531635cd85b7ddbd5196bb39a2b58ce`)
- `paper_bencmark/highambench/tasks/P18/T3/faithfulness/agent_outputs/direct_judge.json` (`24f22350dcd24896ba66caf6b016a29b48282ed4efcd1ffaa966f57508f2bd59`)
- `paper_bencmark/highambench/tasks/P18/T3/faithfulness/agent_outputs/roundtrip_judge.json` (`538dffb814b593ccfe9a79855725cb832f847bc577ea5b6b4aebcfede95e646c`)
- `paper_bencmark/highambench/tasks/P18/T3/faithfulness/agent_outputs/source_contract.json` (`73091c516e5202e341a8ca22a62dbcec6c561adb8565188bd0a603fd9e4ae850`)
- `paper_bencmark/highambench/tasks/P18/T3/faithfulness/decision.json` (`655fe1539db8d0eb85b6f191e1b628e1249ad90571320fb3b2dd3f0869f50a89`)
- `paper_bencmark/highambench/tasks/P18/T3/faithfulness/history/20260821T032511Z/agent_outputs/adjudicator.json` (`f26be36b6bd95d8db71ac076800bfb69b5a5e8906221bcaab9cf2fc833d87c44`)
- `paper_bencmark/highambench/tasks/P18/T3/faithfulness/history/20260821T032511Z/agent_outputs/blind_translation.json` (`6e0eea38d5314e6876a9b89c8de9005e50f9c43d146928816f209ddf4b0c8a6d`)
- `paper_bencmark/highambench/tasks/P18/T3/faithfulness/history/20260821T032511Z/agent_outputs/direct_judge.json` (`56c998e903935bf3936f0b165ae83471058438382699f2341fe05b7915e47f86`)
- `paper_bencmark/highambench/tasks/P18/T3/faithfulness/history/20260821T032511Z/agent_outputs/paper_source_contract.json` (`6de2cebc98667558bfb276c01a2286c46a88edff824491fda40799511abf8891`)
- `paper_bencmark/highambench/tasks/P18/T3/faithfulness/history/20260821T032511Z/agent_outputs/roundtrip_judge.json` (`c70c01e7ab0b809b64bac6eabf9e4e7eb2c5b9c4dd6601eb0e2247438395c92d`)
- `paper_bencmark/highambench/tasks/P18/T3/faithfulness/history/20260821T032511Z/agent_outputs/source_contract.json` (`8b7b58c3af70a576c27e1075f233f618cb1b8aeda01ceefc2826617f39f6ce9f`)
- `paper_bencmark/highambench/tasks/P18/T3/faithfulness/history/20260821T032511Z/decision.json` (`bba6fc64597e49d325f6961ec518a40b83c99165581ba057492b331298eb1956`)
- `paper_bencmark/highambench/tasks/P18/T3/faithfulness/history/20260821T032511Z/inputs/blind_dependency_inventory.json` (`ce89e79c6100d439936167a39052d4630d9ac0ac3c18e4270df060a4686b45a4`)
- `paper_bencmark/highambench/tasks/P18/T3/faithfulness/history/20260821T032511Z/inputs/blind_dossier.md` (`4bdb377e387528cd8d0aa9d347fbd04be79099d5b028dbd506f04bce89ff368c`)
- `paper_bencmark/highambench/tasks/P18/T3/faithfulness/history/20260821T032511Z/inputs/blind_review_packet.md` (`4bdb377e387528cd8d0aa9d347fbd04be79099d5b028dbd506f04bce89ff368c`)
- `paper_bencmark/highambench/tasks/P18/T3/faithfulness/history/20260821T032511Z/inputs/declaration_dossier.md` (`42f9769fe40a4f13d53d05e23ef3136db8aad91dc87c81989356f2fd4694db23`)
- `paper_bencmark/highambench/tasks/P18/T3/faithfulness/history/20260821T032511Z/inputs/dependency_inventory.json` (`476e68f3eaf1769c11ae56affd7b9a314c8e5f36d0f722aa2682cd545695ddfa`)
- `paper_bencmark/highambench/tasks/P18/T3/faithfulness/history/20260821T032511Z/inputs/dependency_reuse_direct.json` (`eea591c851e8f0ca3867018ee4a0065aaf8040324357e247dfb28e8af2af4051`)
- `paper_bencmark/highambench/tasks/P18/T3/faithfulness/history/20260821T032511Z/inputs/direct_review_packet.md` (`99ba47f4aa6cfcfce171f665ef81fe0b16310c50008aa0da18e17c8e6d045a68`)
- `paper_bencmark/highambench/tasks/P18/T3/faithfulness/history/20260821T032511Z/inputs/paper_source_locator.json` (`ba129952837b9f0f76f04aaf15df9d09fbc4e140b4fac00813259e514dd1ea6e`)
- `paper_bencmark/highambench/tasks/P18/T3/faithfulness/history/20260821T032511Z/inputs/source_locator.json` (`6abb00e96af145c08c8ac550e20acd16972f8232d455bcb0e569f56b8a31b062`)
- `paper_bencmark/highambench/tasks/P18/T3/faithfulness/inputs/blind_dependency_inventory.json` (`0ab32f299014337ef7bfc5fd6380166982afa385f7412714e9d1cde292fd368e`)
- `paper_bencmark/highambench/tasks/P18/T3/faithfulness/inputs/blind_dossier.md` (`eb41a9cd082b8fdaef6adcd3f2c02a1e3630dfea7e30d70ac2f926a172b40c5e`)
- `paper_bencmark/highambench/tasks/P18/T3/faithfulness/inputs/blind_review_packet.md` (`eb41a9cd082b8fdaef6adcd3f2c02a1e3630dfea7e30d70ac2f926a172b40c5e`)
- `paper_bencmark/highambench/tasks/P18/T3/faithfulness/inputs/declaration_dossier.md` (`2461096e0a09206e4a6d5319b01b9970bc146d539260a3fd0612aebdb850d35b`)
- `paper_bencmark/highambench/tasks/P18/T3/faithfulness/inputs/dependency_inventory.json` (`747a933861cb11ec71e16a9b6037a9747702aacc1d5649386265746fa021b674`)
- `paper_bencmark/highambench/tasks/P18/T3/faithfulness/inputs/direct_review_packet.md` (`bcb0f8726ef33a06c930585743583dfebce2985767ae909be217281a799a9447`)
- `paper_bencmark/highambench/tasks/P18/T3/faithfulness/inputs/source_locator.json` (`ae90801b3bb2d7345f3eaa0111ca37109af88d86f1645bf8256e6022d0ab2f52`)
