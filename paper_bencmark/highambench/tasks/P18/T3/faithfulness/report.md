# Faithfulness audit: P18-T3

- Classification: `not-faithful-different`
- Accepted as paper-faithful: `false`
- Adjudicated: `true`
- Target SHA-256: `49f3c1f801a32c3b35d3c5fbe9f848f9d3201e4f6664be5e9c14068fbe28c14c`
- Paper SHA-256: `b18628ffc348d7aeec2da02efb989b6e012f0b0fae09b27fbff735bb8a5877cd`

## Decision

The inspected PDF has the required SHA-256 and supports the source packet. The declaration preserves the two exponents and the printed consistency and smooth-cancellation equation patterns, but it changes the subject and proof content: an arbitrary exact tableau replaces the identifiable decimal method; analytic regimes become inert labels; local orders and stability propagation are supplied as certificate assumptions; and purported exact states lack ODE-flow semantics. The decimal residual prevents exact identification without unprinted coefficient data, and D016 does not encode a required small-step family. Accepting the arbitrary normed-space choice cannot repair these independent failures. Both implication directions therefore fail, so the stable adjudicated classification is not-faithful-different.

## Implications

- **Lean implies paper:** `no`. The declaration can apply to an arbitrary exact tableau package rather than the printed Method 4s3pC, while its regime tags constrain nothing and its local orders, stability accumulation, and error split are assumed. Its referenceNext and exactState need not follow the ODE flow, and D016 need not describe a small-step family. Consequently it can hold without establishing either source rate for the identified method.
- **Paper implies lean:** `no`. The paper gives stability-conditional expected rates for one displayed decimal tableau. It supplies neither an exact unrounded tableau satisfying all constructor equalities nor the declaration's exact local bounds, arbitrary-family inequalities, sum-stability certificates, endpoint error decomposition, or exact-state data. The paper therefore does not entail the Lean proposition under its formal quantifiers.

## Findings

- **critical / method identity and coefficient exactness:** No exact source-supported equality identifies the Lean tableau with Method 4s3pC; an unspecified underlying rounded tableau cannot supply that linkage.
- **major / regime and assumed content:** The theorem does not derive the two rates from the paper's regularity distinction and presupposes central accuracy content.
- **major / exact-flow semantics:** Certificates can measure arbitrary stored-state differences rather than truncation or global error against an exact solution.
- **major / big-O semantics:** The formal predicate has no fixed implication relationship with the source's standard asymptotic reading.
- **note / norm semantics:** This is an admissible explicit interpretation and does not alter the negative classification.

## Semantic checklist

| Check | Direct | Round-trip |
|---|---|---|
| `S01` | `fail` | `fail` |
| `S02` | `pass` | `fail` |
| `S03` | `fail` | `fail` |
| `S04` | `fail` | `fail` |
| `S05` | `pass` | `fail` |
| `S06` | `pass` | `fail` |
| `S07` | `fail` | `fail` |
| `S08` | `fail` | `fail` |
| `S09` | `unclear` | `unclear` |
| `S10` | `fail` | `fail` |
| `S11` | `pass` | `fail` |
| `S12` | `fail` | `fail` |
| `S13` | `fail` | `fail` |
| `S14` | `unclear` | `fail` |
| `S15` | `fail` | `fail` |
| `S16` | `fail` | `fail` |

## Dependency coverage

- Blind translator covered `134` dependencies (`0` hash-reused meanings); unclear: `none`.
- Direct judge covered `134` dependencies (`0` hash-reused interpretations); failing or unclear: `D002, D004, D006, D010, D011, D012, D013, D016, D019, D020, D042, D051, D053, D104`.

## Remaining uncertainties

- The PDF does not identify the exact unrounded nonzero coefficients, so existence and uniqueness of an exact tableau rounding to every displayed Method 4s3pC entry cannot be established from the source.
- The particular state or error norm intended for the narrative formulas and Figure 6 remains unspecified, although treating the norm as a formal parameter is admissible.
- The paper does not define the threshold, filter, constant dependence, or joint epsilon/Delta t convention for its big-O notation.
- The source does not fully reconcile its generic nonsmooth sufficient conditions with the stated Method 4s3pC nonsmooth expected rate.

## Audit artifacts

- `paper_bencmark/highambench/tasks/P18/T3/faithfulness/agent_outputs/adjudicator.json` (`50bea60a69e68525adca40df6ddc2a1d750267d593fd0aa6be720ab30f574109`)
- `paper_bencmark/highambench/tasks/P18/T3/faithfulness/agent_outputs/blind_translation.json` (`cf2f71392f0dc558fe108bcfbbe48153e5fc140adfa077d877e750f16405c8ae`)
- `paper_bencmark/highambench/tasks/P18/T3/faithfulness/agent_outputs/direct_judge.json` (`497aff1c1f58684b68186e9d414db63cef52236cc1e4cc713e5e2cf4c11f5cec`)
- `paper_bencmark/highambench/tasks/P18/T3/faithfulness/agent_outputs/roundtrip_judge.json` (`46aef7e9c1803047f3a2b1b2c6aa8cf0c746c1ea72a6ba77449b8a92ab0efa0d`)
- `paper_bencmark/highambench/tasks/P18/T3/faithfulness/agent_outputs/source_contract.json` (`d0918011606cc198b942b36708a8103ee2ca60bd75633b3af5b46c0b428b6d47`)
- `paper_bencmark/highambench/tasks/P18/T3/faithfulness/decision.json` (`6a78024e228e7a2bb2cc5e76560a0597aaa2fa0b08ca0885d2d27a447bf7df4d`)
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
- `paper_bencmark/highambench/tasks/P18/T3/faithfulness/history/20260822T002238Z/agent_outputs/blind_translation.json` (`0b899a02f671d265be5b7a79f51c2d73c531635cd85b7ddbd5196bb39a2b58ce`)
- `paper_bencmark/highambench/tasks/P18/T3/faithfulness/history/20260822T002238Z/agent_outputs/direct_judge.json` (`24f22350dcd24896ba66caf6b016a29b48282ed4efcd1ffaa966f57508f2bd59`)
- `paper_bencmark/highambench/tasks/P18/T3/faithfulness/history/20260822T002238Z/agent_outputs/roundtrip_judge.json` (`538dffb814b593ccfe9a79855725cb832f847bc577ea5b6b4aebcfede95e646c`)
- `paper_bencmark/highambench/tasks/P18/T3/faithfulness/history/20260822T002238Z/agent_outputs/source_contract.json` (`73091c516e5202e341a8ca22a62dbcec6c561adb8565188bd0a603fd9e4ae850`)
- `paper_bencmark/highambench/tasks/P18/T3/faithfulness/history/20260822T002238Z/decision.json` (`655fe1539db8d0eb85b6f191e1b628e1249ad90571320fb3b2dd3f0869f50a89`)
- `paper_bencmark/highambench/tasks/P18/T3/faithfulness/history/20260822T002238Z/inputs/blind_dependency_inventory.json` (`0ab32f299014337ef7bfc5fd6380166982afa385f7412714e9d1cde292fd368e`)
- `paper_bencmark/highambench/tasks/P18/T3/faithfulness/history/20260822T002238Z/inputs/blind_dossier.md` (`eb41a9cd082b8fdaef6adcd3f2c02a1e3630dfea7e30d70ac2f926a172b40c5e`)
- `paper_bencmark/highambench/tasks/P18/T3/faithfulness/history/20260822T002238Z/inputs/blind_review_packet.md` (`eb41a9cd082b8fdaef6adcd3f2c02a1e3630dfea7e30d70ac2f926a172b40c5e`)
- `paper_bencmark/highambench/tasks/P18/T3/faithfulness/history/20260822T002238Z/inputs/declaration_dossier.md` (`2461096e0a09206e4a6d5319b01b9970bc146d539260a3fd0612aebdb850d35b`)
- `paper_bencmark/highambench/tasks/P18/T3/faithfulness/history/20260822T002238Z/inputs/dependency_inventory.json` (`747a933861cb11ec71e16a9b6037a9747702aacc1d5649386265746fa021b674`)
- `paper_bencmark/highambench/tasks/P18/T3/faithfulness/history/20260822T002238Z/inputs/direct_review_packet.md` (`bcb0f8726ef33a06c930585743583dfebce2985767ae909be217281a799a9447`)
- `paper_bencmark/highambench/tasks/P18/T3/faithfulness/history/20260822T002238Z/inputs/source_locator.json` (`ae90801b3bb2d7345f3eaa0111ca37109af88d86f1645bf8256e6022d0ab2f52`)
- `paper_bencmark/highambench/tasks/P18/T3/faithfulness/inputs/blind_dependency_inventory.json` (`2aca26968e3233f693a7895d64f2fe2c1f34d4138a372d2d0062325e0d94d671`)
- `paper_bencmark/highambench/tasks/P18/T3/faithfulness/inputs/blind_dossier.md` (`bc9e30efbef354b21298ec4818f476b95b46389ff0607d2dd0fe65e009a5858e`)
- `paper_bencmark/highambench/tasks/P18/T3/faithfulness/inputs/blind_review_packet.md` (`bc9e30efbef354b21298ec4818f476b95b46389ff0607d2dd0fe65e009a5858e`)
- `paper_bencmark/highambench/tasks/P18/T3/faithfulness/inputs/declaration_dossier.md` (`38fc966a79e8f20b62a6394dc697c44379f78bcb565114947316e63b5d05319d`)
- `paper_bencmark/highambench/tasks/P18/T3/faithfulness/inputs/dependency_inventory.json` (`975eb86d057470678baf4002c38f5324e2005b5f88487cc097ab65bbf16869d7`)
- `paper_bencmark/highambench/tasks/P18/T3/faithfulness/inputs/direct_review_packet.md` (`c70890b64218215f35b772c3b8a71b3fa99396f6824d0731fb284beab6e035e0`)
- `paper_bencmark/highambench/tasks/P18/T3/faithfulness/inputs/source_locator.json` (`ae90801b3bb2d7345f3eaa0111ca37109af88d86f1645bf8256e6022d0ab2f52`)
