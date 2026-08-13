# Faithfulness audit: P18-T3

- Classification: `not-faithful-different`
- Accepted as paper-faithful: `false`
- Adjudicated: `true`
- Target SHA-256: `19c676db2955c73a38faa19bd0b61c955f08938f1434ac37844445c26a3ebbaf`
- Paper SHA-256: `b18628ffc348d7aeec2da02efb989b6e012f0b0fae09b27fbff735bb8a5877cd`

## Decision

The inspected reference PDF has SHA-256 b18628ffc348d7aeec2da02efb989b6e012f0b0fae09b27fbff735bb8a5877cd. It decisively identifies a coefficient-specific, stability-qualified, regularity-dependent global-error claim for Method 4s3pC. The formal declaration instead proves universally valid Euclidean triangle inequalities for exact surrogate vectors, with the desired powers inserted by definition. The PDF's silence about norm and dimension leaves those specializations unsupported rather than contradictory, but even granting them does not restore the algorithm, hypotheses, error notion, or asymptotic semantics. Neither implication holds, so not-faithful-different is the required classification.

## Implications

- **Lean implies paper:** `no`. The Lean theorem proves exact triangle-type inequalities for vectors defined to equal h^3 times an arbitrary scheme vector plus epsilon h^k times an arbitrary perturbation vector. It contains no Method 4s3pC coefficients or stages, F or F^epsilon, tau regularity, stability, numerical trajectory, global forward error, or asymptotic witnesses. It therefore cannot establish either paper regime, regardless of whether the paper's unspecified norm could be Euclidean.
- **Paper implies lean:** `no`. The paper's coefficient-specific, stability-qualified big-O envelopes for actual global error do not assert exact unit-constant inequalities for every arbitrary Fin n vector and every h in [0,1], do not define error as the formal vector sums, and do not compare the two regime bounds by the formal third conjunct. The formal inequalities are independently true algebraic facts, not the semantic consequence expressed by the paper.

## Findings

- **critical / claim-substitution:** The formal theorem is an elementary vector-norm result, not a result about execution or convergence of Method 4s3pC.
- **major / asymptotic-semantics:** The relations have different mathematical meanings, preventing either semantic implication.
- **major / regime-and-hypotheses:** The central smooth-versus-nonsmooth distinction and the assumptions justifying the global orders are absent.
- **minor / unsupported-norm-and-dimension:** This is a genuine but non-pivotal source ambiguity, not evidence of a conflicting norm or dimension.
- **minor / extra-comparison:** The additional conjunct is not part of the source claim and cannot be inferred by comparing big-O expressions with unrelated hidden constants.

## Semantic checklist

| Check | Direct | Round-trip |
|---|---|---|
| `S01` | `pass` | `pass` |
| `S02` | `fail` | `fail` |
| `S03` | `fail` | `fail` |
| `S04` | `fail` | `fail` |
| `S05` | `fail` | `fail` |
| `S06` | `pass` | `pass` |
| `S07` | `fail` | `fail` |
| `S08` | `fail` | `fail` |
| `S09` | `unclear` | `unclear` |
| `S10` | `fail` | `fail` |
| `S11` | `fail` | `fail` |
| `S12` | `fail` | `fail` |
| `S13` | `fail` | `fail` |
| `S14` | `fail` | `fail` |
| `S15` | `fail` | `fail` |
| `S16` | `fail` | `pass` |

## Dependency coverage

- Blind translator covered `33` dependencies (`0` hash-reused meanings); unclear: `none`.
- Direct judge covered `33` dependencies (`3` hash-reused interpretations); failing or unclear: `D001, D002, D003, D006, D007, D008, D012, D019, D029, D030, D031, D032`.

## Remaining uncertainties

- The PDF does not determine whether the theoretical or Figure 6 Error uses an Euclidean 2-norm, another norm, or a different normalization. Thus the formal Euclidean norm is unsupported but not contradicted.
- The PDF does not specify a state-error dimension or coordinate index set. A finite-dimensional realization may be compatible with a spatial discretization, but arbitrary Fin n vectors, including n = 0, are not sourced.
- Neither uncertainty affects the implication verdicts or classification because the missing algorithm linkage, separate regime hypotheses, stability qualification, actual error object, and big-O semantics remain decisive under any compatible norm or finite dimension.

## Audit artifacts

- `paper_bencmark/highambench/tasks/P18/T3/faithfulness/agent_outputs/adjudicator.json` (`f26be36b6bd95d8db71ac076800bfb69b5a5e8906221bcaab9cf2fc833d87c44`)
- `paper_bencmark/highambench/tasks/P18/T3/faithfulness/agent_outputs/blind_translation.json` (`6e0eea38d5314e6876a9b89c8de9005e50f9c43d146928816f209ddf4b0c8a6d`)
- `paper_bencmark/highambench/tasks/P18/T3/faithfulness/agent_outputs/direct_judge.json` (`56c998e903935bf3936f0b165ae83471058438382699f2341fe05b7915e47f86`)
- `paper_bencmark/highambench/tasks/P18/T3/faithfulness/agent_outputs/paper_source_contract.json` (`6de2cebc98667558bfb276c01a2286c46a88edff824491fda40799511abf8891`)
- `paper_bencmark/highambench/tasks/P18/T3/faithfulness/agent_outputs/roundtrip_judge.json` (`c70c01e7ab0b809b64bac6eabf9e4e7eb2c5b9c4dd6601eb0e2247438395c92d`)
- `paper_bencmark/highambench/tasks/P18/T3/faithfulness/agent_outputs/source_contract.json` (`8b7b58c3af70a576c27e1075f233f618cb1b8aeda01ceefc2826617f39f6ce9f`)
- `paper_bencmark/highambench/tasks/P18/T3/faithfulness/decision.json` (`bba6fc64597e49d325f6961ec518a40b83c99165581ba057492b331298eb1956`)
- `paper_bencmark/highambench/tasks/P18/T3/faithfulness/inputs/blind_dependency_inventory.json` (`ce89e79c6100d439936167a39052d4630d9ac0ac3c18e4270df060a4686b45a4`)
- `paper_bencmark/highambench/tasks/P18/T3/faithfulness/inputs/blind_dossier.md` (`4bdb377e387528cd8d0aa9d347fbd04be79099d5b028dbd506f04bce89ff368c`)
- `paper_bencmark/highambench/tasks/P18/T3/faithfulness/inputs/blind_review_packet.md` (`4bdb377e387528cd8d0aa9d347fbd04be79099d5b028dbd506f04bce89ff368c`)
- `paper_bencmark/highambench/tasks/P18/T3/faithfulness/inputs/declaration_dossier.md` (`42f9769fe40a4f13d53d05e23ef3136db8aad91dc87c81989356f2fd4694db23`)
- `paper_bencmark/highambench/tasks/P18/T3/faithfulness/inputs/dependency_inventory.json` (`476e68f3eaf1769c11ae56affd7b9a314c8e5f36d0f722aa2682cd545695ddfa`)
- `paper_bencmark/highambench/tasks/P18/T3/faithfulness/inputs/dependency_reuse_direct.json` (`eea591c851e8f0ca3867018ee4a0065aaf8040324357e247dfb28e8af2af4051`)
- `paper_bencmark/highambench/tasks/P18/T3/faithfulness/inputs/direct_review_packet.md` (`99ba47f4aa6cfcfce171f665ef81fe0b16310c50008aa0da18e17c8e6d045a68`)
- `paper_bencmark/highambench/tasks/P18/T3/faithfulness/inputs/paper_source_locator.json` (`ba129952837b9f0f76f04aaf15df9d09fbc4e140b4fac00813259e514dd1ea6e`)
- `paper_bencmark/highambench/tasks/P18/T3/faithfulness/inputs/source_locator.json` (`6abb00e96af145c08c8ac550e20acd16972f8232d455bcb0e569f56b8a31b062`)
