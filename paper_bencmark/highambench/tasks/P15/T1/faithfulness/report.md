# Faithfulness audit: P15-T1

- Classification: `faithful-equivalent`
- Accepted as paper-faithful: `true`
- Adjudicated: `false`
- Target SHA-256: `cd09d32b3060a89a0f9071e7d1db40086544808e7ba79c750b5c2803938399ce`
- Paper SHA-256: `a5cb8eb779c1571f1549ea6838c7f2269302c960fb4ea21f8410060811270cd7`

## Decision

The target unfolds to the exact Frobenius-norm submultiplicativity inequality for arbitrary conformable finite real matrices. Its norm is the square root of the sum of real entry squares, its product is the standard exact inner-index sum, and its relation is the paper's non-strict inequality with constant 1. It adds no algorithmic, floating-point, rank, block, or error hypotheses. Both implication directions hold, with zero-dimensional Lean instances constituting only valid boundary cases.

## Implications

- **Lean implies paper:** `yes`. After unfolding the three local definitions, Lean states that every conformable finite real A and B satisfies sqrt(sum_ij (sum_k A_ik B_kj)^2) <= sqrt(sum_ik A_ik^2) * sqrt(sum_kj B_kj^2). Because real squares equal squared absolute values, this directly gives the paper's Frobenius submultiplicativity statement.
- **Paper implies lean:** `yes`. The paper's universally stated Frobenius property applies to each positive-dimensional real Matrix (Fin m) (Fin n) instance and the exact product used by Lean. If conventional paper dimensions are taken as positive, every remaining zero-dimensional Lean case independently reduces to 0 <= 0 because an outer dimension is empty or the shared dimension makes both factors and the product zero.

## Findings

- **note / dimension-domain-explication:** This does not change the positive-dimensional claim or the benchmark substance; the added boundary instances are valid trivial cases.

## Semantic checklist

| Check | Direct | Round-trip |
|---|---|---|
| `S01` | `pass` | `pass` |
| `S02` | `pass` | `pass` |
| `S03` | `pass` | `pass` |
| `S04` | `pass` | `pass` |
| `S05` | `pass` | `pass` |
| `S06` | `pass` | `pass` |
| `S07` | `pass` | `pass` |
| `S08` | `not-applicable` | `not-applicable` |
| `S09` | `pass` | `pass` |
| `S10` | `pass` | `pass` |
| `S11` | `not-applicable` | `not-applicable` |
| `S12` | `pass` | `pass` |
| `S13` | `not-applicable` | `not-applicable` |
| `S14` | `not-applicable` | `pass` |
| `S15` | `pass` | `pass` |
| `S16` | `pass` | `pass` |

## Dependency coverage

- Blind translator covered `23` dependencies (`0` hash-reused meanings); unclear: `none`.
- Direct judge covered `23` dependencies (`0` hash-reused interpretations); failing or unclear: `none`.

## Remaining uncertainties

No remaining uncertainties were recorded.

## Audit artifacts

- `paper_bencmark/highambench/tasks/P15/T1/faithfulness/agent_outputs/blind_translation.json` (`a5434247748f7304ceb9534a6dc1721ada16ba88e04e3b780a1b24da1e6aa6a4`)
- `paper_bencmark/highambench/tasks/P15/T1/faithfulness/agent_outputs/direct_judge.json` (`cf8f5fed7d67da97d9caf2df747f5fa25a2d969d5f8a54099e9e5e1fca2daf7f`)
- `paper_bencmark/highambench/tasks/P15/T1/faithfulness/agent_outputs/roundtrip_judge.json` (`cc0cd9f75df87651433bcf42b98f1af918fed6810cfb9fd6663ee5c93a61665a`)
- `paper_bencmark/highambench/tasks/P15/T1/faithfulness/agent_outputs/source_contract.json` (`ba02cacf583bb1d8290c6008e4a9d76c3baa13b171c5c89c489f9b0fceee6e37`)
- `paper_bencmark/highambench/tasks/P15/T1/faithfulness/decision.json` (`b478a8fb1b80d4cbc605eaa17d508f6c321da0a985b16f6cec654992bf6c510b`)
- `paper_bencmark/highambench/tasks/P15/T1/faithfulness/history/20260820T075659Z/agent_outputs/adjudicator.json` (`df166e54946fb567c143372583da4de8a037a233d2c9b90df3432443038c622e`)
- `paper_bencmark/highambench/tasks/P15/T1/faithfulness/history/20260820T075659Z/agent_outputs/blind_translation.json` (`0b458727bad7eaaf02d8e49ffa42e8dd292aa46e580147536d91ef8e62825f2c`)
- `paper_bencmark/highambench/tasks/P15/T1/faithfulness/history/20260820T075659Z/agent_outputs/direct_judge.json` (`440655a6056b010238c94f4a0775955ee84714c0df9877ac5ad610eb2cfd4147`)
- `paper_bencmark/highambench/tasks/P15/T1/faithfulness/history/20260820T075659Z/agent_outputs/paper_source_contract.json` (`339fc5a797919c9e9bcd9c7d27d579722d8bfedc8091d16c4ab89148a1eb498f`)
- `paper_bencmark/highambench/tasks/P15/T1/faithfulness/history/20260820T075659Z/agent_outputs/roundtrip_judge.json` (`0927ac71b3261a533e16682267056e60415477b323fba6604f461812eab87c28`)
- `paper_bencmark/highambench/tasks/P15/T1/faithfulness/history/20260820T075659Z/agent_outputs/source_contract.json` (`1c57848287524d26826de55c88776b38bceadc4a7fefc66b5e6c5dfb329908f2`)
- `paper_bencmark/highambench/tasks/P15/T1/faithfulness/history/20260820T075659Z/decision.json` (`5db63560734a5dcafc1b4067cf8aa3db9e55fa2e55bf322588070d371ac2efb9`)
- `paper_bencmark/highambench/tasks/P15/T1/faithfulness/history/20260820T075659Z/inputs/blind_dependency_inventory.json` (`a2b1986507bb7cfac31736acf32ba28db4f350f409a36919c6bc45b81c972607`)
- `paper_bencmark/highambench/tasks/P15/T1/faithfulness/history/20260820T075659Z/inputs/blind_dossier.md` (`7ed6f37aa855cf5f82eb60ca42bce6feeac7d8cae170a77812c2eb639eb331b1`)
- `paper_bencmark/highambench/tasks/P15/T1/faithfulness/history/20260820T075659Z/inputs/blind_review_packet.md` (`7ed6f37aa855cf5f82eb60ca42bce6feeac7d8cae170a77812c2eb639eb331b1`)
- `paper_bencmark/highambench/tasks/P15/T1/faithfulness/history/20260820T075659Z/inputs/declaration_dossier.md` (`7f78fc172e62b17e1628ee07ac9a280e0be4111e0eb00b4b9658f5c59ae7fe23`)
- `paper_bencmark/highambench/tasks/P15/T1/faithfulness/history/20260820T075659Z/inputs/dependency_inventory.json` (`28723b57200c4d698e93a7fb6bf5e6d8d4b28ca5cde6a3df00adc93998d7d728`)
- `paper_bencmark/highambench/tasks/P15/T1/faithfulness/history/20260820T075659Z/inputs/direct_review_packet.md` (`921be4ffc36d2a9b31af09751441156dc57ba43843c2107cc3d0dc74924b1718`)
- `paper_bencmark/highambench/tasks/P15/T1/faithfulness/history/20260820T075659Z/inputs/paper_source_locator.json` (`568b244880bf84912b78ba1130fd66ae2d43016e0a25f06e4510e3d731ee5223`)
- `paper_bencmark/highambench/tasks/P15/T1/faithfulness/history/20260820T075659Z/inputs/source_locator.json` (`260250b2352e7ec1b1162b22a83469f840de71b33e27c2ab3ea6a18ba3511bdb`)
- `paper_bencmark/highambench/tasks/P15/T1/faithfulness/inputs/blind_dependency_inventory.json` (`fb1523d50905aa5b69d1b4585938acb947d97fcd3cc116826776fc9a5a3c5bc1`)
- `paper_bencmark/highambench/tasks/P15/T1/faithfulness/inputs/blind_dossier.md` (`868b6df91a461b76e93d798ba09f176a9abda8163f9060383c969f579d011ef2`)
- `paper_bencmark/highambench/tasks/P15/T1/faithfulness/inputs/blind_review_packet.md` (`868b6df91a461b76e93d798ba09f176a9abda8163f9060383c969f579d011ef2`)
- `paper_bencmark/highambench/tasks/P15/T1/faithfulness/inputs/declaration_dossier.md` (`8c1076096f94f269cca702fd6efdf8a21316215b87e4aab89210bf3c9c964817`)
- `paper_bencmark/highambench/tasks/P15/T1/faithfulness/inputs/dependency_inventory.json` (`c00380ee615dc604146a023bc061e45d65dc27c1621ed3332c498e970391eef6`)
- `paper_bencmark/highambench/tasks/P15/T1/faithfulness/inputs/direct_review_packet.md` (`d7eff3f141b529a2f19900409bd45d002fbc7855c7cee69c9870670ed127524e`)
- `paper_bencmark/highambench/tasks/P15/T1/faithfulness/inputs/source_locator.json` (`260250b2352e7ec1b1162b22a83469f840de71b33e27c2ab3ea6a18ba3511bdb`)
