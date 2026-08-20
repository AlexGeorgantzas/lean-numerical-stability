# Faithfulness audit: P15-T1

- Classification: `undetermined`
- Accepted as paper-faithful: `false`
- Adjudicated: `true`
- Target SHA-256: `317350b3e17134b5663fd4b741ed6029642a3d73e3073e13c08bbe97dd1664b9`
- Paper SHA-256: `a5cb8eb779c1571f1549ea6838c7f2269302c960fb4ea21f8410060811270cd7`

## Decision

The verified paper states constant-one submultiplicativity for the unsquared Frobenius norm and does not confine the factors to equal square dimensions. The Lean declaration faithfully encodes exact real matrix multiplication and the same inequality shape, but only for common-size square matrices, so Lean-to-paper is definitively no. Establishing paper-to-Lean requires identifying D016's selected norm with the paper's precise Frobenius norm. Because the supplied body delegates that norm to an unexpanded dependency, this identification cannot be made from primary declaration evidence. The remaining uncertainty is material, so the final classification is undetermined and the target is not accepted.

## Implications

- **Lean implies paper:** `no`. Lean quantifies only pairs of real n-by-n matrices sharing one dimension. It therefore supplies no instance of the paper's claim for a genuinely rectangular compatible product, such as an a-by-b matrix multiplied by a b-by-c matrix with unequal outer dimensions. This is reduced applicability, not stronger theorem content.
- **Paper implies lean:** `unclear`. If D016's inherited norm is exactly the paper's unsquared, unnormalized Frobenius norm, the paper claim specializes to the represented square real matrices. The supplied declaration evidence does not establish that identity. The additional n = 0 case is degenerate and does not constitute genuine nonvacuous strength.

## Findings

- **critical / unresolved norm semantics:** Paper-implies-Lean cannot be verified, preventing a faithful-equivalent or not-faithful-weaker final classification.
- **major / dimensional specialization:** Lean does not imply the full paper claim. Even if the norm identity is later confirmed, the appropriate classification would be not-faithful-weaker.
- **note / nonvacuity and strength:** The target is nonvacuous, but neither its square restriction nor its zero-dimensional edge case supplies genuine stronger theorem content.

## Semantic checklist

| Check | Direct | Round-trip |
|---|---|---|
| `S01` | `pass` | `pass` |
| `S02` | `fail` | `fail` |
| `S03` | `pass` | `pass` |
| `S04` | `fail` | `pass` |
| `S05` | `pass` | `pass` |
| `S06` | `pass` | `unclear` |
| `S07` | `pass` | `pass` |
| `S08` | `not-applicable` | `not-applicable` |
| `S09` | `pass` | `unclear` |
| `S10` | `pass` | `pass` |
| `S11` | `not-applicable` | `not-applicable` |
| `S12` | `fail` | `fail` |
| `S13` | `not-applicable` | `not-applicable` |
| `S14` | `not-applicable` | `not-applicable` |
| `S15` | `fail` | `fail` |
| `S16` | `pass` | `pass` |

## Dependency coverage

- Blind translator covered `21` dependencies (`0` hash-reused meanings); unclear: `D016`.
- Direct judge covered `21` dependencies (`0` hash-reused interpretations); failing or unclear: `D001`.

## Remaining uncertainties

- The supplied declaration evidence does not unfold Matrix.frobeniusSeminormedAddCommGroup, so D016 cannot be verified as exactly sqrt(sum_{i,j} |a_ij|^2) with no normalization.

## Audit artifacts

- `paper_bencmark/highambench/tasks/P15/T1/faithfulness/agent_outputs/adjudicator.json` (`df166e54946fb567c143372583da4de8a037a233d2c9b90df3432443038c622e`)
- `paper_bencmark/highambench/tasks/P15/T1/faithfulness/agent_outputs/blind_translation.json` (`0b458727bad7eaaf02d8e49ffa42e8dd292aa46e580147536d91ef8e62825f2c`)
- `paper_bencmark/highambench/tasks/P15/T1/faithfulness/agent_outputs/direct_judge.json` (`440655a6056b010238c94f4a0775955ee84714c0df9877ac5ad610eb2cfd4147`)
- `paper_bencmark/highambench/tasks/P15/T1/faithfulness/agent_outputs/paper_source_contract.json` (`339fc5a797919c9e9bcd9c7d27d579722d8bfedc8091d16c4ab89148a1eb498f`)
- `paper_bencmark/highambench/tasks/P15/T1/faithfulness/agent_outputs/roundtrip_judge.json` (`0927ac71b3261a533e16682267056e60415477b323fba6604f461812eab87c28`)
- `paper_bencmark/highambench/tasks/P15/T1/faithfulness/agent_outputs/source_contract.json` (`1c57848287524d26826de55c88776b38bceadc4a7fefc66b5e6c5dfb329908f2`)
- `paper_bencmark/highambench/tasks/P15/T1/faithfulness/decision.json` (`5db63560734a5dcafc1b4067cf8aa3db9e55fa2e55bf322588070d371ac2efb9`)
- `paper_bencmark/highambench/tasks/P15/T1/faithfulness/inputs/blind_dependency_inventory.json` (`a2b1986507bb7cfac31736acf32ba28db4f350f409a36919c6bc45b81c972607`)
- `paper_bencmark/highambench/tasks/P15/T1/faithfulness/inputs/blind_dossier.md` (`7ed6f37aa855cf5f82eb60ca42bce6feeac7d8cae170a77812c2eb639eb331b1`)
- `paper_bencmark/highambench/tasks/P15/T1/faithfulness/inputs/blind_review_packet.md` (`7ed6f37aa855cf5f82eb60ca42bce6feeac7d8cae170a77812c2eb639eb331b1`)
- `paper_bencmark/highambench/tasks/P15/T1/faithfulness/inputs/declaration_dossier.md` (`7f78fc172e62b17e1628ee07ac9a280e0be4111e0eb00b4b9658f5c59ae7fe23`)
- `paper_bencmark/highambench/tasks/P15/T1/faithfulness/inputs/dependency_inventory.json` (`28723b57200c4d698e93a7fb6bf5e6d8d4b28ca5cde6a3df00adc93998d7d728`)
- `paper_bencmark/highambench/tasks/P15/T1/faithfulness/inputs/direct_review_packet.md` (`921be4ffc36d2a9b31af09751441156dc57ba43843c2107cc3d0dc74924b1718`)
- `paper_bencmark/highambench/tasks/P15/T1/faithfulness/inputs/paper_source_locator.json` (`568b244880bf84912b78ba1130fd66ae2d43016e0a25f06e4510e3d731ee5223`)
- `paper_bencmark/highambench/tasks/P15/T1/faithfulness/inputs/source_locator.json` (`260250b2352e7ec1b1162b22a83469f840de71b33e27c2ab3ea6a18ba3511bdb`)
