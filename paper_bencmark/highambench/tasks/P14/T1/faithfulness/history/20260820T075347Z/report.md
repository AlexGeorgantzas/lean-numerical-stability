# Faithfulness audit: P14-T1

- Classification: `not-faithful-different`
- Accepted as paper-faithful: `false`
- Adjudicated: `false`
- Target SHA-256: `0a667aa6e36e01717511c96133b6fd38517644187bc09a7eeb2bb6f9248fb484`
- Paper SHA-256: `7247047bc49218e001195edc8a2d66131eea7596d252503f34b0ace6328981cd`

## Decision

The PDF hash was verified and the cited passage was checked with its surrounding Algorithm 3.1, equations (1.7), (3.1)-(3.3), and Section 3 assumptions. The Lean theorem is a coherent, nonvacuous exact gamma bound for left-to-right summation of arbitrary nonnegative real inputs under an abstract addition model. That is only the recursive-addition component of P14-T1. The paper result also models computed exponentials, distinguishes s, tilde(s), and hat(s), combines both error sources, and retains an O(u^2) remainder with aggregate coefficient n+1. Because the Lean theorem omits those obligations while asserting a different exact bound over a different domain, both implication directions fail and the result is not faithful-different.

## Implications

- **Lean implies paper:** `no`. The Lean conclusion controls only recursive addition of supplied nonnegative values. It provides no bound on exponential-evaluation error and therefore cannot derive the paper's relation between exact s and final hat(s), its (n+1)u coefficient, or its O(u^2) remainder.
- **Paper implies lean:** `no`. The cited paper result is stated for exponential-generated quantities under no overflow or underflow and gives first-order bounds with O(u^2). It does not state the exact gamma u (n-1) inequality for every arbitrary nonnegative sequence and every StandardAddModel satisfying GammaValid.

## Findings

- **critical / missing-computation-stage:** The theorem proves only an intermediate recursive-summation lemma and cannot establish the selected paper result.
- **major / different-bound:** The constants, normalization, hypotheses, and higher-order semantics differ, so neither proposition implies the other as stated.
- **major / quantity-conflation:** The formal statement cannot express the decomposition on which the paper's total error analysis depends.
- **note / source-typography:** The source typo is real but does not create uncertainty in this judgment because equation (3.3) and the preceding derivation are clear, and the Lean target matches neither aggregate formulation.
- **critical / algorithm-and-quantity-scope:** The translated proposition is not the paper's two-stage error result.
- **major / conclusion-constants-and-error-form:** The constant, normalization, finite-u form, and represented error sources all differ.
- **major / hypotheses-and-numerical-model:** The theorem applies under a materially different contract.
- **major / higher-order-treatment:** The paper's asymptotic and textual meaning is replaced rather than translated.
- **minor / dimension-and-vacuity:** Boundary dimensions do not preserve the paper computation's behavior.

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
| `S09` | `pass` | `fail` |
| `S10` | `fail` | `fail` |
| `S11` | `fail` | `fail` |
| `S12` | `fail` | `fail` |
| `S13` | `fail` | `fail` |
| `S14` | `fail` | `fail` |
| `S15` | `fail` | `fail` |
| `S16` | `pass` | `fail` |

## Dependency coverage

- Blind translator covered `62` dependencies (`0` hash-reused meanings); unclear: `none`.
- Direct judge covered `62` dependencies (`0` hash-reused interpretations); failing or unclear: `D001, D005`.

## Remaining uncertainties

No remaining uncertainties were recorded.

## Audit artifacts

- `paper_bencmark/highambench/tasks/P14/T1/faithfulness/agent_outputs/blind_translation.json` (`d5a0ef51c7edd0b0d65f37202c4f3789bd28545c13157dfbe555336fe96e879c`)
- `paper_bencmark/highambench/tasks/P14/T1/faithfulness/agent_outputs/direct_judge.json` (`355484fc173f1bc14654e92ce769be4b79c78b32ce7b280f191fac1d678e56af`)
- `paper_bencmark/highambench/tasks/P14/T1/faithfulness/agent_outputs/paper_source_contract.json` (`b9f05c969428f95fef40bddc0aa0b2a7c1d291ecdd7ba0ca0f5fb748131f1562`)
- `paper_bencmark/highambench/tasks/P14/T1/faithfulness/agent_outputs/roundtrip_judge.json` (`ebc2c77f6cd66f4abe564e6b702c9e7bdb0ff38be46ca6f56d6d0c7fa14d9218`)
- `paper_bencmark/highambench/tasks/P14/T1/faithfulness/agent_outputs/source_contract.json` (`a6db6f8060b77e3de1227a8f25b86e2bfa59e60a708c7100f5588e01477a1da9`)
- `paper_bencmark/highambench/tasks/P14/T1/faithfulness/decision.json` (`ec36bf88dbe3c4d427995f08c94abb6bba03baad93e1d587f7c9bf26ece67be4`)
- `paper_bencmark/highambench/tasks/P14/T1/faithfulness/inputs/blind_dependency_inventory.json` (`232958a14ed1b329a02aabddcff2ff787e1d87fcc6d16e9e5c30c155a29d2ef5`)
- `paper_bencmark/highambench/tasks/P14/T1/faithfulness/inputs/blind_dossier.md` (`608e35f75ad860de70c845e29b159ef50c94cd3ed1ee1efb8c497c00e3e0da68`)
- `paper_bencmark/highambench/tasks/P14/T1/faithfulness/inputs/blind_review_packet.md` (`608e35f75ad860de70c845e29b159ef50c94cd3ed1ee1efb8c497c00e3e0da68`)
- `paper_bencmark/highambench/tasks/P14/T1/faithfulness/inputs/declaration_dossier.md` (`9b346ffa1c471f654fcdcc6f94608e9dbceb7d3f7b974fc706e6051a35b10673`)
- `paper_bencmark/highambench/tasks/P14/T1/faithfulness/inputs/dependency_inventory.json` (`d8089db76b9ece948720014e5ad61ba2734e696ec20690d958cb41bcf1b1d272`)
- `paper_bencmark/highambench/tasks/P14/T1/faithfulness/inputs/direct_review_packet.md` (`7ce3cae8d9eb21a1b6bbee129b6084f539e1cc46ff00963209359049ff00868c`)
- `paper_bencmark/highambench/tasks/P14/T1/faithfulness/inputs/paper_source_locator.json` (`8627ed196c1c7742168563780358efbf3ebaee357ded297978c4d9199a86318c`)
- `paper_bencmark/highambench/tasks/P14/T1/faithfulness/inputs/source_locator.json` (`0743d6c88f70fe6e0d2d4ba6647096a4162697a6774b21cfea6b247ac705bbb5`)
