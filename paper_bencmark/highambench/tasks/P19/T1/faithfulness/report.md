# Faithfulness audit: P19-T1

- Classification: `faithful-stronger`
- Accepted as paper-faithful: `true`
- Adjudicated: `true`
- Target SHA-256: `2eca9e6678e91b0213d8c9604aaaef94fc97ccccd35e7d4bc3d0a97804a8ce66`
- Paper SHA-256: `67af427c72ae891b7863e386db542ef775b1e3eb306f812bb1a78bdbef86aaad`

## Decision

For the reference PDF with SHA-256 67af427c72ae891b7863e386db542ef775b1e3eb306f812bb1a78bdbef86aaad, equation (C.8) is an exact two-sided norm bracket arising from the additive identity in (C.5). The universal Lean upper triangle inequality recovers the upper branch directly and the lower branch through a second instantiation with the negative correction. Its omission of GMRES construction data broadens rather than weakens the statement, so it remains a genuine, nonvacuous strengthening. The paper's later approximate equality requires additional correction and smallness assumptions and is not conflated with the exact bracket.

## Implications

- **Lean implies paper:** `yes`. Specialize the universal theorem first to the paper's stored product and correction product for the upper branch, then to their sum and the negative correction for the lower branch. Equation (C.5), invariance of the Euclidean norm under negation, and ordinary real rearrangement yield the complete exact bracket in (C.8). Missing GMRES provenance does not obstruct these specializations.
- **Paper implies lean:** `no`. The paper states (C.8) for products constructed within its right-preconditioned GMRES analysis. It does not state the triangle inequality universally for every pair of finite real vectors or for the additional zero-dimensional case admitted by Lean.

## Findings

- **note / derived-lower-branch:** Syntactic omission of the lower branch is not a semantic omission under the protocol's implication-based classification.
- **minor / strict-generalization:** This blocks the reverse implication and makes the accepted theorem strictly stronger, but does not make it unrelated or crossed-strength.
- **note / conditional-consequence-separated:** The universal triangle theorem should not be credited with the approximate equality, but that limitation does not affect its implication of the complete exact bracket.
- **note / nonvacuity:** Its broader scope is genuine mathematical strength rather than vacuity or reduced applicability.

## Semantic checklist

| Check | Direct | Round-trip |
|---|---|---|
| `S01` | `pass` | `pass` |
| `S02` | `fail` | `fail` |
| `S03` | `fail` | `fail` |
| `S04` | `pass` | `fail` |
| `S05` | `fail` | `fail` |
| `S06` | `pass` | `pass` |
| `S07` | `pass` | `fail` |
| `S08` | `fail` | `fail` |
| `S09` | `pass` | `pass` |
| `S10` | `pass` | `fail` |
| `S11` | `not-applicable` | `fail` |
| `S12` | `fail` | `fail` |
| `S13` | `pass` | `pass` |
| `S14` | `pass` | `fail` |
| `S15` | `fail` | `fail` |
| `S16` | `pass` | `pass` |

## Dependency coverage

- Blind translator covered `22` dependencies (`0` hash-reused meanings); unclear: `none`.
- Direct judge covered `22` dependencies (`0` hash-reused interpretations); failing or unclear: `none`.

## Remaining uncertainties

No remaining uncertainties were recorded.

## Audit artifacts

- `paper_bencmark/highambench/tasks/P19/T1/faithfulness/agent_outputs/adjudicator.json` (`22ec752aaab526f77a484704f6c7ee3d633c891dad7a49eefa1702a69604f9dd`)
- `paper_bencmark/highambench/tasks/P19/T1/faithfulness/agent_outputs/blind_translation.json` (`e201854b56440d26c7e06d4683feb5c5498e14315c2bf10b6de85dc1f831568f`)
- `paper_bencmark/highambench/tasks/P19/T1/faithfulness/agent_outputs/direct_judge.json` (`77ca8de2b0e8f2d0c55aff3d498a8f2787f5d0412f9bb13e1ec502b12ed45917`)
- `paper_bencmark/highambench/tasks/P19/T1/faithfulness/agent_outputs/paper_source_contract.json` (`282bdf4dba3e70c740465a2c4663b96debd1a66ef82c3debf273ad41cdbf76e0`)
- `paper_bencmark/highambench/tasks/P19/T1/faithfulness/agent_outputs/roundtrip_judge.json` (`1623bb17a3858bd957613f7a8b9da47a9775ee2193441dc9300a82bde4676b11`)
- `paper_bencmark/highambench/tasks/P19/T1/faithfulness/agent_outputs/source_contract.json` (`59e9b89b18330a53d4eea5c1f3794af5db428c7376c6157a0f8c4b7dffd37422`)
- `paper_bencmark/highambench/tasks/P19/T1/faithfulness/decision.json` (`302b0262b0807d07e322b5423eecd148c37c2a96c6f58db8949bb4ca11b63f83`)
- `paper_bencmark/highambench/tasks/P19/T1/faithfulness/inputs/blind_dependency_inventory.json` (`87cf4d990c310df24e375d2e1ceb5f4e0773da511249da7a0771ec46bae448b0`)
- `paper_bencmark/highambench/tasks/P19/T1/faithfulness/inputs/blind_dossier.md` (`30b164ec405d801195961df33a404a45674f99a5edfa9c56179c54b3bfa77cab`)
- `paper_bencmark/highambench/tasks/P19/T1/faithfulness/inputs/blind_review_packet.md` (`30b164ec405d801195961df33a404a45674f99a5edfa9c56179c54b3bfa77cab`)
- `paper_bencmark/highambench/tasks/P19/T1/faithfulness/inputs/declaration_dossier.md` (`6cbd53416e0c8a3c607fbb0d82cd710b75aeb34bddac2842350213797677bc34`)
- `paper_bencmark/highambench/tasks/P19/T1/faithfulness/inputs/dependency_inventory.json` (`cb9d2427ad22c238e483764e2b84f4b48f0cfd60cd7179f2b9f1c211f0a85673`)
- `paper_bencmark/highambench/tasks/P19/T1/faithfulness/inputs/direct_review_packet.md` (`fe278f8a18c23e46777c26d2779bac46b5acd3ae27f473bca13758d3f778d338`)
- `paper_bencmark/highambench/tasks/P19/T1/faithfulness/inputs/paper_source_locator.json` (`b2b71745c3ba0bc98613f67b2d754faf971558a1974b0f22e4456d4b88500ba1`)
- `paper_bencmark/highambench/tasks/P19/T1/faithfulness/inputs/source_locator.json` (`887c103d899c497b0df1db5db8ba41ce4e424f026757a7b63f2616d30c062acb`)
