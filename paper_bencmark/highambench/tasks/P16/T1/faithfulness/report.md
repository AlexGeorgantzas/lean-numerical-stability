# Faithfulness audit: P16-T1

- Classification: `not-faithful-different`
- Accepted as paper-faithful: `false`
- Adjudicated: `true`
- Target SHA-256: `d58289b7ce54ba1c17daaa783978d4464bc9542f0b92fe95938a77337a3cf5a5`
- Paper SHA-256: `8010a50989428b09ea9f204875cd6cfde6c08c924beb40887a6921287605737a`

## Decision

Primary evidence confirms that the selected paper result is the complete minimum-backward-error equality, not merely the perturbation-to-residual estimate. The Lean theorem is mathematically related and nonvacuous, but it has fixed universal perturbations, an absolute additive bound, and a broader domain. It proves only the necessary lower-bound ingredient for the paper result, while the paper equality does not assert Lean's full universal proposition. With both implication directions negative, not-faithful-different is the consistent classification.

## Implications

- **Lean implies paper:** `no`. After separately adding the paper's relative bounds, the Lean inequality shows that every admissible epsilon is at least the normalized residual, giving only the lower-bound direction for the minimum. It neither constructs perturbations attaining that value nor proves the reverse inequality, minimum equality, or shared-epsilon characterization.
- **Paper implies lean:** `no`. The paper's equality is restricted to nonsingular A and nonzero b and concerns an existential minimization over a shared relative epsilon; it does not state a universal additive inequality for every fixed DeltaA and Deltab, including singular systems, b = 0, and n = 0. Even on the common domain, inserting a fixed perturbation pair into the minimum characterization directly yields only a bound using the maximum of its two relative sizes, not ||DeltaA||_F||x||_2 + ||Deltab||_2. The latter follows from a separate rearrangement, triangle inequality, and Frobenius matrix-vector bound, not from the minimum equality as the asserted proposition.

## Findings

- **critical / minimum-equality-omitted:** Lean omits the paper claim's optimization, shared epsilon, normalization, attainability, and reverse-bound content.
- **major / no-full-paper-to-lean-implication:** The complete paper proposition does not imply the complete universally quantified Lean proposition.
- **major / supporting-lemma-substituted:** Lean formalizes a proof ingredient for one direction of the paper equality rather than the selected equality itself.

## Semantic checklist

| Check | Direct | Round-trip |
|---|---|---|
| `S01` | `pass` | `pass` |
| `S02` | `fail` | `fail` |
| `S03` | `fail` | `fail` |
| `S04` | `fail` | `fail` |
| `S05` | `fail` | `fail` |
| `S06` | `pass` | `pass` |
| `S07` | `pass` | `fail` |
| `S08` | `pass` | `pass` |
| `S09` | `pass` | `fail` |
| `S10` | `fail` | `fail` |
| `S11` | `pass` | `fail` |
| `S12` | `fail` | `fail` |
| `S13` | `fail` | `fail` |
| `S14` | `pass` | `pass` |
| `S15` | `fail` | `fail` |
| `S16` | `pass` | `pass` |

## Dependency coverage

- Blind translator covered `41` dependencies (`0` hash-reused meanings); unclear: `none`.
- Direct judge covered `41` dependencies (`0` hash-reused interpretations); failing or unclear: `none`.

## Remaining uncertainties

No remaining uncertainties were recorded.

## Audit artifacts

- `paper_bencmark/highambench/tasks/P16/T1/faithfulness/agent_outputs/adjudicator.json` (`0a6b05570d40ef42d749f0b9143eee141ba748ec9fb48e8952f7e0e074e92c48`)
- `paper_bencmark/highambench/tasks/P16/T1/faithfulness/agent_outputs/blind_translation.json` (`96ea53e05f9a580d19c3c2ed55ef2cc09d86eeae704f2a1fb66ed7e0041ac709`)
- `paper_bencmark/highambench/tasks/P16/T1/faithfulness/agent_outputs/direct_judge.json` (`de8e4a00e9b8bb029f90b50817580a5a248c3fbc7ad0e0f566357af6b0482dc1`)
- `paper_bencmark/highambench/tasks/P16/T1/faithfulness/agent_outputs/paper_source_contract.json` (`cc856c94ce22bcb89d018b431db65cfb6c20d25df7bb6aaeb660c48c42f5c886`)
- `paper_bencmark/highambench/tasks/P16/T1/faithfulness/agent_outputs/roundtrip_judge.json` (`02ad0f9b9e6b82afc6fc1aa9e8d715828340d42886ee0dc1cc8b8a62ea2943df`)
- `paper_bencmark/highambench/tasks/P16/T1/faithfulness/agent_outputs/source_contract.json` (`157e1e96eb7be4dd7bfe9826a7235e2b7f1ac88e3daeebf4e675c318235e34e8`)
- `paper_bencmark/highambench/tasks/P16/T1/faithfulness/decision.json` (`8f9f35b1a431262ae73f0563d73fec0893e965f4cd171ddde1263815c11d298c`)
- `paper_bencmark/highambench/tasks/P16/T1/faithfulness/inputs/blind_dependency_inventory.json` (`47ca5a37bbef48d85685a5b01ebb64364c2cee04301bdc81f9cf418043f945cd`)
- `paper_bencmark/highambench/tasks/P16/T1/faithfulness/inputs/blind_dossier.md` (`69429830512376754ec300085bf21f7c9f0283cff25ad599d4f6a033fea952e0`)
- `paper_bencmark/highambench/tasks/P16/T1/faithfulness/inputs/blind_review_packet.md` (`69429830512376754ec300085bf21f7c9f0283cff25ad599d4f6a033fea952e0`)
- `paper_bencmark/highambench/tasks/P16/T1/faithfulness/inputs/declaration_dossier.md` (`c06940eff9dc792eb7b953b96f1f1b72be793e6b2a30aae48c0919092397421f`)
- `paper_bencmark/highambench/tasks/P16/T1/faithfulness/inputs/dependency_inventory.json` (`24d2b5c167b9c9cfff40b7cd95c812376260f537599b82c00436f4e2658c6d2b`)
- `paper_bencmark/highambench/tasks/P16/T1/faithfulness/inputs/direct_review_packet.md` (`7f23f2d0b4f1229ed096548f1d0ec13f16c0969460b94375ef415ea0e1e7e1fc`)
- `paper_bencmark/highambench/tasks/P16/T1/faithfulness/inputs/paper_source_locator.json` (`29399d42dec8e4d771178436cda1303a77490d8820b032eb370ddffe5e202bd7`)
- `paper_bencmark/highambench/tasks/P16/T1/faithfulness/inputs/source_locator.json` (`2d202ef66f0135f1f6cbab371b8939b8cd1d0cbee46d1ec16162adba87434ab2`)
