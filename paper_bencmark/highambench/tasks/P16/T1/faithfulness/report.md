# Faithfulness audit: P16-T1

- Classification: `faithful-equivalent`
- Accepted as paper-faithful: `true`
- Adjudicated: `false`
- Target SHA-256: `6cf6a658a6363e5a80fa10a2354101880c5b3f801b04cdcbcf09d61dc81e5dcb`
- Paper SHA-256: `8010a50989428b09ea9f204875cd6cfde6c08c924beb40887a6921287605737a`

## Decision

The Lean proposition is an exact formal rendering of the selected Section 2 normwise backward-error characterization. Its matrix and vector spaces, nonsingularity and nonzero hypotheses, simultaneous existential perturbations, Frobenius and vector 2-norms, common epsilon, residual orientation, denominator, and minimum semantics all agree with the hash-verified PDF. The generic treatment of xHat matches the paper's algorithm-independent definition, and the statement is nonvacuous.

## Implications

- **Lean implies paper:** `yes`. Under the paper's nonsingular real square system and nonzero right-hand side, all Lean definitions unfold to the displayed perturbation set and normalized residual. IsLeast therefore yields exactly the paper's minimum identity for x_hat.
- **Paper implies lean:** `yes`. The paper's exact minimum identity entails that the normalized residual is admissible and no larger than every admissible epsilon, which is precisely IsLeast. Valid Lean instances have the paper's finite real dimensions; the syntactic n=0 case has an impossible b != 0 premise.

## Findings

No findings were recorded.

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
| `S08` | `pass` | `pass` |
| `S09` | `pass` | `pass` |
| `S10` | `pass` | `pass` |
| `S11` | `pass` | `pass` |
| `S12` | `pass` | `pass` |
| `S13` | `pass` | `pass` |
| `S14` | `pass` | `pass` |
| `S15` | `pass` | `pass` |
| `S16` | `pass` | `pass` |

## Dependency coverage

- Blind translator covered `57` dependencies (`0` hash-reused meanings); unclear: `none`.
- Direct judge covered `57` dependencies (`0` hash-reused interpretations); failing or unclear: `none`.

## Remaining uncertainties

No remaining uncertainties were recorded.

## Audit artifacts

- `paper_bencmark/highambench/tasks/P16/T1/faithfulness/agent_outputs/blind_translation.json` (`62b5da535114e568f37fc4ad213cbef2c6147e2ec5cb38432dec0856b73b0de3`)
- `paper_bencmark/highambench/tasks/P16/T1/faithfulness/agent_outputs/direct_judge.json` (`36150b0c1c5f6b46ea04cc6545a21d1d592905a078244b9a9da2f84db0c19db7`)
- `paper_bencmark/highambench/tasks/P16/T1/faithfulness/agent_outputs/roundtrip_judge.json` (`4ebb47be4ddacbef733089ed2c876d7ea37f7615a510c3548da1fdbedafcdfe3`)
- `paper_bencmark/highambench/tasks/P16/T1/faithfulness/agent_outputs/source_contract.json` (`f4cbb352e652880a2cf838e55e2a0c0d4f5f5e576cc70ddf0fb27a03577a2b53`)
- `paper_bencmark/highambench/tasks/P16/T1/faithfulness/decision.json` (`ec23e24dc0dbc1e3ee323e5c3517433caa7618c6b4652358a16ac2e3f820cd15`)
- `paper_bencmark/highambench/tasks/P16/T1/faithfulness/history/20260820T125027Z/agent_outputs/adjudicator.json` (`0a6b05570d40ef42d749f0b9143eee141ba748ec9fb48e8952f7e0e074e92c48`)
- `paper_bencmark/highambench/tasks/P16/T1/faithfulness/history/20260820T125027Z/agent_outputs/blind_translation.json` (`96ea53e05f9a580d19c3c2ed55ef2cc09d86eeae704f2a1fb66ed7e0041ac709`)
- `paper_bencmark/highambench/tasks/P16/T1/faithfulness/history/20260820T125027Z/agent_outputs/direct_judge.json` (`de8e4a00e9b8bb029f90b50817580a5a248c3fbc7ad0e0f566357af6b0482dc1`)
- `paper_bencmark/highambench/tasks/P16/T1/faithfulness/history/20260820T125027Z/agent_outputs/paper_source_contract.json` (`cc856c94ce22bcb89d018b431db65cfb6c20d25df7bb6aaeb660c48c42f5c886`)
- `paper_bencmark/highambench/tasks/P16/T1/faithfulness/history/20260820T125027Z/agent_outputs/roundtrip_judge.json` (`02ad0f9b9e6b82afc6fc1aa9e8d715828340d42886ee0dc1cc8b8a62ea2943df`)
- `paper_bencmark/highambench/tasks/P16/T1/faithfulness/history/20260820T125027Z/agent_outputs/source_contract.json` (`157e1e96eb7be4dd7bfe9826a7235e2b7f1ac88e3daeebf4e675c318235e34e8`)
- `paper_bencmark/highambench/tasks/P16/T1/faithfulness/history/20260820T125027Z/decision.json` (`8f9f35b1a431262ae73f0563d73fec0893e965f4cd171ddde1263815c11d298c`)
- `paper_bencmark/highambench/tasks/P16/T1/faithfulness/history/20260820T125027Z/inputs/blind_dependency_inventory.json` (`47ca5a37bbef48d85685a5b01ebb64364c2cee04301bdc81f9cf418043f945cd`)
- `paper_bencmark/highambench/tasks/P16/T1/faithfulness/history/20260820T125027Z/inputs/blind_dossier.md` (`69429830512376754ec300085bf21f7c9f0283cff25ad599d4f6a033fea952e0`)
- `paper_bencmark/highambench/tasks/P16/T1/faithfulness/history/20260820T125027Z/inputs/blind_review_packet.md` (`69429830512376754ec300085bf21f7c9f0283cff25ad599d4f6a033fea952e0`)
- `paper_bencmark/highambench/tasks/P16/T1/faithfulness/history/20260820T125027Z/inputs/declaration_dossier.md` (`c06940eff9dc792eb7b953b96f1f1b72be793e6b2a30aae48c0919092397421f`)
- `paper_bencmark/highambench/tasks/P16/T1/faithfulness/history/20260820T125027Z/inputs/dependency_inventory.json` (`24d2b5c167b9c9cfff40b7cd95c812376260f537599b82c00436f4e2658c6d2b`)
- `paper_bencmark/highambench/tasks/P16/T1/faithfulness/history/20260820T125027Z/inputs/direct_review_packet.md` (`7f23f2d0b4f1229ed096548f1d0ec13f16c0969460b94375ef415ea0e1e7e1fc`)
- `paper_bencmark/highambench/tasks/P16/T1/faithfulness/history/20260820T125027Z/inputs/paper_source_locator.json` (`29399d42dec8e4d771178436cda1303a77490d8820b032eb370ddffe5e202bd7`)
- `paper_bencmark/highambench/tasks/P16/T1/faithfulness/history/20260820T125027Z/inputs/source_locator.json` (`2d202ef66f0135f1f6cbab371b8939b8cd1d0cbee46d1ec16162adba87434ab2`)
- `paper_bencmark/highambench/tasks/P16/T1/faithfulness/inputs/blind_dependency_inventory.json` (`28d3ca275a6a067da8d52a4461344f146d21f2fa24baa2ff1bbb4cddc7835ede`)
- `paper_bencmark/highambench/tasks/P16/T1/faithfulness/inputs/blind_dossier.md` (`f6550ed07ca08362ce3926067186e388f56d209956e3796b5e23bf04982446f1`)
- `paper_bencmark/highambench/tasks/P16/T1/faithfulness/inputs/blind_review_packet.md` (`f6550ed07ca08362ce3926067186e388f56d209956e3796b5e23bf04982446f1`)
- `paper_bencmark/highambench/tasks/P16/T1/faithfulness/inputs/declaration_dossier.md` (`bdd2ad3701021c7c658f74fde877af76b3dea5c46d29a3e2fb10e1d46b23bc55`)
- `paper_bencmark/highambench/tasks/P16/T1/faithfulness/inputs/dependency_inventory.json` (`4510ec4a1a223d84f00825ed086bb0f2f3bf21bb0739820e2d88c1ee7ad93939`)
- `paper_bencmark/highambench/tasks/P16/T1/faithfulness/inputs/direct_review_packet.md` (`565432347091f0b0ab0fb677f29831fed4a893169a4a78b02098dd6a61f7f1e0`)
- `paper_bencmark/highambench/tasks/P16/T1/faithfulness/inputs/source_locator.json` (`675d8256e875275d129fc67e0b08d700fedbec59b8fe24b924d01d0a7995ffbd`)
