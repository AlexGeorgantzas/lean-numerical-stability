# Faithfulness audit: P14-T3

- Classification: `faithful-equivalent`
- Accepted as paper-faithful: `true`
- Adjudicated: `false`
- Target SHA-256: `d56cba514113097d7cc74ac3e6d4ca04edf9e98792823bf8bc0248a53e9e9595`
- Paper SHA-256: `7247047bc49218e001195edc8a2d66131eea7596d252503f34b0ace6328981cd`

## Decision

The verified PDF directly supports an arbitrary common-shift identity and exact sum-to-one normalization for finite real softmax vectors. After unfolding the two local definitions, the Lean proposition expresses those claims exactly. Its absolute-value normalization is redundant by positivity, its j : Fin n binder correctly makes the unintended empty-vector case vacuous, and it does not conflate the exact invariant with the paper's fp16/bfloat16 experimental diagnostics.

## Implications

- **Lean implies paper:** `yes`. Unfolding p14Softmax and p14ExpSum makes the first Lean conjunct the symmetric form of equation (1.4), while the second conjunct is exactly sum_j g_j = 1. The exact-real, finite-dimensional binders match the paper's intended domain.
- **Paper implies lean:** `yes`. Equations (1.2) and (1.4) imply the Lean shift equality after unfolding definitions, and exact normalization gives the second conjunct. Since exponentials and their nonempty sum are positive, every softmax component is positive, so the paper's ordinary normalization also implies the target's absolute-value normalization.

## Findings

- **note / derived-redundant-conclusion:** This adds no logical strength on the intended nonempty domain because every exact softmax component is positive.
- **note / explicit-l1-corollary:** This is a supported and logically redundant restatement, not an unsupported strengthening.
- **note / zero-dimensional-vacuity:** No substantive zero-dimensional normalization claim is introduced, so the two results remain equivalent on the paper's intended domain.

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

- Blind translator covered `25` dependencies (`0` hash-reused meanings); unclear: `none`.
- Direct judge covered `25` dependencies (`22` hash-reused interpretations); failing or unclear: `none`.

## Remaining uncertainties

No remaining uncertainties were recorded.

## Audit artifacts

- `paper_bencmark/highambench/tasks/P14/T3/faithfulness/agent_outputs/blind_translation.json` (`ac5a7d6abd764f7998a730d0b656c2815715ace28de263812bce106e10dea2ae`)
- `paper_bencmark/highambench/tasks/P14/T3/faithfulness/agent_outputs/direct_judge.json` (`928850642e783b51ebf96d6b3093f50e10fee25a570325fe6c366c3b6d203528`)
- `paper_bencmark/highambench/tasks/P14/T3/faithfulness/agent_outputs/paper_source_contract.json` (`b9f05c969428f95fef40bddc0aa0b2a7c1d291ecdd7ba0ca0f5fb748131f1562`)
- `paper_bencmark/highambench/tasks/P14/T3/faithfulness/agent_outputs/roundtrip_judge.json` (`e2c668b1aec02479d8a6cad15c89936663be450903647f791d94d993c1b45eb3`)
- `paper_bencmark/highambench/tasks/P14/T3/faithfulness/agent_outputs/source_contract.json` (`c416bd8aa79f8e4f9d362c6202ae50ef497972bd1692eb7530734a22c31c06cd`)
- `paper_bencmark/highambench/tasks/P14/T3/faithfulness/decision.json` (`bde64caf7a1b20ee0548b1d4d1eeaad284d636e55b3649bfa3a1029cd9f67e62`)
- `paper_bencmark/highambench/tasks/P14/T3/faithfulness/inputs/blind_dependency_inventory.json` (`2151e224c2625ea58f338d46fc1cefce67fc2163c92eac6b2de934042c45fc72`)
- `paper_bencmark/highambench/tasks/P14/T3/faithfulness/inputs/blind_dossier.md` (`e87809090e017454b51990fdc55ac5eb3b80b62597dee9d55ff3c748714fbe37`)
- `paper_bencmark/highambench/tasks/P14/T3/faithfulness/inputs/blind_review_packet.md` (`e87809090e017454b51990fdc55ac5eb3b80b62597dee9d55ff3c748714fbe37`)
- `paper_bencmark/highambench/tasks/P14/T3/faithfulness/inputs/declaration_dossier.md` (`6f2e1e6515bf4b05bed305e778df3fee3b215570bde8813876a67ee0a48a8fac`)
- `paper_bencmark/highambench/tasks/P14/T3/faithfulness/inputs/dependency_inventory.json` (`d770b0517de148bbfd68357aebd1404dc24a64f6abf1ce718fa1f79bd3cd06f6`)
- `paper_bencmark/highambench/tasks/P14/T3/faithfulness/inputs/dependency_reuse_direct.json` (`835c3bd85decb6fdd67c75a7c7142e80d80fb0693f5017c8d6745ed671cee4d4`)
- `paper_bencmark/highambench/tasks/P14/T3/faithfulness/inputs/direct_review_packet.md` (`0f753ee37ba0bd464c972fb141678cc91cda78602405bd385a8531e73efcf50b`)
- `paper_bencmark/highambench/tasks/P14/T3/faithfulness/inputs/paper_source_locator.json` (`8627ed196c1c7742168563780358efbf3ebaee357ded297978c4d9199a86318c`)
- `paper_bencmark/highambench/tasks/P14/T3/faithfulness/inputs/source_locator.json` (`a10e279a35f6ce25a6c8ce624d8e3e692f83111d0071901a9822fad9bd9a2e19`)
