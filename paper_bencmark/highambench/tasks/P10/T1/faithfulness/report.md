# Faithfulness audit: P10-T1

- Classification: `not-faithful-different`
- Accepted as paper-faithful: `false`
- Adjudicated: `true`
- Target SHA-256: `eb19fb0413ba12647774872f38496b584d03d5fa21d063d3b38a508c9f8dcdf0`
- Paper SHA-256: `0ee818d060542baefdd85cbb7c7f2fd948efcb927101da84c37e418713f87269`

## Decision

Primary evidence distinguishes the paper's claim from the declaration's algebraic lemma. Equation (8) is introduced for a computed product with errors inherited from prior computations and identifies ||A||·err(B,n) by its role in the output-error accounting. The declaration proves only exact Frobenius submultiplicativity. Although that theorem can derive the paper term after conventional perturbation definitions are added, those definitions and their connection to err(C,n) are absent from the proposition. Conversely, the contextual, unnamed-norm paper rule does not state the universal Frobenius theorem. Both implication directions are therefore no, requiring classification as not-faithful-different and accepted=false.

## Implications

- **Lean implies paper:** `no`. The Lean theorem yields the selected paper term only after adding dB=Bcomp-B, an assumption or definition relating ||dB||_F to err(B,n), an identification of A dB with the inherited-right component of the output error, and its embedding in first-order additive error accounting. None of these follows from the target.
- **Paper implies lean:** `no`. Equation (8) states a contextual first-order propagation rule for inherited computational errors in an unnamed norm. It does not universally assert coefficient-one Frobenius submultiplicativity for every pair of square real matrices. Deriving the Lean target requires selecting the Frobenius norm and treating every arbitrary dB as an inherited perturbation with err(B,n)=||dB||_F.

## Findings

- **critical / missing inherited-error identification:** The declaration cannot by itself assert the selected inherited-error contribution.
- **major / different conclusion:** The Lean result is an algebraic supporting lemma, and neither proposition implies the other without unstated bridges.
- **minor / unnamed norm specialized:** The specialization is narrower rather than stronger and independently obstructs an unconditional paper-to-Lean implication.
- **note / partial algebraic correspondence:** These matches show why the theorem is useful in a faithful development, but they do not supply the missing computational-error semantics.

## Semantic checklist

| Check | Direct | Round-trip |
|---|---|---|
| `S01` | `pass` | `pass` |
| `S02` | `pass` | `fail` |
| `S03` | `pass` | `fail` |
| `S04` | `pass` | `fail` |
| `S05` | `pass` | `fail` |
| `S06` | `pass` | `pass` |
| `S07` | `pass` | `fail` |
| `S08` | `pass` | `fail` |
| `S09` | `pass` | `fail` |
| `S10` | `pass` | `fail` |
| `S11` | `pass` | `fail` |
| `S12` | `pass` | `fail` |
| `S13` | `pass` | `fail` |
| `S14` | `pass` | `fail` |
| `S15` | `pass` | `fail` |
| `S16` | `pass` | `pass` |

## Dependency coverage

- Blind translator covered `24` dependencies (`0` hash-reused meanings); unclear: `none`.
- Direct judge covered `24` dependencies (`0` hash-reused interpretations); failing or unclear: `none`.

## Remaining uncertainties

- Equation (8) does not identify its matrix norm, so the source alone does not determine whether Frobenius norm with exact coefficient one is the intended specialization.
- Equation (8) prints an equality although equation (1) and the surrounding discussion use an error-bound model; it remains unclear whether err denotes realized error or a chosen first-order bound.
- The paper does not typographically distinguish exact operands from their computed approximations in equation (8), so more than one explicit perturbation encoding is possible.

## Audit artifacts

- `paper_bencmark/highambench/tasks/P10/T1/faithfulness/agent_outputs/adjudicator.json` (`dcbf8141b6ee91f2870aa2f9bc7cec3dd20a1d8f1a2c9d7026abbcc86c227064`)
- `paper_bencmark/highambench/tasks/P10/T1/faithfulness/agent_outputs/blind_translation.json` (`13980af30160a3aa94e82252e6b82d855790e04ce8c4506daefdaa10b77c564d`)
- `paper_bencmark/highambench/tasks/P10/T1/faithfulness/agent_outputs/direct_judge.json` (`a55dae02340c6957132742a8aec72987d43e9ec606ce0740c2c2bbbf25cb49d0`)
- `paper_bencmark/highambench/tasks/P10/T1/faithfulness/agent_outputs/paper_source_contract.json` (`a730fdcbbc543ec8712373b135d8a67dd310f31f635dedabf0ed548f9316414a`)
- `paper_bencmark/highambench/tasks/P10/T1/faithfulness/agent_outputs/roundtrip_judge.json` (`29a5613f27a9c472f559fe8e78b2a2f508f9da93acaecfb8445c67f7e1e2a663`)
- `paper_bencmark/highambench/tasks/P10/T1/faithfulness/agent_outputs/source_contract.json` (`6377f2213fdc9ed7448bff43d7d5f7b0a5d9342d786adfbedcab4c9c9d3508e2`)
- `paper_bencmark/highambench/tasks/P10/T1/faithfulness/decision.json` (`24f16217e9902ce68deeca697892bd2c586c87199b5919abeba6837eb67adc7f`)
- `paper_bencmark/highambench/tasks/P10/T1/faithfulness/inputs/blind_dependency_inventory.json` (`ea6f316e924735d4747662729846282e651964bc9b9311bc392658fac8b08ad8`)
- `paper_bencmark/highambench/tasks/P10/T1/faithfulness/inputs/blind_dossier.md` (`24476ab5b9b011e4e040fd98de4744aeffdd79fd419e7723ac5f4056362e1c41`)
- `paper_bencmark/highambench/tasks/P10/T1/faithfulness/inputs/blind_review_packet.md` (`24476ab5b9b011e4e040fd98de4744aeffdd79fd419e7723ac5f4056362e1c41`)
- `paper_bencmark/highambench/tasks/P10/T1/faithfulness/inputs/declaration_dossier.md` (`6086ba071c4de3b7d0d07d015fe11f56534252356248b2f3f966657ca026a9d8`)
- `paper_bencmark/highambench/tasks/P10/T1/faithfulness/inputs/dependency_inventory.json` (`2b6c104df908a0a847ee8ea4cfb22f6ef050604370bfaa7f6c87202b68d2a2f2`)
- `paper_bencmark/highambench/tasks/P10/T1/faithfulness/inputs/direct_review_packet.md` (`a2dfb6ebbb9e7986c015e15100dba2365d705a6ba8d46d292553222278d2ae75`)
- `paper_bencmark/highambench/tasks/P10/T1/faithfulness/inputs/paper_source_locator.json` (`91f77a26c65c7ca024e216f6cc35327e6521963eee50d0bda4fd50b72060a4dc`)
- `paper_bencmark/highambench/tasks/P10/T1/faithfulness/inputs/source_locator.json` (`e188951561a2dc17da7c49f73062a5c18c0b4c95b39a01204a693aef5628a233`)
