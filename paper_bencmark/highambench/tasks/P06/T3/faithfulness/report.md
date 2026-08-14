# Faithfulness audit: P06-T3

- Classification: `faithful-equivalent`
- Accepted as paper-faithful: `true`
- Adjudicated: `true`
- Target SHA-256: `81ba8dd1fe214237a86851edcdbc849edd15cb668e86d4f1fcdb15f1801a4cfa`
- Paper SHA-256: `c02a20e9ffa8039a5ad3db9261fba19929de84bf0bff7654547541dffe496a79`

## Decision

The verified PDF and declaration establish that P06-T3 selects the first-order product expansion (4.8)-(4.9), not the complete surrounding Lemma 4.2. The declaration preserves the exact Householder matrices, application order, perturbed product, both unfactored and Q^T-factored single-perturbation sums, endpoint identity products, and an explicit second-order remainder. The round-trip judge's critical omissions all concern later concentration and backward-error conclusions outside that scope. The remaining Big-O and cross-u choices are genuine source ambiguities, but the chosen finite-dimensional interpretation is compatible with the selected equations and does not alter either implication.

## Implications

- **Lean implies paper:** `yes`. After unfolding the product, exact-state, first-order, Q, F, and F-sum definitions, the declaration gives exactly both equalities in (4.8) and the insertion definition (4.9), with all higher-order terms retained by explicit O(u^2) matrix witnesses.
- **Paper implies lean:** `yes`. Within the supplied run encoding of (4.1), expand the finite perturbed product and choose the unfactored remainder as the sum of terms containing at least two DeltaP factors. Multiplying that remainder by the fixed transposed exact product gives the factored witness. Local DeltaP=O(u) makes both witnesses O(u^2) entrywise on the event.

## Findings

- **note / source-scope:** The source contract's broader discussion must not turn those later results into required conclusions of P06-T3.
- **note / remainder-formalization:** This is a compatible fixed-dimensional interpretation, although the paper leaves stronger uniformity questions unresolved.
- **note / algorithm-abstraction:** This abstraction is appropriate for a target whose source begins by rewriting (4.1); it would not suffice as a formalization of all of Lemma 4.1 or Lemma 4.2.
- **note / definitional-equation:** Equation (4.9) is likewise a definition in the paper, so the conjunct is redundant but faithful.

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
| `S11` | `pass` | `pass` |
| `S12` | `pass` | `fail` |
| `S13` | `pass` | `fail` |
| `S14` | `pass` | `fail` |
| `S15` | `pass` | `pass` |
| `S16` | `pass` | `fail` |

## Dependency coverage

- Blind translator covered `146` dependencies (`0` hash-reused meanings); unclear: `none`.
- Direct judge covered `146` dependencies (`0` hash-reused interpretations); failing or unclear: `none`.

## Remaining uncertainties

- The PDF does not specify whether its matrix O(u^2) constant is uniform over outcomes, dimensions, or matrix entries. Lean chooses a pointwise-in-omega, entrywise interpretation; a stronger uniform interpretation cannot be confirmed from the source.
- The PDF does not formally define a common probability-space coupling as u varies or behavior for negative u. Lean makes both choices explicit through one real-indexed family and the two-sided filter nhds 0.

## Audit artifacts

- `paper_bencmark/highambench/tasks/P06/T3/faithfulness/agent_outputs/adjudicator.json` (`7e3dcbb0ff40fc89df136aecd5fc33126850fab05085051a4340144030a7702b`)
- `paper_bencmark/highambench/tasks/P06/T3/faithfulness/agent_outputs/blind_translation.json` (`68c7901c6530fa3e89ade6177f6e9796bb290f78c87228f73ce4eabca5247cae`)
- `paper_bencmark/highambench/tasks/P06/T3/faithfulness/agent_outputs/direct_judge.json` (`416206913d9920a407041c9b008cee489d8a4d72389f398166a08a0e52425ea4`)
- `paper_bencmark/highambench/tasks/P06/T3/faithfulness/agent_outputs/roundtrip_judge.json` (`7764a6d575b514cd12a725e5768ea07feb9800cc4ec45526ad6405c8771149f8`)
- `paper_bencmark/highambench/tasks/P06/T3/faithfulness/agent_outputs/source_contract.json` (`79def281cdad2bda3c377c4091c0b2d7bb167b6ee6d47d9e07d9bc34b13c27fa`)
- `paper_bencmark/highambench/tasks/P06/T3/faithfulness/decision.json` (`e71b8432ca4c27b05fd56261a9b7457c75a93c2ddd2ef660c44a9486457e7aee`)
- `paper_bencmark/highambench/tasks/P06/T3/faithfulness/history/20260814T213023Z/agent_outputs/blind_translation.json` (`9d0330870bf7d93defdfdd3260e510244713a78555d4fab54e2975a3bfbf329a`)
- `paper_bencmark/highambench/tasks/P06/T3/faithfulness/history/20260814T213023Z/agent_outputs/direct_judge.json` (`8cf1d6366363c20d77769730e2759fe40871e31cd50fae031ecd98096ea7ead5`)
- `paper_bencmark/highambench/tasks/P06/T3/faithfulness/history/20260814T213023Z/agent_outputs/paper_source_contract.json` (`5fc79f8dcb892e5e54a0e6404abfb754e2c8f1233e5e586f0036f135448517d2`)
- `paper_bencmark/highambench/tasks/P06/T3/faithfulness/history/20260814T213023Z/agent_outputs/roundtrip_judge.json` (`f1a3eea14a4f96c8bf4fcc5751b086dfe1920346988e20ffa057175b103d4126`)
- `paper_bencmark/highambench/tasks/P06/T3/faithfulness/history/20260814T213023Z/agent_outputs/source_contract.json` (`c365540f97db9bf9f3efc08ac8808787ad4792ebfe853dee42e30d0fa1ed2c29`)
- `paper_bencmark/highambench/tasks/P06/T3/faithfulness/history/20260814T213023Z/decision.json` (`cc9632278a7b0539b84b7e1b5c78d078604af71bd1f336089c6d5155354acbbb`)
- `paper_bencmark/highambench/tasks/P06/T3/faithfulness/history/20260814T213023Z/inputs/blind_dependency_inventory.json` (`3eb97a72d811af61f72e5974ef757c8d84853f3a801253d6e41cfc6d60b07ba1`)
- `paper_bencmark/highambench/tasks/P06/T3/faithfulness/history/20260814T213023Z/inputs/blind_dossier.md` (`5f20af25aa5b4101cbdc8bd45cec040992c80e15c766bce0647850e3bee5af9e`)
- `paper_bencmark/highambench/tasks/P06/T3/faithfulness/history/20260814T213023Z/inputs/blind_review_packet.md` (`5f20af25aa5b4101cbdc8bd45cec040992c80e15c766bce0647850e3bee5af9e`)
- `paper_bencmark/highambench/tasks/P06/T3/faithfulness/history/20260814T213023Z/inputs/declaration_dossier.md` (`a8807c459bb3678b7f00f024f398e11978d2c52bc5bead45b81a65cc4a87e76f`)
- `paper_bencmark/highambench/tasks/P06/T3/faithfulness/history/20260814T213023Z/inputs/dependency_inventory.json` (`cb0bf78d08733c182ad35631ed196369dda0de401e4b52a894570ed44f832793`)
- `paper_bencmark/highambench/tasks/P06/T3/faithfulness/history/20260814T213023Z/inputs/dependency_reuse_direct.json` (`1639764b96c30eb73142ad6f1d63580f5a385f41144cedc5abf6deef03215ca6`)
- `paper_bencmark/highambench/tasks/P06/T3/faithfulness/history/20260814T213023Z/inputs/direct_review_packet.md` (`d43d4a31b402bcb0920a097c0f0539c27b78fcaf2da4f9027fe857f07049ef99`)
- `paper_bencmark/highambench/tasks/P06/T3/faithfulness/history/20260814T213023Z/inputs/paper_source_locator.json` (`d42b3fea8b0a859f7675a27adf15eef5a9d1a4d454377d2374aa02bdd01476fe`)
- `paper_bencmark/highambench/tasks/P06/T3/faithfulness/history/20260814T213023Z/inputs/source_locator.json` (`bb4c152dbcf5669dd64f5c4d1610e7fb7f6338453a2156301183150bd08d96e8`)
- `paper_bencmark/highambench/tasks/P06/T3/faithfulness/inputs/blind_dependency_inventory.json` (`a8259ededd906a211d2b94da4791c028aeb9870ed0215bbc751abd5c89bfab59`)
- `paper_bencmark/highambench/tasks/P06/T3/faithfulness/inputs/blind_dossier.md` (`a9d6a1c83fd2080dae580cb2a67f30a7dc9d77a98e1068e250a9f8c06ca9883a`)
- `paper_bencmark/highambench/tasks/P06/T3/faithfulness/inputs/blind_review_packet.md` (`a9d6a1c83fd2080dae580cb2a67f30a7dc9d77a98e1068e250a9f8c06ca9883a`)
- `paper_bencmark/highambench/tasks/P06/T3/faithfulness/inputs/declaration_dossier.md` (`fa61fc284e123bec8b724c2194b1e5f3adc53da75e1d7212d3399f81388b566f`)
- `paper_bencmark/highambench/tasks/P06/T3/faithfulness/inputs/dependency_inventory.json` (`1b6f6dfbc2d38eec0bc7c859ecb28c39f984f8b5f6e3642f726ccceeb25c57a8`)
- `paper_bencmark/highambench/tasks/P06/T3/faithfulness/inputs/direct_review_packet.md` (`8ecfec5c8a97a26cb16c44380aad6a0f206b20b7b35459178afb85ccd28cb441`)
- `paper_bencmark/highambench/tasks/P06/T3/faithfulness/inputs/source_locator.json` (`7848f739be6e6ec79594e9ffde458eb0493acb42a09304d21d3e657d69150e09`)
