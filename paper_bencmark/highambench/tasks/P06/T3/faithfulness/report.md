# Faithfulness audit: P06-T3

- Classification: `not-faithful-different`
- Accepted as paper-faithful: `false`
- Adjudicated: `false`
- Target SHA-256: `7ab9b1c444e5abf221bf343eb310b90ddc12d47745085cc62f3448bc11603ca2`
- Paper SHA-256: `c02a20e9ffa8039a5ad3db9261fba19929de84bf0bff7654547541dffe496a79`

## Decision

The Lean declaration correctly encodes an exact algebraic expansion of a parametrized finite matrix product: its first-order recurrence reproduces the paper's single-insertion order after reindexing. It nevertheless changes the sourced result in three consequential ways. It is not linked to computed normalized Householder transformations or Model 1.5, it replaces the unspecified matrix-valued O(u^2) remainder by an unbounded explicit vector state, and it omits the Q^T/F_j form in (4.8)-(4.9). Because neither complete statement implies the other, the appropriate classification is not-faithful-different.

## Implications

- **Lean implies paper:** `no`. Even after informally identifying t E_k with Delta P_(k+1), the Lean proposition supplies neither the paper's matrix-valued O(u^2) assertion and local-error scale nor the Q^T/F_j form or computed-Householder linkage. The complete paper contract is therefore not a consequence of the Lean proposition.
- **Paper implies lean:** `no`. The paper states a contextual first-order expansion for computed perturbations of normalized Householder products. It does not assert the target's exact all-t identity for arbitrary real matrix sequences P and E, including the particular recursively defined HigherOrderState.

## Findings

- **major / missing-computational-context:** The theorem is a generic algebraic product identity rather than a statement about the computed Householder process analyzed by the paper.
- **major / higher-order-remainder:** The target neither preserves the source's stated remainder semantics nor directly establishes the paper's first-order approximation.
- **major / missing-factorized-conclusion:** The concentration-ready form and its source-critical factor ordering are absent from the formal statement.
- **critical / higher-order-terms:** The paper's asymptotic first-order numerical claim cannot be recovered, and the remainder's type, dependence, and meaning all change.
- **major / missing-hypotheses:** The statement is detached from the algorithm, rounding model, and assumptions that make the source a numerical-analysis result.
- **major / conclusion-omission:** A central conclusion used to prepare the concentration argument is missing.
- **major / relation-and-error-notion:** The numerical forward-error interpretation is replaced by a different algebraic theorem.
- **minor / domain-and-vacuity:** The translated domain contains unintended degenerate cases.
- **note / partial-structural-correspondence:** The translation preserves one algebraic component of (4.8), but this does not compensate for the missing factored form, hypotheses, and higher-order semantics.

## Semantic checklist

| Check | Direct | Round-trip |
|---|---|---|
| `S01` | `pass` | `fail` |
| `S02` | `fail` | `fail` |
| `S03` | `fail` | `fail` |
| `S04` | `fail` | `fail` |
| `S05` | `fail` | `fail` |
| `S06` | `pass` | `pass` |
| `S07` | `pass` | `pass` |
| `S08` | `fail` | `fail` |
| `S09` | `not-applicable` | `fail` |
| `S10` | `pass` | `fail` |
| `S11` | `fail` | `fail` |
| `S12` | `fail` | `fail` |
| `S13` | `fail` | `fail` |
| `S14` | `fail` | `fail` |
| `S15` | `fail` | `fail` |
| `S16` | `pass` | `fail` |

## Dependency coverage

- Blind translator covered `34` dependencies (`0` hash-reused meanings); unclear: `none`.
- Direct judge covered `34` dependencies (`18` hash-reused interpretations); failing or unclear: `D003, D004`.

## Remaining uncertainties

No remaining uncertainties were recorded.

## Audit artifacts

- `paper_bencmark/highambench/tasks/P06/T3/faithfulness/agent_outputs/blind_translation.json` (`9d0330870bf7d93defdfdd3260e510244713a78555d4fab54e2975a3bfbf329a`)
- `paper_bencmark/highambench/tasks/P06/T3/faithfulness/agent_outputs/direct_judge.json` (`8cf1d6366363c20d77769730e2759fe40871e31cd50fae031ecd98096ea7ead5`)
- `paper_bencmark/highambench/tasks/P06/T3/faithfulness/agent_outputs/paper_source_contract.json` (`5fc79f8dcb892e5e54a0e6404abfb754e2c8f1233e5e586f0036f135448517d2`)
- `paper_bencmark/highambench/tasks/P06/T3/faithfulness/agent_outputs/roundtrip_judge.json` (`f1a3eea14a4f96c8bf4fcc5751b086dfe1920346988e20ffa057175b103d4126`)
- `paper_bencmark/highambench/tasks/P06/T3/faithfulness/agent_outputs/source_contract.json` (`c365540f97db9bf9f3efc08ac8808787ad4792ebfe853dee42e30d0fa1ed2c29`)
- `paper_bencmark/highambench/tasks/P06/T3/faithfulness/decision.json` (`cc9632278a7b0539b84b7e1b5c78d078604af71bd1f336089c6d5155354acbbb`)
- `paper_bencmark/highambench/tasks/P06/T3/faithfulness/inputs/blind_dependency_inventory.json` (`3eb97a72d811af61f72e5974ef757c8d84853f3a801253d6e41cfc6d60b07ba1`)
- `paper_bencmark/highambench/tasks/P06/T3/faithfulness/inputs/blind_dossier.md` (`5f20af25aa5b4101cbdc8bd45cec040992c80e15c766bce0647850e3bee5af9e`)
- `paper_bencmark/highambench/tasks/P06/T3/faithfulness/inputs/blind_review_packet.md` (`5f20af25aa5b4101cbdc8bd45cec040992c80e15c766bce0647850e3bee5af9e`)
- `paper_bencmark/highambench/tasks/P06/T3/faithfulness/inputs/declaration_dossier.md` (`a8807c459bb3678b7f00f024f398e11978d2c52bc5bead45b81a65cc4a87e76f`)
- `paper_bencmark/highambench/tasks/P06/T3/faithfulness/inputs/dependency_inventory.json` (`cb0bf78d08733c182ad35631ed196369dda0de401e4b52a894570ed44f832793`)
- `paper_bencmark/highambench/tasks/P06/T3/faithfulness/inputs/dependency_reuse_direct.json` (`1639764b96c30eb73142ad6f1d63580f5a385f41144cedc5abf6deef03215ca6`)
- `paper_bencmark/highambench/tasks/P06/T3/faithfulness/inputs/direct_review_packet.md` (`d43d4a31b402bcb0920a097c0f0539c27b78fcaf2da4f9027fe857f07049ef99`)
- `paper_bencmark/highambench/tasks/P06/T3/faithfulness/inputs/paper_source_locator.json` (`d42b3fea8b0a859f7675a27adf15eef5a9d1a4d454377d2374aa02bdd01476fe`)
- `paper_bencmark/highambench/tasks/P06/T3/faithfulness/inputs/source_locator.json` (`bb4c152dbcf5669dd64f5c4d1610e7fb7f6338453a2156301183150bd08d96e8`)
