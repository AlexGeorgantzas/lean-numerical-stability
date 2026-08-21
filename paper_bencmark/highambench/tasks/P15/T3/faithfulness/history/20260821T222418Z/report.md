# Faithfulness audit: P15-T3

- Classification: `not-faithful-different`
- Accepted as paper-faithful: `false`
- Adjudicated: `true`
- Target SHA-256: `f45086a8968e238c276f6f26cd6fb71f3d615a1b04d1e71079cad6b5a1349acc`
- Paper SHA-256: `a5cb8eb779c1571f1549ea6838c7f2269302c960fb4ea21f8410060811270cd7`

## Decision

Primary PDF evidence and the complete declaration bodies establish a mixed result: dimensions, norms, c, gamma_(3c), all four xi_p values, the simultaneous backward equation, and both exact perturbation compositions are preserved. The nominal constructor mappings are also unambiguous once the direct dossier is considered. However, those constructors do not constrain an execution; all computed objects and component perturbation guarantees are assumed inside the run record. The target additionally collapses the unresolved A_tilde/A distinction, changes r from the actual factor rank to a shared upper bound, and translates the two big-O terms in incompatible ways. The explicit right-hand-side bound is a genuine nonvacuous strengthening only on this altered record domain, while the matrix K term loses uniform asymptotic content. These independent mismatches establish no implication in either direction, so the final classification is not-faithful-different.

## Implications

- **Lean implies paper:** `no`. The Lean theorem applies only after an abstract record containing all component perturbation contracts has been supplied. It neither represents nor constructs such a record from every successful UFC/UCF computation. Its single A cannot simultaneously preserve the source's A_tilde and A roles, its common rank bound may exclude paper executions, and its run-local K does not express O(u*epsilon). Consequently it does not imply the paper's algorithm-linked asymptotic theorem.
- **Paper implies lean:** `no`. The paper theorem concerns actual computed executions and existential aggregate perturbations. It does not assert the target for every synthetic record satisfying assumed postconditions, does not require the input matrix and both factors to share one rank-at-most-r parameter, and does not state the target's F, H, and 16*c^2*u^2 conjuncts. Therefore it does not imply the complete Lean proposition under the supplied binder correspondence.

## Findings

- **critical / execution-linkage-and-quantification:** The target is an algebraic composition theorem over prepopulated certificates, not the paper's computation-to-backward-error guarantee.
- **major / original-versus-BLR-matrix:** No single source-to-Lean binder mapping preserves the solved matrix, perturbed matrix, BLR structure, and norm scale without silently resolving the paper's notation gap.
- **major / rank-semantics:** The target changes applicability and may weaken constants through an overestimated r, preventing either implication under the stated correspondence.
- **major / higher-order-terms:** The matrix asymptotic guarantee is weakened while the right-hand-side conclusion is strengthened on a different domain, making the overall relation neither uniformly stronger nor uniformly weaker.
- **note / resolved-constructor-mapping-and-preserved-core:** The blind constructor ambiguity is resolved and the central algebra is recognizable, but labels and correct coefficients do not supply the missing operational linkage.

## Semantic checklist

| Check | Direct | Round-trip |
|---|---|---|
| `S01` | `pass` | `pass` |
| `S02` | `fail` | `fail` |
| `S03` | `fail` | `fail` |
| `S04` | `fail` | `fail` |
| `S05` | `fail` | `fail` |
| `S06` | `pass` | `fail` |
| `S07` | `fail` | `fail` |
| `S08` | `fail` | `fail` |
| `S09` | `pass` | `pass` |
| `S10` | `fail` | `fail` |
| `S11` | `fail` | `fail` |
| `S12` | `fail` | `fail` |
| `S13` | `pass` | `pass` |
| `S14` | `fail` | `fail` |
| `S15` | `fail` | `fail` |
| `S16` | `pass` | `pass` |

## Dependency coverage

- Blind translator covered `119` dependencies (`0` hash-reused meanings); unclear: `none`.
- Direct judge covered `119` dependencies (`0` hash-reused interpretations); failing or unclear: `D001, D002, D003, D004, D007, D010, D011, D016, D027, D028, D029, D035, D037, D038, D040, D041, D043, D047, D048`.

## Remaining uncertainties

- The PDF does not locally resolve whether A_tilde in Theorem 4.5's opening is intentional inherited notation or a typographical inconsistency. Section 2.1 strongly supports a distinct BLR-representation relationship, but no local equality connecting A_tilde and A is stated.
- The PDF supplies no explicit uniform constants or quantified asymptotic range for O(u*epsilon) or O(u^2), so the authors' intended hidden constants cannot be identified with the Lean coefficients from primary source evidence.

## Audit artifacts

- `paper_bencmark/highambench/tasks/P15/T3/faithfulness/agent_outputs/adjudicator.json` (`83573753cb17a6343c62420f253a9dd8ac32c952823dc96aca34020c9be2b696`)
- `paper_bencmark/highambench/tasks/P15/T3/faithfulness/agent_outputs/blind_translation.json` (`e8cd65cffc379f33f37796d4fe48342972e1712ef6105129c612d2c52bb82e30`)
- `paper_bencmark/highambench/tasks/P15/T3/faithfulness/agent_outputs/direct_judge.json` (`9c4b38e1bc1897bf4efa40787af8dafb092b359b77226bff69ecd0e9856b91e8`)
- `paper_bencmark/highambench/tasks/P15/T3/faithfulness/agent_outputs/roundtrip_judge.json` (`51295d43d9e5cfc2f2abdf22c81dce8eaf6646592062d8ce7b39463a5c0eb6d7`)
- `paper_bencmark/highambench/tasks/P15/T3/faithfulness/agent_outputs/source_contract.json` (`bf306c9ca6548f0195c3feec452bddea9b13de1de97e41bd15bc92bd48c011be`)
- `paper_bencmark/highambench/tasks/P15/T3/faithfulness/decision.json` (`5a1fbca2bae1203639c7bf901901a80ed80ff9c00675dcf1884b7e0b31d9fc12`)
- `paper_bencmark/highambench/tasks/P15/T3/faithfulness/history/20260820T105914Z/agent_outputs/adjudicator.json` (`4311935f42a62715f3dd0c151b813d51499f63175f836c7cf819ee4d7c90c821`)
- `paper_bencmark/highambench/tasks/P15/T3/faithfulness/history/20260820T105914Z/agent_outputs/blind_translation.json` (`e863d0a2062602a574fe83b7982e8cb51afd1623973ea809ba9781a983be50df`)
- `paper_bencmark/highambench/tasks/P15/T3/faithfulness/history/20260820T105914Z/agent_outputs/direct_judge.json` (`6262e2541e9dce9111b21c18f3a8e2e5418fb00d7d291ebbce25212ae41584e2`)
- `paper_bencmark/highambench/tasks/P15/T3/faithfulness/history/20260820T105914Z/agent_outputs/paper_source_contract.json` (`339fc5a797919c9e9bcd9c7d27d579722d8bfedc8091d16c4ab89148a1eb498f`)
- `paper_bencmark/highambench/tasks/P15/T3/faithfulness/history/20260820T105914Z/agent_outputs/roundtrip_judge.json` (`41433addc668f60a98ced486313d98c95c0bc14478cd1bcfe473a9846f7f18ee`)
- `paper_bencmark/highambench/tasks/P15/T3/faithfulness/history/20260820T105914Z/agent_outputs/source_contract.json` (`9fc7c9554b51771ef8f73ce95234a3e85825ebd2fa3c6fad39d07d445d6368f0`)
- `paper_bencmark/highambench/tasks/P15/T3/faithfulness/history/20260820T105914Z/decision.json` (`1884fe900bd4baabf88cb07a38d7d37479ec61cbe33391b4b35a2c69e03f6d20`)
- `paper_bencmark/highambench/tasks/P15/T3/faithfulness/history/20260820T105914Z/inputs/blind_dependency_inventory.json` (`9cbd2904499a9bf7a5f6d564ea389b8a451afef2ca9086f6e93901fffccc06ad`)
- `paper_bencmark/highambench/tasks/P15/T3/faithfulness/history/20260820T105914Z/inputs/blind_dossier.md` (`ef6a30809f983a0f6286e7b06ab6be570eb28de78f6c5fed9d7abe84e9c978d8`)
- `paper_bencmark/highambench/tasks/P15/T3/faithfulness/history/20260820T105914Z/inputs/blind_review_packet.md` (`ef6a30809f983a0f6286e7b06ab6be570eb28de78f6c5fed9d7abe84e9c978d8`)
- `paper_bencmark/highambench/tasks/P15/T3/faithfulness/history/20260820T105914Z/inputs/declaration_dossier.md` (`c1b94f9ad0c0992839b78287f2ab5ec3b9996bb0006d7788dc24b703ae4ae305`)
- `paper_bencmark/highambench/tasks/P15/T3/faithfulness/history/20260820T105914Z/inputs/dependency_inventory.json` (`2768c2c919d20cf047da9ebad2723933cd72b178b83c0650b0d2b10283fc5269`)
- `paper_bencmark/highambench/tasks/P15/T3/faithfulness/history/20260820T105914Z/inputs/dependency_reuse_direct.json` (`fbd14dfd3917164bfad3b52631711d1545b15975bdf45dbe02e221108117986d`)
- `paper_bencmark/highambench/tasks/P15/T3/faithfulness/history/20260820T105914Z/inputs/direct_review_packet.md` (`1aa029d06e8641698d1c9ffdfbcd36d4834c67e9b5cb58e49f0b65a77546ec59`)
- `paper_bencmark/highambench/tasks/P15/T3/faithfulness/history/20260820T105914Z/inputs/paper_source_locator.json` (`568b244880bf84912b78ba1130fd66ae2d43016e0a25f06e4510e3d731ee5223`)
- `paper_bencmark/highambench/tasks/P15/T3/faithfulness/history/20260820T105914Z/inputs/source_locator.json` (`244a38eb2c34a9f52dab5e2a1622b8ecf82862ab61fbf7d49c0853cf74e6fa2b`)
- `paper_bencmark/highambench/tasks/P15/T3/faithfulness/inputs/blind_dependency_inventory.json` (`f08d73c1521737c2bbfea09bcbea9e22b9feff5636d15547f69b45d91b428832`)
- `paper_bencmark/highambench/tasks/P15/T3/faithfulness/inputs/blind_dossier.md` (`1dea98e2d0e80563200aef63ab6d7ac7d67b0fa9592f9d3880b3afe17be8ae27`)
- `paper_bencmark/highambench/tasks/P15/T3/faithfulness/inputs/blind_review_packet.md` (`1dea98e2d0e80563200aef63ab6d7ac7d67b0fa9592f9d3880b3afe17be8ae27`)
- `paper_bencmark/highambench/tasks/P15/T3/faithfulness/inputs/declaration_dossier.md` (`23e3e6cc6d2cb70dd389ee98e879ae67cb70a4a68acfeb4c59c2fd4d720cd511`)
- `paper_bencmark/highambench/tasks/P15/T3/faithfulness/inputs/dependency_inventory.json` (`df2f634f2b2be5672a237680e3d881e385fe247277ed4e4d1e6b6c5b5d6c72c3`)
- `paper_bencmark/highambench/tasks/P15/T3/faithfulness/inputs/direct_review_packet.md` (`3e9fa8d12a987ed20d2037ce9938878d073305cd401bc8f479865b79d0eeaca3`)
- `paper_bencmark/highambench/tasks/P15/T3/faithfulness/inputs/source_locator.json` (`a0e28441f60a8ba02cc844632b2dea2d670a1a5342b9244a70405225c82d9579`)
