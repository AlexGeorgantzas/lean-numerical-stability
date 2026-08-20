# Faithfulness audit: P15-T2

- Classification: `not-faithful-different`
- Accepted as paper-faithful: `false`
- Adjudicated: `true`
- Target SHA-256: `6e8c3e8528e7e3c053ffa3234471c492a454ea2bbce319bec82e414fb3feb565`
- Paper SHA-256: `a5cb8eb779c1571f1549ea6838c7f2269302c960fb4ea21f8410060811270cd7`

## Decision

The target faithfully preserves the algebraic form of the combined bound and proves a nonvacuous perturbation-composition fact. It does not formalize the paper's derivation of the rounding perturbation from X(Y^T v), and its arbitrary-input universal scope is not the proposition stated by Lemma 3.1. Thus Lean does not imply the paper, and the paper's intended instance does not imply Lean's full universal theorem. The correct classification is not-faithful-different, with rejection unaffected by the remaining uncertainty about the inherited norm formula.

## Implications

- **Lean implies paper:** `no`. Lean assumes the existence and bound of the Atilde-level rounding perturbation through the supplied roundingError. It contains no X, Y, rank r, orthonormality, two-stage floating-point evaluation, unit roundoff, or derivation of gamma_c, so it cannot recover equation (3.1) or the full Lemma 3.1.
- **Paper implies lean:** `no`. The paper guarantees perturbations for outputs of the specified low-rank floating-point computation with gamma_c fixed by b, r, and u. It does not assert Lean's universal conditional for arbitrary Atilde, roundingError, gammaC, and natural n. Its final replacement argument validates the intended paper-generated instance, not the full universal Lean proposition.

## Findings

- **critical / algorithmic-result-assumed:** The central numerical-stability result is an antecedent rather than a conclusion.
- **major / incomparable-quantifier-scope:** Neither complete proposition implies the other; broader conditional applicability does not compensate for omission of the algorithmic existence theorem.
- **major / floating-point-constant-disconnected:** The formal bound has no certified connection to precision, operation count, rank, or the paper's floating-point model.
- **minor / domain-and-hypothesis-change:** Lean includes unsupported and sometimes degenerate cases outside the paper's stated result.
- **minor / norm-match-uncertified:** Exact norm agreement cannot be certified, although the independent algorithmic and quantifier failures already determine nonacceptance.
- **note / combined-bound-preserved:** The mixed epsilon*gammaC*beta contribution is represented correctly, but this does not repair the missing derivation.

## Semantic checklist

| Check | Direct | Round-trip |
|---|---|---|
| `S01` | `pass` | `pass` |
| `S02` | `fail` | `fail` |
| `S03` | `fail` | `fail` |
| `S04` | `fail` | `fail` |
| `S05` | `fail` | `fail` |
| `S06` | `pass` | `unclear` |
| `S07` | `fail` | `fail` |
| `S08` | `fail` | `fail` |
| `S09` | `pass` | `unclear` |
| `S10` | `fail` | `fail` |
| `S11` | `fail` | `fail` |
| `S12` | `fail` | `fail` |
| `S13` | `pass` | `fail` |
| `S14` | `pass` | `pass` |
| `S15` | `fail` | `fail` |
| `S16` | `fail` | `fail` |

## Dependency coverage

- Blind translator covered `34` dependencies (`0` hash-reused meanings); unclear: `D003, D029`.
- Direct judge covered `34` dependencies (`19` hash-reused interpretations); failing or unclear: `none`.

## Remaining uncertainties

- The exact entrywise formula of the norm selected through D003 and D029 cannot be independently certified from the supplied declaration bodies because Matrix.frobeniusSeminormedAddCommGroup is referenced but not unfolded. Consequently the exact D003/D029 paper match and checks S06 and S09 remain unclear.

## Audit artifacts

- `paper_bencmark/highambench/tasks/P15/T2/faithfulness/agent_outputs/adjudicator.json` (`5ca4fba8baa7cba8447e8c4e5d17c8db37928281e651edc50e3666f834205e56`)
- `paper_bencmark/highambench/tasks/P15/T2/faithfulness/agent_outputs/blind_translation.json` (`6513e9977d82f2fbf471fa04470e52c75ed30468725029cfd59b291203411832`)
- `paper_bencmark/highambench/tasks/P15/T2/faithfulness/agent_outputs/direct_judge.json` (`398247ac5db9ed52e2576634b81f9bfdad23dc0e23ee3ac1d68d15971e2a2cb1`)
- `paper_bencmark/highambench/tasks/P15/T2/faithfulness/agent_outputs/paper_source_contract.json` (`339fc5a797919c9e9bcd9c7d27d579722d8bfedc8091d16c4ab89148a1eb498f`)
- `paper_bencmark/highambench/tasks/P15/T2/faithfulness/agent_outputs/roundtrip_judge.json` (`3228c035de2300f30ed94d6f55da524c66a6c6a78cff1caad1f91f39d13af79e`)
- `paper_bencmark/highambench/tasks/P15/T2/faithfulness/agent_outputs/source_contract.json` (`4455adda22e4e4eadeba84ea892687d42f956eee3479e408c3ffa56573fe22fa`)
- `paper_bencmark/highambench/tasks/P15/T2/faithfulness/decision.json` (`8735d55dec3dfa0ae3904265b689b82a8ba89ad37762492029528523c47a5c80`)
- `paper_bencmark/highambench/tasks/P15/T2/faithfulness/inputs/blind_dependency_inventory.json` (`f5eb47df52a02b164230ef26cc5d661455ec5106992a2255f1d75a70de8278d9`)
- `paper_bencmark/highambench/tasks/P15/T2/faithfulness/inputs/blind_dossier.md` (`6d8bb543f7578c2f1c488dbf291c9c900a371c9e1a260443e32703e75e307e7b`)
- `paper_bencmark/highambench/tasks/P15/T2/faithfulness/inputs/blind_review_packet.md` (`6d8bb543f7578c2f1c488dbf291c9c900a371c9e1a260443e32703e75e307e7b`)
- `paper_bencmark/highambench/tasks/P15/T2/faithfulness/inputs/declaration_dossier.md` (`438c7d18c1182e43d8bfd1edb7854f4e8ad8ff8fef9d4201c32b4980c510e0a5`)
- `paper_bencmark/highambench/tasks/P15/T2/faithfulness/inputs/dependency_inventory.json` (`9c2d74cef085c58a341de6b05653f17efd313479c22ec2ceb313ce708cc2eb21`)
- `paper_bencmark/highambench/tasks/P15/T2/faithfulness/inputs/dependency_reuse_direct.json` (`50929ce9988d93bf78236d3728964df2c9808bef33c0a86ca85716cff0244354`)
- `paper_bencmark/highambench/tasks/P15/T2/faithfulness/inputs/direct_review_packet.md` (`3b30d3820cc27dbc331b4cebf11fc6a683bcd53528095602359a30f709d2e46e`)
- `paper_bencmark/highambench/tasks/P15/T2/faithfulness/inputs/paper_source_locator.json` (`568b244880bf84912b78ba1130fd66ae2d43016e0a25f06e4510e3d731ee5223`)
- `paper_bencmark/highambench/tasks/P15/T2/faithfulness/inputs/source_locator.json` (`7685e7e6f4cf635393f93721348220b99764d19b4ef32ad11b0d76f5d27ca76d`)
