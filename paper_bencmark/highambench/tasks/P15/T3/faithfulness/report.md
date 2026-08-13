# Faithfulness audit: P15-T3

- Classification: `not-faithful-different`
- Accepted as paper-faithful: `false`
- Adjudicated: `true`
- Target SHA-256: `d06423c64abe1cb4ef65e8c0bf304ef9e8e1515d8a4cd618208540e606245415`
- Paper SHA-256: `a5cb8eb779c1571f1549ea6838c7f2269302c960fb4ea21f8410060811270cd7`

## Decision

Primary inspection of the hash-verified PDF confirms a faithful exact perturbation-composition core and correct norm semantics. It also confirms that Theorem 4.5 is an algorithm-specific BLR result whose component perturbations, constants, and floating-point meanings are derived from preceding results, whereas Lean assumes those component facts for arbitrary exact real data and leaves the controlling parameters unrelated. Natural parameter identifications reveal genuine local sharpness in part of the Lean algebra, but that is not whole-theorem strength and cannot compensate for the missing algorithmic guarantee and asymptotic contracts. Neither statement implies the other as stated, so the declaration is not-faithful-different.

## Implications

- **Lean implies paper:** `no`. The Lean declaration proves composition only after arbitrary primitive factorization and solve perturbations and their bounds are supplied. It does not establish that either BLR algorithm produces those data, nor does it encode n = pb, BLR ranks, c, gamma definitions, xi_p cases, or the big-O contracts required by Theorem 4.5. Its locally sharper exact coefficients therefore cannot recover the paper theorem by themselves.
- **Paper implies lean:** `no`. The paper asserts a result for outputs of Algorithms 1 and 2 under their BLR, nonsingularity, completion, truncation, and floating-point assumptions. It does not assert the Lean theorem's universal implication for arbitrary matrices and independently supplied errors or its exact bounds over unconstrained gammaP, gammaC, xi, and factorRemainder.

## Findings

- **critical / algorithm-linkage-and-witness-production:** The source theorem about a computed BLR solve is replaced by a generic perturbation-composition lemma.
- **major / parameterization-and-floating-point-model:** The declaration cannot establish the paper's dimension-, rank-, threshold-, or precision-dependent bounds.
- **major / higher-order-semantics:** The asymptotic remainder claims are not formalized, despite preservation of the exact product terms.
- **minor / source-notation-ambiguity:** Lean's single A cannot be confirmed as the intended normalization, although independent defects already determine rejection.
- **note / faithful-algebraic-core:** The declaration faithfully formalizes the exact composition step, but not the complete theorem.

## Semantic checklist

| Check | Direct | Round-trip |
|---|---|---|
| `S01` | `pass` | `pass` |
| `S02` | `fail` | `fail` |
| `S03` | `fail` | `fail` |
| `S04` | `fail` | `fail` |
| `S05` | `fail` | `fail` |
| `S06` | `fail` | `pass` |
| `S07` | `unclear` | `fail` |
| `S08` | `fail` | `fail` |
| `S09` | `pass` | `pass` |
| `S10` | `fail` | `fail` |
| `S11` | `fail` | `fail` |
| `S12` | `fail` | `unclear` |
| `S13` | `pass` | `pass` |
| `S14` | `fail` | `fail` |
| `S15` | `fail` | `fail` |
| `S16` | `pass` | `fail` |

## Dependency coverage

- Blind translator covered `57` dependencies (`0` hash-reused meanings); unclear: `none`.
- Direct judge covered `57` dependencies (`20` hash-reused interpretations); failing or unclear: `D001, D019`.

## Remaining uncertainties

- The PDF does not state whether the A_tilde in Theorem 4.5's opening is a typographical error, a BLR representation of A, or a distinct intended matrix; equations (4.23)-(4.25) and the proof silently use A.
- The hidden constants in O(u*epsilon) and O(u^2), and the absence of any Lean asymptotic contract for factorRemainder, prevent an exact ordering of the isolated final numerical bounds. This does not affect the two overall implication verdicts.

## Audit artifacts

- `paper_bencmark/highambench/tasks/P15/T3/faithfulness/agent_outputs/adjudicator.json` (`4311935f42a62715f3dd0c151b813d51499f63175f836c7cf819ee4d7c90c821`)
- `paper_bencmark/highambench/tasks/P15/T3/faithfulness/agent_outputs/blind_translation.json` (`e863d0a2062602a574fe83b7982e8cb51afd1623973ea809ba9781a983be50df`)
- `paper_bencmark/highambench/tasks/P15/T3/faithfulness/agent_outputs/direct_judge.json` (`6262e2541e9dce9111b21c18f3a8e2e5418fb00d7d291ebbce25212ae41584e2`)
- `paper_bencmark/highambench/tasks/P15/T3/faithfulness/agent_outputs/paper_source_contract.json` (`339fc5a797919c9e9bcd9c7d27d579722d8bfedc8091d16c4ab89148a1eb498f`)
- `paper_bencmark/highambench/tasks/P15/T3/faithfulness/agent_outputs/roundtrip_judge.json` (`41433addc668f60a98ced486313d98c95c0bc14478cd1bcfe473a9846f7f18ee`)
- `paper_bencmark/highambench/tasks/P15/T3/faithfulness/agent_outputs/source_contract.json` (`9fc7c9554b51771ef8f73ce95234a3e85825ebd2fa3c6fad39d07d445d6368f0`)
- `paper_bencmark/highambench/tasks/P15/T3/faithfulness/decision.json` (`1884fe900bd4baabf88cb07a38d7d37479ec61cbe33391b4b35a2c69e03f6d20`)
- `paper_bencmark/highambench/tasks/P15/T3/faithfulness/inputs/blind_dependency_inventory.json` (`9cbd2904499a9bf7a5f6d564ea389b8a451afef2ca9086f6e93901fffccc06ad`)
- `paper_bencmark/highambench/tasks/P15/T3/faithfulness/inputs/blind_dossier.md` (`ef6a30809f983a0f6286e7b06ab6be570eb28de78f6c5fed9d7abe84e9c978d8`)
- `paper_bencmark/highambench/tasks/P15/T3/faithfulness/inputs/blind_review_packet.md` (`ef6a30809f983a0f6286e7b06ab6be570eb28de78f6c5fed9d7abe84e9c978d8`)
- `paper_bencmark/highambench/tasks/P15/T3/faithfulness/inputs/declaration_dossier.md` (`c1b94f9ad0c0992839b78287f2ab5ec3b9996bb0006d7788dc24b703ae4ae305`)
- `paper_bencmark/highambench/tasks/P15/T3/faithfulness/inputs/dependency_inventory.json` (`2768c2c919d20cf047da9ebad2723933cd72b178b83c0650b0d2b10283fc5269`)
- `paper_bencmark/highambench/tasks/P15/T3/faithfulness/inputs/dependency_reuse_direct.json` (`fbd14dfd3917164bfad3b52631711d1545b15975bdf45dbe02e221108117986d`)
- `paper_bencmark/highambench/tasks/P15/T3/faithfulness/inputs/direct_review_packet.md` (`1aa029d06e8641698d1c9ffdfbcd36d4834c67e9b5cb58e49f0b65a77546ec59`)
- `paper_bencmark/highambench/tasks/P15/T3/faithfulness/inputs/paper_source_locator.json` (`568b244880bf84912b78ba1130fd66ae2d43016e0a25f06e4510e3d731ee5223`)
- `paper_bencmark/highambench/tasks/P15/T3/faithfulness/inputs/source_locator.json` (`244a38eb2c34a9f52dab5e2a1622b8ecf82862ab61fbf7d49c0853cf74e6fa2b`)
