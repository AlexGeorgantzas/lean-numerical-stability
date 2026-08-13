# Faithfulness audit: P02-T1

- Classification: `faithful-stronger`
- Accepted as paper-faithful: `true`
- Adjudicated: `true`
- Target SHA-256: `6ae5ba2b7579c90c03fadb3ef191a155a78eb84f008d7736fedfeec489ef9e0e`
- Paper SHA-256: `e7b8523c793ad7345dfc76f681c44d1afbbc3a810fb948912451432ae616512d`

## Decision

Primary PDF evidence identifies the selected proposition as equation (4.7)(i), the exact preservation of the input vector's real sum by the residuals and final prefix. The exact declaration, D002-D005, D027, and the verified ascending semantics of D029 implement that cascade and output layout. The paper's concrete arithmetic embeds into the abstract model through a total extension, so Lean implies the selected paper result. Conversely, the paper does not quantify over arbitrary admissible operations or arbitrary real vectors. Explicit model witnesses establish that this broader theorem is nonvacuous. Thus the implication pair is yes/no and the final accepted classification is faithful-stronger.

## Implications

- **Lean implies paper:** `yes`. Extend the paper's rounded addition and Algorithm 3.1 TwoSum from F pairs to all real pairs by using exact addition and zero residual outside F, set u=eps, map a paper vector of length N to Fin(N), and instantiate Lean with n=N-1. Because paper TwoSum outputs remain in F, every cascade step agrees with Algorithm 4.1. The Lean equality then gives exactly equation (4.7)(i), and the concrete operand-order rewrite in Algorithm 4.3 is extensionally equivalent under equation (3.2).
- **Paper implies lean:** `no`. Equation (4.7)(i) concerns the paper's fixed floating-point operation and F-valued vectors. It does not assert sum preservation for every total ErrorFreeAddModel and every Real-valued vector, including exact-addition and other non-floating models.

## Findings

- **note / selected-scope:** Nearby TwoSum bounds, equation (4.7)(ii), and operation counts are context or separate results, not missing conjuncts of this target.
- **note / genuine-domain-generalization:** The additional applicability is satisfiable and does not exclude the paper case, so it is genuine strength.
- **note / operand-order:** Abstract nonsymmetric models can produce different individual components, but exact sum preservation remains valid and the paper's concrete TwoSum gives the same real-valued pair under argument exchange.
- **note / contract-abstraction:** The target faithfully generalizes the selected invariant but is not a low-level verification of Algorithm 3.1 or its six-flop count.

## Semantic checklist

| Check | Direct | Round-trip |
|---|---|---|
| `S01` | `pass` | `pass` |
| `S02` | `pass` | `fail` |
| `S03` | `pass` | `fail` |
| `S04` | `pass` | `fail` |
| `S05` | `pass` | `fail` |
| `S06` | `pass` | `unclear` |
| `S07` | `pass` | `pass` |
| `S08` | `pass` | `fail` |
| `S09` | `not-applicable` | `pass` |
| `S10` | `pass` | `fail` |
| `S11` | `pass` | `fail` |
| `S12` | `pass` | `fail` |
| `S13` | `pass` | `pass` |
| `S14` | `pass` | `pass` |
| `S15` | `pass` | `fail` |
| `S16` | `pass` | `pass` |

## Dependency coverage

- Blind translator covered `54` dependencies; unclear: `none`.
- Direct judge covered `54` dependencies; failing or unclear: `none`.

## Remaining uncertainties

- The cited PDF passages do not completely specify radix, rounding mode, NaN, infinity, or signed-zero behavior. This adjudication therefore does not claim that ErrorFreeAddModel verifies Algorithm 3.1 for arbitrary hardware semantics; it uses the paper's own Theorem 3.4 contract. That low-level uncertainty is outside the selected real-valued sum-preservation invariant and does not affect the classification.

## Audit artifacts

- `paper_bencmark/highambench/tasks/P02/T1/faithfulness/agent_outputs/adjudicator.json` (`d2a1a2cae17027bcc3e2252b190d0e1a114bd1f0deda115a3b7133d370934f78`)
- `paper_bencmark/highambench/tasks/P02/T1/faithfulness/agent_outputs/blind_translation.json` (`5c2be4d0e5839f4a7b772ea21616bf9abdeda5948e0d4ea91b6a716bdd9ac329`)
- `paper_bencmark/highambench/tasks/P02/T1/faithfulness/agent_outputs/direct_judge.json` (`229e9550b904fb09c7f86305f8d510ebee7ae764a7729cf131299ae5b206d915`)
- `paper_bencmark/highambench/tasks/P02/T1/faithfulness/agent_outputs/roundtrip_judge.json` (`79019608155362e96c0baf27137adb3f19c0f57a126d5b40576df7edc3f7d8d9`)
- `paper_bencmark/highambench/tasks/P02/T1/faithfulness/agent_outputs/source_contract.json` (`e1c7e1af57756cfa3135c4cbda90878ab8f6149524db5e1eb0b06868536b8245`)
- `paper_bencmark/highambench/tasks/P02/T1/faithfulness/decision.json` (`f35bfcecbf1a6f48a1f93b7ab3e0c09c84d1de41d662f8f52b940055485aeafd`)
- `paper_bencmark/highambench/tasks/P02/T1/faithfulness/inputs/blind_dossier.md` (`a8771823a32e9f1c98d91d1a00a68e6ae4fcda4a81bba9b2ee81d6d8e885dc28`)
- `paper_bencmark/highambench/tasks/P02/T1/faithfulness/inputs/declaration_dossier.md` (`9a3f7d68b0a25ccca291d745a53fa91fbfcbb33025fac6b9da5e8fb8860dd4c5`)
- `paper_bencmark/highambench/tasks/P02/T1/faithfulness/inputs/source_locator.json` (`950c2af18bcbc5af5215389620dec8f8c24b028cbd1c20bba8ceecd5a9ff15ea`)
