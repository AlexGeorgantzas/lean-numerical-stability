# Faithfulness audit: P02-T2

- Classification: `faithful-stronger`
- Accepted as paper-faithful: `true`
- Adjudicated: `true`
- Target SHA-256: `6869f7e5200080eb138266e3d9671b6c6f323b987996c748a25f497564fe4903`
- Paper SHA-256: `e7b8523c793ad7345dfc76f681c44d1afbbc3a810fb948912451432ae616512d`

## Decision

Primary evidence fixes the paper theorem as |res-s|<=eps|s|+gamma_(N-1)^2*sum|p_i| under N eps<1, with finite working-precision inputs, no overflow, and underflow allowed. Unfolding Lean gives one TwoSum-based vector transform followed by a left-to-right modeled sum; with N=n+1 its condition and coefficient are exact. The paper arithmetic embeds in the all-real model without changing the paper result, so Lean implies the paper. The paper statement does not imply Lean's theorem for arbitrary real vectors and arbitrary admissible total models, and those extra models are nonvacuous. The resulting yes/no implication pair requires classification as faithful-stronger.

## Implications

- **Lean implies paper:** `yes`. For a paper instance of length N>=1, set Lean n=N-1, u=eps, and v(j)=p_(j+1). Extend the finite no-overflow paper operations to a total ErrorFreeAddModel, retaining them on paper operations and using exact addition and zero residual elsewhere. Equations (2.1), (3.2), and Theorem 3.4 establish the fields. In the paper arithmetic the operand-order variants agree, GammaValid becomes N eps<1, gamma u n becomes gamma_(N-1), and the conclusion is exactly equation (4.8).
- **Paper implies lean:** `no`. Proposition 4.5 states the result only for inputs in the fixed working-precision set F and the paper's arithmetic. It does not quantify arbitrary real vectors, arbitrary nonnegative u, or every total ErrorFreeAddModel, including nonexact noncommutative models admitted by the declaration.

## Findings

- **major / domain-and-model-generalization:** The reverse implication fails, but the paper case embeds without extra restrictions and the broader model class has nonexact inhabitants. This is genuine, nonvacuous strength.
- **minor / algorithm-operand-order-outside-paper-model:** For abstract noncommutative models, Lean's function need not literally be either displayed pseudocode. For the paper specialization all orders coincide, so Lean still implies Proposition 4.5.
- **note / singleton-proof-exposition:** The paper proof requires an implicit singleton base case; this creates no scope mismatch or negative gamma index in the Lean statement.

## Semantic checklist

| Check | Direct | Round-trip |
|---|---|---|
| `S01` | `pass` | `pass` |
| `S02` | `pass` | `fail` |
| `S03` | `pass` | `fail` |
| `S04` | `pass` | `fail` |
| `S05` | `pass` | `pass` |
| `S06` | `pass` | `pass` |
| `S07` | `pass` | `pass` |
| `S08` | `pass` | `fail` |
| `S09` | `pass` | `pass` |
| `S10` | `pass` | `pass` |
| `S11` | `pass` | `fail` |
| `S12` | `pass` | `pass` |
| `S13` | `pass` | `pass` |
| `S14` | `pass` | `pass` |
| `S15` | `pass` | `pass` |
| `S16` | `pass` | `pass` |

## Dependency coverage

- Blind translator covered `90` dependencies; unclear: `none`.
- Direct judge covered `90` dependencies; failing or unclear: `none`.

## Remaining uncertainties

- Section 2 does not contain one standalone sentence globally restating 'round to nearest' at Proposition 4.5; that label is inherited from surrounding discussion. This editorial uncertainty does not affect the verdict because equations (2.1), (2.4), and Theorem 3.4 state the operative properties and Lean assumes them directly.

## Audit artifacts

- `paper_bencmark/highambench/tasks/P02/T2/faithfulness/agent_outputs/adjudicator.json` (`9d9ee4ec13d22d0037f486ed6bcb52753898cfbb21b62366de5bdf389bd4c411`)
- `paper_bencmark/highambench/tasks/P02/T2/faithfulness/agent_outputs/blind_translation.json` (`af599b91cdad3a159232a55ddd5d882b402ea69d4f1dadf3aedc6c04b825d324`)
- `paper_bencmark/highambench/tasks/P02/T2/faithfulness/agent_outputs/direct_judge.json` (`e920212a13d52730f7d0245d9a89c426a671d8254dfdbd590dfb78c51c7b5dc6`)
- `paper_bencmark/highambench/tasks/P02/T2/faithfulness/agent_outputs/roundtrip_judge.json` (`78ffa02ec9fda702102175247a2ef10ce8ebc20afa6671af4a7246545b3b259b`)
- `paper_bencmark/highambench/tasks/P02/T2/faithfulness/agent_outputs/source_contract.json` (`2140c3e44cb2e27efba4a8f766727016db46bf4ade39096a615e97beaf0f2533`)
- `paper_bencmark/highambench/tasks/P02/T2/faithfulness/decision.json` (`0a4edf24aea210045353967b8061ed14b8fcae1e8c7b8a58caf3744846a300f3`)
- `paper_bencmark/highambench/tasks/P02/T2/faithfulness/inputs/blind_dossier.md` (`83c4fd0ba4db87d6b87d36403ef978a2e0c0bfbf918101cc704aad4598c5f4dd`)
- `paper_bencmark/highambench/tasks/P02/T2/faithfulness/inputs/declaration_dossier.md` (`2eb77a681213ac1635c62ccc981a0c24487fe66ad7a78c2280938c87d8bef06f`)
- `paper_bencmark/highambench/tasks/P02/T2/faithfulness/inputs/source_locator.json` (`839064d27dd89e4c07b9f4f71af7d7205bb4503a725d3ecd46e62b3e0a21b061`)
