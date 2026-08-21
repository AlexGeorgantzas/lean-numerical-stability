# Faithfulness audit: P19-T3

- Classification: `not-faithful-different`
- Accepted as paper-faithful: `false`
- Adjudicated: `true`
- Target SHA-256: `f929a2fb2ece11947c9ebced0e01ea12cbca832152d92b035133e5aea4c35ae3`
- Paper SHA-256: `67af427c72ae891b7863e386db542ef775b1e3eb306f812bb1a78bdbef86aaad`

## Decision

For the PDF bound by SHA-256 67af427c72ae891b7863e386db542ef775b1e3eb306f812bb1a78bdbef86aaad, the source's actual results are conditional, existential, first-order forward-error theorems. Lean instead proves a definition-driven exact algebraic lemma over a substantially broader and semantically unconstrained domain. The symbolic omitted-term observation is genuine, but it neither recovers the paper theorems nor makes the paper imply Lean's complete universal conjunction. Both implication directions are therefore no, yielding not-faithful-different.

## Implications

- **Lean implies paper:** `no`. The Lean proposition supplies only exact algebraic facts about two defined expressions. It provides no computed solution, normalized forward error, perturbation model, condition (3.16), fixed-preconditioner execution path, existential iteration, c(n,k), or treatment of omitted higher-order terms, so it cannot yield Theorems 3.3 or 3.4.
- **Paper implies lean:** `no`. The paper supports the three-term versus two-term bracket pattern after specializing to genuine nonsingular matrices and actual inverses. It does not imply the complete Lean proposition over every n and every unrelated matrix pair, including n = 0 and zero condition-number products. The additional exact equality characterization and strictness are independently true algebraic consequences of the Lean definitions; counting that tautology as a paper implication would ignore the protocol's complete-mapping requirement.

## Findings

- **critical / result-substitution:** The formal theorem cannot establish either selected numerical-analysis result.
- **major / unsupported-paper-to-lean-implication:** The matched middle term is insufficient to make the complete Lean proposition a paper consequence.
- **major / condition-number-domain:** Formal norm products may be zero or fail to denote any paper condition number.
- **major / first-order-and-quantifier-loss:** Exact universal bracket algebra cannot be substituted for the complete first-order forward-error theorems.
- **note / matched-bracket-structure:** This is a relevant symbolic correspondence, but only a partial one.

## Semantic checklist

| Check | Direct | Round-trip |
|---|---|---|
| `S01` | `pass` | `pass` |
| `S02` | `fail` | `fail` |
| `S03` | `fail` | `fail` |
| `S04` | `fail` | `fail` |
| `S05` | `fail` | `fail` |
| `S06` | `fail` | `fail` |
| `S07` | `fail` | `fail` |
| `S08` | `fail` | `fail` |
| `S09` | `fail` | `fail` |
| `S10` | `fail` | `fail` |
| `S11` | `fail` | `fail` |
| `S12` | `fail` | `fail` |
| `S13` | `fail` | `fail` |
| `S14` | `fail` | `fail` |
| `S15` | `fail` | `fail` |
| `S16` | `fail` | `fail` |

## Dependency coverage

- Blind translator covered `31` dependencies (`0` hash-reused meanings); unclear: `none`.
- Direct judge covered `31` dependencies (`10` hash-reused interpretations); failing or unclear: `D001, D002, D003, D005, D006, D007, D010, D011, D012, D013, D014, D015, D018, D019, D021, D022`.

## Remaining uncertainties

- The paper does not specify that the generic c(n,k) instances in the two theorem bounds are identical.
- Equation (3.15) does not explicitly resolve the case in which its denominator norm is zero; this does not affect the classification.

## Audit artifacts

- `paper_bencmark/highambench/tasks/P19/T3/faithfulness/agent_outputs/adjudicator.json` (`d9f37b0d1114d356317a32913d7e97f57d1bbd7b628295b20042ab6314bce836`)
- `paper_bencmark/highambench/tasks/P19/T3/faithfulness/agent_outputs/blind_translation.json` (`c4e2a0efe45f5d2d9dc61e0849a741c76dbf2482ab77ccdf3af3c9cc2f432f20`)
- `paper_bencmark/highambench/tasks/P19/T3/faithfulness/agent_outputs/direct_judge.json` (`9bf5ff61131ec949d3c0999fa070be292e3ad530f63bd7baa0563d70ab385993`)
- `paper_bencmark/highambench/tasks/P19/T3/faithfulness/agent_outputs/paper_source_contract.json` (`282bdf4dba3e70c740465a2c4663b96debd1a66ef82c3debf273ad41cdbf76e0`)
- `paper_bencmark/highambench/tasks/P19/T3/faithfulness/agent_outputs/roundtrip_judge.json` (`920bf500fc1a78ba18a5b61d94ca78940ed698706032649d63bedd1eb62a2c55`)
- `paper_bencmark/highambench/tasks/P19/T3/faithfulness/agent_outputs/source_contract.json` (`d9b9b728d225b77628508b1574bf70a411d50227b8120711d3b1921cd6596330`)
- `paper_bencmark/highambench/tasks/P19/T3/faithfulness/decision.json` (`c5d12aac529f8247a8899a3ceef9730c4b8e1d96490770c9e649b5cec5a42cfd`)
- `paper_bencmark/highambench/tasks/P19/T3/faithfulness/inputs/blind_dependency_inventory.json` (`cf0938f317757deff1412d59d70fd1bd3995ab59459c83182690a781a969eb8c`)
- `paper_bencmark/highambench/tasks/P19/T3/faithfulness/inputs/blind_dossier.md` (`b0d8714567f59fb874f4b2f9bf543b6466b3795d176c7c31897c2b0f22aa5800`)
- `paper_bencmark/highambench/tasks/P19/T3/faithfulness/inputs/blind_review_packet.md` (`b0d8714567f59fb874f4b2f9bf543b6466b3795d176c7c31897c2b0f22aa5800`)
- `paper_bencmark/highambench/tasks/P19/T3/faithfulness/inputs/declaration_dossier.md` (`03ab3c80a4baf92982c261f9384a5c3ac84e79307614209f0bf05a9f7d463f89`)
- `paper_bencmark/highambench/tasks/P19/T3/faithfulness/inputs/dependency_inventory.json` (`d5985e67c4c363c499dd39dde7b0dda9eda6996147c22d7c43473c8e5c1291dd`)
- `paper_bencmark/highambench/tasks/P19/T3/faithfulness/inputs/dependency_reuse_direct.json` (`18d04c541cef26b01d303550c587f2ffb9a973ae6035cb1fd28047ce7c4c0510`)
- `paper_bencmark/highambench/tasks/P19/T3/faithfulness/inputs/direct_review_packet.md` (`5dd422ef13089cd2fe52aa06ad2faa961e844c7eae45cc6d1fba7f46b293ecaa`)
- `paper_bencmark/highambench/tasks/P19/T3/faithfulness/inputs/paper_source_locator.json` (`b2b71745c3ba0bc98613f67b2d754faf971558a1974b0f22e4456d4b88500ba1`)
- `paper_bencmark/highambench/tasks/P19/T3/faithfulness/inputs/source_locator.json` (`3e3d8c11da1f2b05a3531b569c750e51a42f25f0a791458ece345cbbe7927cb9`)
