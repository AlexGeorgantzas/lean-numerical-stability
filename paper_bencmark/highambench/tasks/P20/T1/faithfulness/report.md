# Faithfulness audit: P20-T1

- Classification: `not-faithful-different`
- Accepted as paper-faithful: `false`
- Adjudicated: `true`
- Target SHA-256: `1d58f9917ffc13cc95c701370253f1f644dc4559d1f93e37ea9081bfa2bba0a7`
- Paper SHA-256: `ad830de20a73ff77b6e457921892b3250ba9ff70f487501979ee3f1c5f3f31e2`

## Decision

The paper's selected passage specifies row-specific power-of-two scaling factors in the matrix algorithm, with theta fixed by the input and accumulation overflow ceilings, and states that those factors satisfy equation (3.4a). Lean assumes that exact interval and proves only the resulting coordinate range for arbitrary real parameters. Thus it does not imply the selected paper claim, while the paper's restricted algorithmic assertion does not imply Lean's generalized universal conditional. The unresolved inherited norm semantics must remain explicit, but they do not prevent the two independent implication failures or the not-faithful-different classification.

## Implications

- **Lean implies paper:** `no`. Lean assumes the two inequalities constituting equation (3.4a), so it cannot establish the paper's selection or specification of a row-specific power-of-two factor satisfying them. It also neither fixes theta as min(f_max,sqrt(F_max/n)) nor links lambda to the diagonal scaling algorithm. Generalizing the conditional consequence to arbitrary reals is not genuine strength over the omitted central claim.
- **Paper implies lean:** `no`. The paper asserts the scaling relation only for matrix rows, its format-defined theta, and selected power-of-two diagonal factors. It does not assert the full Lean proposition universally for every finite real vector and every arbitrary real lambda and theta satisfying the antecedent. This scope mismatch already defeats the implication, regardless of the unresolved Pi norm formula.

## Findings

- **critical / central-result-assumed:** The declaration proves only a consequence after the selected source condition has already been assumed.
- **major / source-scope-changed:** The formal proposition is neither the paper's algorithm-specific claim nor a genuine strengthening that establishes it by specialization.
- **major / unresolved-norm-semantics:** The exact match between the Lean norm and the paper's infinity norm cannot be certified from the supplied declaration evidence.
- **note / nonvacuous-algebraic-core:** The theorem is not globally vacuous, but nonvacuity does not repair its changed logical role or missing source constraints.

## Semantic checklist

| Check | Direct | Round-trip |
|---|---|---|
| `S01` | `pass` | `pass` |
| `S02` | `pass` | `fail` |
| `S03` | `fail` | `fail` |
| `S04` | `fail` | `fail` |
| `S05` | `fail` | `fail` |
| `S06` | `pass` | `unclear` |
| `S07` | `pass` | `pass` |
| `S08` | `fail` | `fail` |
| `S09` | `pass` | `unclear` |
| `S10` | `fail` | `fail` |
| `S11` | `fail` | `fail` |
| `S12` | `fail` | `fail` |
| `S13` | `pass` | `pass` |
| `S14` | `pass` | `pass` |
| `S15` | `fail` | `fail` |
| `S16` | `pass` | `pass` |

## Dependency coverage

- Blind translator covered `36` dependencies (`0` hash-reused meanings); unclear: `D001, D035, D036`.
- Direct judge covered `36` dependencies (`0` hash-reused interpretations); failing or unclear: `none`.

## Remaining uncertainties

- The supplied dependency bodies do not establish that Pi.normedRing on Fin n -> Real uses max_i |x(i)|.
- The supplied dependency bodies do not establish that the norm inherited by Real.normedCommRing is ordinary absolute value.

## Audit artifacts

- `paper_bencmark/highambench/tasks/P20/T1/faithfulness/agent_outputs/adjudicator.json` (`9e429b6a54431e73f309283d27335e49fc1333a1b2acf53d1d870fc006c3f941`)
- `paper_bencmark/highambench/tasks/P20/T1/faithfulness/agent_outputs/blind_translation.json` (`f0a2e3f893b82cdf46375fbe4023707ebd031405f7ffb39b214770880066e36d`)
- `paper_bencmark/highambench/tasks/P20/T1/faithfulness/agent_outputs/direct_judge.json` (`cf9058d4e2cc05724c0dbaf9c0f580b36a9b66bb5e1c896dc7632ad59dd76f73`)
- `paper_bencmark/highambench/tasks/P20/T1/faithfulness/agent_outputs/paper_source_contract.json` (`a0c8bbaa2e261f7adc023b1698c08de77fd260aafddc9aa341073c2704530e40`)
- `paper_bencmark/highambench/tasks/P20/T1/faithfulness/agent_outputs/roundtrip_judge.json` (`51584315b72708ced275c0a4d03ca6e90aca19e448325ba8035a1181008eae26`)
- `paper_bencmark/highambench/tasks/P20/T1/faithfulness/agent_outputs/source_contract.json` (`f5253076f8203d022a69a7eabc0503053afcb8cfef361fbd9fce0546a1a95dd8`)
- `paper_bencmark/highambench/tasks/P20/T1/faithfulness/decision.json` (`2bf82c5a8e2eb22ca7af49a3ca561236a76da036ae539f10d27a7729c3738378`)
- `paper_bencmark/highambench/tasks/P20/T1/faithfulness/inputs/blind_dependency_inventory.json` (`0949e2ebcd9dfd0a9f039b6eb1b6bf88a2c1797efa9407d88570ce03c9b0f02d`)
- `paper_bencmark/highambench/tasks/P20/T1/faithfulness/inputs/blind_dossier.md` (`d40ac8ca2ddd3459a169e2ec4ebd02a7ed9f2623c975bf7ec8392f5ad3dc9706`)
- `paper_bencmark/highambench/tasks/P20/T1/faithfulness/inputs/blind_review_packet.md` (`d40ac8ca2ddd3459a169e2ec4ebd02a7ed9f2623c975bf7ec8392f5ad3dc9706`)
- `paper_bencmark/highambench/tasks/P20/T1/faithfulness/inputs/declaration_dossier.md` (`ee508e11f2305d5095c1869082697f3a31816dfa62d6814f65655b78db585976`)
- `paper_bencmark/highambench/tasks/P20/T1/faithfulness/inputs/dependency_inventory.json` (`48eb9bac7af6c92db998f6a416b8b33ca2e7497644b4d3a4e7be4fc56246adcd`)
- `paper_bencmark/highambench/tasks/P20/T1/faithfulness/inputs/direct_review_packet.md` (`16d509be04c4afaf6c760bc56a869f25375758bb81d574e163bdc747fe34e2df`)
- `paper_bencmark/highambench/tasks/P20/T1/faithfulness/inputs/paper_source_locator.json` (`413757004ac4d15ac7e55e926e2486e54bdac2db1523d83303ddb4cbffe644f4`)
- `paper_bencmark/highambench/tasks/P20/T1/faithfulness/inputs/source_locator.json` (`66da6a9c6ea70bdea0a7b29a4dde9639c4bd1d860675857f9063693dfa6d60c8`)
