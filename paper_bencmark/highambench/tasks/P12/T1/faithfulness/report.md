# Faithfulness audit: P12-T1

- Classification: `faithful-stronger`
- Accepted as paper-faithful: `true`
- Adjudicated: `false`
- Target SHA-256: `8789c920e124f1456e39446d0e7dddd922e630a41130ddae87b341c6dfc8f3dd`
- Paper SHA-256: `0569d969cebaabe42de69fef10fa91002af12d62149af7485d0712414b53c2a1`

## Decision

The target captures the exact nearest-addition argument behind equations (9) and (10): x is a representable comparison candidate, so a nearest representable s cannot be farther from x+y than x is, and that comparison distance is |y|. All arithmetic and absolute-value dependencies have standard exact-real semantics. Lean strictly strengthens the source by abstracting F to an arbitrary predicate and dropping representability of y; these changes are valid because neither the floating-point structure nor y∈F is needed for this isolated inequality. Consequently Lean implies the paper result, the converse does not hold at the stated generality, and the appropriate accepted classification is faithful-stronger.

## Implications

- **Lean implies paper:** `yes`. Instantiate representable with membership in the paper's F, take paper operands x,y∈F, and set s=x⊕y. Membership gives hx, while the nearest-addition definition and codomain give p12Nearest F (x+y) s. Lean then yields equation (10) exactly.
- **Paper implies lean:** `no`. The paper states the result for its specific floating-point sets, with both operands in F and s produced by a map F×F→F. It does not quantify arbitrary real predicates or cover nonrepresentable y, both of which are included in the Lean proposition.

## Findings

- **note / domain-and-model-generalization:** This prevents the paper-to-Lean implication but does not lose or distort the benchmark result. The paper statement is a direct, nonvacuous specialization of the Lean theorem.
- **major / binder-and-floating-point-model generalization:** The translated theorem strictly generalizes the paper result, so the reverse implication fails, but every paper instance remains covered.
- **minor / algorithm linkage and quantifier packaging:** Explicit computational provenance and global operation structure are lost, although the pointwise condition is exactly sufficient to derive the source inequality.

## Semantic checklist

| Check | Direct | Round-trip |
|---|---|---|
| `S01` | `pass` | `pass` |
| `S02` | `fail` | `fail` |
| `S03` | `pass` | `fail` |
| `S04` | `fail` | `fail` |
| `S05` | `pass` | `pass` |
| `S06` | `pass` | `pass` |
| `S07` | `pass` | `pass` |
| `S08` | `pass` | `fail` |
| `S09` | `pass` | `pass` |
| `S10` | `pass` | `pass` |
| `S11` | `fail` | `fail` |
| `S12` | `pass` | `pass` |
| `S13` | `pass` | `pass` |
| `S14` | `pass` | `pass` |
| `S15` | `pass` | `pass` |
| `S16` | `pass` | `pass` |

## Dependency coverage

- Blind translator covered `14` dependencies (`0` hash-reused meanings); unclear: `none`.
- Direct judge covered `14` dependencies (`0` hash-reused interpretations); failing or unclear: `none`.

## Remaining uncertainties

No remaining uncertainties were recorded.

## Audit artifacts

- `paper_bencmark/highambench/tasks/P12/T1/faithfulness/agent_outputs/blind_translation.json` (`81d87b23d25af9e39a3da541223928a8eb1cd68a9129730d0ffbc726e893667b`)
- `paper_bencmark/highambench/tasks/P12/T1/faithfulness/agent_outputs/direct_judge.json` (`5c9879b316aa888cf2971828a15e75d8abbe21f16f7849cfadf6907fe9130e60`)
- `paper_bencmark/highambench/tasks/P12/T1/faithfulness/agent_outputs/paper_source_contract.json` (`c14eaa2ba1c25d2284fb972ef8a21fb4aa3b9f4953061dea7bb0ea5b382a6321`)
- `paper_bencmark/highambench/tasks/P12/T1/faithfulness/agent_outputs/roundtrip_judge.json` (`23a0a0fdb4879c4f1224fa2dd3ff9d18d519f907b6ce0a62c8d6698b197c639d`)
- `paper_bencmark/highambench/tasks/P12/T1/faithfulness/agent_outputs/source_contract.json` (`a1933d789199b2e126f244031d6613b41d40abb7dbef88b2adc694ae12dafed6`)
- `paper_bencmark/highambench/tasks/P12/T1/faithfulness/decision.json` (`abbc3350680f246ca26e6179929b6e932355f29873c8f9f58109bf2aca450d45`)
- `paper_bencmark/highambench/tasks/P12/T1/faithfulness/inputs/blind_dependency_inventory.json` (`ba10c771b1617e5e3fb6441af43780bc46203e62da0a75be20204b3db5b04fa2`)
- `paper_bencmark/highambench/tasks/P12/T1/faithfulness/inputs/blind_dossier.md` (`63cee7bad54cf877ef471adf469b4c721264a6c0a2c27ab20c07c7465b3d9dcb`)
- `paper_bencmark/highambench/tasks/P12/T1/faithfulness/inputs/blind_review_packet.md` (`63cee7bad54cf877ef471adf469b4c721264a6c0a2c27ab20c07c7465b3d9dcb`)
- `paper_bencmark/highambench/tasks/P12/T1/faithfulness/inputs/declaration_dossier.md` (`797225d7bb3f3a56cd3c8fcb6c68f83689f0a71ec2758bb779190c7875fad420`)
- `paper_bencmark/highambench/tasks/P12/T1/faithfulness/inputs/dependency_inventory.json` (`8119d92727d666ccddf5ffada95288ad43e01dbc587056245ef443a36ac75444`)
- `paper_bencmark/highambench/tasks/P12/T1/faithfulness/inputs/direct_review_packet.md` (`31b53aa6a7b35b6ea1d17173cf4798c250e752230891f95473a3d9dec44f3463`)
- `paper_bencmark/highambench/tasks/P12/T1/faithfulness/inputs/paper_source_locator.json` (`515de0f8e7e7ece14b209a55702074a38799c848bbb9eb747b29a9993464642f`)
- `paper_bencmark/highambench/tasks/P12/T1/faithfulness/inputs/source_locator.json` (`562e1f845b9e407f0e835772eaca057b1d9f36ebe4c503361662f07649ed1f40`)
