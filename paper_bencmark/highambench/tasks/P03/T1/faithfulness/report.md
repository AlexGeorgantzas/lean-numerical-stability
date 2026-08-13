# Faithfulness audit: P03-T1

- Classification: `faithful-stronger`
- Accepted as paper-faithful: `true`
- Adjudicated: `false`
- Target SHA-256: `6de2787b760937b2e0b20ef82c6dbb221a7be6f8683b9a963070abee2439e717`
- Paper SHA-256: `952c6827db21fb2a9362b5aa4d38a1b2c75361f2cc7a3badbb7cd4a232d7b7bc`

## Decision

The Lean proposition is a nonvacuous pointwise real-algebra generalization of equation (4.1). After unfolding p03MatVec, it preserves the exact residual sign, all four right-hand terms, the update offset, and the distinct residual- and update-error variables. Every paper instance satisfies its two hypotheses, so Lean implies the selected paper identity. The reverse implication fails because Lean drops nonsingularity and algorithmic and floating-point provenance and quantifies over arbitrary conforming tuples. Those omissions broaden rather than weaken the exact algebraic result, so the fixed classification is faithful-stronger.

## Implications

- **Lean implies paper:** `yes`. For each paper iteration k, instantiate x=xHat_k, y=xHat_(k+1), d=dHat_k, rHat=rHat_k, Delta-r=Delta-r_k, and Delta-x=Delta-x_k. Equations (3.3) and (3.6) supply hres and hupdate, and D001 identifies p03MatVec with matrix-vector multiplication. The componentwise Lean conclusion is therefore exactly equation (4.1).
- **Paper implies lean:** `no`. The paper asserts (4.1) only in the inherited context of nonsingular A and quantities produced by Algorithm 1.1. It does not, as a stated result, quantify over singular matrices, arbitrary algebraic tuples, n=0, or tuples unrelated to an execution. Elementary algebra independently proves that extension, but the contextual paper result alone does not imply the full Lean quantification.

## Findings

- **minor / contextual-generalization:** The declaration is not contextually equivalent to the paper result, and the paper-to-Lean implication fails. The extension is nonvacuous and still covers every intended paper instance.
- **note / floating-point-provenance:** The theorem certifies the isolated algebraic identity but cannot by itself establish that supplied values arose from the paper's floating-point algorithm or satisfy its rounding bounds.
- **major / algorithm-and-computation-context:** The translation cannot independently express execution provenance or support the paper's numerical error estimates, although its broader algebraic theorem still covers every paper instance of equation (4.1).
- **minor / domain-and-hypothesis-generalization:** The translation is not source-equivalent; it is strictly stronger over the algebraic domain.
- **note / exact-identity:** There is no changed coefficient, sign, norm, error direction, or omitted higher-order term in the selected conclusion.

## Semantic checklist

| Check | Direct | Round-trip |
|---|---|---|
| `S01` | `pass` | `pass` |
| `S02` | `pass` | `fail` |
| `S03` | `fail` | `fail` |
| `S04` | `fail` | `fail` |
| `S05` | `pass` | `pass` |
| `S06` | `pass` | `pass` |
| `S07` | `pass` | `fail` |
| `S08` | `fail` | `fail` |
| `S09` | `pass` | `not-applicable` |
| `S10` | `pass` | `pass` |
| `S11` | `fail` | `fail` |
| `S12` | `pass` | `fail` |
| `S13` | `pass` | `fail` |
| `S14` | `pass` | `pass` |
| `S15` | `pass` | `pass` |
| `S16` | `pass` | `pass` |

## Dependency coverage

- Blind translator covered `18` dependencies (`0` hash-reused meanings); unclear: `none`.
- Direct judge covered `18` dependencies (`0` hash-reused interpretations); failing or unclear: `none`.

## Remaining uncertainties

No remaining uncertainties were recorded.

## Audit artifacts

- `paper_bencmark/highambench/tasks/P03/T1/faithfulness/agent_outputs/blind_translation.json` (`25501d1769416539be8d3879b7a12404fee84171282edbebc635de49b6a844c9`)
- `paper_bencmark/highambench/tasks/P03/T1/faithfulness/agent_outputs/direct_judge.json` (`7dc5ab10ad3b4c70134d0137006e86ef8603c34e3fecf99cb4dbfbe9f2d2ac31`)
- `paper_bencmark/highambench/tasks/P03/T1/faithfulness/agent_outputs/paper_source_contract.json` (`cc0f2d27697c7df47ddee702a54285359037d701ffa45ec71a92ca67f9cf3902`)
- `paper_bencmark/highambench/tasks/P03/T1/faithfulness/agent_outputs/roundtrip_judge.json` (`eee9070820b207133c350eddda0a2427e3e3602fcfccb6d67641267b872bd96f`)
- `paper_bencmark/highambench/tasks/P03/T1/faithfulness/agent_outputs/source_contract.json` (`7d3a8323a65a9bdb82f4680472b3c10db30b0a634f6f8530ec4a4e9e8b9328b2`)
- `paper_bencmark/highambench/tasks/P03/T1/faithfulness/decision.json` (`ee50cc03e7c00b34edcf0c8c6fec693b19fa2225d6a53cc76240e4c76a6a20be`)
- `paper_bencmark/highambench/tasks/P03/T1/faithfulness/inputs/blind_dependency_inventory.json` (`8cede65214ee2e6cec24be4741e24fa32f86da3bad8918f28d3582f5b31fd06c`)
- `paper_bencmark/highambench/tasks/P03/T1/faithfulness/inputs/blind_dossier.md` (`5b7ad88522ec1f0428d6cbabeeaa433cdc6ac8d06cfdc51ac2c0e9bbd9064829`)
- `paper_bencmark/highambench/tasks/P03/T1/faithfulness/inputs/blind_review_packet.md` (`5b7ad88522ec1f0428d6cbabeeaa433cdc6ac8d06cfdc51ac2c0e9bbd9064829`)
- `paper_bencmark/highambench/tasks/P03/T1/faithfulness/inputs/declaration_dossier.md` (`495f1f3ce44ba4e44ca798c535713cd7425986fa504104801629e17c55247a90`)
- `paper_bencmark/highambench/tasks/P03/T1/faithfulness/inputs/dependency_inventory.json` (`82b03141ac1d815f3f77d0d3a35d45c1a125b4256124e803b7345df682556fc7`)
- `paper_bencmark/highambench/tasks/P03/T1/faithfulness/inputs/direct_review_packet.md` (`e1dbf8b352b736035e0d366424933943d19c74237087dfba62de1c4a21f8deaf`)
- `paper_bencmark/highambench/tasks/P03/T1/faithfulness/inputs/paper_source_locator.json` (`d325b31e2cf1ecac253237196c87cfb8e169960305af1f36083a03802a8829df`)
- `paper_bencmark/highambench/tasks/P03/T1/faithfulness/inputs/source_locator.json` (`3a635772cded2567adc7fa9c45570ab67aca715ed4c00919fed969954a7323ac`)
