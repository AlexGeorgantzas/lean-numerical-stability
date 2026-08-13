# Faithfulness audit: P12-T2

- Classification: `not-faithful-different`
- Accepted as paper-faithful: `false`
- Adjudicated: `false`
- Target SHA-256: `c0e659193763c9d16fdfdcae671afddf5748751c77ec10d7e2e78e0946a6e13a`
- Paper SHA-256: `0569d969cebaabe42de69fef10fa91002af12d62149af7485d0712414b53c2a1`

## Decision

The target preserves the three-step dataflow, exact final identity, scalar residual bound, and nearest-addition relation. It does not preserve Theorem 2's substantive contract: x and y in a structured floating-point system, an existential representation of x satisfying condition (7), and faithful subtraction from which both exact subtraction steps are proved. Instead it quantifies an arbitrary representability predicate, omits representability of y and all base/precision/exponent data, assumes both exact differences representable, and applies nearest rounding to every operation. These changes make the target a nonvacuous but largely immediate abstract lemma, not a faithful strengthening or specialization. Because neither proposition implies the other under their stated domains and hypotheses, the result is not-faithful-different.

## Implications

- **Lean implies paper:** `no`. The Lean proposition cannot recover Theorem 2 from condition (7), nearest addition, and faithful subtraction because it contains no floating-point representation structure or condition (7) and requires hst, hye, and nearest relations for the subtraction outputs. Establishing those premises is precisely the central work of the paper result.
- **Paper implies lean:** `no`. The paper is scoped to a set F of the form (1), inputs x,y∈F, specified operations, and condition (7). It does not establish the Lean proposition's universal implication for every predicate Real→Prop, arbitrary real y, and arbitrary relational trace under the different antecedents.

## Findings

- **critical / core-proof-obligation-replaced-by-premises:** The target does not formalize the paper's main numerical result. It proves only an abstract algebraic consequence after the central exactness facts have effectively been supplied.
- **major / floating-point-model-mismatch:** The formal operation model is neither the paper's model nor a justified specialization of it.
- **major / domain-and-quantifier-mismatch:** The Lean and paper propositions range over different cases and have incomparable antecedents, preventing either implication.
- **major / conclusion-incompleteness:** The target fails to expose two required parts of the selected paper result and shifts them out of the theorem's delivered conclusions.
- **critical / derived-exactness-assumed:** The principal mathematical content of the paper theorem is assumed rather than translated.
- **major / missing-condition-7:** The translated statement cannot express the paper's generalization for arbitrary bases or its sufficient input condition.
- **major / algorithm-and-rounding-mismatch:** The statement describes a different selection model and does not establish correctness of the paper's algorithm.
- **major / floating-point-domain-erased:** The domain, format structure, and input representability requirements are not preserved.
- **major / logical-strength-incomparable:** Neither theorem statement implies the other under their stated binders and hypotheses.

## Semantic checklist

| Check | Direct | Round-trip |
|---|---|---|
| `S01` | `pass` | `pass` |
| `S02` | `fail` | `fail` |
| `S03` | `fail` | `fail` |
| `S04` | `fail` | `fail` |
| `S05` | `fail` | `fail` |
| `S06` | `fail` | `fail` |
| `S07` | `pass` | `fail` |
| `S08` | `pass` | `fail` |
| `S09` | `pass` | `pass` |
| `S10` | `fail` | `fail` |
| `S11` | `fail` | `fail` |
| `S12` | `fail` | `fail` |
| `S13` | `pass` | `pass` |
| `S14` | `pass` | `pass` |
| `S15` | `fail` | `fail` |
| `S16` | `fail` | `fail` |

## Dependency coverage

- Blind translator covered `20` dependencies (`0` hash-reused meanings); unclear: `none`.
- Direct judge covered `20` dependencies (`14` hash-reused interpretations); failing or unclear: `D005, D012`.

## Remaining uncertainties

No remaining uncertainties were recorded.

## Audit artifacts

- `paper_bencmark/highambench/tasks/P12/T2/faithfulness/agent_outputs/blind_translation.json` (`4d5cbece83c6f5d97976986f4d37894cd76e57ad76a04f85282db04f87d8ef30`)
- `paper_bencmark/highambench/tasks/P12/T2/faithfulness/agent_outputs/direct_judge.json` (`dfaf65b1701caa07f898a1e191aa701a4ca7ede77b3f593dc30e1cd0e49b546d`)
- `paper_bencmark/highambench/tasks/P12/T2/faithfulness/agent_outputs/paper_source_contract.json` (`c14eaa2ba1c25d2284fb972ef8a21fb4aa3b9f4953061dea7bb0ea5b382a6321`)
- `paper_bencmark/highambench/tasks/P12/T2/faithfulness/agent_outputs/roundtrip_judge.json` (`6fba70776af23ad14e4c57649165551e73cdb87d0f92bbe61cfe92ba8c9341ea`)
- `paper_bencmark/highambench/tasks/P12/T2/faithfulness/agent_outputs/source_contract.json` (`47144455f1f2ed0ce9e54c6f8e0d30526465d81d5686bbff28b50ff2075f0dcc`)
- `paper_bencmark/highambench/tasks/P12/T2/faithfulness/decision.json` (`9aedb858bc88697db6c7378d736823d03b3483d3aaea913c410868e5a7ca5cbe`)
- `paper_bencmark/highambench/tasks/P12/T2/faithfulness/inputs/blind_dependency_inventory.json` (`4f6061cda5daf81866ddde25ac898c1e418320e376eabe39461828d83e13be41`)
- `paper_bencmark/highambench/tasks/P12/T2/faithfulness/inputs/blind_dossier.md` (`2f81ddc7f6915ee4e168a1b1e3ef4258a7587ebe12f1ce1e3287b3e69e545d0b`)
- `paper_bencmark/highambench/tasks/P12/T2/faithfulness/inputs/blind_review_packet.md` (`2f81ddc7f6915ee4e168a1b1e3ef4258a7587ebe12f1ce1e3287b3e69e545d0b`)
- `paper_bencmark/highambench/tasks/P12/T2/faithfulness/inputs/declaration_dossier.md` (`ce68f7d8494fb5b1c1175de6b201ddd63c5a3e7ca2863b1a3ec47c9277102309`)
- `paper_bencmark/highambench/tasks/P12/T2/faithfulness/inputs/dependency_inventory.json` (`0b95e5fa47a5243f0803a420e6e1044294160fc42f6ce8435ad37028aafb4644`)
- `paper_bencmark/highambench/tasks/P12/T2/faithfulness/inputs/dependency_reuse_direct.json` (`559df889b80af0c4ee1618bbfd62c39e146443164b272c67313338a3398b47c8`)
- `paper_bencmark/highambench/tasks/P12/T2/faithfulness/inputs/direct_review_packet.md` (`8b5adc1e7aa2b4d2360a1ed6d3a619a8f12af0e6402e1f726c502e6ce2f966e6`)
- `paper_bencmark/highambench/tasks/P12/T2/faithfulness/inputs/paper_source_locator.json` (`515de0f8e7e7ece14b209a55702074a38799c848bbb9eb747b29a9993464642f`)
- `paper_bencmark/highambench/tasks/P12/T2/faithfulness/inputs/source_locator.json` (`f956480b09f86c030e7fd95f06f82ef07a23bd04ae6be5c2c9114d90cc0e7581`)
