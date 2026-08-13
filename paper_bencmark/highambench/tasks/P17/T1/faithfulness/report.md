# Faithfulness audit: P17-T1

- Classification: `not-faithful-weaker`
- Accepted as paper-faithful: `false`
- Adjudicated: `true`
- Target SHA-256: `003a394c8a361bdbad3c41d5ee8971d4be789afd1f7d64aa1044c7055cb1e28e`
- Paper SHA-256: `df1ce5dd33285adfcffc6a4c7ab94f9604b46739cb848c6cbb5f997e8fac597d`

## Decision

The endpoint powers, exponent n, inequality directions, and conjunction agree, but the mathematical object and assumptions do not. The paper claim structurally yields the declaration through constant random variables, while the declaration cannot recover the paper's conditional stochastic statement. The target is satisfiable and nontrivial, yet its apparent pathwise strength comes solely from stronger assumptions and reduced applicability. Therefore the compatible implication pattern is lean-to-paper no and paper-to-lean yes, giving not-faithful-weaker and accepted=false.

## Implications

- **Lean implies paper:** `no`. The Lean declaration says nothing about random delta values that are controlled only through bounded conditional means beta. It cannot derive an expectation-after-product result or the SR_{p,r} specialization. The explicit two-outcome counterexample also shows that the paper's literal abstract conclusion does not follow from its printed hypotheses, while its unbounded delta_1 lies outside the declaration's reduced domain.
- **Paper implies lean:** `yes`. At the level of the paper's claimed theorem schema, every Lean instance with n>=1 and 0<B<=1 embeds nonvacuously into a singleton probability space by setting paper delta_k=paper beta_k=Lean delta(k-1). Expectations and conditional expectations then equal those constants, the beta bound is exactly the Lean delta bound, and the paper conclusion becomes the Lean product bound. The n=0 and B=0 cases follow directly from the empty-product and zero-perturbation identities.

## Findings

- **critical / probabilistic-conclusion-removed:** The declaration proves an interval-product lemma, not the paper's accumulated stochastic-bias envelope.
- **critical / wrong-error-variable-and-hypotheses:** The declaration applies only to a restricted deterministic regime and cannot model the paper's random errors with larger pathwise excursions.
- **major / limited-precision-rounding-linkage-omitted:** Using B=u_{p+r} would require the SR output errors themselves to be bounded by u_{p+r}, which the paper does not assert.
- **major / paper-positivity-gap:** The abstract paper theorem is not valid literally as printed, although its intended SR specialization can supply the missing positivity.
- **minor / boundary-domain-changes:** These elementary boundary changes further confirm specialization rather than equivalence.

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
| `S14` | `pass` | `pass` |
| `S15` | `fail` | `fail` |
| `S16` | `pass` | `pass` |

## Dependency coverage

- Blind translator covered `28` dependencies (`0` hash-reused meanings); unclear: `none`.
- Direct judge covered `28` dependencies (`0` hash-reused interpretations); failing or unclear: `D004, D011, D014, D025`.

## Remaining uncertainties

- The PDF does not specify the intended repair to the abstract Theorem 3.6: it could explicitly require nonnegative accumulated factors and B<=1, or restrict the theorem to actual SR_{p,r} errors that inherit those properties. Either repair leaves the declaration unfaithful because it still omits expectation, beta variables, conditional means, and the radius B=u_{p+r}.

## Audit artifacts

- `paper_bencmark/highambench/tasks/P17/T1/faithfulness/agent_outputs/adjudicator.json` (`51d78ddc48bc903aaab5b871acd07a255a5d2ff80105f8c24aa3270917b2561d`)
- `paper_bencmark/highambench/tasks/P17/T1/faithfulness/agent_outputs/blind_translation.json` (`1f2d06c226b818dc237beda4b661813cddb1d6590e7ec405c942edf3545be72a`)
- `paper_bencmark/highambench/tasks/P17/T1/faithfulness/agent_outputs/direct_judge.json` (`46bd2c06c77c05f6b16c59ac1e695a525148308428cffbdfa6ac34cf437f6ed1`)
- `paper_bencmark/highambench/tasks/P17/T1/faithfulness/agent_outputs/paper_source_contract.json` (`5856f4d88e51aeb1df8e36f051f77e90c96a2896bb707ed0186c2f74cf1ebc0b`)
- `paper_bencmark/highambench/tasks/P17/T1/faithfulness/agent_outputs/roundtrip_judge.json` (`be29887fd5d53b00b978b6891327a4695445696f2c8bd1528f9407154231ac99`)
- `paper_bencmark/highambench/tasks/P17/T1/faithfulness/agent_outputs/source_contract.json` (`820c34c52160f610645afc98d542084852ce6f41a4219d73a6d2bbe7d4c2c8fa`)
- `paper_bencmark/highambench/tasks/P17/T1/faithfulness/decision.json` (`4e8029293986a6a4cdee2e3ea8c3dda00a4c03400bfb66d8f1a1a943aa18bfd3`)
- `paper_bencmark/highambench/tasks/P17/T1/faithfulness/inputs/blind_dependency_inventory.json` (`5415ad0e0c4adf83c894c54596a6d280b9faff238046b4ee4654236dfd2f8ac8`)
- `paper_bencmark/highambench/tasks/P17/T1/faithfulness/inputs/blind_dossier.md` (`89ab60844d77ed45208b548ecf912778cafd9cf9b66d54cea35db01af7a3b61b`)
- `paper_bencmark/highambench/tasks/P17/T1/faithfulness/inputs/blind_review_packet.md` (`89ab60844d77ed45208b548ecf912778cafd9cf9b66d54cea35db01af7a3b61b`)
- `paper_bencmark/highambench/tasks/P17/T1/faithfulness/inputs/declaration_dossier.md` (`0e87e49ff1f7f9d1620ba1e42d7f967fcc0fb6315c85e4d34fb960d6b9e22512`)
- `paper_bencmark/highambench/tasks/P17/T1/faithfulness/inputs/dependency_inventory.json` (`5415ad0e0c4adf83c894c54596a6d280b9faff238046b4ee4654236dfd2f8ac8`)
- `paper_bencmark/highambench/tasks/P17/T1/faithfulness/inputs/direct_review_packet.md` (`aa273787224e8f562a342905f6196eaf6b3443ff420f9d3c54c47e76344444d8`)
- `paper_bencmark/highambench/tasks/P17/T1/faithfulness/inputs/paper_source_locator.json` (`7b6e846a522a4293bd50e70522a875cdc8dd30515338efc2e70d99739bcb7161`)
- `paper_bencmark/highambench/tasks/P17/T1/faithfulness/inputs/source_locator.json` (`ffb5a6823f320a0c5f61c22a56f06d8cce93918509f725de65564f41d0715356`)
