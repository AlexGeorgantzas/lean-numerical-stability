# Faithfulness audit: P16-T2

- Classification: `not-faithful-different`
- Accepted as paper-faithful: `false`
- Adjudicated: `true`
- Target SHA-256: `34afa46e62ca706b5e59c8868da30b3304cda19e8b10da2f2b8fd99c5fa67af0`
- Paper SHA-256: `8010a50989428b09ea9f204875cd6cfde6c08c924beb40887a6921287605737a`

## Decision

Primary evidence confirms four distinct layers: (4.18) is an exact algebraic identity; (4.15) is a qualitative lesssim recurrence; its proof uses an unstated qualitative iterate-norm comparison; and Lean replaces that comparison by exact hxmono to obtain an exact <= conclusion. The resulting Lean theorem is mathematically coherent and nonvacuous. Nonsingularity, b != 0, parameter smallness, and w/omega nonnegativity are unnecessary for its exact conditional algebra, so their omission broadens its domain, sometimes nonvacuously. Exact hxmono simultaneously narrows the domain relative to the paper, while exact <= strengthens the conclusion relative to lesssim. These mixed changes make the target neither faithfully stronger nor merely weaker but a logically different repaired theorem. The inlined dependency definitions independently confirm the intended real matrix, matrix-vector product, Euclidean norm, Frobenius norm, and residual semantics; dependency-reuse records were treated only as provenance.

## Implications

- **Lean implies paper:** `no`. Even granting that an exact <= bound implies the paper's qualitative lesssim bound on a shared instance, Lean applies only when exact hxmono holds. The published lemma does not state that condition, and its proof uses only an unstated qualitative iterate-norm comparison. Thus Lean does not cover every source-admissible step. Its broader treatment of singular A, zero b, large epsilon values, and signed w or omega does not remove this applicability restriction.
- **Paper implies lean:** `no`. The paper's qualitative lesssim recurrence, with unspecified omitted second-order terms, does not entail an unqualified exact <= recurrence. Moreover, the paper is confined to nonsingular A, nonzero b, small nonnegative epsilon parameters, and nonnegative w and omega, while Lean asserts its conditional theorem for arbitrary A and b and without the latter restrictions. The source therefore does not establish the complete Lean statement.

## Findings

- **critical / relation-strength-and-higher-order-terms:** The central recurrence has been changed from a qualitative first-order estimate into an exact mathematical inequality.
- **major / exact-iterate-norm-repair:** This exact hypothesis repairs the derivation of the exact bound but narrows the admissible step domain. The stronger conclusion is therefore not a faithful stronger theorem.
- **major / omitted-source-domain-conditions:** Lean generalizes the exact algebraic result to singular systems, zero right-hand sides, large error parameters, and some satisfiable signed-coefficient cases. These extensions make the domains incomparable with the source domain rather than making the target merely weaker.
- **note / exact-composition-identity:** There is no sign, residual-definition, or exact-versus-computed mismatch in the composition identity. Its exactness does not transfer to the paper's subsequent qualitative recurrence.
- **note / nonvacuity:** Lean's repaired exact theorem has genuine nonvacuous content, but that does not overcome its restricted hxmono domain or make it a faithful strengthening.

## Semantic checklist

| Check | Direct | Round-trip |
|---|---|---|
| `S01` | `pass` | `pass` |
| `S02` | `pass` | `fail` |
| `S03` | `pass` | `pass` |
| `S04` | `fail` | `fail` |
| `S05` | `pass` | `fail` |
| `S06` | `pass` | `pass` |
| `S07` | `pass` | `pass` |
| `S08` | `pass` | `fail` |
| `S09` | `pass` | `pass` |
| `S10` | `pass` | `pass` |
| `S11` | `fail` | `pass` |
| `S12` | `fail` | `fail` |
| `S13` | `pass` | `pass` |
| `S14` | `fail` | `fail` |
| `S15` | `fail` | `fail` |
| `S16` | `pass` | `fail` |

## Dependency coverage

- Blind translator covered `42` dependencies (`0` hash-reused meanings); unclear: `none`.
- Direct judge covered `42` dependencies (`40` hash-reused interpretations); failing or unclear: `D012, D019`.

## Remaining uncertainties

- The paper assigns no numerical constant or explicit remainder to lesssim or to the qualitative iterate-norm comparison. Consequently, the quantitative size of the gap between (4.15) and Lean's exact bound cannot be recovered, although the logical mismatch and final classification are determinate.

## Audit artifacts

- `paper_bencmark/highambench/tasks/P16/T2/faithfulness/agent_outputs/adjudicator.json` (`1b8959d2395c14cb7189660f1ae067008578d70549c4d3a411699582e9bdadeb`)
- `paper_bencmark/highambench/tasks/P16/T2/faithfulness/agent_outputs/blind_translation.json` (`5c9a00047f3cb9813163120f1eee6b33b1971674bf133751c7e087fe00834548`)
- `paper_bencmark/highambench/tasks/P16/T2/faithfulness/agent_outputs/direct_judge.json` (`b047420c779d23bb80c30034c2270b51ec4f2f4ad00836f75ed532cfe8bf83bf`)
- `paper_bencmark/highambench/tasks/P16/T2/faithfulness/agent_outputs/paper_source_contract.json` (`cc856c94ce22bcb89d018b431db65cfb6c20d25df7bb6aaeb660c48c42f5c886`)
- `paper_bencmark/highambench/tasks/P16/T2/faithfulness/agent_outputs/roundtrip_judge.json` (`7d93fca173362bd374eb788da4b1ce2a5e7520ac69fe8c0e001949691c975870`)
- `paper_bencmark/highambench/tasks/P16/T2/faithfulness/agent_outputs/source_contract.json` (`e1d181bd77d7b8c9b9b292be1fc2276b17a9554977b9abf781fd20cb5c26c5de`)
- `paper_bencmark/highambench/tasks/P16/T2/faithfulness/decision.json` (`d03f965dfd639d090cf8c87646d766d2ee4ce1099816948e5b5fe39973f82104`)
- `paper_bencmark/highambench/tasks/P16/T2/faithfulness/inputs/blind_dependency_inventory.json` (`16dc7b65cb4bd6f0f76fa5585c49f0979dba60b163f8cf1dc3c9bd3e2f543964`)
- `paper_bencmark/highambench/tasks/P16/T2/faithfulness/inputs/blind_dossier.md` (`949361f0cf8c550acb646de63287bb6f07aea3530ba6be2b9cb5775b3fe6de59`)
- `paper_bencmark/highambench/tasks/P16/T2/faithfulness/inputs/blind_review_packet.md` (`949361f0cf8c550acb646de63287bb6f07aea3530ba6be2b9cb5775b3fe6de59`)
- `paper_bencmark/highambench/tasks/P16/T2/faithfulness/inputs/declaration_dossier.md` (`4d2a699808e29d897b8dde89f2702935a390164f78f4902d13dc2acd3950f058`)
- `paper_bencmark/highambench/tasks/P16/T2/faithfulness/inputs/dependency_inventory.json` (`3c886a74cbb732dc7fdf8c2cc18430a344e642faba3cc73e9653630161c9e3bb`)
- `paper_bencmark/highambench/tasks/P16/T2/faithfulness/inputs/dependency_reuse_direct.json` (`f3914a20e8ced9b6bf1423ed488bddad18f4a4e2e9fa38a43312d7af5a141c8f`)
- `paper_bencmark/highambench/tasks/P16/T2/faithfulness/inputs/direct_review_packet.md` (`d37eb5e7721b942f5a744027cbbd07717b816fc114c92affb696cfecd27e7825`)
- `paper_bencmark/highambench/tasks/P16/T2/faithfulness/inputs/paper_source_locator.json` (`29399d42dec8e4d771178436cda1303a77490d8820b032eb370ddffe5e202bd7`)
- `paper_bencmark/highambench/tasks/P16/T2/faithfulness/inputs/source_locator.json` (`fdd20bedee03410eed50151bee4551892c4f79ae6d8fe62492a246d75b1eb45a`)
