# Faithfulness audit: P18-T2

- Classification: `not-faithful-weaker`
- Accepted as paper-faithful: `false`
- Adjudicated: `true`
- Target SHA-256: `85c598e55eecc695203ffa1b9b6aabe2b1b261c4a93f13a5c142128a917160b1`
- Paper SHA-256: `b18628ffc348d7aeec2da02efb989b6e012f0b0fae09b27fbff735bb8a5877cd`

## Decision

The SHA-verified paper states a conditional asymptotic global-error envelope for a specific corrected mixed-precision implicit midpoint method. The complete formal dossier instead defines an exact arbitrary vector combination and proves its Euclidean triangle bound. The PDF's omissions concerning norm and state dimension create genuine compatibility uncertainties, but only about unsupported modeling choices; they do not establish contradictions and do not affect the complete implications. Lean cannot imply the paper result, while the paper implies Lean only because Lean is independently valid. The consistent classification is therefore not-faithful-weaker.

## Implications

- **Lean implies paper:** `no`. The Lean target contains no F, F^epsilon, stages, update, numerical trajectory, global error, stability assumption, approximation hypothesis, asymptotic limit, or hidden constants. Its exact norm inequality cannot establish the paper's conditional global-error result for method (4.1).
- **Paper implies lean:** `yes`. The complete definitions reduce the target to ||h^2 scheme + epsilon h^2 perturbation||_2 <= h^2 (||scheme||_2 + |epsilon| ||perturbation||_2). Since h^2 is nonnegative, Euclidean homogeneity and the triangle inequality prove this for every finite n and all inputs, independently of the paper. Thus the implication is logically valid but carries no substantive paper content; the unresolved source norm and dimension do not affect it.

## Findings

- **critical / algorithm-linkage-and-error-notion:** The declaration proves no property of the corrected implicit midpoint computation or its global numerical error.
- **major / asymptotic-scope-and-hypotheses:** Stability, operator approximation, small-step asymptotics, hidden constants, and local-to-global accumulation are absent.
- **major / unsupported-norm-specialization:** The norm choice is not source-supported, although the PDF supplies no evidence that it is contradictory.
- **minor / unsupported-dimension-model:** The dimensional scope cannot be validated from the source, but this does not repair or worsen the decisive algorithmic mismatch.
- **note / independent-validity:** Its paper-independent validity supports paper_implies_lean = yes, but it is strength about an unrelated synthetic quantity rather than the paper's numerical method.

## Semantic checklist

| Check | Direct | Round-trip |
|---|---|---|
| `S01` | `pass` | `pass` |
| `S02` | `fail` | `fail` |
| `S03` | `fail` | `fail` |
| `S04` | `fail` | `fail` |
| `S05` | `fail` | `fail` |
| `S06` | `pass` | `pass` |
| `S07` | `fail` | `fail` |
| `S08` | `fail` | `fail` |
| `S09` | `fail` | `unclear` |
| `S10` | `fail` | `fail` |
| `S11` | `fail` | `fail` |
| `S12` | `fail` | `fail` |
| `S13` | `fail` | `fail` |
| `S14` | `fail` | `fail` |
| `S15` | `pass` | `unclear` |
| `S16` | `fail` | `fail` |

## Dependency coverage

- Blind translator covered `30` dependencies (`0` hash-reused meanings); unclear: `none`.
- Direct judge covered `30` dependencies (`3` hash-reused interpretations); failing or unclear: `D001, D002, D003, D004, D005, D010, D017, D026, D028`.

## Remaining uncertainties

- The PDF does not decide whether the theoretical or plotted Error uses the Euclidean norm; Lean's choice is unsupported but not contradicted.
- The PDF does not specify the theorem-level state space or dimension, so it does not decide whether arbitrary finite real dimensions, particularly n = 0, are intended.

## Audit artifacts

- `paper_bencmark/highambench/tasks/P18/T2/faithfulness/agent_outputs/adjudicator.json` (`56159e26ef99045d071e312b79c863811b01dba8a03d9763234d7e4386602677`)
- `paper_bencmark/highambench/tasks/P18/T2/faithfulness/agent_outputs/blind_translation.json` (`1eebad43ec9d5ea0ac6b487bd941564cb5a663c3a14f55f789e80bfd5f7412b4`)
- `paper_bencmark/highambench/tasks/P18/T2/faithfulness/agent_outputs/direct_judge.json` (`3ad35386f880b095eac20d57d6aa9e2af853bfc7073ee86c6c361c7599a7af46`)
- `paper_bencmark/highambench/tasks/P18/T2/faithfulness/agent_outputs/paper_source_contract.json` (`6de2cebc98667558bfb276c01a2286c46a88edff824491fda40799511abf8891`)
- `paper_bencmark/highambench/tasks/P18/T2/faithfulness/agent_outputs/roundtrip_judge.json` (`817604d2424fc870ac317e480f7851516865d9d4e80ad91a15a23e00acefd389`)
- `paper_bencmark/highambench/tasks/P18/T2/faithfulness/agent_outputs/source_contract.json` (`ddd7d68c331a25f5a20c9bdeb6bc46be6be140314bb6da08a1c7060256893f14`)
- `paper_bencmark/highambench/tasks/P18/T2/faithfulness/decision.json` (`893204dcdc7fb89bedecaf7bc47593110d34c96922e02f86e4a1d548cf32de15`)
- `paper_bencmark/highambench/tasks/P18/T2/faithfulness/inputs/blind_dependency_inventory.json` (`8d80b204e9589819269851852b1fc39d278fb5a8998c2c77f54fc3213729309d`)
- `paper_bencmark/highambench/tasks/P18/T2/faithfulness/inputs/blind_dossier.md` (`e481dec0860548d72ab6710531ebdd290f51a62bde10f877ca2515aabcbacd2a`)
- `paper_bencmark/highambench/tasks/P18/T2/faithfulness/inputs/blind_review_packet.md` (`e481dec0860548d72ab6710531ebdd290f51a62bde10f877ca2515aabcbacd2a`)
- `paper_bencmark/highambench/tasks/P18/T2/faithfulness/inputs/declaration_dossier.md` (`7318322c14bff24bd9fcf1873634299118f2eabf139d40f765e2f7e4d9efa2d7`)
- `paper_bencmark/highambench/tasks/P18/T2/faithfulness/inputs/dependency_inventory.json` (`9ff81ac0f0f1b0604922c2e0a3314eca1aaed1ecd0d8724fb16107397daa8532`)
- `paper_bencmark/highambench/tasks/P18/T2/faithfulness/inputs/dependency_reuse_direct.json` (`ad044f09607371de6ed2daf6746d04101a044bd13d1fa62afac1e468796ce6a4`)
- `paper_bencmark/highambench/tasks/P18/T2/faithfulness/inputs/direct_review_packet.md` (`a46954508d1f648f046baac0aeda4c3851f83c8497ca6f2e5fcdf36d5bbb9219`)
- `paper_bencmark/highambench/tasks/P18/T2/faithfulness/inputs/paper_source_locator.json` (`ba129952837b9f0f76f04aaf15df9d09fbc4e140b4fac00813259e514dd1ea6e`)
- `paper_bencmark/highambench/tasks/P18/T2/faithfulness/inputs/source_locator.json` (`d7f48453f74dd4d0901641bf3b21e3b4bf43b5a674d4e24862ae98f476012d47`)
