# Faithfulness audit: P16-T3

- Classification: `not-faithful-different`
- Accepted as paper-faithful: `false`
- Adjudicated: `true`
- Target SHA-256: `4673ced6d389102473dc6b8f2307c084c43b89703cf9265030bd4f4cad6d0ad0`
- Paper SHA-256: `8010a50989428b09ea9f204875cd6cfde6c08c924beb40887a6921287605737a`

## Decision

The declaration correctly represents the finite real system, exact and computed quantities, Euclidean and Frobenius norms, backward and forward error definitions, useful contraction inequality direction, and first-order floor scales. The complete dossier nevertheless shows that it replaces the fixed-precision fully stored MGS-GMRES theorem with a nonuniform asymptotic statement over abstract runs whose crucial correction contractions are already assumptions. Because actual paper executions are not supplied by the Lean proposition and the paper does not cover all Lean certificate families, neither implication holds.

## Implications

- **Lean implies paper:** `no`. Lean proves per-index eventual recurrences only for filter-indexed runs already carrying abstract correction certificates. It does not establish that a fixed nonzero-precision fully stored MGS-GMRES execution supplies such a run, nor does it give one fixed precision at which every restart recurrence and attainable-floor conclusion hold.
- **Paper implies lean:** `no`. The paper's fixed-precision theorem does not establish the declaration's arbitrary-filter family statement, a t-uniform key dimension, exact shared P(n,n), or explicit per-index Big-O witnesses. It also does not assert the result for abstract certificate-bearing runs unrelated to MGS generation.

## Findings

- **critical / algorithm-linkage-and-assumed-core-result:** The declaration states an abstract certificate-composition result rather than Theorem 6.3 for the specified algorithm.
- **major / precision-and-quantifier-scope:** No single fixed nonzero precision parameter is guaranteed to satisfy all restart recurrences, so repeated geometric contraction to the stated floors cannot be recovered.
- **major / low-precision-operation-model:** The formal certificate does not preserve the selected algorithm's modular floating-point hypotheses.
- **major / constant-and-key-dimension-model:** The inner-dimension dependence and low-degree worst-case constant convention are materially changed.
- **note / higher-order-terms:** This choice is reasonable in isolation and is not a basis for rejection, but its exact filter semantics are stronger and more specific than the paper states.

## Semantic checklist

| Check | Direct | Round-trip |
|---|---|---|
| `S01` | `pass` | `pass` |
| `S02` | `fail` | `unclear` |
| `S03` | `fail` | `fail` |
| `S04` | `fail` | `unclear` |
| `S05` | `fail` | `fail` |
| `S06` | `fail` | `unclear` |
| `S07` | `pass` | `pass` |
| `S08` | `fail` | `unclear` |
| `S09` | `pass` | `pass` |
| `S10` | `fail` | `fail` |
| `S11` | `fail` | `unclear` |
| `S12` | `fail` | `pass` |
| `S13` | `pass` | `pass` |
| `S14` | `pass` | `unclear` |
| `S15` | `fail` | `unclear` |
| `S16` | `fail` | `unclear` |

## Dependency coverage

- Blind translator covered `120` dependencies (`0` hash-reused meanings); unclear: `D027, D037`.
- Direct judge covered `120` dependencies (`0` hash-reused interpretations); failing or unclear: `D001, D005, D007, D008, D010, D011, D013, D016, D017, D018, D019, D023, D027, D028, D029, D030, D031, D037, D038, D049, D064, D065`.

## Remaining uncertainties

- The paper does not uniquely formalize its discarded second-order terms, so the precise joint Big-O scale and filter semantics are not determined by the source.
- Theorem 6.3 suppresses the restart dependence of c(n,k_i), so the exact intended uniformization over varying key dimensions is not explicit.

## Audit artifacts

- `paper_bencmark/highambench/tasks/P16/T3/faithfulness/agent_outputs/adjudicator.json` (`5846938a59bd31bd2136cecb5de74d9d860f666e2e0f1a8c72f62270658eb0f4`)
- `paper_bencmark/highambench/tasks/P16/T3/faithfulness/agent_outputs/blind_translation.json` (`0bd6e5ca9d407db6a7059d88640098aa305a3468c80df1c65ac0f20f805c6f4c`)
- `paper_bencmark/highambench/tasks/P16/T3/faithfulness/agent_outputs/direct_judge.json` (`00fbbfd091f8311e375fab9bb8d0a3bf31dd0efc1ceb657330cbba658d82272d`)
- `paper_bencmark/highambench/tasks/P16/T3/faithfulness/agent_outputs/roundtrip_judge.json` (`a11a107ed4394d1a3acdb124867d42cdbe04bfe1d89733a7d846f39bdd9819e6`)
- `paper_bencmark/highambench/tasks/P16/T3/faithfulness/agent_outputs/source_contract.json` (`0aacd322891b6156deaab73e5155df812157665e0916cbbad007330470c048e9`)
- `paper_bencmark/highambench/tasks/P16/T3/faithfulness/decision.json` (`ec2a8cf7775648da503ea6e74b2d9e57f06acabd26c5d0e462adfce849a1c2b5`)
- `paper_bencmark/highambench/tasks/P16/T3/faithfulness/history/20260820T151927Z/agent_outputs/adjudicator.json` (`3025456eff60a9c9af18c6c1f9421d7be4d0ebde73e0cbf181457e53eddb6af6`)
- `paper_bencmark/highambench/tasks/P16/T3/faithfulness/history/20260820T151927Z/agent_outputs/blind_translation.json` (`e104660039d3b031f903f515e8f7296fde48c853ca781817491cbf15b54902a9`)
- `paper_bencmark/highambench/tasks/P16/T3/faithfulness/history/20260820T151927Z/agent_outputs/direct_judge.json` (`8eba7e89c400fdc521b17b82cbbb8b4a9f18019b1648440344a5821aadb01d0e`)
- `paper_bencmark/highambench/tasks/P16/T3/faithfulness/history/20260820T151927Z/agent_outputs/paper_source_contract.json` (`cc856c94ce22bcb89d018b431db65cfb6c20d25df7bb6aaeb660c48c42f5c886`)
- `paper_bencmark/highambench/tasks/P16/T3/faithfulness/history/20260820T151927Z/agent_outputs/roundtrip_judge.json` (`3d42a123faab7da7fb94e3706528e9e493c1bf3989a722611ec9157adfd3d770`)
- `paper_bencmark/highambench/tasks/P16/T3/faithfulness/history/20260820T151927Z/agent_outputs/source_contract.json` (`cae96a861777731d67ac9ede8d9bc2817755f7ed2ee01592e13d0cfbd8f9dc70`)
- `paper_bencmark/highambench/tasks/P16/T3/faithfulness/history/20260820T151927Z/decision.json` (`a9f3751fafb151aea9974a1e88cc94c4e6f0a4a2f7f5d6fb024c0462c5c601e1`)
- `paper_bencmark/highambench/tasks/P16/T3/faithfulness/history/20260820T151927Z/inputs/blind_dependency_inventory.json` (`0f77a178b783d81dd3d4e10f286135cb7e3daa777bf968f3a643c7b985e240d7`)
- `paper_bencmark/highambench/tasks/P16/T3/faithfulness/history/20260820T151927Z/inputs/blind_dossier.md` (`594676c557447428fa04d3999eb96b85169e0039cd6882467b539ffe7cb8fe48`)
- `paper_bencmark/highambench/tasks/P16/T3/faithfulness/history/20260820T151927Z/inputs/blind_review_packet.md` (`594676c557447428fa04d3999eb96b85169e0039cd6882467b539ffe7cb8fe48`)
- `paper_bencmark/highambench/tasks/P16/T3/faithfulness/history/20260820T151927Z/inputs/declaration_dossier.md` (`60a799365b1773519458d839c1ee04d267ddfb309acbea6ae400e8365e3a14e0`)
- `paper_bencmark/highambench/tasks/P16/T3/faithfulness/history/20260820T151927Z/inputs/dependency_inventory.json` (`2749561c9343fb18101cd6f4dc1c9029ff9d100be9a6ee78b66f47ebd722ee4d`)
- `paper_bencmark/highambench/tasks/P16/T3/faithfulness/history/20260820T151927Z/inputs/dependency_reuse_direct.json` (`acb3838c216564c282ba4e3e4487840de14d506f28f7b10501c4ffe625ca5064`)
- `paper_bencmark/highambench/tasks/P16/T3/faithfulness/history/20260820T151927Z/inputs/direct_review_packet.md` (`4d621852b9a906d1bafa361b163ab305a87c034b648cac359603affbdbac66ad`)
- `paper_bencmark/highambench/tasks/P16/T3/faithfulness/history/20260820T151927Z/inputs/paper_source_locator.json` (`29399d42dec8e4d771178436cda1303a77490d8820b032eb370ddffe5e202bd7`)
- `paper_bencmark/highambench/tasks/P16/T3/faithfulness/history/20260820T151927Z/inputs/source_locator.json` (`d1ae628acc118c8d298e3add396694d62b669089f91e02000ae0d849f48bade6`)
- `paper_bencmark/highambench/tasks/P16/T3/faithfulness/inputs/blind_dependency_inventory.json` (`b6bc214f974565af989b50884268797ea4e3dbde928ee63e3f3860c5f3c0cde9`)
- `paper_bencmark/highambench/tasks/P16/T3/faithfulness/inputs/blind_dossier.md` (`6fe713ab7c72ecb9e9d96cfd28523943aac19a7dea1e011c6641c908ee9ed56e`)
- `paper_bencmark/highambench/tasks/P16/T3/faithfulness/inputs/blind_review_packet.md` (`6fe713ab7c72ecb9e9d96cfd28523943aac19a7dea1e011c6641c908ee9ed56e`)
- `paper_bencmark/highambench/tasks/P16/T3/faithfulness/inputs/declaration_dossier.md` (`3e8dc6ae9aa80638d51d67a6a5840d6e164eeae5a3cd002228c4900381513434`)
- `paper_bencmark/highambench/tasks/P16/T3/faithfulness/inputs/dependency_inventory.json` (`d2d487d1aa68942f4fb13d4862bab45ad02feda6ecd70f4e1f197563478e40d9`)
- `paper_bencmark/highambench/tasks/P16/T3/faithfulness/inputs/direct_review_packet.md` (`e3172064dd23626fc0f280a01ae29a21fc2f463c053dfcde702bf9cc29e57043`)
- `paper_bencmark/highambench/tasks/P16/T3/faithfulness/inputs/source_locator.json` (`dc203ccec366dac29723aa263699667cf7ecd81e9f076407eea37d3d5e6531f8`)
