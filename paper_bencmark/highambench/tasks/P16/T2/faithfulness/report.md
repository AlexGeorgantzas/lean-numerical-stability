# Faithfulness audit: P16-T2

- Classification: `not-faithful-weaker`
- Accepted as paper-faithful: `false`
- Adjudicated: `true`
- Target SHA-256: `1c582176b5d6f0ea639794f09f49d14c1343fed97e7e030bd8cc1c506739809a`
- Paper SHA-256: `8010a50989428b09ea9f204875cd6cfde6c08c924beb40887a6921287605737a`

## Decision

The verified PDF hash is 8010a50989428b09ea9f204875cd6cfde6c08c924beb40887a6921287605737a. The declaration preserves the independent branch's matrix and vector domains, residual sign, computed quantities, Euclidean and Frobenius norms, complete correction bound, coefficients, and exact current/next placements. Its exact (4.18) conjunct is redundant. The decisive mismatch is scope: the paper states a fixed-iteration recurrence with given small parameters, whereas the Lean theorem concerns families whose epsilon functions converge to zero and produces only an eventual estimate under an explicit asymptotic iterate-comparison premise. The chosen filter-level O(scale^2) semantics is not compelled by the paper, but the paper's exact pre-lesssim inequality proves it under those added Lean premises. Therefore the paper implies the restricted Lean corollary, the Lean theorem does not imply the full paper statement, and the correct classification is not-faithful-weaker rather than faithful-stronger or undetermined.

## Implications

- **Lean implies paper:** `no`. The Lean theorem cannot be specialized to arbitrary fixed small positive epsilon_r and epsilon_u: constant positive epsilon functions violate the required convergence to zero on a nonbottom filter, and an isolated occurrence is not covered by an eventual conclusion. Thus it does not establish the paper's fixed-iteration statement.
- **Paper implies lean:** `yes`. For a family satisfying the Lean premises, the paper's exact identity and exact inequality following (4.18) apply pointwise. D020 additionally supplies an eventual iterate comparison with q=O(scale^2). Since epsilonR tends to zero it is eventually bounded, so epsilonR*||A||_F*q remains O(scale^2), yielding D014's eventual recurrence. The exact conjunct follows algebraically from the same residual and update equations.

## Findings

- **major / fixed-parameter-applicability:** A substantive class of paper instances cannot be obtained from the Lean theorem, making the target weaker through reduced applicability.
- **major / higher-order-semantics:** This is a defensible conditional formalization but is not equivalent to semantics established by the source.
- **major / additional-hypothesis:** The formal theorem repairs the derivation by narrowing its domain; the added premise cannot count as genuine strengthening.
- **minor / binder-and-index-model:** Current-versus-next algebra remains correct, but the declaration does not directly represent the paper's fixed iteration with globally given operation parameters.
- **note / redundant-exact-conclusion:** It adds no independent strength and does not affect the classification.

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
| `S08` | `pass` | `pass` |
| `S09` | `pass` | `pass` |
| `S10` | `pass` | `fail` |
| `S11` | `pass` | `fail` |
| `S12` | `pass` | `unclear` |
| `S13` | `pass` | `pass` |
| `S14` | `pass` | `unclear` |
| `S15` | `pass` | `fail` |
| `S16` | `pass` | `pass` |

## Dependency coverage

- Blind translator covered `77` dependencies (`0` hash-reused meanings); unclear: `none`.
- Direct judge covered `77` dependencies (`0` hash-reused interpretations); failing or unclear: `none`.

## Remaining uncertainties

- The PDF does not provide a unique quantitative interpretation of lesssim, so it remains uncertain which limiting variable, scale, and uniformity conditions the authors would endorse.
- The notation epsilon_r, epsilon_u much less than 1 has no numerical threshold in the cited passage; the paper therefore does not determine a precise admissible fixed-parameter range.

## Audit artifacts

- `paper_bencmark/highambench/tasks/P16/T2/faithfulness/agent_outputs/adjudicator.json` (`43141fb2239d34a2e0064bdd09f768ede1b3e0702244950e3f0d43e260e4cc08`)
- `paper_bencmark/highambench/tasks/P16/T2/faithfulness/agent_outputs/blind_translation.json` (`63194d60f21475463b0c4358cd4fc69a078fb1b5be1601e529776b632a4dea29`)
- `paper_bencmark/highambench/tasks/P16/T2/faithfulness/agent_outputs/direct_judge.json` (`ef6dfc67ac776b4ff8a54ef091a4f298665c89d4bb3d95dba9793f4a899ec7ff`)
- `paper_bencmark/highambench/tasks/P16/T2/faithfulness/agent_outputs/roundtrip_judge.json` (`6a67a2c438891814319f2bec3695292eaffdd8c47306877bcc8d5454597e0118`)
- `paper_bencmark/highambench/tasks/P16/T2/faithfulness/agent_outputs/source_contract.json` (`a74af040321d52231a9682211dbde11bf1b7ce6ad7cc0e5f27607fe91f3b761f`)
- `paper_bencmark/highambench/tasks/P16/T2/faithfulness/decision.json` (`2e275776737dce1fde4ff0c60fc6cd14513c0dbf4afc0b6c8d860d7c8a5e2d20`)
- `paper_bencmark/highambench/tasks/P16/T2/faithfulness/history/20260820T132415Z/agent_outputs/adjudicator.json` (`1b8959d2395c14cb7189660f1ae067008578d70549c4d3a411699582e9bdadeb`)
- `paper_bencmark/highambench/tasks/P16/T2/faithfulness/history/20260820T132415Z/agent_outputs/blind_translation.json` (`5c9a00047f3cb9813163120f1eee6b33b1971674bf133751c7e087fe00834548`)
- `paper_bencmark/highambench/tasks/P16/T2/faithfulness/history/20260820T132415Z/agent_outputs/direct_judge.json` (`b047420c779d23bb80c30034c2270b51ec4f2f4ad00836f75ed532cfe8bf83bf`)
- `paper_bencmark/highambench/tasks/P16/T2/faithfulness/history/20260820T132415Z/agent_outputs/paper_source_contract.json` (`cc856c94ce22bcb89d018b431db65cfb6c20d25df7bb6aaeb660c48c42f5c886`)
- `paper_bencmark/highambench/tasks/P16/T2/faithfulness/history/20260820T132415Z/agent_outputs/roundtrip_judge.json` (`7d93fca173362bd374eb788da4b1ce2a5e7520ac69fe8c0e001949691c975870`)
- `paper_bencmark/highambench/tasks/P16/T2/faithfulness/history/20260820T132415Z/agent_outputs/source_contract.json` (`e1d181bd77d7b8c9b9b292be1fc2276b17a9554977b9abf781fd20cb5c26c5de`)
- `paper_bencmark/highambench/tasks/P16/T2/faithfulness/history/20260820T132415Z/decision.json` (`d03f965dfd639d090cf8c87646d766d2ee4ce1099816948e5b5fe39973f82104`)
- `paper_bencmark/highambench/tasks/P16/T2/faithfulness/history/20260820T132415Z/inputs/blind_dependency_inventory.json` (`16dc7b65cb4bd6f0f76fa5585c49f0979dba60b163f8cf1dc3c9bd3e2f543964`)
- `paper_bencmark/highambench/tasks/P16/T2/faithfulness/history/20260820T132415Z/inputs/blind_dossier.md` (`949361f0cf8c550acb646de63287bb6f07aea3530ba6be2b9cb5775b3fe6de59`)
- `paper_bencmark/highambench/tasks/P16/T2/faithfulness/history/20260820T132415Z/inputs/blind_review_packet.md` (`949361f0cf8c550acb646de63287bb6f07aea3530ba6be2b9cb5775b3fe6de59`)
- `paper_bencmark/highambench/tasks/P16/T2/faithfulness/history/20260820T132415Z/inputs/declaration_dossier.md` (`4d2a699808e29d897b8dde89f2702935a390164f78f4902d13dc2acd3950f058`)
- `paper_bencmark/highambench/tasks/P16/T2/faithfulness/history/20260820T132415Z/inputs/dependency_inventory.json` (`3c886a74cbb732dc7fdf8c2cc18430a344e642faba3cc73e9653630161c9e3bb`)
- `paper_bencmark/highambench/tasks/P16/T2/faithfulness/history/20260820T132415Z/inputs/dependency_reuse_direct.json` (`f3914a20e8ced9b6bf1423ed488bddad18f4a4e2e9fa38a43312d7af5a141c8f`)
- `paper_bencmark/highambench/tasks/P16/T2/faithfulness/history/20260820T132415Z/inputs/direct_review_packet.md` (`d37eb5e7721b942f5a744027cbbd07717b816fc114c92affb696cfecd27e7825`)
- `paper_bencmark/highambench/tasks/P16/T2/faithfulness/history/20260820T132415Z/inputs/paper_source_locator.json` (`29399d42dec8e4d771178436cda1303a77490d8820b032eb370ddffe5e202bd7`)
- `paper_bencmark/highambench/tasks/P16/T2/faithfulness/history/20260820T132415Z/inputs/source_locator.json` (`fdd20bedee03410eed50151bee4551892c4f79ae6d8fe62492a246d75b1eb45a`)
- `paper_bencmark/highambench/tasks/P16/T2/faithfulness/history/20260821T225718Z/agent_outputs/adjudicator.json` (`e7ed62ab3d6cbd739727ee5cd9a17405b39d8345a271083cc16ce0693047ac3b`)
- `paper_bencmark/highambench/tasks/P16/T2/faithfulness/history/20260821T225718Z/agent_outputs/blind_translation.json` (`612ada7e02c1017721b3f271ab06420c1c7d2fe954b21f907819a2c66db71707`)
- `paper_bencmark/highambench/tasks/P16/T2/faithfulness/history/20260821T225718Z/agent_outputs/direct_judge.json` (`e26184c1056721914d3c7b6955a693cef4aad8da10886602a66649d8df2fb545`)
- `paper_bencmark/highambench/tasks/P16/T2/faithfulness/history/20260821T225718Z/agent_outputs/roundtrip_judge.json` (`b72a1a340ebf6c0568175ec2e32a0bdedb5bb76225d3c76c58b90066de3d23ec`)
- `paper_bencmark/highambench/tasks/P16/T2/faithfulness/history/20260821T225718Z/agent_outputs/source_contract.json` (`4e27507df9d886c93512cab4f3bc5ad1e36c206681d1cdc4ee8f13318d544972`)
- `paper_bencmark/highambench/tasks/P16/T2/faithfulness/history/20260821T225718Z/decision.json` (`1e161efa050652c78f63b6ca6a048d1d7e96ba75cf201074d916539cb97e0460`)
- `paper_bencmark/highambench/tasks/P16/T2/faithfulness/history/20260821T225718Z/inputs/blind_dependency_inventory.json` (`cc4db05db44a27ceb5798713819fa836637982f8bad6578aa398044b59eeaff9`)
- `paper_bencmark/highambench/tasks/P16/T2/faithfulness/history/20260821T225718Z/inputs/blind_dossier.md` (`070aa76520bd211b5d085872c47d451382cc9b5ee77520763055ffd0ca07b2ce`)
- `paper_bencmark/highambench/tasks/P16/T2/faithfulness/history/20260821T225718Z/inputs/blind_review_packet.md` (`070aa76520bd211b5d085872c47d451382cc9b5ee77520763055ffd0ca07b2ce`)
- `paper_bencmark/highambench/tasks/P16/T2/faithfulness/history/20260821T225718Z/inputs/declaration_dossier.md` (`cc819da3b14b4610985069f8d35e6ae11caef9961ed6c17320a17542ed54ae77`)
- `paper_bencmark/highambench/tasks/P16/T2/faithfulness/history/20260821T225718Z/inputs/dependency_inventory.json` (`a5c943007118ade426fa61a17b29a249a6a421d6fde910ef505fffcc31e6d995`)
- `paper_bencmark/highambench/tasks/P16/T2/faithfulness/history/20260821T225718Z/inputs/direct_review_packet.md` (`9676235fc0d20bbecb9e1910de47f20ee3a54be69a4bfe86f74e08d747a210db`)
- `paper_bencmark/highambench/tasks/P16/T2/faithfulness/history/20260821T225718Z/inputs/source_locator.json` (`bb48d9ef1a2d4bb35de11367b04e7983b303f3a6a76f066cc78a7c8b26b10d9d`)
- `paper_bencmark/highambench/tasks/P16/T2/faithfulness/inputs/blind_dependency_inventory.json` (`cc4db05db44a27ceb5798713819fa836637982f8bad6578aa398044b59eeaff9`)
- `paper_bencmark/highambench/tasks/P16/T2/faithfulness/inputs/blind_dossier.md` (`070aa76520bd211b5d085872c47d451382cc9b5ee77520763055ffd0ca07b2ce`)
- `paper_bencmark/highambench/tasks/P16/T2/faithfulness/inputs/blind_review_packet.md` (`070aa76520bd211b5d085872c47d451382cc9b5ee77520763055ffd0ca07b2ce`)
- `paper_bencmark/highambench/tasks/P16/T2/faithfulness/inputs/declaration_dossier.md` (`5d01ffae364757108405f1967ba7ae68d21e6f4483ccb7c64afbf22e38f0f041`)
- `paper_bencmark/highambench/tasks/P16/T2/faithfulness/inputs/dependency_inventory.json` (`a5c943007118ade426fa61a17b29a249a6a421d6fde910ef505fffcc31e6d995`)
- `paper_bencmark/highambench/tasks/P16/T2/faithfulness/inputs/direct_review_packet.md` (`9676235fc0d20bbecb9e1910de47f20ee3a54be69a4bfe86f74e08d747a210db`)
- `paper_bencmark/highambench/tasks/P16/T2/faithfulness/inputs/source_locator.json` (`bb48d9ef1a2d4bb35de11367b04e7983b303f3a6a76f066cc78a7c8b26b10d9d`)
