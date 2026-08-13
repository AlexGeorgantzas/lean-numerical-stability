# Faithfulness audit: P06-T2

- Classification: `faithful-equivalent`
- Accepted as paper-faithful: `true`
- Adjudicated: `false`
- Target SHA-256: `f92d55c304f3ea2d46dafcd9ff71f3d0e1160bd4660f48b15b2526ee5a99af6e`
- Paper SHA-256: `c02a20e9ffa8039a5ad3db9261fba19929de84bf0bff7654547541dffe496a79`

## Decision

The verified source passage defines exactly the same real symmetric dilation as the Lean dependency. The Lean target replaces the scalar equality in equation (3.4) by its universal nonnegative-threshold form: the subordinate 2-norm is at most L exactly when the dilation is Loewner-bounded by L times the identity. After unfolding all dependencies, the block order, transpose, zero blocks, Euclidean norm, finite sums, and matrix order all match. The reformulation is bidirectionally equivalent, deterministic, nonvacuous, and introduces no missing numerical-model or error assumptions.

## Implications

- **Lean implies paper:** `yes`. The Lean theorem equates, for every nonnegative L, the predicate ||M||_2 <= L with phi(M) <= L I. For a finite real symmetric matrix, the latter is equivalent to lambda_max(phi(M)) <= L. Equality of these upper-bound predicates for all nonnegative L yields lambda_max(phi(M)) = ||M||_2, and D004 supplies exactly the paper's dilation.
- **Paper implies lean:** `yes`. From lambda_max(phi(M)) = ||M||_2, the standard symmetric-matrix characterization phi(M) <= L I iff lambda_max(phi(M)) <= L and the subordinate-norm characterization p06RectOpNorm2Le M L iff ||M||_2 <= L give the Lean Iff for every L >= 0.

## Findings

- **note / equivalent-threshold-reformulation:** This changes representation but not mathematical content: the two statements imply each other using the standard largest-eigenvalue characterization of Loewner upper bounds.
- **note / indirect equality characterization:** Because L is universally quantified, this is an equivalent epigraph characterization and does not weaken the result.
- **note / zero-dimensional extension:** These additional cases are tautological under L >= 0 and do not alter the intended positive-dimensional identity.

## Semantic checklist

| Check | Direct | Round-trip |
|---|---|---|
| `S01` | `pass` | `pass` |
| `S02` | `pass` | `pass` |
| `S03` | `pass` | `pass` |
| `S04` | `pass` | `pass` |
| `S05` | `pass` | `pass` |
| `S06` | `pass` | `pass` |
| `S07` | `not-applicable` | `not-applicable` |
| `S08` | `not-applicable` | `not-applicable` |
| `S09` | `pass` | `pass` |
| `S10` | `pass` | `pass` |
| `S11` | `not-applicable` | `not-applicable` |
| `S12` | `pass` | `pass` |
| `S13` | `not-applicable` | `not-applicable` |
| `S14` | `not-applicable` | `not-applicable` |
| `S15` | `pass` | `pass` |
| `S16` | `pass` | `pass` |

## Dependency coverage

- Blind translator covered `55` dependencies (`0` hash-reused meanings); unclear: `none`.
- Direct judge covered `55` dependencies (`22` hash-reused interpretations); failing or unclear: `none`.

## Remaining uncertainties

No remaining uncertainties were recorded.

## Audit artifacts

- `paper_bencmark/highambench/tasks/P06/T2/faithfulness/agent_outputs/blind_translation.json` (`dd78854d152e1342f8eab2af1ecc7ef8e31913b9ad21a077e3d16bc555a352a8`)
- `paper_bencmark/highambench/tasks/P06/T2/faithfulness/agent_outputs/direct_judge.json` (`98622e996bd2102bf81e23763bb9e5c2fffd189eafbf0dd0b8ec764ff237beae`)
- `paper_bencmark/highambench/tasks/P06/T2/faithfulness/agent_outputs/paper_source_contract.json` (`5fc79f8dcb892e5e54a0e6404abfb754e2c8f1233e5e586f0036f135448517d2`)
- `paper_bencmark/highambench/tasks/P06/T2/faithfulness/agent_outputs/roundtrip_judge.json` (`16f37882c006979737d639ef3028bbd4c9e1ec8c4e4ae31f3372944a8f8b08b3`)
- `paper_bencmark/highambench/tasks/P06/T2/faithfulness/agent_outputs/source_contract.json` (`786dda88a1c7256af691be3b989a8dae8c26198c47cc1608362a3b041848fe71`)
- `paper_bencmark/highambench/tasks/P06/T2/faithfulness/decision.json` (`2238f7540d700f4cbd3cd74d82ea5ad4ce0de3727d30e07655948bbdd4c84e92`)
- `paper_bencmark/highambench/tasks/P06/T2/faithfulness/inputs/blind_dependency_inventory.json` (`4a38b9331a2deb8784734372a5cca8ff92c9001e22d00a8f92373c94690f435d`)
- `paper_bencmark/highambench/tasks/P06/T2/faithfulness/inputs/blind_dossier.md` (`617096bf5e4beb1c502e25c056a35384f4256883ba0002c6d345f62c37cbac8e`)
- `paper_bencmark/highambench/tasks/P06/T2/faithfulness/inputs/blind_review_packet.md` (`617096bf5e4beb1c502e25c056a35384f4256883ba0002c6d345f62c37cbac8e`)
- `paper_bencmark/highambench/tasks/P06/T2/faithfulness/inputs/declaration_dossier.md` (`32c51321ecfc10ce90cf46e30c82496814f8d7948a5e3a1b85253ce0cc9f4a15`)
- `paper_bencmark/highambench/tasks/P06/T2/faithfulness/inputs/dependency_inventory.json` (`95db7b43dd63e2c03c2ba7cba9cf1fb22cd8c46a6ad10b6ba05cb4e811041c17`)
- `paper_bencmark/highambench/tasks/P06/T2/faithfulness/inputs/dependency_reuse_direct.json` (`c7dfebe32b9da83645b6d36173b951ee34492eb7795fc3744e7ae817e4f3deb0`)
- `paper_bencmark/highambench/tasks/P06/T2/faithfulness/inputs/direct_review_packet.md` (`e5478b38396739fc7d975141354917419fb3d5eacd287293f9f5db2423593d13`)
- `paper_bencmark/highambench/tasks/P06/T2/faithfulness/inputs/paper_source_locator.json` (`d42b3fea8b0a859f7675a27adf15eef5a9d1a4d454377d2374aa02bdd01476fe`)
- `paper_bencmark/highambench/tasks/P06/T2/faithfulness/inputs/source_locator.json` (`c129e6fb54d5507635c88f4b69f4eedf73df2dc985ff8bf2770feb626480dd14`)
