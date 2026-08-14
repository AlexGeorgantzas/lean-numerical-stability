# Faithfulness audit: P05-T2

- Classification: `not-faithful-weaker`
- Accepted as paper-faithful: `false`
- Adjudicated: `false`
- Target SHA-256: `2ad0285ce2bb990d3d8fe2709531887d27677205d670f26be9b509532d9e9fe2`
- Paper SHA-256: `dd8b525c0eabc509a68b325ee5008cf6f1d4ef262bef8ba54e1947fe3cdb3db6`

## Decision

The matrix-product, absolute-value, exact-identity, and square coefficients are encoded correctly. Nevertheless, the declaration assumes the paper's principal square residual estimate, omits the floating-point Gaussian-elimination model, and drops the rectangular and local results. It is therefore a nonvacuous but essentially algebraic corollary of the paper, not a faithful formalization of Theorem 4.2.

## Implications

- **Lean implies paper:** `no`. The Lean theorem cannot derive hlocal from Gaussian elimination, does not model floating-point execution, and says nothing about the rectangular n*u result or the local estimates; therefore it does not imply Theorem 4.2.
- **Paper implies lean:** `yes`. After specializing Theorem 4.2 to m=n and translating one-based row i to Fin.val+1, equation (4.2) supplies the exact DeltaA identity and both target bounds. The target's broader arbitrary-real cases require no additional numerical claim because hlocal itself algebraically supplies the retained rowwise result.

## Findings

- **critical / assumed-core-result:** The formal theorem only packages DeltaA=LU-A and derives the uniform coefficient; it does not formalize the numerical-stability result.
- **major / missing-floating-point-algorithm:** There is no semantic linkage between the formal proposition and an LU algorithm run.
- **major / incomplete-theorem-scope:** Even apart from the circular hlocal premise, the declaration does not cover the full benchmark task claimed by the source contract.
- **critical / core-result-moved-to-hypothesis:** The translated statement does not prove the central numerical-stability result and reduces it to an elementary residual-repackaging lemma.
- **major / dimension-and-conclusion-loss:** The full rectangular theorem and its distinct general bound are absent.
- **major / algorithm-and-floating-point-model:** The statement no longer asserts anything about the accuracy or backward stability of an implemented factorization.
- **major / local-doolittle-estimates:** The proof-level numerical content required by the task source contract is entirely omitted.
- **minor / empty-dimension-vacuity:** The translation adds an unintended vacuous case and subtraction semantics not present in the source result.

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
| `S09` | `pass` | `pass` |
| `S10` | `fail` | `fail` |
| `S11` | `fail` | `fail` |
| `S12` | `fail` | `fail` |
| `S13` | `pass` | `pass` |
| `S14` | `pass` | `pass` |
| `S15` | `fail` | `fail` |
| `S16` | `fail` | `fail` |

## Dependency coverage

- Blind translator covered `35` dependencies (`0` hash-reused meanings); unclear: `none`.
- Direct judge covered `35` dependencies (`29` hash-reused interpretations); failing or unclear: `D006, D016`.

## Remaining uncertainties

No remaining uncertainties were recorded.

## Audit artifacts

- `paper_bencmark/highambench/tasks/P05/T2/faithfulness/agent_outputs/blind_translation.json` (`36fa2ad1734a9feea8493c522b1daa289e652077460a92100b12fff0c6a26383`)
- `paper_bencmark/highambench/tasks/P05/T2/faithfulness/agent_outputs/direct_judge.json` (`8e2dfc0a93151547e3c42f974b4b6af6553d13ed26d2c4b6390435d95045e939`)
- `paper_bencmark/highambench/tasks/P05/T2/faithfulness/agent_outputs/paper_source_contract.json` (`90bcb3f32112e46567a1fde6c0c742ef1d157d1829c1eb2b2cb5ebb4d58d4c1d`)
- `paper_bencmark/highambench/tasks/P05/T2/faithfulness/agent_outputs/roundtrip_judge.json` (`4e81ded2b048c61b2114e49b98832b3b851402ee75492b3158027f8052dc8531`)
- `paper_bencmark/highambench/tasks/P05/T2/faithfulness/agent_outputs/source_contract.json` (`e2e2fd479d2d1c03cabe0f8baef74c7bd8c9da70a251d4a3093a17877090f718`)
- `paper_bencmark/highambench/tasks/P05/T2/faithfulness/decision.json` (`7997e5e5958e59ea1afd99867c7becc8264f1c83af8cfb21141d0516c2dc6ba5`)
- `paper_bencmark/highambench/tasks/P05/T2/faithfulness/inputs/blind_dependency_inventory.json` (`c56549ba28c0a6dc92dc0edf5d686405ed884820822811e6a5adfd3ec01f7937`)
- `paper_bencmark/highambench/tasks/P05/T2/faithfulness/inputs/blind_dossier.md` (`2000282daaa2678d82e662c5f674a4e653a2b8587cd8bae85039f503d083f00e`)
- `paper_bencmark/highambench/tasks/P05/T2/faithfulness/inputs/blind_review_packet.md` (`2000282daaa2678d82e662c5f674a4e653a2b8587cd8bae85039f503d083f00e`)
- `paper_bencmark/highambench/tasks/P05/T2/faithfulness/inputs/declaration_dossier.md` (`f0232a3af8da7802bb6b66afc07fd0779ee87c762c41571c1d999615ea10af8b`)
- `paper_bencmark/highambench/tasks/P05/T2/faithfulness/inputs/dependency_inventory.json` (`c13980e3175f6606ab215fcb97d5a9d5a0bdce8dc5b5a3f268349f4403ceb810`)
- `paper_bencmark/highambench/tasks/P05/T2/faithfulness/inputs/dependency_reuse_direct.json` (`1b65ef5194934195e90c3d73c982f7127d2a4ac67aa9bbbd5f84c5d5123afb9d`)
- `paper_bencmark/highambench/tasks/P05/T2/faithfulness/inputs/direct_review_packet.md` (`f6d7622f8a53de126a8ab2a435148c8f81cd2a30c3989d70ac37b0069d129121`)
- `paper_bencmark/highambench/tasks/P05/T2/faithfulness/inputs/paper_source_locator.json` (`417f8e6a6ff934c35d3c2379d9faefe1c21d44b1f14a69f7674c0ef303123327`)
- `paper_bencmark/highambench/tasks/P05/T2/faithfulness/inputs/source_locator.json` (`9fb63ab1035cdbe5b25034bf13d2341b0813504a3fb962b5ac3a1801f93c4fd3`)
