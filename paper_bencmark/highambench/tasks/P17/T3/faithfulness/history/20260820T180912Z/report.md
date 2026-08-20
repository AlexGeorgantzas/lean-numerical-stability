# Faithfulness audit: P17-T3

- Classification: `not-faithful-different`
- Accepted as paper-faithful: `false`
- Adjudicated: `false`
- Target SHA-256: `7a2ec9477871b1e7c116f704e15f44dc6da12bb5eb768dd51fc69c8b427a5dd1`
- Paper SHA-256: `df1ce5dd33285adfcffc6a4c7ab94f9604b46739cb848c6cbb5f997e8fac597d`

## Decision

Direct inspection of Theorem 4.3 and its surrounding definitions shows that the Lean target is a generic finite-space second-moment-plus-fixed-bias inequality, not the stated SR_{p,r} recursive-summation result. Its probability primitives and scalar operators are conventional, but it omits the algorithm, exact and computed sums, gamma constants, indexing, and relative-error definition. Most decisively, the paper's limited-precision remainder A is outcome-dependent and only pathwise bounded, whereas Lean supplies one deterministic scalar bias. Neither proposition implies the other under the meanings actually stated, so the result is not-faithful-different.

## Implications

- **Lean implies paper:** `no`. The Lean proposition does not identify its random expression with |hat y - y| / |y|, does not provide the concrete gamma budgets, and cannot instantiate its single scalar bias as the paper's outcome-dependent pathwise remainder A. Therefore its conclusion does not entail equation (4.11).
- **Paper implies lean:** `no`. Theorem 4.3 concerns one SR_{p,r} recursive-summation distribution and its derived quantities. It does not assert the target's universal concentration theorem for every finite probability model, arbitrary random function, arbitrary fixed bias, and arbitrary budgets.

## Findings

- **critical / algorithm-linkage-and-result-identity:** The proposition does not state the benchmarked recursive-summation theorem.
- **critical / random-remainder-replaced-by-fixed-bias:** The paper's decomposition M + A cannot be mapped to centered omega + bias, so the abstract event does not yield the paper's final error event.
- **major / constants-indexing-and-error-notion:** The exact theorem cannot be recovered from the Lean statement even if the generic probability inequality is mathematically valid.
- **major / hypothesis-domain-and-nonvacuity:** The target admits trivial lambda >= 1 and kappa = 0 cases and excludes the zero-variance boundary, so its domain is not the paper's domain.
- **critical / algorithm-and-binders:** The formal statement is no longer a proposition about the paper's summation algorithm.
- **critical / error-decomposition:** The fixed-bias model cannot represent the paper's random pathwise remainder, preventing translation-implies-paper.
- **major / constants-and-numerical-model:** The theorem's dimensions, precision dependence, exact higher-order terms, and rounding model are lost.
- **major / vacuity-and-scope:** Large parts of the translated quantifier domain satisfy the conclusion for trivial reasons unrelated to probabilistic error analysis.

## Semantic checklist

| Check | Direct | Round-trip |
|---|---|---|
| `S01` | `pass` | `pass` |
| `S02` | `fail` | `fail` |
| `S03` | `fail` | `fail` |
| `S04` | `fail` | `fail` |
| `S05` | `fail` | `fail` |
| `S06` | `pass` | `fail` |
| `S07` | `fail` | `fail` |
| `S08` | `fail` | `fail` |
| `S09` | `fail` | `fail` |
| `S10` | `fail` | `fail` |
| `S11` | `fail` | `fail` |
| `S12` | `fail` | `fail` |
| `S13` | `fail` | `fail` |
| `S14` | `fail` | `fail` |
| `S15` | `fail` | `fail` |
| `S16` | `fail` | `fail` |

## Dependency coverage

- Blind translator covered `49` dependencies (`0` hash-reused meanings); unclear: `none`.
- Direct judge covered `49` dependencies (`20` hash-reused interpretations); failing or unclear: `D001, D008`.

## Remaining uncertainties

No remaining uncertainties were recorded.

## Audit artifacts

- `paper_bencmark/highambench/tasks/P17/T3/faithfulness/agent_outputs/blind_translation.json` (`45c3803f78d44bff49877c547e50a7099e3fa0db742993a470b0b8c5dbe0509d`)
- `paper_bencmark/highambench/tasks/P17/T3/faithfulness/agent_outputs/direct_judge.json` (`67c3818080ec3cd091d1c796961273b66301bdb0c97bfdd6c98eeff350e670e1`)
- `paper_bencmark/highambench/tasks/P17/T3/faithfulness/agent_outputs/paper_source_contract.json` (`5856f4d88e51aeb1df8e36f051f77e90c96a2896bb707ed0186c2f74cf1ebc0b`)
- `paper_bencmark/highambench/tasks/P17/T3/faithfulness/agent_outputs/roundtrip_judge.json` (`7a572bdd0fd8520995cfc5172b21c1c50557c0dde3596b9fe329cae3f19924ce`)
- `paper_bencmark/highambench/tasks/P17/T3/faithfulness/agent_outputs/source_contract.json` (`697b1c807ea2e27af0e3e98bafbf9612ff439eadc422810794e12255b641767a`)
- `paper_bencmark/highambench/tasks/P17/T3/faithfulness/decision.json` (`243877dfb5d546b7983dfdbf512100089c622e38697c8dc0ef909e2233c76e6d`)
- `paper_bencmark/highambench/tasks/P17/T3/faithfulness/inputs/blind_dependency_inventory.json` (`b3be8da80da110ed8ce5ce52f409d075af008d02c5ae1dd45c3fbd8a42a249e2`)
- `paper_bencmark/highambench/tasks/P17/T3/faithfulness/inputs/blind_dossier.md` (`a5b756b20fe20b51b5dec8374581e42a0833b210678a1dff681d829fbbbcb4cd`)
- `paper_bencmark/highambench/tasks/P17/T3/faithfulness/inputs/blind_review_packet.md` (`a5b756b20fe20b51b5dec8374581e42a0833b210678a1dff681d829fbbbcb4cd`)
- `paper_bencmark/highambench/tasks/P17/T3/faithfulness/inputs/declaration_dossier.md` (`7829cee4c6d0ec6d0274b50c5f1137c54c0eb14cc880d2584655de9b826a5b80`)
- `paper_bencmark/highambench/tasks/P17/T3/faithfulness/inputs/dependency_inventory.json` (`464130cd244d525bbbd8c155d22ae5cae80d53470d13bf1498ad46e1b5942734`)
- `paper_bencmark/highambench/tasks/P17/T3/faithfulness/inputs/dependency_reuse_direct.json` (`296db121ef2c13d91112c669d12f7ea0f20a83e6980c05d1deed23c20f1ed969`)
- `paper_bencmark/highambench/tasks/P17/T3/faithfulness/inputs/direct_review_packet.md` (`dd6ca79107f1911e7c97031ceebbd16ae2f44acd172bdf2e60a7dd41c6943693`)
- `paper_bencmark/highambench/tasks/P17/T3/faithfulness/inputs/paper_source_locator.json` (`7b6e846a522a4293bd50e70522a875cdc8dd30515338efc2e70d99739bcb7161`)
- `paper_bencmark/highambench/tasks/P17/T3/faithfulness/inputs/source_locator.json` (`856e809348a4ffac1444cae1a818a03af5f943b2b50dc55d83e3f0ebbc8ccdcf`)
