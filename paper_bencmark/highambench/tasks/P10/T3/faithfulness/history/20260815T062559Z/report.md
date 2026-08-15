# Faithfulness audit: P10-T3

- Classification: `not-faithful-different`
- Accepted as paper-faithful: `false`
- Adjudicated: `true`
- Target SHA-256: `678e0d48115267a7b9ba48c8d8b0a31ca85c421c08147fa0377eb1d70612ae61`
- Paper SHA-256: `0ee818d060542baefdd85cbb7c7f2fd948efcb927101da84c37e418713f87269`

## Decision

Primary PDF evidence and the complete declaration bodies resolve D043, S09, and S12 without relying on vote counts or reuse hashes. Lean preserves the local coefficients and gives a valid, nonvacuous affine-recurrence unrolling. It nevertheless omits the SylR execution, Sylvester data dependencies, size halving, numerical model, equation (20), and logarithmic-stability conclusion. Its apparent generality is not genuine paper-level strengthening: it results from moving the paper-specific recurrence into an antecedent and removing the conditions and conclusions that give it numerical meaning. With both implication directions negative, the consistent classification is not-faithful-different and accepted is false.

## Implications

- **Lean implies paper:** `no`. The Lean theorem assumes an abstract scalar recurrence and only unrolls it. It does not establish that SylR generates the recurrence, define sep(A,B), connect R or err to exact and computed Sylvester solutions, derive equation (20), or conclude logarithmic stability.
- **Paper implies lean:** `no`. The paper proves an algorithm-specific, size-halving recurrence and asymptotic result for SylR. It does not assert the Lean theorem's universal conditional for arbitrary independent dimensions, depths, matrices, scalar parameters, and real sequences. The paper recurrence can motivate one constrained instance, not the full quantified declaration.

## Findings

- **critical / algorithm-linkage:** The central numerical-analysis burden is assumed rather than proved, leaving a generic recurrence lemma instead of a theorem about SylR.
- **major / missing-conclusions:** The declaration omits the selected result's principal asymptotic and stability claims.
- **major / binders-and-indexing:** The declaration cannot recover the paper's size-dependent exponents or multiplication-error indexing without substantial external assumptions.
- **major / separation-and-error-semantics:** The symbols carrying the paper's conditioning and forward-error content are detached from the matrices and algorithm.
- **minor / norm-specialization:** The specialization is compatible and not independently disqualifying, but it does not repair the missing definition of sep or algorithmic linkage.
- **note / recurrence-relation:** The Lean inequality direction is faithful for a dominating error bound and is not a source of rejection.

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
| `S09` | `pass` | `unclear` |
| `S10` | `fail` | `fail` |
| `S11` | `fail` | `fail` |
| `S12` | `pass` | `unclear` |
| `S13` | `fail` | `fail` |
| `S14` | `fail` | `fail` |
| `S15` | `fail` | `fail` |
| `S16` | `pass` | `fail` |

## Dependency coverage

- Blind translator covered `44` dependencies (`0` hash-reused meanings); unclear: `D043`.
- Direct judge covered `44` dependencies (`22` hash-reused interpretations); failing or unclear: `D002, D003, D016`.

## Remaining uncertainties

- The paper does not typographically identify every unsubscripted recurrence norm, although Frobenius is an admissible and contextually supported specialization.
- The selected paper passage does not conclusively specify whether the matrix scalar field is real or complex; Lean specializes to real matrices.
- Equation (20) leaves its big-O constants, finite-n threshold, and suppressed higher-order terms unspecified.

## Audit artifacts

- `paper_bencmark/highambench/tasks/P10/T3/faithfulness/agent_outputs/adjudicator.json` (`6e1622cefd63b1ac0a8fa7a956911832ed3317a6b7a62561bb9abb56c2424226`)
- `paper_bencmark/highambench/tasks/P10/T3/faithfulness/agent_outputs/blind_translation.json` (`13fe8c3784c3e21150701b15fdf6a77d19bc30a6bcc6b5c7517c0bb6ec2657ff`)
- `paper_bencmark/highambench/tasks/P10/T3/faithfulness/agent_outputs/direct_judge.json` (`2cfc5b96b26e914acc7842f8dee5be9327497487b1266d22783c6c48548a9c8a`)
- `paper_bencmark/highambench/tasks/P10/T3/faithfulness/agent_outputs/paper_source_contract.json` (`a730fdcbbc543ec8712373b135d8a67dd310f31f635dedabf0ed548f9316414a`)
- `paper_bencmark/highambench/tasks/P10/T3/faithfulness/agent_outputs/roundtrip_judge.json` (`72bf1e6126a74c3a3de86a69aa8f6cba4911244cbe2aadfbb7836b856d9ac318`)
- `paper_bencmark/highambench/tasks/P10/T3/faithfulness/agent_outputs/source_contract.json` (`8efac3e47a1bc50618231ce1fc451cbe8d17d2a680e7d0f83e953c44ae888184`)
- `paper_bencmark/highambench/tasks/P10/T3/faithfulness/decision.json` (`7557b95cb0ea441d32eca1215aff2955243da00cbe9b27859395ce379610d0e3`)
- `paper_bencmark/highambench/tasks/P10/T3/faithfulness/inputs/blind_dependency_inventory.json` (`e6e1e63de5c03181ea762421b4af0ff3f227cd32578d2286f77f8d578a12b3a0`)
- `paper_bencmark/highambench/tasks/P10/T3/faithfulness/inputs/blind_dossier.md` (`719b4d67c6e21357302ebc4493123dea7fceffde1c58ed9091101dc88280126f`)
- `paper_bencmark/highambench/tasks/P10/T3/faithfulness/inputs/blind_review_packet.md` (`719b4d67c6e21357302ebc4493123dea7fceffde1c58ed9091101dc88280126f`)
- `paper_bencmark/highambench/tasks/P10/T3/faithfulness/inputs/declaration_dossier.md` (`a748607e03908e6f1837a9cd6a747d55e2744eb26ee73d3d8acccabe4d66a47d`)
- `paper_bencmark/highambench/tasks/P10/T3/faithfulness/inputs/dependency_inventory.json` (`e896a8536f096464d33672f122968a460409d83ce8eb9dc38864668fa1dad48c`)
- `paper_bencmark/highambench/tasks/P10/T3/faithfulness/inputs/dependency_reuse_direct.json` (`6d40017070ef9b09a33230c3d2de7549a8eec696e7b08b74611a9fe586c59bf0`)
- `paper_bencmark/highambench/tasks/P10/T3/faithfulness/inputs/direct_review_packet.md` (`70a35c142f16e4806a68726f7a0ea0453d8534d87d4a940a194029c235dce993`)
- `paper_bencmark/highambench/tasks/P10/T3/faithfulness/inputs/paper_source_locator.json` (`91f77a26c65c7ca024e216f6cc35327e6521963eee50d0bda4fd50b72060a4dc`)
- `paper_bencmark/highambench/tasks/P10/T3/faithfulness/inputs/source_locator.json` (`c42d916d212b72c2dd5775fe26ed54385d4194a33841d840176614d9adebb304`)
