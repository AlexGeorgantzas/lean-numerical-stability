# Faithfulness audit: P19-T2

- Classification: `not-faithful-different`
- Accepted as paper-faithful: `false`
- Adjudicated: `false`
- Target SHA-256: `3e5946431b5d9cfd06265bf2930b39daff5aab91e8c6ab5ba56c2e2f48b70129`
- Paper SHA-256: `67af427c72ae891b7863e386db542ef775b1e3eb306f812bb1a78bdbef86aaad`

## Decision

The declaration faithfully reproduces only the scalar four-term definition of xi. Its asserted theorem is instead an exact Euclidean triangle inequality for four arbitrary same-dimensional vectors. It omits the GMRES algorithm, heterogeneous perturbation models, smallness and nonsingularity hypotheses, existential iteration, basis-conditioning conclusion, normalized forward error, explicit coefficient definitions, polynomial factor, outer condition number, and first-order approximation semantics. Because neither statement implies the other under a faithful correspondence of objects, the result is not-faithful-different.

## Implications

- **Lean implies paper:** `no`. The Lean triangle inequality provides no computed GMRES solution, existential iteration, basis-conditioning result, modular floating-point models, coefficient definitions, normalized forward error, c(n,k), or outer condition-number factor, so it cannot establish Theorem 3.1 or equation (3.8).
- **Paper implies lean:** `no`. The paper result concerns its algorithmically generated heterogeneous perturbations and derived coefficients; it does not assert a universal inequality for four arbitrary same-dimensional vectors and arbitrary nonnegative coefficients. The Lean proposition is independently true by norm algebra, not a consequence stated by the paper under a faithful variable correspondence.

## Findings

- **critical / conclusion-substitution:** The central numerical-analysis theorem is replaced by a generic triangle inequality.
- **major / missing-algorithmic-context:** The formal statement cannot measure reasoning about the paper's GMRES result.
- **major / error-and-norm-mismatch:** The source meanings, shapes, and normwise models are conflated.
- **major / coefficient-and-factor-omission:** The proposition loses the conditioning and basis dependence that gives the paper bound its content.
- **major / approximation-mismatch:** The logical relation and higher-order-term semantics do not match.
- **note / preserved-subexpression:** The four-term aggregate is preserved as a subexpression, but this does not repair the replacement of the full theorem.
- **critical / conclusion replacement:** The principal theorem and its numerical-analysis content are absent.
- **major / binders and quantifiers:** Witness dependence, matrix dimensions, rank conditions, and preconditioner scope cannot be recovered.
- **major / algorithm and numerical model:** The claim is detached from GMRES and floating-point execution.
- **major / norm and error semantics:** Matrix-product error and forward error are replaced by different mathematical quantities.
- **major / coefficients and constants:** The scaling and conditioning content of equation (3.8) is lost.
- **major / higher-order treatment:** The translated relation has a different formal strength and justification.
- **note / preserved fragment:** The coefficient ordering is faithful, but this isolated fragment is insufficient to represent the source result.

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
| `S14` | `fail` | `fail` |
| `S15` | `fail` | `fail` |
| `S16` | `fail` | `fail` |

## Dependency coverage

- Blind translator covered `30` dependencies (`0` hash-reused meanings); unclear: `none`.
- Direct judge covered `30` dependencies (`22` hash-reused interpretations); failing or unclear: `D002, D003, D004, D005, D006, D007, D008, D009, D012`.

## Remaining uncertainties

No remaining uncertainties were recorded.

## Audit artifacts

- `paper_bencmark/highambench/tasks/P19/T2/faithfulness/agent_outputs/blind_translation.json` (`5ece5e5732c21b0e179d6bee4aecf8bf5db288c1b68d0d545f76137b156636c0`)
- `paper_bencmark/highambench/tasks/P19/T2/faithfulness/agent_outputs/direct_judge.json` (`a41deaf570d409888e2b2e08bc2577e57bf8c99388e7c9ed912a8c3c5abc869f`)
- `paper_bencmark/highambench/tasks/P19/T2/faithfulness/agent_outputs/paper_source_contract.json` (`282bdf4dba3e70c740465a2c4663b96debd1a66ef82c3debf273ad41cdbf76e0`)
- `paper_bencmark/highambench/tasks/P19/T2/faithfulness/agent_outputs/roundtrip_judge.json` (`24afa3b2a0a0cb5ffc638262914d28638a8d19c35ed983ae669eac2a99b677f1`)
- `paper_bencmark/highambench/tasks/P19/T2/faithfulness/agent_outputs/source_contract.json` (`dd0d2bca250671eb54008fe6991d62753daf66112a7a2271b59c6dcc1567e999`)
- `paper_bencmark/highambench/tasks/P19/T2/faithfulness/decision.json` (`f4bacc33043fba7f132cd6b9e4227176eef7bcec965a75ad277dc92b96479de2`)
- `paper_bencmark/highambench/tasks/P19/T2/faithfulness/inputs/blind_dependency_inventory.json` (`ec138d7e7422dcbc4046b9de8e07396d88b56e6e8add192676de7a2721aad2f3`)
- `paper_bencmark/highambench/tasks/P19/T2/faithfulness/inputs/blind_dossier.md` (`30488ba9c655efb7e89d355d763b5b315834ffe2b5f091689b780e722e67a310`)
- `paper_bencmark/highambench/tasks/P19/T2/faithfulness/inputs/blind_review_packet.md` (`30488ba9c655efb7e89d355d763b5b315834ffe2b5f091689b780e722e67a310`)
- `paper_bencmark/highambench/tasks/P19/T2/faithfulness/inputs/declaration_dossier.md` (`418693f6115bcee06a30e8b43d98426b575cfeaf0efeea1c14dd12781a43e55d`)
- `paper_bencmark/highambench/tasks/P19/T2/faithfulness/inputs/dependency_inventory.json` (`05e54919f44802e2c919335c432acea16eda5d837976d444a726524a271a4bd1`)
- `paper_bencmark/highambench/tasks/P19/T2/faithfulness/inputs/dependency_reuse_direct.json` (`12d4bef658bdd1e736e525973b9a4e7bcf7a33e63b0e0cc8f6963605d89757cc`)
- `paper_bencmark/highambench/tasks/P19/T2/faithfulness/inputs/direct_review_packet.md` (`279dca4b8eac123f63d7a37f7c1fe51271fa672a079b0682f6fe28f5974236aa`)
- `paper_bencmark/highambench/tasks/P19/T2/faithfulness/inputs/paper_source_locator.json` (`b2b71745c3ba0bc98613f67b2d754faf971558a1974b0f22e4456d4b88500ba1`)
- `paper_bencmark/highambench/tasks/P19/T2/faithfulness/inputs/source_locator.json` (`41c7217c655d70ebb73d0b6037c21d54f22f6119435a2bb382ff077e98e78af7`)
