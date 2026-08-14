# Faithfulness audit: P05-T1

- Classification: `not-faithful-different`
- Accepted as paper-faithful: `false`
- Adjudicated: `false`
- Target SHA-256: `23f5b3761aa4c7b0641e34d71b832225d8e91893117d04a7bf97cca512307408`
- Paper SHA-256: `dd8b525c0eabc509a68b325ee5008cf6f1d4ef262bef8ba54e1947fe3cdb3db6`

## Decision

The PDF hash, cited passage, and surrounding definitions were checked directly. The best index alignment is paper K = Lean k + 1, which reconciles the number of products and the general linear coefficient. The substantive statements nevertheless differ: Lean assumes a generic real residual estimate, includes c among its coefficient sources, permits c to be perturbed, omits b_K and the floating-point execution model, and omits the sharper b_K = 1 case. Its assumptions are satisfiable, but the theorem reduces to an all-source residual allocation rather than the paper's algorithmic backward-error result. Because neither full proposition implies the other, the appropriate classification is not-faithful-different.

## Implications

- **Lean implies paper:** `no`. Even under the favorable alignment K = k + 1 and computed = b_K*y_hat, Lean produces an extra theta_c and cannot force c to remain unperturbed. For example, with k = 0, u = 1/2, computed = 1/2, and c = 1, herror holds and the Lean identity has theta0 = 0 and theta_c = -1/2, but an unperturbed-c identity computed*(1+theta0) = c would require theta0 = 1, outside the bound. Lean also supplies no derivation of herror from the paper's floating-point execution.
- **Paper implies lean:** `no`. On valid paper instances, the paper's stronger result can yield a restricted Lean-style identity by taking theta_c = 0 after K = k + 1 and computed = b_K*y_hat. However, the paper does not establish the full Lean proposition for arbitrary real tuples and arbitrary nonnegative u satisfying Lean's different all-source herror premise. Thus it does not imply the universal Lean statement.

## Findings

- **critical / unperturbed-c violation:** Residual can be absorbed into c, so the target does not provide the paper's required coefficientwise backward identity or its downstream interpretation for fixed input data.
- **critical / algorithmic result assumed away:** The target proves only an algebraic residual-distribution fact and does not formalize the central numerical-analysis claim.
- **major / denominator and computed linkage:** The general division case cannot be recovered from the Lean proposition without adding external definitions and hypotheses.
- **major / floating-point model omitted:** The target has unsupported scope and does not preserve the theorem's numerical model or exceptional-value conditions.
- **major / unit-denominator case omitted:** A required conclusion of the selected paper result is absent.
- **note / index reparameterization:** These two features align under K = k + 1 and are not independently defective, but this reindexing does not repair the other semantic differences.
- **critical / algorithm-and-floating-point-model:** The translated statement neither models nor guarantees the paper's computation.
- **critical / protected-input-backward-error:** Allowing theta_c changes the central backward-error guarantee and does not imply the protected-c identity.
- **major / dimensions-denominator-and-indexing:** The binders and algorithmic dimensions cannot be identified without an unstated reindexing, and the denominator behavior remains missing.
- **major / constants-and-special-case:** The translation omits a required sharp conclusion and does not preserve the paper's parameter dependence.
- **major / residual-hypothesis-substitution:** A derived proof ingredient is replaced by a weaker assumed condition, changing both logical direction and error semantics.

## Semantic checklist

| Check | Direct | Round-trip |
|---|---|---|
| `S01` | `pass` | `pass` |
| `S02` | `fail` | `fail` |
| `S03` | `fail` | `pass` |
| `S04` | `fail` | `fail` |
| `S05` | `fail` | `fail` |
| `S06` | `fail` | `pass` |
| `S07` | `fail` | `fail` |
| `S08` | `fail` | `fail` |
| `S09` | `pass` | `pass` |
| `S10` | `fail` | `fail` |
| `S11` | `fail` | `fail` |
| `S12` | `fail` | `fail` |
| `S13` | `fail` | `fail` |
| `S14` | `pass` | `pass` |
| `S15` | `fail` | `fail` |
| `S16` | `fail` | `pass` |

## Dependency coverage

- Blind translator covered `42` dependencies (`0` hash-reused meanings); unclear: `none`.
- Direct judge covered `42` dependencies (`0` hash-reused interpretations); failing or unclear: `D001, D018, D019, D033, D040`.

## Remaining uncertainties

No remaining uncertainties were recorded.

## Audit artifacts

- `paper_bencmark/highambench/tasks/P05/T1/faithfulness/agent_outputs/blind_translation.json` (`05208189ac745fdf59e4d42742f60e3f4913ce4828338550052100f796b62497`)
- `paper_bencmark/highambench/tasks/P05/T1/faithfulness/agent_outputs/direct_judge.json` (`1c8317016360b1946ba18ad934401e2e4c55467ce8ab4b21c62c04dd07e39349`)
- `paper_bencmark/highambench/tasks/P05/T1/faithfulness/agent_outputs/paper_source_contract.json` (`90bcb3f32112e46567a1fde6c0c742ef1d157d1829c1eb2b2cb5ebb4d58d4c1d`)
- `paper_bencmark/highambench/tasks/P05/T1/faithfulness/agent_outputs/roundtrip_judge.json` (`87d28a54fc8428f376f6acfc8ead1ef77140b9a65e4d5366b01fd69d90b86278`)
- `paper_bencmark/highambench/tasks/P05/T1/faithfulness/agent_outputs/source_contract.json` (`11d8619c966e9dfddf63c80cb311da3c474db4e245ea5b25e17b3d9d1e62250d`)
- `paper_bencmark/highambench/tasks/P05/T1/faithfulness/decision.json` (`21329756740e0fd7b2c750dc3b54d3151815dffbf815e124da600b35f75c31b1`)
- `paper_bencmark/highambench/tasks/P05/T1/faithfulness/inputs/blind_dependency_inventory.json` (`a82223c2956ced080c44d63e602bf5bcc97ac72d70aba51d9adc0bce549d5868`)
- `paper_bencmark/highambench/tasks/P05/T1/faithfulness/inputs/blind_dossier.md` (`dea1dfb802bb0ac29df718b16a78b07401973d3b517d6dc07ebf6424dd085528`)
- `paper_bencmark/highambench/tasks/P05/T1/faithfulness/inputs/blind_review_packet.md` (`dea1dfb802bb0ac29df718b16a78b07401973d3b517d6dc07ebf6424dd085528`)
- `paper_bencmark/highambench/tasks/P05/T1/faithfulness/inputs/declaration_dossier.md` (`f6a4a88b553ed06db46519962fcf2f7638d72b34ed60a71f6c78c473d69747ea`)
- `paper_bencmark/highambench/tasks/P05/T1/faithfulness/inputs/dependency_inventory.json` (`d1341023c6aed372538f3140646341eb085bd7d641a2f587758efc94fe58951f`)
- `paper_bencmark/highambench/tasks/P05/T1/faithfulness/inputs/direct_review_packet.md` (`2655aad3e60f6016b0d840eca3eaae82ec8e1c4a74c4b3c3f73356a7aa940ded`)
- `paper_bencmark/highambench/tasks/P05/T1/faithfulness/inputs/paper_source_locator.json` (`417f8e6a6ff934c35d3c2379d9faefe1c21d44b1f14a69f7674c0ef303123327`)
- `paper_bencmark/highambench/tasks/P05/T1/faithfulness/inputs/source_locator.json` (`ec02206ad77a57f53e7301f350edb6fef3d9312f97956e4bb423c0001dfe8219`)
