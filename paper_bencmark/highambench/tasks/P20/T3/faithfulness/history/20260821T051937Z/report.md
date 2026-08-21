# Faithfulness audit: P20-T3

- Classification: `not-faithful-weaker`
- Accepted as paper-faithful: `false`
- Adjudicated: `true`
- Target SHA-256: `05bc9bca28d9ea01d058bdcce95013cf05f56f374563f3214ddfd12c71f042ad`
- Paper SHA-256: `ad830de20a73ff77b6e457921892b3250ba9ff70f487501979ee3f1c5f3f31e2`

## Decision

The source and Lean statements are related, but only through the displayed right-hand-side formulas. The paper proves an order-level forward-error estimate for a specific scaled mixed-precision computation. Lean instead defines the narrow expression to be the range-free expression plus two underflow expressions and proves the resulting ordered-ring facts. Because B795-B796 explicitly present and compare those same terms, the paper entails this formula-level corollary after unfolding the definitions. Conversely, the corollary cannot recover any computed output, error inequality, algorithm, floating-point model, scaling hypothesis, or higher-order interpretation. The implication pattern is therefore paper-to-Lean yes and Lean-to-paper no, giving not-faithful-weaker and rejection.

## Implications

- **Lean implies paper:** `no`. Exact identities among self-defined right-hand-side envelopes place no constraint on a computed matrix product and cannot establish the paper's normwise forward-error bound or its floating-point algorithm assumptions.
- **Paper implies lean:** `yes`. The raw coefficient expression displayed in (4.32) is the expression displayed in (4.33) plus the two nonnegative underflow contributions, exactly as stated in the comparison on B796. After unfolding the Lean definitions, elementary ordered-real algebra yields every Lean conjunct. This is only a weak consequence about chosen expressions, not an exact interpretation of lesssim.

## Findings

- **critical / missing-forward-error-result:** Lean cannot establish the selected paper theorem's central claim.
- **major / algorithm-and-model-omission:** The Lean theorem is independent of the floating-point computation analyzed by the paper.
- **major / relation-strength:** The exact Lean relations are valid algebraic facts about definitions but must not be interpreted as exact versions of the paper's error bounds.
- **major / definition-driven-content:** The substantive Lean conclusions follow from distributivity and nonnegativity rather than matrix-multiplication error analysis.
- **note / matched-formula-corollary:** This direct formula-level relationship supports not-faithful-weaker rather than not-faithful-different.

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
| `S09` | `fail` | `pass` |
| `S10` | `fail` | `fail` |
| `S11` | `fail` | `fail` |
| `S12` | `fail` | `fail` |
| `S13` | `fail` | `fail` |
| `S14` | `fail` | `fail` |
| `S15` | `fail` | `fail` |
| `S16` | `fail` | `fail` |

## Dependency coverage

- Blind translator covered `66` dependencies (`0` hash-reused meanings); unclear: `none`.
- Direct judge covered `66` dependencies (`19` hash-reused interpretations); failing or unclear: `D002, D009, D010, D013, D015, D018, D022, D028, D040, D043`.

## Remaining uncertainties

- The paper does not define the constants hidden by lesssim, so no exact comparison between fully instantiated numerical bound constants can be recovered.
- Theorem 4.1 does not explicitly state the positive domain of p or conventions for zero-dimensional matrices, although its p-word indexing implicitly requires p at least one.

## Audit artifacts

- `paper_bencmark/highambench/tasks/P20/T3/faithfulness/agent_outputs/adjudicator.json` (`33b91bea9848f9e284403ba5996ef9d573290bdee539d90aff7aea9658eb8962`)
- `paper_bencmark/highambench/tasks/P20/T3/faithfulness/agent_outputs/blind_translation.json` (`fd82eef2c6de222d0c0ac907e2dd4e8c73985046fb74d6327ad740ea03d3da22`)
- `paper_bencmark/highambench/tasks/P20/T3/faithfulness/agent_outputs/direct_judge.json` (`1e4c437b52e42019cf8afb9b3b2b65e419aa40b982e11a1fe87a7063baa9bc44`)
- `paper_bencmark/highambench/tasks/P20/T3/faithfulness/agent_outputs/paper_source_contract.json` (`a0c8bbaa2e261f7adc023b1698c08de77fd260aafddc9aa341073c2704530e40`)
- `paper_bencmark/highambench/tasks/P20/T3/faithfulness/agent_outputs/roundtrip_judge.json` (`ac758b88d7a7beca06ca377ea164852ac001db62773eab33ddeb9d19e160af6b`)
- `paper_bencmark/highambench/tasks/P20/T3/faithfulness/agent_outputs/source_contract.json` (`9eae542570f015fc88674a2ddca25ffc17c3f6674875ffa7b1d509a94bfbca4f`)
- `paper_bencmark/highambench/tasks/P20/T3/faithfulness/decision.json` (`555aca327b67e395ae2a1d8d83be3ac568f4c5ab88d638f14a40c786958e02c7`)
- `paper_bencmark/highambench/tasks/P20/T3/faithfulness/inputs/blind_dependency_inventory.json` (`707ebbfaffdc2dac59f2e36035ed9a35870686745713caf7d6157b185652e362`)
- `paper_bencmark/highambench/tasks/P20/T3/faithfulness/inputs/blind_dossier.md` (`ed55d301c9b1849584a259886a4dcfe6ed0bc0dde3fe5d5ac94ecaa8d83259ad`)
- `paper_bencmark/highambench/tasks/P20/T3/faithfulness/inputs/blind_review_packet.md` (`ed55d301c9b1849584a259886a4dcfe6ed0bc0dde3fe5d5ac94ecaa8d83259ad`)
- `paper_bencmark/highambench/tasks/P20/T3/faithfulness/inputs/declaration_dossier.md` (`de0a20bdcc798c7ed05f41742d8c4f9dcde4fd3addf6ef2d118d6ba4f42f2eaf`)
- `paper_bencmark/highambench/tasks/P20/T3/faithfulness/inputs/dependency_inventory.json` (`730438286fea988a1a591a527816d04d9d01909c2e2b36068ce90ed1717e8581`)
- `paper_bencmark/highambench/tasks/P20/T3/faithfulness/inputs/dependency_reuse_direct.json` (`1fcf1c1503943d5ff72546eed502004eca7f0d13975c702cb7ee1e6fa864bcb8`)
- `paper_bencmark/highambench/tasks/P20/T3/faithfulness/inputs/direct_review_packet.md` (`dc155ab8beb53199995d6e0ceedb7aaebde0eae65573f5adf492f5fcb61368b7`)
- `paper_bencmark/highambench/tasks/P20/T3/faithfulness/inputs/paper_source_locator.json` (`413757004ac4d15ac7e55e926e2486e54bdac2db1523d83303ddb4cbffe644f4`)
- `paper_bencmark/highambench/tasks/P20/T3/faithfulness/inputs/source_locator.json` (`decd8905bc8147d8e38b138ea8aa111abc6f17edffd6a0a7b11b676f4bc89fd7`)
