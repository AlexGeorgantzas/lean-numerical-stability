# Chapter 21 Proof-Source Ledger

## Scope

This ledger records nontrivial proof sources used for the 2026-07-18 Chapter
21 audit. External prose or a second-model suggestion is never treated as a
Lean proof.

| Source | Exact role | Lean disposition | Status |
|---|---|---|---|
| Higham, 2nd ed., Chapter 21, pp. 407–414 | Primary labels, equations, algorithms, constants, and scope | Rendered and compared row-by-row with the source inventory and theorem types | ADOPTED AND FORMALIZED / CLASSIFIED |
| Demmel and Higham, “Improved Error Bounds for Underdetermined System Solvers,” SIAM J. Matrix Anal. Appl. 14(1), 1993, §3, especially (3.10)–(3.20) | Primary proof route behind the SNE sentence following (21.11); signed factorwise cancellation, (3.18), and (3.20) | The signed identities and factor bounds are proved in `Higham21SNESigned.lean`; `Higham21SNEUniform.lean` freezes the actual computation on a source-defined radius and proves `higham21_sne_householder_actual_output_source_relative_unit_roundoff_sq` | ADOPTED AND FORMALIZED |
| Kielbasiński and Schwetlick result cited by Lemma 21.2 | Source attribution for one-perturbation symmetrization | The construction and norm bounds are proved locally in `higham21_lemma21_2_source_bundle`; no citation-only axiom remains | ADOPTED AND FORMALIZED |
| Sun–Sun result cited by Theorem 21.3 | Source attribution for the normwise backward-error formula | Equality, lower bound, epsilon-attaining construction, attainment boundary, and scalar witness are proved locally | ADOPTED AND FORMALIZED WITH BOUNDARY CORRECTION |
| Higham Chapter 19 Householder analysis | QR backward error, orthogonality, and rounded Q-action dependencies | Existing repository declarations are instantiated by Chapter 21 wrappers | REUSED |
| Mathlib and `NumStability` norms, inverses, QR, triangular solves, and rounding | Standard foundations and implementation-backed certificates | Reused through normal imports; no parallel axiom API introduced | REUSED |
| Rendered chapter/paper pages under `tmp/pdfs/` | Formula, label, sign, dimension, and citation verification | Audit evidence only; never staged | ADVISORY |
| Oracle / GPT-5.5 Pro, session `chapter21-sne-proof-review` | Requested independent theorem-design review of the SNE closure | Session stalled after an introductory sentence; no mathematical claim or code was adopted | REJECTED / NO SUBSTANTIVE OUTPUT |

## Source Proof Status

| Selected claim | Printed proof status | Local closure status |
|---|---|---|
| Theorem 21.1 and (21.6)–(21.9) | Full proof/sketch in the chapter | Proved with exact finite-radius remainders and rank preservation |
| Lemma 21.2 | Full proof | Proved locally, including source bundle and norm bounds |
| Theorem 21.3 | Statement with external attribution | Proved locally; source boundary case corrected and witnessed |
| Theorem 21.4, Householder | Chapter proof using earlier QR results | `Higham21QMethodFullRowRankComputedQRDomain.of_source_smallness` derives computed top-block nonbreakdown from the rowwise QR perturbation, source right inverse, and rank stability; `higham21_theorem21_4_computed_qhat_rowwise_backward_stable_source` closes the actual rounded panel/solve/action theorem |
| Theorem 21.4, Givens | Included in the printed alternative | `Higham21GivensActualReplayEtaQ_lt_one_of_operational_gammaValid` derives replay smallness from the complete operation schedule, `higham21_givens_actual_topBlock_nonbreakdown_of_source_smallness` derives `hdiag`, and `higham21_theorem21_4_givens_actual_rounded_rowwise_backward_stable_source` closes the actual staged QR/replay theorem |
| Equation (21.11), Q method | Derived in chapter text | Proved through row-wise backward error and (21.7), including the square scalar boundary |
| Equation (21.11), SNE | Citation to Demmel–Higham analysis | Proved for the actual Householder panel, two rounded triangular solves, and rounded `Aᵀŷ` formation; relative error is against canonical `x`, with original `cond2(A)` first-order dependence and an explicit `fp.u²` remainder whose fixed-radius coefficient depends only on `A`, `b`, the dimensions, and `tau` |
| Corrected MGS stability sentence | Citation-only and qualitative | Recurrence proved; stability sentence excluded as `SKIP-QUALITATIVE` |

## Rejected Routes

| Route | Reason rejected |
|---|---|
| Aggregate SNE envelope through `|(AAᵀ)⁻¹|` | Taking absolute values before QR cancellation can introduce an extra condition factor |
| `Higham21SNESplitFactorwiseCond2TransferInput`, aggregate bridge, or a theorem premise named `hTransferred` | Encodes the missing source-level estimate rather than proving it |
| Fixed-`u` coefficient chosen from the final error divided by `u²` | Does not establish a uniform quadratic remainder. The accepted route first majorizes the normalized direction, nearby Gram inverse, QR factors, rounded normal solution, and signed remainder on a fixed source-defined radius, then converts the resulting `theta²` coefficient to an explicit `fp.u²` coefficient under standard half-radius bounds. |
| Givens theorem with a caller-supplied replay/application certificate | Does not account for the actual rounded replay operation |

## Independent Audit Record

| Fragile surface | First check | Independent check | Final disposition |
|---|---|---|---|
| Theorem 21.1 / (21.6)–(21.9) | Focused module builds and theorem-type review | Direction-envelope, rank, remainder, and source-constant comparison | PASS |
| Lemma 21.2 | Source bundle and component theorem review | Assumption and axiom audit | PASS |
| Theorem 21.3 | Formula/attainment modules compile | Boundary witness and theorem-type comparison | PASS WITH CORRECTION |
| Theorem 21.4, Householder | Actual computed path review | Fresh source wrapper derives `lsTheorem20_4ComputedQRNonbreakdown` by perturbation/rank stability; focused closure-module build passed | PASS |
| Theorem 21.4, Givens | Stored-replay theorem review | Fresh source wrapper derives `hdiag` and `hQsmall` from source rank, smallness, and one operational gamma-validity index; focused closure-module build passed | PASS |
| Equation (21.11), Q method | Main, uniform, and scalar endpoints compile | Dimension-boundary, source, and standard-axiom audit | PASS |
| Equation (21.11), SNE | Signed identities, condition transfer, QR majorants, remainder bounds, actual-output closure, and fixed-radius uniform closure compile | Concrete actual-object, original-condition first-order term, source-defined coefficient independent of active computation data, explicit `fp.u²` remainder, public smallness assumptions, and standard-axiom audit | PASS |
