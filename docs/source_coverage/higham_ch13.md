# Higham Chapter 13 Formalization Report — "Block LU Factorization"

## Source and scope

- Edition: Nicholas J. Higham, *Accuracy and Stability of Numerical
  Algorithms*, 2nd ed. (SIAM, 2002).
- Chapter: 13, "Block LU Factorization," printed pp. 245-259 (chapter body
  §§13.1-13.4 pp. 245-257; Problems 13.1-13.9 pp. 257-259).
- Extracted source of truth for this audit:
  `scratchpad/ch13.txt` (rendered 2nd-ed. chapter text).
- Mode: core.
- Parallel split: 3A (Block LU / Matrix Inversion / Condition Estimation
  cluster, Chapters 13-15).
- Primary Lean modules (`NumStability/Algorithms/LU/`):
  `BlockLU.lean` (monolithic core, ~82k lines), plus the source-closure and
  family layers `BlockLUSourceClosure`, `BlockLURowSourceClosure`,
  `BlockLUArbitraryNormSourceClosure`, `BlockLUSPDSourceClosure`,
  `BlockLUSPDFamilies`, `BlockLUComputationSourceClosure`,
  `BlockLUFirstOrderFamilies`, `BlockLUPointRowGrowthSourceClosure`,
  `BlockLUScalarGrowthBridge`, `BlockLUVarying`, `BlockLUTable13_1Families`.
- **Selected-scope gate: PASS** (0 open primary or numbered-equation rows).

This audit is statement-level: I verified each Lean statement against the
printed row for honest strength (no hidden target-equivalent hypothesis,
constants derived, correct object), on top of the worktree's existing green
build. Load-bearing declarations were axiom-checked.

## Primary-label assessment

| Source label | Printed summary | Status | Lean decl(s) | Scope / honest-strength notes |
|---|---|---|---|---|
| Algorithm 13.1 | Partitioned outer-product LU: factor A11, solve U12/L21, form Schur S, recurse | VERIFIED | `higham13_algorithm13_1_partitioned_lu_reconstructs`, `higham13_algorithm13_1_schur_complement_eq`, `higham13_eq13_1_partitioned_outer_product_lu` | Exact block-matrix reconstruction from the four step equations; step 4 identified with the Schur complement `A22 − A21 A11⁻¹ A12`. |
| Theorem 13.2 | Unique block LU ⟺ first m−1 leading principal block submatrices nonsingular | VERIFIED | `BlockLUFactSpec.existsUnique_iff_leadingPrincipalBlockNonsingular13_2` (both directions), `LeadingPrincipalBlockNonsingular13_2` | Iff proved. For an (m+1)-block matrix the hypothesis is nonsingularity of leading prefixes of sizes 1..m, i.e. the first m = (m+1)−1 leading principal block submatrices — matches the printed count. |
| Algorithm 13.3 | Block LU: U11=A11, U12=A12, solve L21, S=A22−L21A12, recurse | VERIFIED | `higham13_algorithm13_3_block_lu_reconstructs`, `higham13_algorithm13_3_schurStageMatrixBlock`, `..._lowerFromMatrixStages`, `..._upperFromMatrixStages`, `BlockLUFactSpec` | Concrete recursive stage machinery producing genuine block-triangular factors with identity diagonal. |
| Algorithm 13.4 | Recursively partitioned LU (half-size, no block-size choice) | VERIFIED | `higham13_algorithm13_4_recursive_partitioned_lu_reconstructs`, `higham13_eq13_3_recursive_partitioned_lu` | Exact three-factor reconstruction of the (13.3) recursive partition. |
| Theorem 13.5 (Demmel & Higham) | Partitioned LU backward error (13.7): ‖ΔA‖ ≤ u(δ‖A‖+θ‖L̂‖‖Û‖)+O(u²), δ/θ recurrences | VERIFIED | `higham13_theorem13_5_eq13_7_from_computation`, `blockErrorDelta`, `blockErrorTheta`, `higham13_eq13_{8,9,10,11,12,13}_*`, `higham13_theorem13_5_eq13_7_from_computation` | Proved for an actual recursively computed execution (`PartitionedLUComputationFirstOrder`); δ,θ recurrences match (13.7). Underlying (13.4)-(13.6) are the source's BLAS3/local-LU assumption models. |
| Theorem 13.6 (Demmel, Higham & Schreiber) | Block LU + solve backward error (13.16): ‖ΔAᵢ‖ ≤ dₙu(‖A‖+‖L̂‖‖Û‖)+O(u²) | VERIFIED | `higham13_theorem13_6_eq13_16_from_factor_solve_estimates`, `..._firstOrder_...`, DHS path `demmelHighamSchreiber13_6_*`, and computation-derived `higham13_theorem13_6_implementation1_family_from_partitioned_computation_and_conventional_recursive_solve` | Book omits its proof (cites DHS [326]). Lean gives (a) a structured derivation from assumptions (13.4),(13.14),(13.15) and (b) a genuine Implementation-1 endpoint that derives the conventional BLAS/solve constants from the FP roundoff model — at or above source strength. |
| Theorem 13.7 (DHS) | Block-diagonally-dominant A has block LU; Schur complements inherit the dominance | VERIFIED | `higham13_theorem13_7_algorithm13_3_opNorm2_column`, `..._row`, `higham13_theorem13_7_and_13_8_clm_column_source_closure`, `..._clm_row_...` | Constructs the whole pivot table from source hypotheses (full nonsingularity + BDD); no all-leading-prefix or prebuilt-pivot assumption. Column & row, Euclidean and arbitrary subordinate operator norm. |
| Theorem 13.8 (DHS) | For BDD A, max active Schur block norm ≤ 2·max block norm of A | VERIFIED | `higham13_theorem13_8_algorithm13_3_opNorm2_column`, `..._row`, arbitrary-norm halves in `..._clm_column/row_source_closure` | Printed `2·max` growth estimate proved on the actual active stages, column & row, Euclidean & arbitrary norm. |
| Lemma 13.9 (DHS) | SPD ⟹ ‖A21 A11⁻¹‖₂ ≤ κ₂(A)^{1/2} | VERIFIED | `higham13_lemma13_9_cholesky_route_rectOpNorm2Le_from_spd_leading_nonsingInv_kappa2` | Derives from bare `IsSymPosDef` via `cholesky_existence`; `A11⁻¹` = `R11⁻¹R11⁻ᵀ`, bound `√(κ₂(A))` = `√(‖A‖₂‖A⁻¹‖₂)`. (The book's stronger attainable bound in the Notes is not claimed.) |
| Lemma 13.10 (DHS) | SPD ⟹ κ₂(S) ≤ κ₂(A) for S = A22 − A21A11⁻¹A21ᵀ | VERIFIED (two operator halves) | `higham13_lemma13_10_schur_opNorm2Le_of_full_operator_bound` (‖S‖₂ ≤ ‖A‖₂ via Loewner) + `higham13_problem13_4_Sinv_finiteOpNorm2Le_from_source_posDef_block_inverse` (‖S⁻¹‖₂ ≤ ‖A⁻¹‖₂) | The two halves multiply to κ₂(S) ≤ κ₂(A); both used in the SPD (13.24) chain. Honest decomposition, no separate monolithic κ₂ theorem needed. |

All ten primary labels: **VERIFIED**.

## Numbered-equation coverage

Printed chapter 13 numbers equations **(13.1)–(13.26)** only. There are no
(13.27)–(13.29) in the source (the "(13.1)–(13.29)" in the audit brief is an
overcount; (13.26) is the last, appearing in Problem 13.4).

| Eq. | Content | Status | Lean evidence |
|---|---|---|---|
| (13.1) | Partitioned outer-product identity | VERIFIED | `higham13_eq13_1_partitioned_outer_product_lu` |
| (13.2) | One block LU step, Schur form | VERIFIED | `higham13_eq13_2_block_lu_step` |
| (13.3) | Recursive partition identity | VERIFIED | `higham13_eq13_3_recursive_partitioned_lu` |
| (13.4) | Level-3 BLAS matmul error model | VERIFIED (assumption model) | `higham13_eq13_4_from_matmul_spec` |
| (13.5) | Triangular multi-RHS solve error model | VERIFIED (assumption model) | `higham13_eq13_5_from_triangular_solve_spec` |
| (13.6) | Local A11 LU error assumption | VERIFIED (assumption model) | `higham13_eq13_6_from_local_lu_spec` |
| (13.7) | Theorem 13.5 backward bound + δ,θ | VERIFIED | `higham13_theorem13_5_eq13_7_from_computation` |
| (13.8)–(13.9) | L11U12/L21U11 residuals | VERIFIED | `higham13_eq13_{8,9}` machinery in `higham13_theorem13_5_*` |
| (13.10) | S formation subtraction error | VERIFIED | `higham13_eq13_10_from_subtraction_spec` |
| (13.11a/b) | Trailing Schur residual | VERIFIED | `higham13_eq13_11a/b_*`, `higham13_eq13_11_from_matmul_subtraction_specs` |
| (13.12a/b) | Inductive Schur factor assumption | VERIFIED | `higham13_eq13_12_from_induction_spec` |
| (13.13) | ΔA22 combined bound | VERIFIED | `higham13_eq13_13_*` |
| (13.14) | Block-solve residual model (13.3 step 2) | VERIFIED (assumption model) | `higham13_eq13_14_from_block_solve_spec` |
| (13.15) | Diagonal-block solve model | VERIFIED (assumption model) | `higham13_eq13_15_from_diagonal_block_solve_spec` |
| (13.16) | Theorem 13.6 bound | VERIFIED | `higham13_theorem13_6_eq13_16_*` |
| (13.17) | Block diagonal dominance (columns) | VERIFIED (definition) | `IsBlockDiagDomCol`, `IsBlockDiagDomRow`, `blockDiagDomGamma`, `isBlockDiagDomCol_iff_gamma_nonneg` |
| (13.18) | Theorem 13.7 column-dominance chain | VERIFIED | `higham13_eq13_18_min_lower_bound`, `..._vecNorm2_min_lower_bound`, `..._schur_column_dominance` |
| (13.19) | max‖Aij‖ ≤ ‖A‖ ≤ Σ‖Aij‖ | VERIFIED | `higham13_eq13_19`, `..._block_le_norm`, `..._norm_le_sum` |
| (13.20) | General r×r partition | VERIFIED | `higham13_eq13_20_partition` |
| (13.21) | ‖U‖ ≤ ρₙ‖A‖ (block max-norm) | VERIFIED | `higham13_eq13_21_blockMaxNorm_bound*`, `SchurStageUpperBlockBound13_21` |
| (13.22) | ‖L‖‖U‖ ≤ nρₙ³κ(A)‖A‖ (arbitrary) | VERIFIED | `higham13_problem13_4_eq13_22_exists_blockLUFact_succ_of_pivot_right_inverse` — exact Algorithm-13.3 pivot-right-inverse data, nonsingularity, and the dimension budget construct the block factors and full recursive endpoint; no factor-norm or target-scale premise. |
| (13.23) | Point-row: ‖L‖‖U‖ ≤ 8nκ(A)‖A‖ | VERIFIED | `higham13_problem13_4_eq13_23_exists_blockLUFact_succ_of_pointRow`, using `higham13_algorithm13_3_active_entry_eq_noPivotReducedStage` and `..._matrixStageHistory_le_noPivotReducedHistory` — point-row dominance constructs scalar no-pivot LU with `ρₙ≤2`, transfers that bound to every active block-Schur stage, and invokes the global (13.22) aggregation. |
| (13.24) | SPD ‖L‖₂‖U‖₂ ≤ √m(1+m√κ₂)‖A‖₂ | VERIFIED | `higham13_eq13_24_algorithm13_3_spd` (from Lemmas 13.9–13.10, no factor-norm premises) |
| (13.25) | SPD backward error cₙ√m u‖A‖₂(2+m√κ₂) | VERIFIED (as Thm-13.6 corollary) | `higham13_eq13_25_spd_firstOrder_from_eq13_24`, `higham13_eq13_25_algorithm13_3_spd`, family forms in `BlockLUSPDFamilies` — conditional on the Theorem 13.6 conclusion, exactly the source's "It follows from Theorem 13.6 …" |
| (13.26) | Problem 13.4 partition | VERIFIED | `higham13_eq13_26_partition` |

## Central definitions

- Block LU factorization object: `BlockLUFactSpec` (identity-diagonal block-
  triangular L, block-upper U, product = A) — matches the display on p. 246.
- Block diagonal dominance (13.17), columns and rows: `IsBlockDiagDomCol`,
  `IsBlockDiagDomRow`, with `γⱼ` amount `blockDiagDomGamma` and the
  transpose-duality `isBlockDiagDomRow_iff_col_transpose`.
- Schur complement stage: `higham13_algorithm13_3_schurStageBlock/MatrixBlock`,
  `blockSchur`, `higham13_clmBlockSchur` (arbitrary-norm).
- Varying block dimensions ("the blocks can be of different dimensions",
  p. 247): `Higham13VaryingBlockLUFactSpec` and its step/uniqueness lemmas in
  `BlockLUVarying.lean`.

## Problems accounting (13.1–13.9)

| Problem | Content | Status | Lean evidence |
|---|---|---|---|
| 13.1 (Varah) | Block tridiagonal ‖Li,i−1‖, ‖Uii‖ bounds, col & row | VERIFIED | `higham13_problem13_1_column_step_bounds`, `..._row_step_bounds` |
| 13.2 | Diag dom ⇏ block diag dom and vice versa (1-,∞-norms) | VERIFIED | `higham13_problem13_2_*` counterexample defs + `higham13_problem13_2_incomparability` |
| 13.3 | Symmetric + positive diag + block-row-BDD ⇒ posdef? (No) | VERIFIED | `higham13_problem13_3_counterexample` (+ symmetric/positive-diag/row-BDD/singular/not-SPD witnesses) |
| 13.4 | ‖A21A11⁻¹‖ ≤ nρₙκ(A); κ(S) ≤ ρₙκ(A) | VERIFIED | Local source-growth forms `higham13_problem13_4_maxEntry_bounds_from_source_growthFactorEntry_exact_kappa`, `..._L21_eq13_22_premise_from_source_growthFactorEntry_exact_kappa`; recursive active-suffix assembly and factor endpoint `higham13_problem13_4_eq13_22_exists_blockLUFact_succ_of_pivot_right_inverse`. The source's data-dependent `ρₙ` remains the defined growth factor, not an assumed target bound. |
| 13.5 | Point-col-BDD ⇒ ‖A21A11⁻¹‖₁ ≤ 1 | VERIFIED | `higham13_problem13_5_oneNormRect_bound` (+ tail/diag chain) |
| 13.6 | Ax=b and AX=B backward error under Thm 13.5 conditions | VERIFIED | `higham13_problem13_6_single_rhs_backward_error_*`, `..._multiple_rhs_residual_*` (identities + first-order) |
| 13.7 | det(X)=det(A)det(D−CA⁻¹B); commuting-block corollary | VERIFIED | `higham13_problem13_7_det_schur`, `..._det_commuting_AC` |
| 13.8 | Block 2×2 inverse via Schur complement | VERIFIED | `higham13_problem13_8_block_inverse` |
| 13.9 | (I−AB)⁻¹ identity; Sherman–Morrison–Woodbury | VERIFIED | `higham13_problem13_9_resolvent_identity`, `..._sherman_morrison_woodbury` |

## Honest-strength notes

- **(13.22)/(13.23) and Problem 13.4 are source-closed.** The arbitrary route
  constructs the full recursive block-factor witness from Algorithm 13.3 pivot
  right inverses and the actual finite matrix-stage growth object. For the
  point-row row, `BlockLUPointRowGrowthSourceClosure` constructs exact scalar
  no-pivot LU factors and proves the scalar equation-(9.5) history has
  `ρₙ ≤ 2`. `BlockLUScalarGrowthBridge` proves that every active block Schur
  entry at stage `k` is the scalar reduced entry after `k*r` pivots, so the
  complete block history is dominated by the scalar history. The final
  `8nκ(A)‖A‖` theorem has no growth, factor-norm, or target-scale hypothesis.
- **Theorem 13.6 exceeds the book.** The source omits the proof; the Lean
  supplies both an assumption-level derivation and an Implementation-1 endpoint
  whose (13.14)/(13.15) perturbations are *derived* from the conventional
  floating-point model (`FPModel`, `gamma`) rather than assumed.
- **Lemma 13.10** appears as the two operator inequalities (‖S‖₂≤‖A‖₂ and
  ‖S⁻¹‖₂≤‖A⁻¹‖₂) whose product is κ₂(S)≤κ₂(A); this is the exact content, used
  in the (13.24) chain.
- **(13.24)** assumes no factor-norm premises — the two factor bounds and their
  product are derived from SPD via Lemmas 13.9–13.10.
- **(13.25)** is stated conditionally on the Theorem 13.6 conclusion for the
  computed factors plus the source's explicit exact/computed product
  comparison — matching the printed "It follows from Theorem 13.6 …".
- Table 13.1 (empirical summary table) is formalized as product/backward-error
  families per row in `BlockLUTable13_1Families.lean` and
  `higham13_table13_1_*` (col-BDD, point-col-BDD, block-row-BDD, point-row,
  arbitrary, SPD); the arbitrary row uses the actual matrix-stage `ρₙ`, and the
  point-row row inherits the source-closed (13.23) specialization.

## Axiom spot-check

`lake build NumStability.Algorithms.LU.BlockLUScalarGrowthBridge` passes
(3053 jobs). `#print axioms` on the new active-entry identity, whole-history
domination, point-row block-history `ρ≤2`, and final source-facing (13.23)
factor witness each reports only `[propext, Classical.choice, Quot.sound]`.
The earlier eight load-bearing checks (Theorems 13.2, 13.5, 13.7–13.8,
(13.24), Lemma 13.9, and Problem 13.9) report the same. No `sorry` or custom
axioms.

## Cross-chapter role

- **Consumes:** Chapter 9 Gaussian elimination — the growth factor ρₙ for GE
  without pivoting, and the point-diagonal-dominance growth bound ρₙ≤2
  (Theorem 9.9), which underpin (13.21)–(13.23) and the Table 13.1 point/block
  rows (`BlockLUPointRowGrowthSourceClosure` supplies the scalar Thm-9.9 route;
  `BlockLUScalarGrowthBridge` transfers its history to every Algorithm-13.3
  block stage). The conventional level-3 BLAS and triangular-solve error models
  behind (13.4)/(13.5)/(13.14)/(13.15) reuse the inner-product / substitution
  roundoff machinery (Chapters 3, 8) via `FPModel`/`gamma`; the SPD lemmas
  reuse Cholesky existence (Chapter 10). Chapter 12 (iterative refinement) is
  **not** a dependency of Chapter 13; if anything refinement is applied
  *downstream* to block-LU solutions.
- **Provides:** existence/uniqueness of block LU (Theorem 13.2), the
  backward-error theory for partitioned (Theorem 13.5) and block (Theorem 13.6)
  LU, the stability classification of Table 13.1, and the reusable
  Schur-complement determinant/inverse and Sherman–Morrison–Woodbury identities
  (Problems 13.7–13.9), which are foundational for matrix inversion (Chapter 14)
  and elsewhere.

## Selected-scope gate

**PASS.** All ten primary labels, all numbered equations (13.1)–(13.26), the
central definitions, and Problems 13.1–13.9 are VERIFIED. In particular,
(13.22) constructs the arbitrary-matrix `nρₙ³κ(A)‖A‖` factor witness, and
(13.23) constructs the point-row `8nκ(A)‖A‖` witness after deriving `ρₙ≤2`
from the actual scalar no-pivot history. No MISSING, PARTIAL, or BLOCKED rows.
