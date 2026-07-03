# Higham Chapter 16 Source Coverage Ledger

## Source and Scope

- Edition: Higham, *Accuracy and Stability of Numerical Algorithms*, 2nd ed. (SIAM, 2002), verified from `pdfinfo` title metadata and source DOI path.
- Chapter: 16, "The Sylvester Equation".
- Printed pages read: 305-319.
- Source file: `References/1.9780898718027.ch16.pdf`.
- Mode: core.
- Parallel split: 3B.
- Planning documents consulted: `chapter_splitting/HIGHAM_PARALLEL_FORMALIZATION_BLUEPRINT.md`, the Split 3B section of `chapter_splitting/split_primary_contracts.md`, and the Chapter 16 rows of `chapter_splitting/chapter_index.md`.
- Selected-scope gate: FAIL. Several central square-Frobenius results, the rectangular vec/Kronecker formulation, the diagonal (16.3) foundation, and a conditional exact Schur-coordinate transform are proved, but the full core pass still has open selected rows for Kronecker spectra/eigenvalue criteria, Schur/Hessenberg-Schur method surfaces, floating-point stability, exact condition-number formulas, and the practical error bound.

## Completed Selected Targets

| Source label | Lean declaration | File | Theorem surface | Notes |
|---|---|---|---|---|
| (16.1), rectangular setup | `sylvesterOpRect`, `IsSylvesterSolutionRect` | `LeanFpAnalysis/FP/Algorithms/Sylvester/Higham16.lean` | Definition/predicate | Source-facing rectangular statement. |
| (16.1), square specialization | `sylvesterOp`, `sylvesterOpRect_square_eq_sylvesterOp` | `SylvesterSpec.lean`, `Higham16.lean` | Definition/theorem | Existing proved infrastructure is square; wrapper records the relationship. |
| (16.2), vec/Kronecker system | `sylvesterVecCoeff`, `sylvesterVecCoeff_mulVec_vec`, `sylvester_vec_system_iff_solution` | `Higham16.lean` | Definition/theorems | Source-facing rectangular coefficient `(I_n kron A) - (B^T kron I_m)` with the vectorized system iff the Sylvester equation. |
| p.306 prose `vec(AXB)` identity | `vec_triple_product_rect`, `vec_left_mul_rect`, `vec_right_mul_rect` | `Higham16.lean` | Theorems | Thin wrappers over Mathlib `Matrix.vec`/Kronecker identities in the column-stacking product index order. |
| (16.3), diagonal coefficient foundation | `sylvesterVecCoeff_diagonal`, `sylvesterVecCoeff_diagonal_det`, `sylvesterVecCoeff_diagonal_det_ne_zero_iff` | `Higham16.lean` | Theorems | Diagonal-basis determinant and nonsingularity fragment; full Kronecker spectral theorem remains open. |
| (16.5), exact Schur-coordinate transform | `sylvester_schur_transform_identity`, `sylvester_schur_transform_solution_iff` | `Higham16.lean` | Theorems | Operator identity and equation-level equivalence conditional on supplied orthogonal Schur-style factors; does not assert Schur existence, triangular solves, or floating-point stability. |
| (16.9), residual object only | `sylvesterResidualRect`, `sylvesterResidual` | `Higham16.lean`, `SylvesterSpec.lean` | Definition | The floating-point stability bound itself remains open. |
| (16.10) | `IsBackwardError` | `SylvesterSpec.lean` | Predicate | Square Frobenius backward-error feasibility predicate. |
| (16.11) | `residual_decomposition` | `SylvesterSpec.lean` | Theorem | Square residual decomposition from perturbations. |
| (16.12) | `residual_bound` | `SylvesterSpec.lean` | Theorem | Square Frobenius residual bound from backward perturbation bounds. |
| (16.13) | `IsSVD`, `svdResidual` | `SylvesterBackward.lean` | Definitions | SVD-coordinate setup for the square case. |
| (16.14) | `backward_error_lower_sq` | `SylvesterBackward.lean` | Theorem | Entrywise Cauchy-Schwarz lower-cost direction for the uncoupled equations. |
| (16.16) | `xiSq`, `xiSq_nonneg` | `SylvesterBackward.lean` | Definition/lemma | Squared xi functional. |
| (16.15), (16.17)-(16.19), partial | `sylvesterBackwardResidual`, `isSVD_eq_matMul_diag`, `svdResidual_backwardResidual`, `xiSq_le_three_eta_sq_of_original_residual`, `xiSq_le_three_eta_sq_of_backward_error`, `sylvesterAmplificationMu`, `sylvesterAmplificationMuSquare`, `sylvesterAmplificationMu_square_eq`, `one_le_sylvesterAmplificationMuSquare`, `xiSq_amplification_bound`, `amplification_factor_bound`, `xiSq_le_mu_relative_residual_sq` | `SylvesterBackward.lean` | Definitions/theorems | Names the source amplification factor and square specialization, proves the conditional square-case `mu >= 1` algebra, proves that a square Frobenius backward-error certificate at cost `eta` bounds SVD-coordinate `xi^2` by `3 * eta^2`, and bounds xi-squared in the μ-relative-residual form; the full optimizer/minimum eta theorem remains open. |
| Lyapunov specialization | `lyapunovOp`, `lyapunovOp_eq_sylvesterOp` | `SylvesterSpec.lean` | Definition/theorem | Models the Lyapunov operator as a Sylvester special case. |
| Lyapunov p.312 symmetric uniqueness | `lyapunov_solution_iff_sylvester_special`, `lyapunov_unique_solution_of_sep`, `lyapunov_transpose_solution_of_symmetric_rhs`, `lyapunov_solution_symmetric_of_symmetric_rhs` | `Higham16.lean` | Theorems | Uses `sep(A,-A^T)` to prove uniqueness and symmetry for symmetric right-hand sides. |
| (16.21), partial | `lyapunovSpectralTransform`, `lyapunovSpectralTransform_frobNormSq`, `lyapunovBackwardResidual`, `lyapunovSpectralTransform_backwardResidual`, `lyapunovSpectralBackwardResidual`, `lyapunovSpectralBackwardResidual_eq_diagMatrix`, `lyapunovBackwardScalarEq`, `lyapunovBackwardScalarEq_iff_unscaled`, `lyapunovBackwardScalarEq_iff_residual_eq`, `lyapunovBackwardScalarEq_of_spectral_decomposition`, `lyapunovBackwardScalarEq_iff_diagMatrix_eq`, `lyapunovXiSq`, `lyapunovXiSqSimpleBound`, `lyapunovXiSq_le_simple_bound`, `lyapunovAmplificationMu`, `lyapunovXiSq_le_min_eigen_bound`, `lyapunovXiSq_spectral_le_min_eigen_bound`, `lyapunovXiSq_le_mu_relative_residual_sq` | `SylvesterBackward.lean` | Definitions/theorems | Records the Lyapunov spectral-coordinate transform, original perturbation residual, original-to-spectral residual bridge for `Y = U Lambda U^T`, printed scaled scalar equation, diagonal-matrix residual form, `xi^2` formula, simple `xi^2` upper bound, Lyapunov amplification factor, and xi-level μ-relative-residual bound; the eta theorem remains open. |
| (16.22), algebraic perturbation identity | `sylvester_perturbation_equation`, `sylvester_perturbation_first_order` | `SylvesterPerturbation.lean` | Theorems | Matrix-form Kronecker statement is still open. |
| (16.25), sep-weakened perturbation route | `sylvester_perturbation_bound`, `sylvester_relative_perturbation`, `condSylvester` | `SylvesterPerturbation.lean` | Theorem/definition | Uses `SepLowerBound`; exact `P^{-1}` condition-number surface remains open. |
| (16.26), sep definition/lower-bound form | `sylvesterSepRatios`, `sylvesterSepInf`, `sylvesterSepInf_nonneg`, `sylvesterSepInf_le_ratio`, `SepLowerBound_le_sylvesterSepInf_of_nonempty`, `SepLowerBound_of_pos_le_sylvesterSepInf`, `SepLowerBound_iff_pos_le_sylvesterSepInf_of_nonempty`, `SepLowerBound` | `Higham16.lean`, `SylvesterSpec.lean` | Definition/theorems/predicate | Exact nonnegative infimum model plus an equivalence between the existing lower-bound predicate and positive lower bounds of the infimum when the feasible ratio set is nonempty; attained-minimum bridge remains open. |
| (16.28), a posteriori route | `sylvester_aposteriori_bound`, `sylvester_relative_aposteriori_bound` | `SylvesterPerturbation.lean`, `Higham16.lean` | Theorems | Square Frobenius error-residual bound and relative source wrapper via `SepLowerBound`. |
| (16.30) | `generalizedSylvesterAXB_CXD_residual`, `IsGeneralizedSylvesterAXB_CXD_Solution`, `generalizedSylvesterAXB_CXD_residual_zero_iff_solution` | `Higham16.lean` | Definition/predicate/theorem | Residual surface plus zero-residual equivalence for the generalized equation. |
| (16.31) | `IsGeneralizedSylvesterPairSolution` | `Higham16.lean` | Predicate | Coupled generalized Sylvester surface. |
| (16.32) | `riccatiResidual`, `IsRiccatiSolution`, `riccatiResidual_zero_iff_solution` | `Higham16.lean` | Definition/predicate/theorem | Residual surface plus zero-residual equivalence for the algebraic Riccati equation. |

## Source Inventory

| ID | Source location | Kind | Statement summary | Precision | Generality | Source proof | Dependencies | Decision | Reason code | Lean artifact/status |
|---|---|---|---|---|---|---|---|---|---|---|
| H16.Eq16_1.sylvester_equation | p.306, (16.1) | equation/definition | Sylvester equation operator and solution predicate. | precise | general rectangular | not applicable | matrix product | FORMALIZE_CORE | CORE-NUMBERED-EQUATION | `sylvesterOpRect`, `IsSylvesterSolutionRect`; square proofs use `sylvesterOp`. |
| H16.Eq16_2.vec_kronecker_system | p.306, (16.2) | equation | Vec/Kronecker linear-system form. | precise | general rectangular | citation/background | Kronecker, vec | FORMALIZE_CORE | CORE-NUMBERED-EQUATION | `sylvesterVecCoeff`, `sylvesterVecCoeff_mulVec_vec`, `sylvester_vec_system_iff_solution`. |
| H16.Vec_AXB | p.306, prose | identity | Vec relation for triple matrix product. | precise | general rectangular | citation/background | Kronecker, vec | FORMALIZE_CORE | CORE-PRECISE-PROSE | `vec_triple_product_rect`; special left/right wrappers `vec_left_mul_rect`, `vec_right_mul_rect`. |
| H16.Eq16_3.kronecker_eigenvalues | p.306, (16.3) | equation | Eigenvalue difference formula for the structured coefficient matrix. | precise | general | citation-only | Kronecker spectrum | FORMALIZE_CORE | CORE-NUMBERED-EQUATION | Partial diagonal foundation: `sylvesterVecCoeff_diagonal`, `sylvesterVecCoeff_diagonal_det`, `sylvesterVecCoeff_diagonal_det_ne_zero_iff`; full spectral theorem open. |
| H16.NonsingularCommonEigenvalues | p.306, prose | precise prose | Nonsingularity criterion via no common eigenvalues. | precise | general | follows from (16.3) | H16.Eq16_3 | DEFER | DEFER-MISSING-PRECISE-STATEMENT | Open until (16.3) is formalized. |
| H16.Eq16_4.real_schur | p.307, (16.4) | equation | Real Schur decompositions for A and B. | precise | general | citation | Schur decomposition | DEFER | DEFER-MISSING-PRECISE-STATEMENT | Existence open; `sylvester_schur_transform_identity` is conditional on supplied factors and does not prove (16.4). |
| H16.Eq16_5.schur_transform | p.307, (16.5) | equation | Transformed Sylvester equation under Schur factors. | precise | general | sketch | H16.Eq16_4 | FORMALIZE_CORE | CORE-NUMBERED-EQUATION | Supplied-factor exact algebra: `sylvester_schur_transform_identity` and `sylvester_schur_transform_solution_iff`; Schur existence and solve path remain open. |
| H16.Eq16_6.block_recurrence | p.307, (16.6) | recurrence | Block quasi-triangular solve recurrence. | precise | block family | sketch | Schur/block API | DEFER | DEFER-MISSING-PRECISE-STATEMENT | Open algorithm/spec row. |
| H16.Eq16_7.triangular_big_system_error | p.307, (16.7) | error bound | Triangular-system backward-error model for the vectorized Schur system. | precise | floating-point model | upstream theorem | Ch8 triangular solve | DEFER | DEFER-LATER-CHAPTER | Open; depends on upstream Ch8 theorem instantiation and vec/Kronecker bridge. |
| H16.Eq16_8.schur_residual_componentwise | pp.307-308, (16.8) | inequality | Componentwise residual consequence of (16.7). | precise | floating-point model | sketch | H16.Eq16_7 | DEFER | DEFER-MISSING-PRECISE-STATEMENT | Open. |
| H16.Eq16_9.overall_residual_bound | p.308, (16.9) | inequality | Normwise residual guarantee for computed solution. | precise | floating-point model | citation/sketch | QR backward stability, Schur method | DEFER | DEFER-LATER-CHAPTER | Open; depends on Ch19-style QR stability and computed-path modeling. |
| H16.Eq16_10.backward_error | p.309, (16.10) | definition | Normwise backward error with tolerances. | precise | square current API | not applicable | perturbation predicates | FORMALIZE_CORE | CORE-NUMBERED-EQUATION | `IsBackwardError`; minimum itself is represented as feasibility predicate. |
| H16.Eq16_11.residual_decomposition | p.309, (16.11) | equation | Backward perturbations imply residual decomposition. | precise | square current API | algebraic | `sylvesterResidual` | FORMALIZE_CORE | CORE-NUMBERED-EQUATION | `residual_decomposition`; rectangular residual object in `Higham16`. |
| H16.Eq16_12.residual_bound | p.309, (16.12) | inequality | Residual norm bound from perturbation tolerances. | precise | square current API | complete | Frobenius norm lemmas | FORMALIZE_CORE | CORE-NUMBERED-EQUATION | `residual_bound`. |
| H16.Eq16_13.svd_coordinates | p.309, (16.13) | equation | SVD-coordinate transformed residual equation. | precise | square current API | sketch | SVD, orthogonality | FORMALIZE_CORE | CORE-NUMBERED-EQUATION | `IsSVD`, `svdResidual`; full perturbation optimizer still open. |
| H16.Eq16_14.uncoupled_equations | p.309, (16.14) | equation | Entrywise uncoupled scalar constraints. | precise | square current API | sketch | H16.Eq16_13 | FORMALIZE_CORE | CORE-NUMBERED-EQUATION | `backward_error_lower_sq` lower-cost theorem. |
| H16.Eq16_15.eta_xi_bounds | p.310, (16.15) | inequality | Eta bounded above and below by xi up to sqrt(3). | precise | square current API | sketch | optimizer existence | FORMALIZE_CORE | CORE-NUMBERED-EQUATION | Partial lower-direction bridge: `backward_error_eta_bound`, `sylvesterBackwardResidual`, `svdResidual_backwardResidual`, `xiSq_le_three_eta_sq_of_original_residual`, `xiSq_le_three_eta_sq_of_backward_error`; full optimizer/minimum and upper-direction eta theorem open. |
| H16.Eq16_16.xi_formula | p.310, (16.16) | equation | Xi residual-weighted formula. | precise | square current API | derivation | SVD residual | FORMALIZE_CORE | CORE-NUMBERED-EQUATION | `xiSq`, `xiSq_nonneg`. |
| H16.Eq16_17.eta_residual_amplification | p.310, (16.17) | inequality | Backward error bounded by amplified relative residual. | precise | square current API | follows from 16.15-16.16 | eta/xi closure | FORMALIZE_CORE | CORE-NUMBERED-EQUATION | Partial: backward-error certificates imply the lower-direction `xi^2 <= 3 eta^2` bridge via `xiSq_le_three_eta_sq_of_backward_error`, and the xi-squared μ-form is `xiSq_le_mu_relative_residual_sq`; full eta result open. |
| H16.Eq16_18.mu_definition | p.310, (16.18) | definition | Amplification factor. | precise | rectangular scalar surface | not applicable | singular values | FORMALIZE_CORE | CORE-NUMBERED-EQUATION | `sylvesterAmplificationMu`. |
| H16.Eq16_19.square_mu | p.310, (16.19) | equation/prose | Square-case amplification factor and conditional `mu >= 1` algebra. | precise | square | follows | H16.Eq16_18 | FORMALIZE_CORE | CORE-NUMBERED-EQUATION | `sylvesterAmplificationMuSquare`, `sylvesterAmplificationMu_square_eq`, `one_le_sylvesterAmplificationMuSquare`; residual xi-squared bound is expressed by `amplification_factor_bound` and `xiSq_le_mu_relative_residual_sq`. |
| H16.Eq16_20.large_mu_conditions | p.310, (16.20) | heuristic inequalities | Qualitative "large" regime using much-greater notation. | partly precise | qualitative | explanatory | none | SKIP | SKIP-QUALITATIVE | Not encoded in core. |
| H16.LyapunovDefinition | pp.311-312 | definition | Lyapunov equation as Sylvester special case. | precise | square | not applicable | transpose | FORMALIZE_CORE | DEP-REQUIRED | `lyapunovOp`, `lyapunovOp_eq_sylvesterOp`. |
| H16.LyapunovSymmetricUniqueness | p.312 | precise prose | Symmetric right-hand side and nonsingularity imply unique symmetric solution. | precise | square | sketch | uniqueness, spectrum | FORMALIZE_CORE | CORE-PRECISE-PROSE | `lyapunov_unique_solution_of_sep`, `lyapunov_solution_symmetric_of_symmetric_rhs`; uses `SepLowerBound` as the nonsingularity certificate. |
| H16.Eq16_21.lyapunov_uncoupled | p.312, (16.21) | equation/formula group | Lyapunov backward-error scalar equations, `xi^2` expression, simple `xi^2` upper bound, Lyapunov amplification factor, and xi-level μ relative-residual bound. | precise | square | derivation | spectral decomposition | FORMALIZE_CORE | CORE-NUMBERED-EQUATION | Partial: `lyapunovSpectralTransform`, `lyapunovSpectralTransform_frobNormSq`, `lyapunovBackwardResidual`, `lyapunovSpectralTransform_backwardResidual`, `lyapunovSpectralBackwardResidual`, `lyapunovSpectralBackwardResidual_eq_diagMatrix`, `lyapunovBackwardScalarEq`, `lyapunovBackwardScalarEq_iff_unscaled`, `lyapunovBackwardScalarEq_iff_residual_eq`, `lyapunovBackwardScalarEq_of_spectral_decomposition`, `lyapunovBackwardScalarEq_iff_diagMatrix_eq`, `lyapunovXiSq`, `lyapunovXiSqSimpleBound`, `lyapunovXiSq_le_simple_bound`, `lyapunovAmplificationMu`, `lyapunovXiSq_le_min_eigen_bound`, `lyapunovXiSq_spectral_le_min_eigen_bound`, `lyapunovXiSq_le_mu_relative_residual_sq`; eta bridge still open. |
| H16.Eq16_22.perturbation_kronecker | p.313, (16.22) | equation | First-order perturbation system in vec/Kronecker form. | precise | general | derivation | Kronecker/vec | FORMALIZE_CORE | CORE-NUMBERED-EQUATION | Partial algebraic identity: `sylvester_perturbation_equation`, `sylvester_perturbation_first_order`; Kronecker form open. |
| H16.Eq16_23.psi_bound | p.313, (16.23) | inequality | Sharp first-order perturbation bound. | precise | condition-number route | sketch | `Psi`, operator norm | FORMALIZE_CORE | CORE-NUMBERED-EQUATION | Open. |
| H16.Eq16_24.psi_definition | p.313, (16.24) | definition | Structured condition number Psi. | precise | condition-number route | not applicable | inverse/operator norm | FORMALIZE_CORE | CORE-NUMBERED-EQUATION | Open. |
| H16.Eq16_25.phi_bound | p.313, (16.25) | inequality | Weaker perturbation bound via sep. | precise | square current API | derivation | `SepLowerBound` | FORMALIZE_CORE | CORE-NUMBERED-EQUATION | `sylvester_perturbation_bound`, `sylvester_relative_perturbation`; exact `P^{-1}` version open. |
| H16.Eq16_26.sep_definition | p.313, (16.26) | definition | Separation of A and B. | precise | square current API | not applicable | Frobenius norm | FORMALIZE_CORE | CORE-NUMBERED-EQUATION | `sylvesterSepRatios`, `sylvesterSepInf`, `sylvesterSepInf_nonneg`, `sylvesterSepInf_le_ratio`, `SepLowerBound_le_sylvesterSepInf_of_nonempty`, `SepLowerBound_of_pos_le_sylvesterSepInf`, `SepLowerBound_iff_pos_le_sylvesterSepInf_of_nonempty`; `SepLowerBound` remains the theorem-facing certificate. Attained-minimum bridge open. |
| H16.Eq16_27.lyapunov_condition | p.314, (16.27) | definition | Lyapunov condition number using vec-permutation. | precise | square | derivation | vec-permutation matrix | FORMALIZE_CORE | CORE-NUMBERED-EQUATION | Open. |
| H16.Eq16_28.aposteriori | p.315, (16.28) | inequality | A posteriori error-residual bound. | precise | square current API | derivation | `SepLowerBound` | FORMALIZE_CORE | CORE-NUMBERED-EQUATION | `sylvester_aposteriori_bound`, `sylvester_relative_aposteriori_bound`; relative wrapper assumes `frobNorm X > 0`. |
| H16.Eq16_29.practical_error_bound | p.315, (16.29) | inequality | Componentwise practical error bound with computed residual budget. | precise | implementation-facing | sketch | componentwise abs, inverse estimator, rounded residual | FORMALIZE_CORE | CORE-NUMBERED-EQUATION | Open. |
| H16.Eq16_30.generalized_axb_cxd | p.316, (16.30) | equation | Generalized Sylvester equation `AXB + CXD = E`. | precise | general rectangular | not applicable | rectangular products | FORMALIZE_CORE | CORE-NUMBERED-EQUATION | `generalizedSylvesterAXB_CXD_residual`, `IsGeneralizedSylvesterAXB_CXD_Solution`, `generalizedSylvesterAXB_CXD_residual_zero_iff_solution`. |
| H16.Eq16_31.coupled_generalized | p.316, (16.31) | equation | Coupled generalized Sylvester equations. | precise | general rectangular | not applicable | rectangular products | FORMALIZE_CORE | CORE-NUMBERED-EQUATION | `IsGeneralizedSylvesterPairSolution`. |
| H16.Eq16_32.riccati | p.316, (16.32) | equation | Algebraic Riccati equation residual. | precise | general rectangular | not applicable | rectangular products | FORMALIZE_CORE | CORE-NUMBERED-EQUATION | `riccatiResidual`, `IsRiccatiSolution`, `riccatiResidual_zero_iff_solution`. |
| H16.LAPACKRoutines | p.318 | software | LAPACK routine discussion. | underspecified | software | not applicable | machine/library semantics | SKIP | SKIP-PROGRAMMING-LANGUAGE | Core skip. |
| H16.Problems16_1_16_5 | p.318-319 | problems | benchmark-reserved; statement not transcribed | precise | benchmark | not applicable | none | BENCHMARK_CANDIDATE | BENCHMARK-RESERVED | not encoded. |
| H16.AppA16_1_16_4 | Appendix A split ledger | appendix solutions | benchmark-reserved; statement not transcribed | precise | benchmark | not applicable | none | BENCHMARK_CANDIDATE | BENCHMARK-RESERVED | not encoded. |

## Reused from Repository or Mathlib

| Source concept/result | Existing declaration | File/module |
|---|---|---|
| Legacy square matrix product | `matMul` | `LeanFpAnalysis.FP.Analysis.MatrixAlgebra` |
| Rectangular matrix product | `matMulRect`, `rectMatMul` | `LeanFpAnalysis.FP.Analysis.MatrixAlgebra` |
| Frobenius norm and squared norm | `frobNorm`, `frobNormSq`, `frobNorm_matMul_le`, triangle/subtraction lemmas | `LeanFpAnalysis.FP.Analysis.MatrixAlgebra` |
| Orthogonality and norm invariance | `IsOrthogonal`, `frobNormSq_orthogonal_left`, `frobNormSq_orthogonal_right` | `LeanFpAnalysis.FP.Analysis.MatrixAlgebra` |
| Transpose | `matTranspose` | `LeanFpAnalysis.FP.Analysis.MatrixAlgebra` |
| Column-stacking vectorization and Kronecker products | `Matrix.vec`, `Matrix.kronecker`, `Matrix.kronecker_mulVec_vec`, `Matrix.vec_mul_eq_mulVec` | `Mathlib.LinearAlgebra.Matrix.Vec` |

## New Dependencies

| Declaration | Why needed | Used by | Feasibility status |
|---|---|---|---|
| `sylvesterOpRect` | Avoids presenting square-only infrastructure as the full source shape. | `IsSylvesterSolutionRect`, `sylvesterResidualRect` | implemented |
| `sylvesterResidualRect` | Records residual semantics for rectangular source rows. | inventory rows for (16.9), (16.11), (16.29) | implemented |
| `sylvesterVecCoeff` | Records the exact rectangular coefficient matrix from (16.2) in Mathlib's `Matrix.vec` product-index order. | `sylvesterVecCoeff_mulVec_vec`, `sylvester_vec_system_iff_solution` | implemented |
| `sylvesterVecCoeff_diagonal`, `sylvesterVecCoeff_diagonal_det`, `sylvesterVecCoeff_diagonal_det_ne_zero_iff` | Captures the diagonal-basis algebra behind (16.3): the Kronecker coefficient is diagonal with entries `a_i - b_j`, and its determinant is nonzero exactly when no diagonal entries coincide. | H16.Eq16_3.kronecker_eigenvalues | implemented partial foundation |
| `sylvester_schur_transform_identity`, `sylvester_schur_transform_solution_iff` | Captures the exact operator and equation-level algebra behind (16.5) once orthogonal Schur-style factors are supplied. | H16.Eq16_5.schur_transform | implemented supplied-factor foundation |
| `sylvesterSepRatios`, `sylvesterSepInf`, `sylvesterSepInf_nonneg`, `sylvesterSepInf_le_ratio`, `SepLowerBound_le_sylvesterSepInf_of_nonempty`, `SepLowerBound_of_pos_le_sylvesterSepInf`, `SepLowerBound_iff_pos_le_sylvesterSepInf_of_nonempty` | Models (16.26) as an infimum of nonzero Frobenius ratios, proves the infimum is nonnegative and below each feasible ratio, and relates positive lower bounds of the infimum to the existing `SepLowerBound` certificate. | H16.Eq16_26.sep_definition | implemented infimum foundation |
| `sylvesterBackwardResidual`, `isSVD_eq_matMul_diag`, `svdResidual_sub_sub`, `svdResidual_mul_svd_right`, `svdResidual_svd_left_mul`, `svdResidual_backwardResidual`, `xiSq_le_three_eta_sq_of_original_residual`, `xiSq_le_three_eta_sq_of_backward_error`, `sylvesterAmplificationMu`, `sylvesterAmplificationMuSquare`, `sylvesterAmplificationMu_square_eq`, `one_le_sylvesterAmplificationMuSquare`, `xiSq_le_mu_relative_residual_sq` | Records the original perturbation residual, the SVD-coordinate residual derivation, the lower-direction bridge from backward-error certificates to `xi^2 <= 3 eta^2`, the scalar amplification factor from (16.18), its square-case formula (16.19), the conditional square-case `mu >= 1` algebra, and the xi-squared residual bound in μ-relative-residual form. | H16.Eq16_15.eta_xi_bounds, H16.Eq16_17.eta_residual_amplification, H16.Eq16_18.mu_definition, H16.Eq16_19.square_mu | implemented lower-direction/certificate and definition/formula foundation; optimizer/upper eta bridge open |
| `lyapunov_solution_iff_sylvester_special` | Provides a source-facing bridge from Lyapunov equations to the proved Sylvester uniqueness theorem. | `lyapunov_unique_solution_of_sep`, `lyapunov_solution_symmetric_of_symmetric_rhs` | implemented |
| `lyapunovSpectralTransform`, `lyapunovBackwardResidual`, `lyapunovSpectralTransform_add_sub`, `lyapunovSpectralTransform_mul_spectral_right`, `lyapunovSpectralTransform_spectral_left_transpose`, `lyapunovSpectralTransform_backwardResidual`, `lyapunovSpectralBackwardResidual`, `lyapunovSpectralBackwardResidual_eq_diagMatrix`, `lyapunovBackwardScalarEq`, `lyapunovBackwardScalarEq_iff_unscaled`, `lyapunovBackwardScalarEq_iff_residual_eq`, `lyapunovBackwardScalarEq_of_spectral_decomposition`, `lyapunovBackwardScalarEq_iff_diagMatrix_eq`, `lyapunovXiSq`, `lyapunovXiSqSimpleBound`, `lyapunovXiSq_le_simple_bound`, `lyapunovAmplificationMu`, `lyapunovXiSq_le_min_eigen_bound`, `lyapunovXiSq_spectral_le_min_eigen_bound`, `lyapunovXiSq_le_mu_relative_residual_sq` | Captures the original and spectral-coordinate residual objects, the original-to-spectral residual derivation for `Y = U Lambda U^T`, printed scaled scalar equation, diagonal-matrix residual form, Lyapunov `xi^2` formula and simple upper bound, Lyapunov amplification factor, and xi-level μ relative-residual bound. | H16.Eq16_21.lyapunov_uncoupled | implemented partial surface; eta bridge open |
| `sylvester_relative_aposteriori_bound` | Presents (16.28) in the source's relative error shape. | H16.Eq16_28.aposteriori | implemented |
| `IsGeneralizedSylvesterAXB_CXD_Solution`, `IsRiccatiSolution` | Turns generalized residual definitions into explicit source-equation predicates. | H16.Eq16_30.generalized_axb_cxd, H16.Eq16_32.riccati | implemented |

## Empirical Source Outputs

| Source location | Printed claim/output | Missing machine details | Precise subclaim/replacement theorem | Status |
|---|---|---|---|---|
| p.311 MATLAB Bartels-Stewart/GEPP example | Reports small residual but much larger backward error, with GEPP worse on the same constructed case. | MATLAB version, BLAS/LAPACK details, rounding path, Schur implementation, exact singular vector construction. | The mathematical `xiSq` and residual/backward-error inequalities are formalized in the square Frobenius setting. | SKIP-EMPIRICAL in core. |
| pp.315-316 Jordan-block practical-bound example | Reports a large gap between the traditional and practical error bounds. | LAPACK/Schur implementation details, computed residual path, estimator implementation, exact rounding model. | (16.29) remains the selected implementation-facing target. | Open selected row plus SKIP-EMPIRICAL output. |

## Open Selected-Scope Items

| Source location | Exact claim | Current Lean status | Missing foundation | Next theorem |
|---|---|---|---|---|
| (16.3) and common-eigenvalue criterion | Eigenvalues of the Kronecker coefficient are pairwise differences, and nonsingularity is equivalent to no common eigenvalues. | vec/Kronecker formulation complete; diagonal determinant/nonsingularity case proved by `sylvesterVecCoeff_diagonal_det_ne_zero_iff`; general spectral criterion open | Kronecker spectrum theorem and eigenvalue/nonsingularity bridge | Prove the spectrum of `(I_n kron A) - (B^T kron I_m)` or add a reusable Mathlib wrapper if available. |
| (16.4)-(16.8) | Schur/Bartels-Stewart solve route and triangular/quasi-triangular error propagation. | supplied-factor exact algebra for (16.5) proved by `sylvester_schur_transform_identity` and `sylvester_schur_transform_solution_iff`; Schur existence, block recurrence, triangular solve, and error propagation remain open | Schur decomposition surface, block quasi-triangular API, Ch8 triangular solve instantiation | Connect to a Schur decomposition surface if available, then state the block triangular solve recurrence. |
| (16.9) | Floating-point residual guarantee for computed solution. | unstarted | computed Schur method path and Ch19-style QR backward stability | State a conditional theorem only after computed quantities are inventoried. |
| (16.15), (16.17)-(16.19) | Full eta/xi/mu backward-error amplification theorem. | partial foundation; backward-error certificates now imply `xi^2 <= 3 eta^2` via `xiSq_le_three_eta_sq_of_backward_error`; `mu` definition, square formula, conditional `mu >= 1`, and xi-level μ-relative-residual bound implemented | optimizer/minimum surface proving existence of perturbations attaining the xi upper direction and relating the feasible predicate to eta as an infimum/minimum | Prove the missing eta upper-direction/optimizer wrapper or reclassify as infimum-based. |
| (16.21), (16.27) | Lyapunov-specific backward-error and condition formulas. | uniqueness/symmetry complete; (16.21) original-to-spectral residual bridge, scalar/diagonal spectral-coordinate equation, `xi^2`, simple-bound, `mu`, and xi-level μ-relative-residual surfaces implemented; eta theorem and condition formulas open | Lyapunov optimizer surface and vec-permutation API | Prove the Lyapunov eta/xi optimizer bridge, then close the condition-number surface. |
| (16.23)-(16.24) | Structured condition number Psi and sharp perturbation bound. | unstarted | operator norm and inverse-panel API | Define `Psi` after vec/Kronecker surface exists. |
| (16.26) | Exact sep as a minimum/infimum. | nonnegative infimum surface implemented by `sylvesterSepInf`; for nonempty feasible ratios, `SepLowerBound` is equivalent to being a positive lower bound of the infimum | attained-minimum/minimizer bridge if a later theorem needs the literal source minimum | Prove existence of a minimizing nonzero matrix, or keep downstream theorem surfaces phrased via `sylvesterSepInf`/`SepLowerBound`. |
| (16.29) | Practical componentwise error bound. | unstarted | componentwise residual rounding model and `|P^{-1}|` estimator bridge | Define the computed-residual budget first. |

## Hidden-Hypothesis Summary

- The existing proved square theorems assume explicit Frobenius-norm bounds, `SepLowerBound`, nonzero norm-squared hypotheses where needed, and supplied linearized equations. These are domain/reused-theorem assumptions, not replacements for the target equation.
- `sylvesterSepInf` records the exact infimum object for `sep(A,B)`; `SepLowerBound` is now equivalent to a positive lower bound of that infimum when the feasible ratio set is nonempty. Rows needing an attained minimum remain open until minimizer existence is proved.
- `sylvester_schur_transform_identity` and `sylvester_schur_transform_solution_iff` assume supplied factorizations and orthogonality; they are not proofs of Schur decomposition existence or triangular/quasi-triangular solvability.
- No new global axioms, `sorry`, `admit`, `unsafe`, or opaque placeholders are introduced by the Chapter 16 companion module.

## Verification

- Baseline before edits:
  - `lake env lean LeanFpAnalysis/FP/Algorithms/Sylvester/SylvesterSpec.lean`: passed.
  - `lake env lean LeanFpAnalysis/FP/Algorithms/Sylvester/SylvesterBackward.lean`: passed.
  - `lake env lean LeanFpAnalysis/FP/Algorithms/Sylvester/SylvesterPerturbation.lean`: passed.
- Current milestone:
  - `lake env lean LeanFpAnalysis/FP/Algorithms/Sylvester/Higham16.lean`: passed after adding the Lyapunov uniqueness/symmetry wrappers.
  - `lake env lean LeanFpAnalysis/FP/Algorithms/Sylvester/Higham16.lean`: passed after adding the relative a posteriori wrapper.
  - `lake env lean LeanFpAnalysis/FP/Algorithms/Sylvester/Higham16.lean`: passed after adding generalized/Riccati source-equation predicates.
  - `lake env lean LeanFpAnalysis/FP/Algorithms/Sylvester/Higham16.lean`: passed after adding the (16.2) vec/Kronecker wrappers.
  - `lake build LeanFpAnalysis.FP.Algorithms.Sylvester.Higham16`: passed after syncing the vec/Kronecker milestone with `origin/main`.
  - `lake env lean LeanFpAnalysis/FP/Algorithms/Sylvester/Higham16.lean`: passed after adding `sylvesterVecCoeff_diagonal`.
  - `lake env lean LeanFpAnalysis/FP/Algorithms/Sylvester/Higham16.lean`: passed after adding `sylvesterVecCoeff_diagonal_det` and `sylvesterVecCoeff_diagonal_det_ne_zero_iff`.
  - `lake env lean LeanFpAnalysis/FP/Algorithms/Sylvester/Higham16.lean`: passed after adding `sylvester_schur_transform_identity`.
  - `lake env lean LeanFpAnalysis/FP/Algorithms/Sylvester/Higham16.lean`: passed after adding `sylvester_schur_transform_solution_iff`.
  - `lake env lean LeanFpAnalysis/FP/Algorithms/Sylvester/Higham16.lean`: passed after adding `sylvesterSepInf`.
  - `lake env lean LeanFpAnalysis/FP/Algorithms/Sylvester/Higham16.lean`: passed after adding `SepLowerBound_le_sylvesterSepInf_of_nonempty`.
  - `lake build LeanFpAnalysis.FP.Algorithms.Sylvester.Higham16 LeanFpAnalysis.FP.Algorithms.HighamChapter9`: passed after merging the subsequent Chapter 9 update.
  - `lake env lean examples/LibraryLookup.lean`: passed after importing `MatrixPowersJordan` and after the subsequent Chapter 9 merge.
  - `lake env lean LeanFpAnalysis/FP/Algorithms/Sylvester/SylvesterBackward.lean`: passed after adding `sylvesterAmplificationMu` and the square-case formula.
  - `lake env lean LeanFpAnalysis/FP/Algorithms/Sylvester/Higham16.lean`: passed after adding `sylvesterSepInf_nonneg`.
  - `lake build LeanFpAnalysis.FP.Algorithms.Sylvester.Higham16`: passed after adding `sylvesterSepInf_nonneg`.
  - `#print axioms` for `sylvesterSepInf_nonneg`: only `propext`, `Classical.choice`, and `Quot.sound`.
  - `lake env lean LeanFpAnalysis/FP/Algorithms/Sylvester/Higham16.lean`: passed after adding the reverse `sylvesterSepInf`/`SepLowerBound` bridge.
  - `lake build LeanFpAnalysis.FP.Algorithms.Sylvester.Higham16`: passed after adding the reverse `sylvesterSepInf`/`SepLowerBound` bridge.
  - `#print axioms` for `SepLowerBound_of_pos_le_sylvesterSepInf` and `SepLowerBound_iff_pos_le_sylvesterSepInf_of_nonempty`: only `propext`, `Classical.choice`, and `Quot.sound`.
  - `lake build LeanFpAnalysis.FP.Algorithms.Sylvester.Higham16 LeanFpAnalysis.FP.Algorithms.HighamChapter9`: passed after merging the latest Chapter 9 update.
  - `lake env lean examples/LibraryLookup.lean`: passed after merging the latest Chapter 9 update.
  - `lake env lean LeanFpAnalysis/FP/Algorithms/Sylvester/SylvesterBackward.lean`: passed after adding `xiSq_le_mu_relative_residual_sq`.
  - `lake env lean LeanFpAnalysis/FP/Algorithms/Sylvester/SylvesterBackward.lean`: passed after adding `one_le_sylvesterAmplificationMuSquare`.
  - `lake env lean LeanFpAnalysis/FP/Algorithms/Sylvester/SylvesterBackward.lean`: passed after adding the (16.21) Lyapunov spectral-coordinate scalar equation surface.
  - `lake build LeanFpAnalysis.FP.Algorithms.Sylvester.SylvesterBackward`: passed after the same (16.21) addition.
  - `#print axioms` for `lyapunovBackwardScalarEq_iff_residual_eq` and `lyapunovSpectralTransform_frobNormSq`: only `propext`, `Classical.choice`, and `Quot.sound`.
  - `lake env lean LeanFpAnalysis/FP/Algorithms/Sylvester/SylvesterBackward.lean`: passed after adding the (16.21) diagonal-matrix residual bridge.
  - `lake build LeanFpAnalysis.FP.Algorithms.Sylvester.SylvesterBackward`: passed after the same diagonal-matrix residual bridge.
  - `#print axioms` for `lyapunovBackwardScalarEq_iff_diagMatrix_eq` and `lyapunovSpectralBackwardResidual_eq_diagMatrix`: only `propext`, `Classical.choice`, and `Quot.sound`.
  - `lake env lean LeanFpAnalysis/FP/Algorithms/Sylvester/SylvesterBackward.lean`: passed after adding `lyapunovXiSq`, `lyapunovXiSqSimpleBound`, `lyapunovXiSq_le_simple_bound`, and `lyapunovAmplificationMu`.
  - `lake build LeanFpAnalysis.FP.Algorithms.Sylvester.SylvesterBackward`: passed after the same Lyapunov `xi`/`mu` addition.
  - `#print axioms` for `lyapunovXiSq_le_simple_bound`: only `propext`, `Classical.choice`, and `Quot.sound`.
  - `lake env lean LeanFpAnalysis/FP/Algorithms/Sylvester/SylvesterBackward.lean`: passed after adding the Lyapunov xi-level min-eigen and μ-relative-residual bounds.
  - `lake build LeanFpAnalysis.FP.Algorithms.Sylvester.SylvesterBackward`: passed after the same xi-level μ-relative-residual bounds.
  - `#print axioms` for `lyapunovXiSq_le_min_eigen_bound` and `lyapunovXiSq_le_mu_relative_residual_sq`: only `propext`, `Classical.choice`, and `Quot.sound`.
  - `lake env lean LeanFpAnalysis/FP/Algorithms/Sylvester/SylvesterBackward.lean`: passed after adding `lyapunovBackwardResidual`, the orthogonal transform bridge lemmas, `lyapunovSpectralTransform_backwardResidual`, and `lyapunovBackwardScalarEq_of_spectral_decomposition`.
  - `lake build LeanFpAnalysis.FP.Algorithms.Sylvester.SylvesterBackward LeanFpAnalysis.FP.Algorithms.LeastSquares.LSPerturbation`: passed after merging the latest LeastSquares update.
  - `lake build LeanFpAnalysis.FP.Algorithms.Sylvester.SylvesterBackward`: passed after the subsequent documentation-only merge.
  - `#print axioms` for `lyapunovSpectralTransform_backwardResidual` and `lyapunovBackwardScalarEq_of_spectral_decomposition`: only `propext`, `Classical.choice`, and `Quot.sound`.
  - `lake env lean LeanFpAnalysis/FP/Algorithms/Sylvester/SylvesterBackward.lean`: passed after adding `sylvesterBackwardResidual`, the SVD residual bridge lemmas, `xiSq_le_three_eta_sq_of_original_residual`, and `xiSq_le_three_eta_sq_of_backward_error`.
  - `lake build LeanFpAnalysis.FP.Algorithms.Sylvester.SylvesterBackward LeanFpAnalysis.FP.Algorithms.HighamChapter9`: passed after merging the subsequent Chapter 9 update.
  - `lake env lean examples/LibraryLookup.lean`: passed after merging the subsequent lookup update.
  - `#print axioms` for `xiSq_le_three_eta_sq_of_original_residual` and `xiSq_le_three_eta_sq_of_backward_error`: only `propext`, `Classical.choice`, and `Quot.sound`.

## Git and Local-Only Notes

- `chapter_splitting/` and `References/` are local-only policy/source artifacts and must remain unstaged.
- Remaining local untracked file before this milestone: `.codex/config.toml`.
