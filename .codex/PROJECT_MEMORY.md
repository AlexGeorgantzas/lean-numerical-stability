# Codex Project Memory

Project: `LeanFpAnalysis`, a Lean 4 library for floating-point arithmetic and
automatic stability analysis. The model is axiomatic and intentionally not tied
to IEEE 754. All core results should be stated over `FPModel` and `Real`.

Last review by Codex: 2026-04-28.
Current `main` is for the stable core library.  The main commit before the
end-to-end stability rebuild is tagged as
`main-stable-before-end-to-end-20260527` at
`d5c0fa90c69c36f794f176c96f2dd4d293bb5aa3`.
Benchmark work lives on branch `benchmark`.

## Build State

- `lake build` succeeds with Lean toolchain `leanprover/lean4:v4.29.0-rc3`.
- No real `sorry`, `admit`, `axiom`, or `opaque` declarations were found in
  `LeanFpAnalysis`.
- Current build warnings are cleanup warnings concentrated in QR/least-squares:
  unused simp arguments in `QR/GivensSpec.lean`, unused variables in
  `QR/HouseholderQR.lean`, `QR/GivensQR.lean`, `QR/QRSolve.lean`,
  `LeastSquares/LSQRSolve.lean`, `LeastSquares/LSNormalEquations.lean`, and
  `FastMatMul.lean`.
- After the 2026-04-26 fix pass, `main` was fast-forward merged to
  `015d6c4`.  Later benchmark work was split onto branch `benchmark`.
- `.vscode/` remains unrelated untracked local editor state.

## Earlier Context Found

- Old in-repo agent settings and benchmark prompt files were removed so the
  repository no longer carries tool-specific benchmark guidance.
- Earlier project notes framed the project as a VSCL/Thrust A thesis library
  for compositional stability-carrying foundations, not as a goal to formalize
  all of Higham.
- Durable user/project preferences: formalize only reusable stepping stones for
  future stability proofs; always search the existing codebase before claiming
  a theorem or definition is missing; put proof sketches in docstrings; keep
  Higham constants exact.

## Top-Level Structure

- `LeanFpAnalysis.lean` imports `LeanFpAnalysis.FP`.
- `LeanFpAnalysis/FP.lean` imports `Model`, `Analysis`, and `Algorithms`.
- `LeanFpAnalysis/FP/Analysis.lean` re-exports:
  `Error`, `Rounding`, `Summation`, `SubtractionFold`, `Stability`,
  `ForwardError`, `MatrixAlgebra`, `PerturbationTheory`.
- `LeanFpAnalysis/FP/Algorithms.lean` re-exports the algorithm families:
  summation, dot/matvec/matmul, triangular solves and bounds, LU, Cholesky,
  QR, least squares, Sylvester, iterative refinement, matrix inversion,
  stationary iteration, matrix powers, underdetermined systems, fast matmul.

## Foundation Modules

- `Model.lean`: `FPModel` with `u`, `u_nonneg`, `fl_add/sub/mul/div/sqrt`,
  exact `fl_add_zero`, and standard relative-error axioms for each operation.
  The square-root axiom is stated for nonnegative inputs.
- `Analysis/Error.lean`: `absError`, `relError`, `compRelErrorBounded`.
- `Analysis/Stability.lean`: scalar/vector backward-error predicates,
  componentwise relative backward stability, scalar `condNumber`, and
  `forward_from_backward`.
- `Analysis/Rounding.lean`: `gamma`, `gammaValid`, gamma monotonicity and
  arithmetic, `prod_error_bound`, `gamma_mul`, `gamma_inv`, `gamma_div`,
  `gamma_inv_mul_roundoff`, and absorption lemmas such as
  `three_gamma_plus_sq_le_gamma`.
- `Analysis/Summation.lean`: `fl_sum_error`, `fl_sum_error_init`,
  `fl_sum_error_tight`.
- `Analysis/SubtractionFold.lean`: subtraction-fold and inverse-product
  error lemmas used by triangular substitution proofs.
- `Analysis/MatrixAlgebra.lean`: exact matrix operations, inverses, norms,
  transpose, Frobenius algebra, orthogonal matrices, Neumann-series style
  bounds. This is foundational but very large and could eventually be split.
- `Analysis/PerturbationTheory.lean`: residual, normwise/componentwise
  perturbation, Oettli-Prager, Rigal-Gaches, Skeel condition definitions.

## Strong Reuse Chain

- `Rounding` supports `Summation` and `SubtractionFold`.
- `Summation` supports `DotProduct`.
- Exact algebraic operations should be separated from rounded algorithms.
  For dot product, Mathlib's `x ⬝ᵥ y = ∑ i, x i * y i` is the exact
  specification, while local `fl_dotProduct` is the rounded left-to-right
  recurrence using `fp.fl_mul` and `fp.fl_add`.  Stability theorems should
  compare the rounded algorithm to the exact Mathlib specification; they should
  not pretend the whole dot product always has a single global relative error,
  because cancellation can make that false.
- `DotProduct` supports `MatVec`.
- `MatVec` supports `MatMul` and matrix inversion residual results.
- `DotProduct` supports `Norm2`, which gives the reusable `fl_norm2Sq` and
  `fl_norm2` kernels needed by later Householder reflector construction.
  `Norm2` states exact facts directly over Mathlib's `x ⬝ᵥ x` and
  `‖WithLp.toLp 2 x‖`; it should not reintroduce exact vector-norm aliases.
  Premature Householder construction/application modules were removed from
  `end-to-end-rebuild` so the branch can proceed bottom-up from foundations
  before returning to QR-specific kernels.
- `TriangularSolve` and `ForwardSub` use `SubtractionFold`/`Rounding` and feed
  `TriangularSolveCombined`, `ForwardError`, `MMatrix`, LU solve, Cholesky
  solve, matrix inversion, and underdetermined systems.
- `ForwardError` combines triangular backward error with exact inverse
  predicates from `MatrixAlgebra`.
- LU modules build from Gaussian elimination specs into solve and growth-factor
  results; Cholesky solve reuses triangular solves and Cholesky specs.

## Known Weak Spots

These compile, but should not be treated as fully derived stability results:

- `Algorithms/MatrixInversion.lean` no longer has `True` placeholder fields in
  `BlockMethod1BSpec`.  The block-indexing details remain abstract, but the
  spec now exposes the concrete per-column backward-error contract used to
  prove `triInv_method1B_right_residual_from_spec`.
- Several high-level theorems are wrappers around a hypothesis that is already
  essentially the conclusion:
  `GaussJordan.lean` recurrence/forward/backward/SPD residual wrappers;
  `MatrixInversion.lean` method 2, method 2C, method D, and SPD method D
  wrappers; `CholeskyDemmel.lean` scaled forward-error wrapper;
  `CholeskyIndefinite.lean` Bunch-Parlett/Bunch-Kaufman wrappers;
  `CholeskyNonsym.lean` nonsymmetric PD growth and Mathias success wrappers;
  `CholeskyPSD.lean` Schur perturbation, W-norm, complete-pivoting, and
  termination wrappers; `CholeskyPerturbation.lean` normwise perturbation
  wrapper; `SylvesterPerturbation.lean` first-order linearized wrapper.
- These wrappers are acceptable as named interfaces only if the supplied
  hypothesis is intentionally an abstract external theorem. They should not be
  advertised as internally proved from the FP model.  These wrappers were
  redocumented as abstract interfaces in the 2026-04-26 fix pass.

## Organization Notes

- The core library organization is coherent: model -> analysis infrastructure
  -> low-level algorithms -> higher-level algorithms.
- `MatrixAlgebra.lean` is over 1200 lines and mixes general algebra, norms,
  orthogonality, and Neumann theory. A future split into matrix basics, norms,
  orthogonal/Frobenius, and Neumann/resolvent infrastructure would improve
  maintainability.
- Triangular inverse infrastructure is split across
  `TriangularForwardBound.lean` and `InverseBounds.lean`. This works, but a
  neutral `Analysis/TriangularAlgebra.lean` or `Algorithms/TriangularInverse`
  module would make the dependency story cleaner.
- `MMatrix.lean` proves the Corollary 8.10 relative-error statement in μ-form
  via `mmatrix_forwardSub_relative_error`.  It does not separately formalize
  the asymptotic simplification `μ_i ≤ (n²+n+1)u + O(u²)` as a Big-O theorem.
## Branch Notes

- Benchmark artifacts and benchmark-specific decision notes were moved to
  branch `benchmark` on 2026-04-28.
- Keep benchmark task files, stubs, generated-workspace scripts, run protocols,
  and task-selection rationale off `main` unless the user explicitly decides to
  merge them back.
- Library implementation work after the benchmark audit lives on
  `end-to-end-rebuild`, renamed from the earlier QR-specific branch.
  The branch should proceed bottom-up: stabilize the general foundations first,
  then add concrete rounded kernels, then prove bridge theorems showing those
  kernels satisfy the existing contracts.

## 2026-05 End-To-End Rebuild Work

- End goal for this branch: each important high-level stability contract should
  eventually be backed by a concrete rounded `fl_*` algorithm and a theorem
  proving that algorithm satisfies the contract from `FPModel`, rather than
  only assuming the contract.
- Step 1 foundation audit began with `FPModel`, `Rounding`, `Summation`,
  `SubtractionFold`, `Stability`, and `MatrixAlgebra`.  The scan found no
  `sorry`, `admit`, `axiom`, or `opaque` in these files.  The main immediate
  gap was documentation precision: distinguish the Higham standard model from
  extra exactness assumptions, and mark `MatrixAlgebra` as exact algebra rather
  than floating-point algorithm code.
- Foundation cleanup replaced the old locally-defined `infNorm hn A` API with
  Mathlib-backed compatibility wrappers: `infNormVec v := ‖v‖` and
  `infNorm A := ‖Matrix.of A‖` with a local Mathlib `linfty` operator-norm
  instance.  `infNormBound n M c` is now the clean norm inequality
  `infNorm M ≤ c`, with row-wise bridge lemmas `row_sum_le_infNorm`,
  `infNorm_le_of_row_sum_le`, and `row_sum_le_of_infNormBound` for
  Neumann proofs.
- Exact norm policy: use Mathlib norm/dot-product infrastructure directly for
  exact algebra and avoid duplicate local aliases when practical.  Exact vector
  aliases `exactNorm2Sq`, `exactNorm2`, `norm2Sq`, and `norm2Vec` were removed;
  `Norm2` now states exact facts over `x ⬝ᵥ x` and `‖WithLp.toLp 2 x‖`
  directly.  Floating-point kernels such as `fl_dotProduct`, `fl_norm2Sq`, and
  `fl_norm2` remain local because they encode rounded operation order.
- Matrix shape aliases were added in `MatrixAlgebra`: `RVec n := Fin n → ℝ`,
  `RMat m n := Matrix (Fin m) (Fin n) ℝ`, `RSqMat n := RMat n n`, and
  `RMatFn m n := Fin m → Fin n → ℝ`.  New exact matrix-facing APIs should
  prefer `RMat` when possible, while existing algorithm code may keep using
  `RMatFn` during gradual migration.
- Current exact Frobenius policy: keep `frobNorm` as a readable rectangular
  compatibility wrapper over Mathlib, not as an independent norm definition:
  `frobNorm A := ‖(Matrix.of A : RMat m n)‖`.  The source of truth is
  Mathlib's Frobenius norm, while public statements over legacy function-shaped
  matrices stay readable.  Keep `frobNormSq` only as a squared convenience for
  existing sum-of-squares algebra and sep/Sylvester proofs until a separate
  squared-norm migration is planned.
- Matrix-shape policy for the rebuild: rectangular real matrices are needed
  before full QR/least-squares implementation-backed proofs.  Avoid adding new
  square-only exact infrastructure unless the algorithm is inherently square.
  Prefer APIs that can move toward `Matrix (Fin m) (Fin n) ℝ` or compatible
  `Fin m → Fin n → ℝ` wrappers.  Do not attempt a silent global migration to
  complex matrices: complex floating-point arithmetic needs an explicit later
  model, probably built from real rounded operations on real and imaginary
  parts rather than by treating `ℂ` operations as primitive.
- Corrected the QR implementation plan to start with missing low-level
  primitives rather than treating reflector construction as permanently out of
  scope.
- Extended `FPModel` with `fl_sqrt` and `model_sqrt` for nonnegative real
  inputs.
- Added `Algorithms/Norm2.lean` with floating 2-norm kernels `fl_norm2Sq` and
  `fl_norm2`, plus exact Mathlib facts over `x ⬝ᵥ x` and
  `‖WithLp.toLp 2 x‖`: `norm_toLp_two_eq_sqrt_dotProduct`,
  `dotProduct_self_nonneg_real`, `dotProduct_self_eq_zero_iff_real`,
  `dotProduct_self_ne_zero_iff_real`, `dotProduct_self_pos_iff_real`, and
  `norm_toLp_two_nonneg`.
- Removed premature `HouseholderReflector` and `HouseholderApply` additions from
  the active branch.  They were useful prototypes, but the user decided the
  rebuild should not move into Householder-specific kernels before auditing the
  lower-level foundation chain.
- Current next step is the bottom-up audit/cleanup beginning with `DotProduct`
  and its exact-specification bridge to Mathlib `dotProduct`.
- Rebuild standard clarified with the dot-product/QR contrast.  `DotProduct.lean`
  is the positive template: it defines a concrete rounded algorithm
  `fl_dotProduct` from `FPModel` primitives and proves
  `dotProduct_backward_error` from that definition using summation and gamma
  lemmas.  QR is not yet at that standard: `householder_qr_backward` consumes an
  assumed `OrthogonalSequenceBackwardError`, and `HouseholderAppError` is a
  specification of one-step reflector application rather than a theorem derived
  from concrete rounded Householder construction/application code.
- Whole-library repass aim: keep contracts/specification structures as useful
  modular interfaces, but add implementation-backed bridge theorems wherever a
  public algorithmic stability result currently depends only on a supplied
  contract.  The desired chain is `FPModel` primitives -> concrete `fl_*`
  algorithm -> theorem that the algorithm satisfies its contract -> final
  stability theorem.  Avoid claiming end-to-end stability for modules that stop
  before the bridge theorem.
- A local Codex skill for this workflow was created at
  `~/.codex/skills/lean-fp-stability-audit/SKILL.md`.  Use it when auditing or
  rebuilding modules for implementation-backed stability proofs.
- Skill/source policy: always compare the proof boundary against the original
  source, not just the current Lean file.  If Higham or another source proves a
  lower-level bound, the rebuild should formalize that bound rather than treating
  it as a permanent assumption in a higher-level theorem.  QR/Householder in
  Higham Chapter 18 is the motivating example.
- Internal rebuild planning files were created under ignored `thesis/`:
  `thesis/IMPLEMENTATION_BACKED_AUDIT.md` records the current module-by-module
  classification, and `thesis/REPASS_LEDGER.md` records the phased checklist for
  the repass.  Future work should use these with the
  `lean-fp-stability-audit` skill.
- Treat `thesis/REPASS_LEDGER.md` as living documentation.  Update it whenever
  a higher-level proof reveals a missing lower-level rounded operation, bridge
  theorem, source reference, or dependency not visible in the initial audit.
- Phase 1 foundation audit completed on 2026-06-01.  Targeted `lake env lean`
  passed for `FP/Model.lean`, `Analysis/Rounding.lean`, `Analysis/Error.lean`,
  `Analysis/Summation.lean`, `Analysis/SubtractionFold.lean`,
  `Analysis/Stability.lean`, and `Analysis/MatrixAlgebra.lean`.  Only narrow
  documentation edits were made: `fl_add_zero` is explicitly an extra exactness
  hypothesis, and `gammaValid` is described as model-parametric rather than
  IEEE-specific.
- Phase 2 scalar/vector audit completed on 2026-06-01.  Targeted `lake env lean`
  passed for `RecursiveSum.lean`, `PairwiseSum.lean`, `SumTree.lean`,
  `DotProduct.lean`, `OuterProduct.lean`, and `Norm2.lean`.  `DotProduct` is the
  positive implementation-backed template.  `OuterProduct` documentation was
  corrected to stress that its perturbation theorem is row-wise and not a global
  backward-stability result, matching Higham's discussion after equation (3.6).
  `Norm2` is implementation-backed as a kernel.  Later Phase 5 work added the
  Householder-specific norm bridges needed for Chapter 18 reflector
  construction.
- Phase 3 basic matrix-kernel audit completed on 2026-06-01.  Targeted
  `lake env lean` passed for `MatVec.lean`, `MatMul.lean`, and
  `LeastSquares/LSNormalEquations.lean`.  Added concrete bridge theorems
  `gramProductError_from_fl_matMul` and `gramVecError_from_fl_matVec`, so the
  normal-equations Gram product/vector contracts can now be proved from
  `fl_matMul` and `fl_matVec`.  Cholesky remains the contract-level dependency
  in normal equations.
- Phase 4 triangular-solve audit completed on 2026-06-01.  `TriangularSolve` and
  `ForwardSub` are implementation-backed: the concrete recursive rounded
  algorithms prove `fl_backSub_satisfies_spec` and
  `fl_forwardSub_satisfies_spec`, then the backward-error theorems consume those
  proved row-spec bridges.  `TriangularSolveCombined` only composes those proved
  results.  The derived forward-error/comparison/M-matrix theorems take exact
  inverse, exact-solution, diagonal-dominance, M-matrix, and `gammaValid`
  hypotheses; these are mathematical problem assumptions, not missing rounded
  algorithm contracts.  `TriangularForwardComparison` was relabelled so the
  backward-error-derived comparison bound is not confused with Higham's direct
  Theorem 8.9 μ-bound (`forwardSub_forward_error_mu_bound`).
- Phase 5 low-level QR rebuild started on 2026-06-01.  Added
  `Algorithms/QR/HouseholderReflector.lean` with concrete rounded kernels
  `fl_householderScale`, `fl_householderVector`, and `fl_householderBeta`.
  Source alignment matters here: Higham Lemma 18.1 computes
  `s = sign(x_0)||x||_2`, `v_0 = fl_add x_0 s_hat`, and
  `beta_hat = fl_div 1 (fl_mul s_hat v_hat_0)`.  The dot-product beta path
  `2/fl_dotProduct(v,v)` is an alternate algorithm and should not be used to
  claim Higham's `γ_{4n+8}` bound.  Applying `sign(x_0)` is exact in Higham's
  operation count, so `fl_householderScale` is an exact sign change of
  `fl_norm2`, not a rounded multiplication.  The current kernels follow the source order.
  Their unroll lemmas reduce the construction to existing `fl_norm2`,
  `fp.model_add`, `fp.model_mul`, and `fp.model_div` layers.
  Added `Algorithms/QR/HouseholderApply.lean` with concrete rounded
  `fl_householderApply`, modeling `b - beta * v * (v^T b)` and unrolling it into
  dot-product, multiplication, and subtraction errors.  Lemma 18.1 is now
  implementation-backed by later bridge theorems; Lemma 18.2 application
  stability remains the next missing bridge.
- Phase 5 source boundary update on 2026-06-02: inspecting `References/Chapter18.pdf`
  page images confirmed that Higham Lemma 18.2 assumes the normalized reflector
  perturbation model from equation (18.3) before deriving the application error
  `y_hat = (P + ΔP)b`.  Added `HouseholderVectorError` to
  `HouseholderSpec.lean` to represent that intermediate contract explicitly, and
  added `householder_matMulVec_eq` in `HouseholderApply.lean` to connect the
  exact reflector matrix with the closed-form expression
  `b - beta * v * (v^T b)`.  Do not add a vacuous theorem that proves
  `HouseholderAppError` by manufacturing an arbitrary post-hoc `ΔP`; the real
  bridge is `fl_householderVector -> HouseholderVectorError`, followed by
  `fl_householderApply + HouseholderVectorError -> HouseholderAppError`.
- Phase 5 exact-form update on 2026-06-02: added exact Householder construction
  definitions `householderScale`, `householderAlpha`, `householderVector`,
  `householderBeta`, and `householderBetaFromScale`, plus
  `householderBeta_mul_norm_sq`.  Added normalized-form support
  `householderNormalizedVector`, `householder_normalizedVector_eq`, and
  `householderNormalizedVector_norm_sq`.  This proves the algebraic bridge
  between the library's unnormalized `I - beta v v^T` reflector and Higham's
  normalized `I - v v^T` equation (18.3) form.  Later bridge theorems prove the
  rounded construction satisfies the normalized-vector perturbation model.
- Also added `householder_exact_orthogonal`: exact `householderVector` together
  with exact `householderBeta` produces an orthogonal reflector whenever
  `v^T v` is nonzero.  Later rounded proofs should compare the computed
  construction against this exact reflector rather than re-proving exact
  orthogonality algebra.
- Added `fl_householderVector_tail_eq_householderVector`, proving the
  implementation-backed exact-copy part of Higham Lemma 18.1: all non-first
  components of the rounded Householder vector agree with the exact vector.
- Added `HouseholderConstructionError`, the explicit Higham Lemma 18.1 contract:
  tail equality, first-component relative error bounded by `γ_{n+2}`, and beta
  relative error bounded by `γ_{4n+8}`.  Also added exact source-alignment
  lemmas `householderScale_mul_self`,
  `householderVector_norm_sq_eq_two_scale_mul`, and
  `householderBetaFromScale_eq_householderBeta`, connecting the source beta
  formula `1/(s*v_0)` with the reflector beta formula `2/(v^T v)`.
- Added Householder-facing norm bridges in `Norm2.lean`:
  `weighted_sum_relative_error_nonneg`, `fl_norm2Sq_relative_error`, and
  `fl_norm2_relative_error_sqrt_factor`.  These prove the source step
  `fl(x^T x) = (1+θ_n)x^T x` and expose
  `fl(||x||_2) = sqrt(x^T x) * sqrt(1+θ_n) * (1+δ)`.
  Added the exact square-root perturbation lemma
  `sqrt_one_add_sub_one_abs_le_abs`, the gamma bridge
  `sqrt_one_add_mul_roundoff_gamma`, and the source-style norm theorem
  `fl_norm2_relative_error`, so the rounded norm now has
  `fl_norm2 x = ||x||_2 * (1+θ_{n+1})` from the concrete `fl_norm2`
  implementation.
- Added `householderVector_zero_abs_eq`, proving the exact no-cancellation fact
  `|x_0+s| = |x_0| + |s|`, and
  `fl_householderScale_relative_error_sqrt_factor`, which composes the new
  `fl_norm2` bridge with exact sign application.  Added
  `fl_householderScale_relative_error` and
  `fl_householderVector_zero_relative_error`, proving the
  first-component `γ_{n+2}` part of Higham Lemma 18.1 for nonzero inputs from
  the concrete rounded Householder vector implementation.
- Added `gamma_inv_mul_roundoff` in `Rounding.lean` so a reciprocal of a
  `γ_k`-perturbed denominator plus the final division rounding can be bounded
  by `γ_{2k}`.  This preserves Higham's beta constant rather than weakening it
  by one extra gamma index.
- Added `fl_householderBeta_denominator_relative_error`,
  `fl_householderBeta_relative_error`, and `fl_householderConstructionError`.
  For nonzero inputs, the concrete rounded Householder construction now
  satisfies the full `HouseholderConstructionError` contract matching Higham
  Lemma 18.1: exact tail copy, first-component `γ_{n+2}` perturbation, and
  beta `γ_{4n+8}` perturbation.
- Added `sqrt_one_add_mul_relative_gamma` in `Norm2.lean` and the normalized
  Householder construction bridges `householderVectorError_from_construction`
  and `fl_householderVectorError`.  For nonzero inputs and a stronger
  `gammaValid fp (8*n+16)` side condition, the concrete rounded construction
  now satisfies Higham equation (18.3) after algebraic normalization, with
  explicit bound `γ_{5n+10}` as a concrete instance of Higham's generic
  `γ_{cm}`.
- Added `householderApplyRoundedMatrix`,
  `householderApplyDeltaMatrix`, `fl_householderApply_matrix_unroll`, and
  `fl_householderApply_appError_of_matrix_bound`.  These prove that the
  concrete rounded Householder application is multiplication by a matrix
  determined by the primitive rounding errors, and they isolate the exact
  remaining Lemma 18.2 obligation: prove a Frobenius norm bound for that
  concrete delta matrix from `HouseholderVectorError` and the primitive error
  bounds.  This is not yet the full Lemma 18.2 stability theorem.
- Added exact norm helpers in `MatrixAlgebra.lean` turning entrywise absolute
  bounds into Frobenius bounds, plus `HouseholderVectorError` consequences in
  `HouseholderSpec.lean`: sum-of-squares for the normalized vector, a
  componentwise magnitude bound for the computed vector, and relative factors
  `v_hat_i = v_i(1+alpha_i)`.  Added `HouseholderApply` factorization and
  entrywise gamma theorems for the normalized application delta.  The current
  next gap is now the final Frobenius summation estimate that turns these
  entrywise gamma facts into a concrete `HouseholderAppError` bound.
- Completed the normalized one-reflector Householder application bridge:
  `householderApply_sub_error_frob_bound`,
  `householderApply_outer_gamma_frob_bound`,
  `householderApplyDeltaMatrix_normalized_frob_bound`, and
  `fl_householderApply_normalized_appError`.  This proves that if equation
  (18.3) is supplied for a normalized computed vector, then the concrete
  rounded `fl_householderApply fp n v_hat 1 b` satisfies `HouseholderAppError`.
  The bound is currently the raw expression
  `sqrt(n*u^2) + 2*gamma(2a+n+3)`, not yet collapsed into Higham's generic
  `gamma_cm` notation.
- Added `Algorithms/QR/HouseholderOneStep.lean` with
  `fl_householderConstructApply_appError`, combining the concrete construction
  bridge `fl_householderVectorError` with
  `fl_householderApply_normalized_appError`.  For nonzero input vectors and
  `gammaValid fp (11*n+23)`, concrete construction plus concrete application
  now satisfies `HouseholderAppError` for one reflector, again with the raw
  bound `sqrt(n*u^2) + 2*gamma(11*n+23)`.
- Added `Algorithms/QR/HouseholderMatrixStep.lean` with
  `fl_householderApplyMatrix`, `ColumnwiseHouseholderStepError`, and
  `fl_householderConstructApply_matrix_step_error`.  This lifts the concrete
  one-vector reflector result to a concrete matrix-column step: each output
  column of `fl_householderApplyMatrix` satisfies `HouseholderAppError` with a
  column-dependent perturbation matrix.  This is intentionally weaker than the
  existing `orthogonal_sequence_one_step` hypothesis, which uses one global
  `ΔP` for the whole matrix step; Higham's Lemma 18.3 proof is columnwise, so
  the next QR bridge must aggregate column-dependent perturbations rather than
  silently forcing them into a global perturbation.
- Added exact columnwise Frobenius aggregation lemmas in `MatrixAlgebra.lean`:
  `matMulVec_sum_sq_le_frobNormSq_mul_sum_sq`,
  `frobNormSq_columnwise_matMulVec_le`, and
  `frobNorm_columnwise_matMulVec_le`.  `HouseholderMatrixStep.lean` now exposes
  `ColumnwiseHouseholderStepError.exists_residual_matrix_bound`, proving that a
  columnwise Householder step has a single residual matrix `E` with
  `A_hat = P*A + E` and `‖E‖_F ≤ c*‖A‖_F`.  The next gap is turning repeated
  residual steps into the final `Qᵀ(A+ΔA)`/QR backward-error statement.
- Added residual-form sequence one-step theorems in `HouseholderQR.lean`:
  `orthogonal_sequence_one_step_of_residual` and
  `orthogonal_sequence_one_step_of_columnwise_error`.  These advance the
  sequence invariant from `A_hat = Qᵀ(A+ΔA)` through a step
  `A_next = P*A_hat + E` with `‖E‖_F ≤ c‖A_hat‖_F`, and the columnwise version
  consumes `ColumnwiseHouseholderStepError` directly.  This avoids the stronger
  old assumption that one global `ΔP` explains a whole matrix step.  The
  remaining QR gap is the repeated-step induction/loop model and the final
  connection to `HouseholderQRBackwardError`.
- Added `idMatrix_orthogonal` in `MatrixAlgebra.lean` and the conservative
  repeated residual theorem `residual_orthogonal_sequence_backward_error` in
  `HouseholderQR.lean`.  If each step has
  `A_{k+1} = P_k*A_k + E_k`, each `P_k` is orthogonal, and
  `‖E_k‖_F ≤ c‖A_k‖_F`, the theorem proves
  `A_r = Qᵀ(A_0+ΔA)` with
  `‖ΔA‖_F ≤ residualAccumBound c r * ‖A_0‖_F`.  This keeps higher-order terms
  via a recurrence instead of forcing the first-order `r*c` simplification.
  The next QR gap is a concrete Householder QR loop/sequence feeding these
  hypotheses, plus a sourced gamma-collapse lemma if the public theorem should
  recover Higham's `r*c`/`γ_cm` style bound.
- Added `columnwise_householder_sequence_backward_error`,
  `householderConstructApplyBound`, `householderConstructApplyBound_nonneg`,
  and `fl_householder_sequence_backward_error`.  The last theorem proves that
  any matrix sequence updated by repeated concrete
  `fl_householderApplyMatrix` steps, with reflectors concretely constructed
  from nonzero `xseq k`, satisfies the residual orthogonal-sequence
  backward-error theorem.  This is still not full QR factorization because the
  theorem does not yet define/select the QR trailing-column vectors or prove
  triangularization; it is the implementation-backed repeated-reflector bridge
  needed before that final QR loop theorem.
- Added rectangular panel infrastructure for Householder QR trailing updates:
  `matMulRect` in `MatrixAlgebra.lean`,
  `frobNormSq_columnwise_matMulVec_le_rect`,
  `frobNorm_columnwise_matMulVec_le_rect`,
  `fl_householderApplyMatrixRect`,
  `ColumnwiseHouseholderStepErrorRect`, and
  `fl_householderConstructApply_matrix_step_error_rect`.  A square
  Householder reflector can now be applied to an `m × p` panel, and the
  concrete rounded panel update has a columnwise backward-error contract plus a
  single residual matrix bound `‖E‖_F ≤ c‖A‖_F`.  This is needed before the
  real QR loop can operate on trailing rectangular panels instead of only
  square full matrices.
- Added exact rectangular orthogonal algebra:
  `matMulRect_id_left`, `matMulRect_add_right`,
  `matMulRect_assoc_square_left`, `frobNormSq_orthogonal_left_rect`, and
  `frobNorm_orthogonal_left_rect`.  Added rectangular residual sequence
  theorems in `HouseholderQR.lean`:
  `orthogonal_sequence_one_step_of_residual_rect`,
  `residual_orthogonal_sequence_backward_error_rect`,
  `columnwise_householder_panel_sequence_backward_error`, and
  `fl_householder_panel_sequence_backward_error`.  Repeated concrete
  Householder panel updates now satisfy a rectangular backward-error sequence
  theorem.  Remaining QR work: define the actual trailing-panel loop and prove
  it supplies these panel update hypotheses and triangularization.
- Added `panelFirstColumn` and
  `fl_householder_first_column_panel_step_error`.  This specializes the
  rectangular panel bridge to the first-column choice used by a Householder QR
  panel step.  It is the first link from arbitrary supplied construction
  vectors toward an actual QR loop, but it still does not define recursive
  trailing panels or prove triangularization.
- Added `fl_householder_first_column_panel_sequence_backward_error`, which
  repeats the first-column panel choice over a fixed rectangular panel shape.
  This removes the arbitrary `xseq` layer for fixed panels.  Remaining QR work
  is still the dependent trailing-panel loop with shrinking dimensions and the
  triangularization/package proof.
- Added exact trailing-panel indexing infrastructure in `HouseholderQR.lean`:
  `panelDropFirstRow`, `panelDropFirstCol`, and `trailingPanel`, plus the
  concrete rounded shrinking step `fl_householderTrailingPanelStep`.  This
  models one QR move from an `(m+1) × (p+1)` panel to its updated trailing
  `m × p` panel.  This is still an indexing/algorithm-definition layer; the
  next proof gap is an induction over these dependent shrinking panel shapes
  and the exact triangularization property.
- Added `frobNormSq_trailingPanel_le`, `frobNorm_trailingPanel_le`, and
  `fl_householderTrailingPanelStep_residual`.  The concrete one-step shrinking
  QR panel update now has a residual representation inherited from the full
  first-column Householder panel step.  Remaining QR work: dependent induction
  across changing dimensions, exact zeroing/triangularization, and packaging
  into the final `HouseholderQRBackwardError`.
- Added exact Householder zeroing lemmas in `HouseholderOneStep.lean`:
  `householderVector_dot_original_eq_scale_mul_zero`,
  `householder_constructed_matMulVec_first`, and
  `householder_constructed_matMulVec_tail_zero`.  These prove the exact
  triangularization kernel for one constructed reflector:
  the source column is mapped to `-s e_0`, so all tail components are zero.
  This is exact algebra, not yet a rounded triangularization theorem for the
  full QR loop.
- Added panel-level exact triangularization bridges in `HouseholderQR.lean`:
  `householder_first_column_panel_exact_first` and
  `householder_first_column_panel_exact_tail_zero`.  These lift the exact
  one-vector zeroing theorem to the first column of a rectangular panel after
  applying the constructed exact reflector.  The next QR gap is to combine this
  exact zeroing fact with the rounded residual theorem in the shrinking-panel
  induction.
- Added panel decomposition infrastructure in `HouseholderQR.lean`:
  `panelTopLeft`, `panelTopRowTail`, `panelFirstColumnTail`, and
  `panelFirstColumnTailZero`.  Added exact bridges
  `householder_panel_exact_topLeft` and
  `householder_panel_exact_firstColumnTailZero`, so the one-step exact
  triangularization result is now stated in the panel shape that the future QR
  loop will consume.
- Added `fl_householder_first_column_panel_step_residual_and_shape`, which
  packages one concrete rounded first-column Householder panel update with:
  a residual matrix bound for the computed full-panel update, the exact
  top-left value of the underlying reflector step, and exact first-column tail
  zeroing.  This is the one-step implementation-backed panel bridge; remaining
  QR work is the dependent induction over shrinking panels and final packaging.
- Added `IsUpperTriangular` and
  `StructuredHouseholderQRBackwardError` in `HouseholderQR.lean`.  The original
  `HouseholderQRBackwardError` remains the normwise backward-error contract
  only; the structured contract explicitly includes the `R_hat` upper-triangular
  shape requirement.  `structured_householder_qr_backward` is only a packaging
  theorem from the old backward-error theorem plus a supplied triangularity
  proof; the rebuild still has to prove triangularity from the concrete rounded
  QR loop.
- Added `HouseholderPanelState`, `householderPanelStateStep`, and
  `householderPanelStateIterate` as the first dependent-loop substrate for
  Householder QR.  The state tracks the active trailing panel and the concrete
  step shrinks nonempty panels using `fl_householderTrailingPanelStep`.  It does
  not yet store the accumulated `Q` or completed `R` rows, so it is not a full
  QR algorithm definition yet.
- Added `householderPanelStateStep_nonempty_residual_and_shape`, the state-level
  one-step bridge.  For a nonempty active panel, the concrete state transition
  has a residual representation for the next active panel and reuses the exact
  top-left/first-column-tail-zero facts for the underlying reflector step.
  Remaining QR work: induction over `householderPanelStateIterate`, plus a
  richer state that records accumulated `Q` and completed `R` structure.
- Added `HouseholderPanelStepReady` and `HouseholderPanelRunReady`, plus
  `householderPanelRunReady_head` and `householderPanelRunReady_tail`.  These
  predicates record the per-step nonzero-column and gamma-validity hypotheses
  needed to use the implementation-backed one-step panel bridge during an
  induction over `householderPanelStateIterate`.
- Added `householderPanelStateStep_nonempty_residual_and_shape_of_ready`, so the
  state-level one-step bridge can consume `HouseholderPanelStepReady` directly
  instead of unpacking nonzero-column and gamma-validity hypotheses at every
  future induction site.
- Added `householderPanelRunReady_succ_iff`, splitting a ready run of length
  `r+1` into a ready current step and a ready tail after
  `householderPanelStateStep`.  This is the intended induction shape for future
  repeated active-panel proofs.
- Added `householderPanelStepReady_nonempty_of_global_gammaValid`, allowing a
  global `gammaValid fp (11*N+23)` assumption for an original row dimension to
  satisfy the current active panel's smaller per-step gamma condition.
- Added `embedTrailingOne` in `HouseholderQR.lean`, embedding an active-panel
  square matrix as the lower-right block of a matrix with leading scalar
  identity.  This is the exact algebraic bridge needed before a trailing-panel
  Householder reflector can be composed as a full-size QR transformation.
- Added exact embedding algebra for `embedTrailingOne`: transpose commutation,
  multiplication commutation, identity preservation, and orthogonality
  preservation.  This means an orthogonal active-panel reflector can now be
  lifted to a full-size orthogonal transformation.
- Added rectangular panel action lemmas for `embedTrailingOne`: left
  multiplication leaves the top row unchanged and the trailing panel becomes
  the smaller `matMulRect` action on the old trailing panel.  These lemmas
  connect full-size embedded transformations with active-panel updates.
- Added `panelFromTopAndTrailing`, exact QR bookkeeping that reconstructs a
  nonempty panel from the computed top row and trailing panel while setting the
  first-column tail to zero.  This supports an implementation-backed `R_hat`
  algorithm whose upper-triangular shape is by construction, not by assuming
  rounded operations produce exact zeros.  A recursive triangularity lemma for
  this constructor is also available.
- Added `fl_householderQRPanel_R` and square alias `fl_householderQR_R`, the
  first recursive rounded Householder QR loop that returns an `R` panel.  It
  applies the concrete rounded first-column reflector, stores the computed top
  row, zeroes the completed first-column tail by construction, and recurses on
  the computed trailing panel.  Proved `fl_householderQR_R_upper`; backward
  error for this recursive loop is still pending.
- Added projection lemmas for `fl_householderQRPanel_R`: the top-left entry
  and top-row tail are the values computed by the current rounded panel step,
  the completed first-column tail is structurally zero, and the trailing panel
  is exactly the recursive output on `fl_householderTrailingPanelStep`.
- Added the stored first-column panel residual bridge:
  `fl_householder_first_column_panel_stored_residual_and_shape`.  It proves
  that after the rounded first-column panel step, replacing the completed
  first-column tail by structural zeros preserves the same residual bound,
  because the exact Householder application has zero tail there and the
  Frobenius norm cannot increase when that residual slice is zeroed.
- Added `panelTrailingPerturbation` and its Frobenius norm equality, plus
  `panelFromTopAndTrailing_lift_trailing_rep`.  These exact algebra lemmas
  lift a tail backward representation into the full panel using
  `embedTrailingOne`, which is the block-composition step needed for the
  recursive QR backward-error induction.
- Added `HouseholderQRPanelReady`, a recursive readiness predicate for the
  concrete `fl_householderQRPanel_R` loop.  Each nonempty panel requires a
  nonzero current first column, the matching gamma-validity condition, and
  readiness of the concrete trailing-panel step.
- Added `householderQRPanelBackwardCoeff` and square alias
  `householderQRBackwardCoeff`, the recursive coefficient intended for the
  future implementation-backed QR backward-error induction.
- Added `HouseholderQRPanelBackwardError`, the rectangular induction target for
  the recursive QR implementation, plus trivial empty-row and empty-column base
  cases.  This target records `R_hat = Qᵀ(A + ΔA)` for rectangular panels; the
  square wrapper still needs to convert it to the existing
  `HouseholderQRBackwardError` form.
- Proved `householder_qr_panel_backward_cons`, the generic recursive cons
  theorem: a stored one-step residual bound for the current panel plus a
  rectangular QR backward-error proof for the trailing panel yields a full-panel
  backward-error proof.  This composes the tail proof with `embedTrailingOne`
  and uses the coefficient update `c + α*(1+c)`.
- Proved `fl_householderQRPanel_R_backward_error`, the implementation-backed
  recursive backward-error theorem for the concrete rounded
  `fl_householderQRPanel_R` loop under `HouseholderQRPanelReady`.  This closes
  the rectangular/panel-level bridge from concrete QR recursion to
  `HouseholderQRPanelBackwardError`; the remaining QR work is the square wrapper
  into `HouseholderQRBackwardError`/`StructuredHouseholderQRBackwardError`.
- Proved the square wrappers:
  `householder_qr_panel_backward_to_square`,
  `fl_householderQR_R_backward_error`, and
  `fl_householderQR_R_structured_backward_error`.  The concrete recursive
  Householder QR `R` algorithm now satisfies the existing structured QR
  backward-error contract, with the explicit `HouseholderQRPanelReady`
  assumptions and recursive coefficient `householderQRBackwardCoeff`.
- In `QR/QRSolve.lean`, added `qr_solve_backward_error_from_components`, which
  packages the existing QR-factorization, `Qᵀb`, and back-substitution component
  equations plus perturbation bounds into `QRSolveBackwardError`.  This fixes
  the algebraic packaging gap for Higham Theorem 18.5, but it is still not a
  concrete `fl_qr_solve` implementation-backed theorem.
- Added concrete QR-solve objects in `QR/QRSolve.lean`:
  `fl_householderQRPanel_rhs`, square alias `fl_householderQR_rhs`, and
  `fl_householderQR_solve`.  The RHS recursion applies the same rounded
  Householder reflectors chosen from the active `A` panel to `b`, then the solve
  definition calls `fl_backSub` on `fl_householderQR_R` and the transformed RHS.
- Added RHS one-step residual bridge in `QR/QRSolve.lean`:
  `HouseholderAppError.exists_residual_vector`,
  `fl_householder_first_column_rhs_step_error`, and
  `fl_householder_first_column_rhs_step_residual`.  These expose the computed
  RHS update as `P*b + e` with `e = ΔP*b`, using the same panel-selected
  Householder reflector as the QR factorization step.
- Added exact componentwise support in `MatrixAlgebra.lean`:
  `abs_entry_le_frobNorm`, `abs_matMulVec_le_card_frobNorm_infNormVec`,
  `abs_matMulVec_le_card_bound_infNormVec`, and orthogonal transport bounds
  `IsOrthogonal.abs_entry_le_one`,
  `IsOrthogonal.abs_matMulVec_le_card_infNormVec`, and
  `IsOrthogonal.infNormVec_matMulVec_le_card`.  These are crude but proved
  exact bounds needed to track QR-solve residual vectors without introducing
  a new assumption.
- Added `HouseholderAppError.exists_residual_vector_bound` and
  `fl_householder_first_column_rhs_step_residual_bound` in `QR/QRSolve.lean`.
  The concrete first-column RHS Householder step now has an explicit
  componentwise residual bound
  `(m+1) * householderConstructApplyBound fp (m+1) * infNormVec b`.
  Added `HouseholderQRRhsPanelBackwardError`,
  `householderQRRhsPanelBackwardBound`,
  `householder_qr_rhs_panel_backward_cons`,
  `fl_householderQRPanel_rhs_backward_error`, and
  `fl_householderQR_rhs_backward_error`.  The concrete RHS reflector recursion
  is now implementation-backed under `HouseholderQRPanelReady`, with a
  recursive componentwise perturbation bound.
- Added the simultaneous shared-orthogonal-factor bridge
  `HouseholderQRPanelSolveBackwardError`,
  `householder_qr_panel_solve_backward_cons`,
  `fl_householderQRPanel_solve_components_backward_error`, and
  `fl_householderQR_solve_components_backward_error`.  This closes the
  common-`Q` gap between the concrete `R` proof and concrete RHS proof.
- Added `fl_householderQR_solve_backward_error`, the implementation-backed
  theorem for the concrete Householder QR solve.  It combines the shared-`Q`
  QR/RHS component theorem with `backSub_backward_error`.  Side assumptions are
  explicit: `HouseholderQRPanelReady`, nonzero diagonal of the computed
  `fl_householderQR_R`, `0 < n`, and `gammaValid fp n`.  The matrix bound is
  `householderQRBackwardCoeff fp n * ‖A‖_F +
  gamma fp n * ‖fl_householderQR_R fp n A‖_F`; the RHS bound is
  `householderQRRhsBackwardBound fp n A b`.
- Began the Givens rebuild in `QR/GivensSpec.lean`.  Added concrete
  `fl_givensApply`, which applies supplied exact `c,s` parameters by two
  rounded multiplications plus rounded add/sub on the affected components and
  copies all other components exactly.  Added exact unroll lemmas for the
  computed and exact `p`, `q`, and unaffected components.  Added
  `fl_givensApply_supplied_app_error`, proving the concrete supplied-parameter
  kernel satisfies `GivensAppError` with the conservative bound
  `gamma fp 2 * ‖givensRotation n p q c s‖_F`.  This is implementation-backed
  for exact supplied `c,s`; rounded rotation-parameter construction and the
  full `fl_givens_qr` loop are still pending.
- Added exact Givens coefficient construction from Higham (18.14):
  `givensDenom`, `givensC`, and `givensS`, plus exact facts
  `givensCoeff_norm_sq`, `givensCoeff_zero_second`,
  `givensCoeff_first_component`, and `givensRotation_constructed_orthogonal`.
  Added rounded coefficient kernels `fl_givensDenom`, `fl_givensC`, and
  `fl_givensS`, with the denominator deliberately routed through the existing
  `fl_norm2` kernel.  Added conservative implementation-backed coefficient
  bridges `fl_givensC_relative_error_conservative` and
  `fl_givensS_relative_error_conservative`, proving `gamma fp 6` relative
  error bounds from `fl_norm2` plus rounded division.  Added the
  `GivensCoeffError` wrapper and `fl_givensCoeffError_conservative` so later
  Givens application/sequence proofs can consume coefficient contracts without
  unpacking both scalar theorems manually.  The sharper Higham Lemma 18.6
  target `ĉ = c(1+θ₄)` and `ŝ = s(1+θ'₄)` is still pending.
- Added `fl_givensApply_coeffError_app_error` and
  `fl_givensApply_computed_app_error_conservative`.  These close the concrete
  Givens coefficient-plus-application path: coefficients are computed by
  `fl_givensC`/`fl_givensS` and then used by `fl_givensApply`, producing a
  `GivensAppError` for the exact constructed rotation.  The bound is the
  conservative `gamma fp 8 * ‖G‖_F`, obtained by combining the current
  `gamma fp 6` coefficient bridge with two rounded operations in the
  application.  This is implementation-backed but not the sharp Higham Lemma
  18.7 constant `sqrt 2 * gamma_6`.
- Added `QR/GivensMatrixStep.lean`, defining `fl_givensApplyMatrix` and
  `fl_givensApplyMatrixRect` plus square/rectangular `ColumnwiseGivensStepError`
  contracts.  Proved `fl_givensApply_computed_matrix_step_error` and its
  rectangular version from the concrete computed-coefficient vector bridge, then
  proved residual matrix aggregation lemmas.  Added
  `fl_givens_sequence_backward_error` and
  `fl_givens_panel_sequence_backward_error` in `GivensQR.lean`, which accumulate
  any supplied concrete sequence of computed Givens updates via the existing
  residual orthogonal sequence theorem under an explicit uniform per-step bound.
  The remaining gap for full Givens QR is choosing/formalizing the annihilation
  schedule and proving the produced sequence has the QR triangular shape and a
  source-clean uniform bound.
- Added exact vector embedding algebra for the QR RHS recursion:
  `vectorTrailingPerturbation`, `embedTrailingOne_matMulVec_top`,
  `vectorTail_embedTrailingOne_matMulVec`, and
  `vectorFromTopTail_lift_trailing_rep`.  These are the vector analogues of the
  panel block-lift lemmas and prepare the recursive RHS backward-error proof.

## 2026-04-26 Fix Pass

- Created and used branch `codex/library-integrity-fixes`.
- Replaced the explicit Method 1B block-inversion placeholders with a meaningful
  `BlockMethod1BSpec` containing `block_count_le_dim`,
  `lower_triangular_inverse`, and `column_backward_error`.
- Added `triInv_method1B_right_residual_from_spec`, which derives the Method 1B
  residual from the new spec using the existing per-column residual proof.
- Redocumented abstract high-level interfaces in `MatrixInversion`,
  `GaussJordan`, Cholesky chapter modules, and Sylvester perturbation so their
  hypothesis status is explicit.
- Corrected the `MMatrix` Corollary 8.10 documentation and README theorem name
  (`mmatrix_forwardSub_relative_error`, not `corollary_8_10`).
- Removed a misleading prose false-positive for `admit` in the SPD docstring of
  `LU/GaussianElimination.lean`.
- Validation after edits: `lake build` completed successfully; scans found no
  Lean `sorry`/`admit`/`axiom`/`opaque` tokens and no explicit `True`
  placeholder block specs or stale “full Corollary 8.10 future work” claims.
  The remaining build warnings are the pre-existing linter warnings in
  QR/least-squares/fast-matmul modules.

## Maintenance Rules For Future Work

- Preserve the axiomatic `FPModel`; do not add IEEE-specific assumptions unless
  they are in a separate optional module.
- Prefer deriving new algorithm bounds from existing foundation theorems rather
  than restating a bound as a hypothesis.
- When adding high-level theorem wrappers around external assumptions, label
  them as abstract/specification transfer theorems, not as full internal error
  analyses.
- Keep public constants exact when Higham gives exact gamma constants. Avoid
  weakening constants unless the theorem name and docs say so.
- Before saying something is absent, search with `rg`/`rg --files`; this
  library is large enough that memory alone is unreliable.
- Prioritize fixes and new formalizations that improve compositional reuse for
  stability proofs, especially kernel contracts useful in larger algorithms.
- Run `lake build` after edits and check for new warnings.
