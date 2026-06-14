# Codex Project Memory

Project: `LeanFpAnalysis`, a Lean 4 library for floating-point arithmetic and
automatic stability analysis. The model is axiomatic and intentionally not tied
to IEEE 754. All core results should be stated over `FPModel` and `Real`.

Last review by Codex: 2026-05-28.
Current RandNLA work is on branch `RandNLA_Kimon`.  Current `main` is for the
stable core library, and benchmark work lives on branch `benchmark`.  The main
commit before the
end-to-end stability rebuild is tagged as
`main-stable-before-end-to-end-20260527` at
`d5c0fa90c69c36f794f176c96f2dd4d293bb5aa3`.

## Build State

- `lake build` succeeds with Lean toolchain `leanprover/lean4:v4.29.0-rc3`.
- No real `sorry`, `admit`, `axiom`, `unsafe`, or `opaque` declarations were
  found in `LeanFpAnalysis` during the 2026-05-23 health check.
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
  `ForwardError`, `FiniteProbability`, `MatrixAlgebra`, `PerturbationTheory`.
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
  absorption lemmas such as `three_gamma_plus_sq_le_gamma`.
- `Analysis/Summation.lean`: `fl_sum_error`, `fl_sum_error_init`,
  `fl_sum_error_tight`.
- `Analysis/SubtractionFold.lean`: subtraction-fold and inverse-product
  error lemmas used by triangular substitution proofs.
- `Analysis/FiniteProbability.lean`: lightweight finite probability spaces,
  finite Markov, Chebyshev, exponential Markov, and Chernoff kernels.
- `Analysis/MatrixAlgebra.lean`: exact matrix operations, inverses, norms,
  transpose, Frobenius algebra, vector 2-norm/operator-2 predicate bounds,
  orthogonal matrices, Neumann-series style bounds. This is foundational but
  very large and could eventually be split.
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
- RandNLA Algorithm 1 now builds as:
  `ElementwiseSampling` for squared-magnitude probabilities, deterministic
  sampled-entry updates, traces, hit counts, and entrywise stability events;
  `Analysis/FiniteProbability` for generic probability kernels; and
  `HitCountConcentration` for Markov, pairwise-Chebyshev, and canonical
  product-law Chernoff concentration plus high-probability stability.
  `ElementwiseSpectral` adds the deterministic equation (2) transfer layer:
  exact rectangular `rectOpNorm2Le` spectral residual events transfer to
  floating-point residual events by adding the Frobenius norm of a proved
  entrywise FP perturbation budget. This does not prove the missing exact
  matrix concentration theorem.
  It also contains `algorithm1ExactFrobEvent` and the bridge theorems
  `probability_algorithm1_exact_spectral_of_frob` and
  `probability_algorithm1_fl_spectral_of_exact_frob`, which transfer a proved
  exact Frobenius residual event to exact/FP rectangular operator events.
  The canonical product trace law now also proves the weaker nonconditional
  Frobenius/Markov route:
  `sqMagTraceProbability_expectationReal_elementwiseTraceResidual_frob_sq_le`,
  `sqMagTraceProbability_eventProb_algorithm1ExactSpectralEvent_ge_one_sub_frob`,
  and
  `sqMagTraceProbability_eventProb_algorithm1FlSpectralEvent_ge_one_sub_frob`.
  Do not cite these as CACM equation (2); they carry an `m*n` Frobenius factor
  and do not replace matrix Bernstein/Khintchine.
  The scalar entrywise route now also uses the generic finite-intersection
  union bound
  `FiniteProbability.eventProb_forall_ge_one_sub_sum` to prove
  `sqMagTraceProbability_eventProb_algorithm1ExactEntrywiseEvent_ge_one_sub`,
  `sqMagTraceProbability_eventProb_algorithm1ExactSpectralEvent_ge_one_sub_entrywise`,
  and
  `sqMagTraceProbability_eventProb_algorithm1FlSpectralEvent_ge_one_sub_entrywise`.
  This is a real high-probability support theorem, but it is still only
  Markov-plus-union-bound over entries and must not be cited as CACM equation
  (2)'s Bernstein/Khintchine spectral concentration theorem.
  `MatrixAlgebra` now provides vector-norm homogeneity and
  `rectUnitBallCover`/`rectOpNorm2Le_of_unit_ball_cover`.  Algorithm 1 composes
  this deterministic cover geometry with finite-test-set Markov tails and a
  Frobenius residual event in
  `sqMagTraceProbability_eventProb_algorithm1ExactSpectralEvent_ge_one_sub_cover`
  and
  `sqMagTraceProbability_eventProb_algorithm1FlSpectralEvent_ge_one_sub_cover`.
  These theorems assume a supplied finite unit-ball cover and are still support
  infrastructure, not a construction of an optimal net or a replacement for
  matrix Bernstein/Khintchine.
  The matrix-concentration route now also has self-adjoint dilation
  infrastructure in `MatrixAlgebra`: `finiteVecNorm2`, `finiteMatVec`,
  `finiteFrobNormSq`, `finiteMatMul`, `finiteIdMatrix`, `finiteTranspose`,
  `finiteTrace`,
  `finiteTrace_add`, `finiteTrace_smul`, `finiteTrace_finiteMatMul_comm`,
  `finiteMatVec_finiteMatMul`, `finiteMatVec_finiteIdMatrix`,
  `finiteVecNorm2Sq_finiteMatVec_le_finiteFrobNormSq_mul`,
  `finiteOpNorm2Le`, `finiteQuadraticForm`, `finitePSD`,
  `finiteLoewnerLe`,
  `abs_finiteVecInnerProduct_finiteMatVec_le_of_finiteOpNorm2Le`,
  `finiteQuadraticForm_add`, `finiteQuadraticForm_neg`,
  `finiteQuadraticForm_sub`,
  `finiteQuadraticForm_finset_sum`,
  `finiteQuadraticForm_finset_sum_smul`,
  `finiteQuadraticForm_fintype_sum`,
  `finiteQuadraticForm_fintype_sum_smul`,
  `finitePSD_fintype_sum_of_finitePSD`,
  `finitePSD_fintype_sum_smul_of_nonneg`,
  `abs_finiteQuadraticForm_le_of_loewnerLe_neg`,
  `finiteQuadraticForm_finiteMatMul_self_of_symmetric`,
  `finitePSD_finiteMatMul_self_of_symmetric`,
  `finiteQuadraticForm_finiteMatMul_self_le_finiteFrobNormSq_mul_of_symmetric`,
  `finiteMatMul_self_loewnerLe_scalar_id_of_finiteOpNorm2Le`,
  `finiteOpNorm2Le_of_finiteMatMul_self_loewnerLe_scalar_id`,
  `rectSelfAdjointDilation`,
  `finitePSD_rectSelfAdjointDilation_square`,
  `rectSelfAdjointDilation_square_loewnerLe_scalar_id_of_finiteOpNorm2Le`,
  `rectSelfAdjointDilation_opNorm2Le_of_square_loewnerLe_scalar_id`,
  `rectOpNorm2Le_of_selfAdjointDilation_square_loewnerLe_scalar_id`,
  `finiteFrobNormSq_rectSelfAdjointDilation`,
  `finiteTrace_finiteMatMul_rectSelfAdjointDilation_self`, and
  `rectOpNorm2Le_of_selfAdjointDilation`.  `ElementwiseSpectral` connects this
  to Algorithm 1 with `algorithm1ExactDilationEvent`,
  `algorithm1ExactDilationSquareEvent`,
  `algorithm1ExactDilationSquareEvent_subset_exactDilationEvent`,
  `algorithm1ExactDilationSquareEvent_subset_exactSpectralEvent`,
  `rectSelfAdjointDilation_elementwiseTraceResidual_eq_sum_sampleResidualIncrement`,
  `sqMagProb_sum_rectSelfAdjointDilation_elementwiseSampleResidualIncrement_eq_zero`,
  `sqMagProb_sum_finiteFrobNormSq_rectSelfAdjointDilation_elementwiseSampleResidualIncrement_le`,
  `sqMagProb_sum_finiteQuadraticForm_rectSelfAdjointDilation_square_le`,
  `sqMagProb_sum_steps_finiteQuadraticForm_rectSelfAdjointDilation_square_le`,
  `sqMagProb_sum_rectSelfAdjointDilation_square_loewnerLe_scalar_id`,
  `sqMagProb_sum_rectSelfAdjointDilation_square_psd`,
  `sqMagProb_sum_steps_rectSelfAdjointDilation_square_loewnerLe_scalar_id`,
  `sqMagProb_sum_steps_rectSelfAdjointDilation_square_psd`,
  `sqMagProb_sum_finiteTrace_rectSelfAdjointDilation_square_le`,
  `sqMagProb_sum_steps_finiteTrace_rectSelfAdjointDilation_square_le`,
  `probability_algorithm1_exact_spectral_of_dilation`, and
  `probability_algorithm1_fl_spectral_of_exact_dilation`, plus
  `probability_algorithm1_exact_spectral_of_dilation_square` and
  `probability_algorithm1_fl_spectral_of_exact_dilation_square`.  These remain
  bridge and quadratic-form/Loewner/PSD/trace variance-proxy theorems, plus
  deterministic trace/order algebra, trace monotonicity, scalar-identity trace
  bounds, symmetric operator-square trace bounds, and trace-of-square
  identities for the dilation; they do not prove Bernstein/Khintchine.
  The matrix algebra layer also bridges local finite symmetry to mathlib's
  matrix API through `IsSymmetricFiniteMatrix.to_matrix_isSymm` and
  `Matrix_isSymm.to_IsSymmetricFiniteMatrix`, plus the Hermitian bridge
  `IsSymmetricFiniteMatrix.to_matrix_isHermitian` and
  `Matrix_isHermitian.to_IsSymmetricFiniteMatrix`, so a future
  largest-eigenvalue or trace-exponential proof can use mathlib symmetry and
  Hermitian facts without changing the RandNLA algorithm definitions.  The same layer now bridges
  local `finitePSD`/`finiteLoewnerLe` facts to mathlib `Matrix.PosSemidef`
  through `finitePSD.to_matrix_posSemidef`,
  `Matrix_posSemidef.to_finitePSD`,
  `finitePSD_iff_matrix_posSemidef_of_symmetric`,
  `finiteLoewnerLe.to_matrix_posSemidef_sub`, and
  `Matrix_posSemidef_sub.to_finiteLoewnerLe`, plus the iff theorem
  `finiteLoewnerLe_iff_matrix_posSemidef_sub_of_symmetric`.
  `Analysis/MatrixSpectral.lean` now adds `finiteHermitianEigenvalues`,
  `finiteHermitianEigenvalues_mem_spectrum_real`, and
  `finiteTrace_eq_sum_finiteHermitianEigenvalues`, a mathlib-backed spectral
  hook for finite real symmetric matrices.  It also has
  `finitePSD_iff_finiteHermitianEigenvalues_nonneg`,
  `finiteLoewnerLe_iff_sub_finiteHermitianEigenvalues_nonneg`, and
  `finiteLoewnerLe_smul_id_iff_sub_finiteHermitianEigenvalues_nonneg`, so
  local PSD and scalar-identity Loewner upper events can be read as
  nonnegativity of Hermitian eigenvalues of difference matrices.  This is still foundation only; the
  matrix Bernstein/Khintchine tail is not proved.
  `FiniteProbability` now has real-valued exponential Markov in
  `eventProb_real_ge_le_exp_mul_mgf` and
  `eventProb_real_le_ge_one_sub_exp_mul_mgf`.
  External literature search recorded Tropp, "User-friendly tail bounds for
  sums of random matrices" (Found. Comput. Math. 12 (2012), arXiv:1004.4389)
  as advisory guidance for the next source-chain targets: Theorem 3.6,
  Corollary 3.7, Theorem 1.4, and Theorem 1.6. These are not formalized or
  used as hidden hypotheses.
- RandNLA Algorithm 2 row sampling builds in `Algorithms/RandNLA/RowSampling.lean`
  and `Algorithms/RandNLA/RowSamplingGram.lean`: equation (4) norm-squared row
  probabilities, literal sampled rows, local one-division FP stability,
  elementwise unbiasedness of `Atildeᵀ Atilde`, the iid variance calculation,
  high-probability equation (5), the probability-one support theorem for
  positive-probability row traces, and explicit FP perturbation/bias theorems
  for the Gram matrix.
  Do not cite any grouped row-hit or Chernoff-count theorem for Algorithm 2;
  Algorithm 2 does not accumulate repeated sampled rows.
- RandNLA Algorithm 2 leverage-score row sampling builds in
  `Algorithms/RandNLA/RowSamplingLeverage.lean`: equation (6) is formalized as
  the existing row-norm-squared distribution applied to an orthonormal-column
  matrix `U`, proving `p_i = ||U_i*||_2^2 / n`, `rowGram U = I`, and equation
  (7) in vector-action operator-2 form. The fully floating-point equation (7)
  corollary reuses `rowSampleGramFullFpPerturbBudget` and `dotProduct_error_bound`.
- RandNLA equation (8) least-squares work now includes
  `Algorithms/RandNLA/LeastSquaresSketch.lean`: `lsObjective`,
  `PreservesLSObjective`, and deterministic sketched-minimizer residual
  objective theorems. It also has the coordinate quadratic-error bridge
  `preservesLSObjective_of_coordinate_quadratic_error` and finite-probability
  transfer `eventProb_preservesLSObjective_of_coordinate_quadratic_error`,
  which turn an already proved operator-2 Gram-error event into
  `PreservesLSObjective`. The high-probability theorem that a concrete random
  sketch supplies the residual coordinates and operator event with the survey
  sample complexity remains open.
- The Section 7 open backlog is tracked in
  `docs/RANDNLA_CACM_NOT_PROVED_LEDGER.md`. Open paper-level items remain:
  Algorithm 1 equation (2) exact matrix concentration, matrix
  Bernstein/Khintchine, randomized LS embedding for equation (8), low-rank
  equation (9), and matrix completion equations (10)--(11).

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
- `HitCountConcentration.lean` is large but now logically narrower after moving
  generic finite-probability kernels to `Analysis/FiniteProbability.lean`. It
  remains internally sectioned; future growth could justify splitting hit-count
  moments, budgets, and the squared-magnitude product trace law.
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
- RandNLA Algorithm 1 deterministic and randomized stability work lives on
  branch `RandNLA_Kimon`. The public entry point is
  `LeanFpAnalysis.FP.Algorithms.RandNLA`.
- Algorithm 2 row sampling is also on `RandNLA_Kimon`; cite
  `fl_rowSampleSketch_error_bound` for the local sampled-entry FP division
  bound, `rowSqNormTraceProbability_expectationReal_rowSampleGram_entry` for
  unbiasedness of `Atildeᵀ Atilde`,
  `rowSqNormTraceProbability_eventProb_rowSampleGram_frob_error_le_epsilon`
  for the exact high-probability equation (5) bound, and
  `rowSqNormTraceProbability_eventProb_fl_rowSampleGramDot_frob_error_le_epsilon_add_explicit_budget`
  for the fully floating-point Gram corollary; it reuses `fl_dotProduct` /
  `dotProduct_error_bound` and has an explicit budget with `δτ = 0`.
- For Algorithm 2 equation (6)/(7), cite
  `leverageTraceProbability_eventProb_rowSampleGram_opNorm2_error_le_epsilon`
  for the exact leverage-score subspace-embedding theorem and
  `leverageTraceProbability_eventProb_fl_rowSampleGramDot_opNorm2_error_le_epsilon_add_budget`
  for the fully floating-point theorem. These use `opNorm2Le`, the vector-action
  form of an operator-2-norm bound, rather than a supremum-valued spectral norm.
- For Algorithm 1 equation (2)-style floating-point transfer, cite
  `fl_elementwiseTraceResidual_rectOpNorm2Le_of_exact`,
  `fl_elementwiseTraceResidual_rectOpNorm2Le_of_exact_and_hitCount_le`, and
  `probability_algorithm1_fl_spectral_of_exact_spectral`. Do not cite these as
  the exact equation (2) concentration theorem; they require an exact spectral
  event as input.
- For the weaker Frobenius-to-operator route, cite
  `algorithm1ExactFrobEvent_subset_exactSpectralEvent`,
  `probability_algorithm1_exact_spectral_of_frob`, and
  `probability_algorithm1_fl_spectral_of_exact_frob`. These require a proved
  exact Frobenius residual event as input and do not close equation (2).
- For equation (8) deterministic least-squares sketching, cite
  `lsObjective_le_of_sketch_preserves` and
  `lsObjective_le_one_add_eta_of_sketch_preserves`. Do not cite these as a
  randomized sampling/sample-complexity theorem.
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

## 2026-05-22 RandNLA Algorithm 1 Work

- Added `Algorithms/RandNLA/ElementwiseSampling.lean` and
  `Algorithms/RandNLA/HitCountConcentration.lean`, re-exported through
  `Algorithms/RandNLA.lean` and `Algorithms.lean`.
- Formalized squared-magnitude sampling probabilities
  `p_ij = A_ij^2 / ‖A‖_F^2`, deterministic Algorithm 1 sampled-entry updates,
  trace hit counts, and entrywise floating-point stability budgets.
- Proved high-probability stability routes using Markov, pairwise-Chebyshev,
  and Chernoff concentration for the hit counter.
- Closed the Chernoff gap for the canonical independent Algorithm 1 sampler:
  `sqMagTraceProbability` is the finite product trace law, and
  `sqMagTraceProbability_chernoff_mgf_bound` proves the Bernoulli-sum MGF bound
  from that product law rather than assuming it.
- The final canonical high-probability stability APIs are
  `highProbability_sqMagTraceStability_of_independent_chernoff_budget` and
  `highProbability_sqMagTraceStability_of_independent_chernoff_optimized_tail_budget`.
- Generic `*_of_mgf_bound` lemmas remain only as reusable probability bridges;
  they are not the final theorem to cite for Algorithm 1.
- `docs/LIBRARY_LOOKUP.md`, `examples/LibraryLookup.lean`,
  `docs/RANDNLA_ALGORITHM1_STABILITY_LEDGER.md`, and
  `docs/Algorithm1_Stability_Proof_Summary.pdf` document the current theorem
  map.

## 2026-05-23 RandNLA Algorithm 2 Work

- Added `Algorithms/RandNLA/RowSampling.lean` for Algorithm 2 from the CACM
  RandNLA paper, using equation (4)
  `p_i = ||A_i*||_2^2 / ||A||_F^2`, and
  `Algorithms/RandNLA/RowSamplingGram.lean` for the Gram-matrix analysis.
- Formalized row norms, row probabilities, literal sampled sketches
  (`rowSampleSketch`, `fl_rowSampleSketch`), the canonical independent product
  row-trace law, `rowGram`, `rowSampleGram`, and `fl_rowSampleGram`.
- Correction: the earlier grouped row-hit/count material and the sampled-sketch
  probability-one event were removed from the Algorithm 2 API because Algorithm
  2 returns an `s × n` sampled matrix and does not sum repeated row samples.
  The later 2026-05-23 health pass also removed the unused `rowSampleHits`
  helper to keep the row-sampling API away from hit-count terminology.
- Closed the later FP-premise gap: `rowTracePositiveProb` and
  `rowSqNormTraceProbability_eventProb_rowTracePositiveProb` prove the product
  law has probability-one support on positive-probability sampled rows, and
  `rowSampleGramFpPerturbBudget` /
  `rowSampleGram_perturb_budget_le_explicit` give an explicit deterministic
  Gram perturbation budget.
- Added the fully floating-point Gram path `fl_rowSampleGramDot`, which reuses
  the repository's `fl_dotProduct` and `dotProduct_error_bound` instead of
  re-proving dot-product rounding inside RandNLA. Its final closed corollary is
  `rowSqNormTraceProbability_eventProb_fl_rowSampleGramDot_frob_error_le_epsilon_add_explicit_budget`.
- Main APIs:
  `fl_rowSampleSketch_error_bound`,
  `rowSqNormTraceProbability_eventProb_rowTracePositiveProb`,
  `rowSqNormTraceProbability_expectationReal_rowSampleGram_entry`,
  `rowSqNormTraceProbability_expectationReal_rowSampleGram_frob_error_sq_le`,
  `rowSqNormTraceProbability_eventProb_rowSampleGram_frob_error_le_epsilon`,
  `rowSqNormTraceProbability_eventProb_rowSampleGram_frob_error_le_epsilon_of_budget`,
  `rowSampleGram_entry_error_bound_of_entrywise`,
  `rowSampleGram_frob_error_bound_of_entrywise`,
  `rowSampleGramFpPerturbBudget`,
  `rowSampleGramDotProductBudget`,
  `rowSampleGramFullFpPerturbBudget`,
  `rowSampleGram_perturb_budget_le_explicit`,
  `rowSampleGram_dot_product_budget_le_explicit`,
  `rowSqNormTraceProbability_expectationReal_fl_rowSampleGram_entry_bias_bound_of_entrywise`,
  `rowSqNormTraceProbability_eventProb_fl_rowSampleGram_frob_error_le_epsilon_add_tau`,
  `rowSqNormTraceProbability_eventProb_fl_rowSampleGram_frob_error_le_epsilon_add_tau_of_forall`,
  `rowSqNormTraceProbability_eventProb_fl_rowSampleGram_frob_error_le_epsilon_add_tau_of_entrywise_budget`,
  `rowSqNormTraceProbability_eventProb_fl_rowSampleGram_frob_error_le_epsilon_add_explicit_budget`,
  `rowSqNormTraceProbability_eventProb_fl_rowSampleGramDot_frob_error_le_epsilon_add_explicit_budget`.
- Important distinction: `..._epsilon_add_tau` is a generic union-bound
  transfer theorem with a separate perturbation failure `δτ`. The final
  theorem to cite is now `..._add_explicit_budget`; it proves the support,
  entrywise FP stability, explicit budget, and `δτ = 0` internally.
- Natural-language theorem/corollary summary:
  `docs/Algorithm2_RowSampling_Stability_Proof_Summary.pdf`.

## 2026-05-24 RandNLA Algorithm 2 Leverage Work

- Added `vecNorm2Sq`, `vecNorm2`, `opNorm2Le`, and
  `opNorm2Le_of_frobNorm_le` to `Analysis/MatrixAlgebra.lean`. This provides a
  formally proved bridge from Frobenius bounds to vector-action operator-2
  bounds without adding a new spectral-norm supremum object. Later added
  `frobNorm_const` to expose closed forms for constant Gram-budget matrices.
- Added `Algorithms/RandNLA/RowSamplingLeverage.lean` and re-exported it
  through `Algorithms/RandNLA.lean`.
- Formalized the equation (6) leverage-score row probabilities for an
  orthonormal-column matrix `U`:
  `HasOrthonormalColumns`, `leverageScore`, `leverageScoreProb`,
  `rowSqNormProbDen_eq_nat_of_orthonormal_columns`, and
  `leverageScoreProb_eq_rowNormSq_div_nat`.
- Proved equation (7) in exact arithmetic as
  `leverageTraceProbability_eventProb_rowSampleGram_opNorm2_error_le_epsilon`.
  It reuses the existing equation (5) Frobenius high-probability theorem applied
  to `U`, then transfers Frobenius control to `opNorm2Le`.
- Proved the fully floating-point equation (7) corollary
  `leverageTraceProbability_eventProb_fl_rowSampleGramDot_opNorm2_error_le_epsilon_add_budget`.
  The added FP term is exactly `rowSampleGramFullFpPerturbBudget fp s U`.
- Added `rowSampleGramFpPerturbBudget_eq_nat_mul` and
  `rowSampleGramDotProductBudget_eq_nat_mul` in `RowSamplingGram.lean`, making
  explicit that the row-scaling and dot-product FP budgets include the Gram
  dimension factor `n` hidden in the type `A : Fin m → Fin n → ℝ`.

## 2026-05-25 RandNLA Algorithm 3 Preconditioning Work

- Added `Algorithms/RandNLA/Preconditioning.lean` and re-exported it through
  `Algorithms/RandNLA.lean`.
- Formalized the three explicit branches of Algorithm 3 from the CACM RandNLA
  paper: `preconditionRows` for `PiL * A`, `preconditionColumns` for
  `A * PiR`, and `preconditionElements` for `PiL * A * PiR`.
- Reused existing matrix multiplication infrastructure rather than proving a
  new local product theorem: the floating-point definitions
  `fl_preconditionRows`, `fl_preconditionColumns`, and
  `fl_preconditionElements` are built from `fl_matMul`.
- Main exact results:
  `preconditionRows_frobNorm_orthogonal`,
  `preconditionColumns_frobNorm_orthogonal`, and
  `preconditionElements_frobNorm_orthogonal`.
- Deterministic leverage-basis results added on 2026-05-31:
  `preconditionRows_hasOrthonormalColumns_of_orthogonal`,
  `preconditionColumns_hasOrthonormalColumns_of_orthogonal`,
  `preconditionElements_hasOrthonormalColumns_of_orthogonal`,
  `rowSqNormProbDen_preconditionRows_eq_nat_of_orthogonal`,
  `rowSqNormProbDen_preconditionColumns_eq_nat_of_orthogonal`, and
  `rowSqNormProbDen_preconditionElements_eq_nat_of_orthogonal`. These reuse
  the local equation (6) leverage-score basis and denominator theorem; they do
  not prove distribution-specific random-projection uniformization.
- SRHT deterministic route results added on 2026-05-31:
  `IsOrthogonal.diagMatrix_of_sq_eq_one`,
  `signedOrthogonalPreconditioner_isOrthogonal`,
  `signedOrthogonalPreconditionRows_hasOrthonormalColumns`, and
  `rowSqNormProbDen_signedOrthogonalPreconditionRows_eq_nat`.  These close the
  signed-diagonal/orthogonal prerequisite in the proof-source route through
  Tropp's 2011 SRHT row-norm lemma; the Rademacher/Hadamard row-norm
  concentration and finite union bound remain open.
- SRHT Rademacher sign-law route results added on 2026-05-31:
  `RademacherTrace`, `rademacherSign`, `rademacherSignVector`,
  `rademacherTraceProbability`, and
  `rademacherTraceProbability_eventProb_signedOrthogonalPreconditionRows_eq_one`.
  These define the uniform finite sign-vector law and prove the signed
  orthogonal preprocessing support event with probability one.  They do not
  prove Hadamard flatness, row-norm concentration, or maximum-leverage
  uniformization.
- SRHT Rademacher moment and flat-Hadamard expectation results added on
  2026-05-31: `rademacherTraceProbability_expectationReal_sign_eq_zero`,
  `rademacherTraceProbability_expectationReal_sign_mul_eq_ite`,
  `rademacherTraceProbability_expectationReal_sq_sum_mul_sign_eq_sum_sq`,
  `HadamardFlat`, `signedHadamardPreconditionRows_entry`, and
  `rademacherTraceProbability_expectationReal_rowNormSq_signedHadamard_eq`.
  These prove the finite sign moment algebra and the expectation identity
  `E ||(H D_omega U)_{i,*}||_2^2 = n/m` under `HadamardFlat H` and
  `UᵀU = I`.  This is still not the high-probability Tropp row-norm tail or
  maximum-leverage uniformization theorem.
- SRHT weak Markov/union row-norm auxiliary added on 2026-05-31:
  `rademacherTraceProbability_eventProb_rowNormSq_signedHadamard_le_ge_one_sub`,
  `rademacherTraceProbability_eventProb_forall_rowNormSq_signedHadamard_le_ge_one_sub_sum`,
  `rademacherTraceProbability_eventProb_forall_rowNormSq_signedHadamard_le_ge_one_sub`,
  and
  `rademacherTraceProbability_eventProb_forall_rowNormSq_signedHadamard_le_ge_one_sub_delta`.
  These reuse the local finite Markov inequality and finite union bound to
  prove an all-row high-probability threshold theorem from the expectation
  identity.  This is weaker than Tropp's SRHT row-norm concentration and does
  not close source-level Algorithm 3 random-projection uniformization.
- Main FP results:
  `fl_preconditionRows_error_bound`,
  `fl_preconditionColumns_error_bound`,
  `preconditionColumns_entry_error_bound_of_entrywise`, and
  `fl_preconditionElements_error_bound`.
- Scope note: the paper's random-projection uniformization discussion is
  distribution-specific and descriptive in the CACM survey. The formalized
  Algorithm 3 results are deterministic after the preprocessing matrices are
  drawn; no random-projection concentration theorem is claimed.

## 2026-05-25 Full RandNLA CACM Paper Audit

- Updated `docs/RANDNLA_CACM_NOT_PROVED_LEDGER.md` from a Section-7-only
  backlog into a full-paper algorithm/application inventory.
- Explicit algorithms in the CACM paper are Algorithm 1 element-wise sampling,
  Algorithm 2 row sampling, and Algorithm 3 random-projection preconditioning.
  Later sections also describe application-level algorithmic claims for least
  squares, low-rank approximation, matrix completion, and Laplacian solvers.
- Do not claim the full-paper final gate passes. Open paper-level foundations
  still include Algorithm 1 spectral concentration, matrix Bernstein/Khintchine,
  randomized LS embedding,
  Algorithm 3 distribution-specific uniformization, low-rank equation (9),
  matrix completion equations (10)--(11), and Laplacian/effective-resistance
  sparsification.
- New exact Algorithm 1 subtheorems from the full-paper audit:
  `sqMagTraceProbability_expectationReal_elementwiseTraceSketch_nonzero_entry`,
  `sqMagTraceProbability_expectationReal_elementwiseTraceSketch_zero_entry`,
  `sqMagTraceProbability_expectationReal_elementwiseTraceSketch_entry`, and
  `sqMagTraceProbability_expectationReal_elementwiseTraceSketch_matrix`
  prove support-inclusive unbiasedness under the canonical independent
  squared-magnitude trace law when `steps = s` and `(s : ℝ) ≠ 0`.
- Existing deterministic/probabilistic subtheorems remain valid but must stay
  separated from those open paper-level rows in PDFs, README, lookup docs, and
  final reports.
- 2026-05-25 full-paper gate rerun with the updated automation prompt searched
  local library and bundled mathlib for the remaining foundations. No matrix
  Bernstein/Khintchine, rectangular spectral random-matrix concentration,
  randomized LS embedding theorem, rectangular low-rank/SVD/pseudoinverse
  package, nuclear-norm matrix-completion machinery, or effective-resistance
  sparsification theorem was available to close an open paper-level row. Keep
  reporting the full-paper gate as FAIL while those ledger rows remain open.
- 2026-05-25 ledger-structure pass added
  `docs/RANDNLA_CACM_THEOREM_LEDGER.md` so the full-paper loop has a live
  theorem ledger separate from the not-proved backlog. It records extracted
  algorithms/equations, random variables, events, classifications, Lean theorem
  names, hypothesis classes, current status, and next proof step for each CACM
  RandNLA claim. The not-proved ledger remains the authoritative FAIL/PASS
  gate for open paper-level results.
- 2026-05-25 continuation-rule update: for full-paper or "prove every
  not-proved item" requests, a failed final gate is a checkpoint, not a stopping
  condition. If any requested paper-level row remains open, select the
  highest-leverage open row and continue with the next concrete Lean theorem or
  reusable foundation proof. Only return a "still open" report when the user
  asks for status/pause, a mathematical choice is genuinely required, or an
  external blocker prevents further local proof work.
- 2026-05-25 Algorithm 1 equation (2) continuation: added the residual
  increment foundation. `elementwiseTraceResidual_eq_sum_sampleResidualIncrement`
  proves the exact residual is a sum of one-sample increments when `steps = s`;
  `sqMagProb_sum_elementwiseSampleResidualIncrement_entry_eq_zero`,
  `sqMagTraceProbability_expectationReal_elementwiseTraceResidual_entry_eq_zero`,
  and the vector-action variants
  `sqMagProb_sum_rectMatMulVec_elementwiseSampleResidualIncrement_eq_zero` and
  `sqMagTraceProbability_expectationReal_rectMatMulVec_elementwiseTraceResidual_eq_zero`
  prove the corresponding mean-zero facts. This is not a spectral tail theorem;
  A1.5 now has self-adjoint dilation, trace-of-square, finite PSD/Loewner,
  trace monotonicity, squared-Loewner-to-operator adapters, and
  quadratic-form/Loewner/PSD/trace variance-proxy prerequisites, but still
  needs largest-eigenvalue/trace-exponential or Bernstein/Khintchine-style
  concentration.
- 2026-05-25 Algorithm 1 equation (2) continuation: added the variance-proxy
  layer for those increments. New proved support theorems include
  `sqMagProb_sum_elementwiseSampleContribution_entry_sq_le`,
  `sqMagProb_sum_elementwiseSampleResidualIncrement_entry_sq_le`,
  `sqMagProb_sum_elementwiseSampleResidualIncrement_frob_sq_le`,
  `sqMagProb_sum_vecNorm2Sq_rectMatMulVec_elementwiseSampleResidualIncrement_le`,
  `sqMagTraceProbability_expectationReal_vecNorm2Sq_rectMatMulVec_elementwiseTraceResidual_le`,
  and
  `sqMagTraceProbability_eventProb_vecNorm2_rectMatMulVec_elementwiseTraceResidual_le_ge_one_sub`.
  Also added the FP fixed-vector transfer
  `fl_elementwiseTraceResidual_vecNorm2_le_of_exact_fixed_vector` and
  probability corollary
  `sqMagTraceProbability_eventProb_fl_vecNorm2_rectMatMulVec_elementwiseTraceResidual_le_ge_one_sub`.
  The finite-test-set support layer is
  `sqMagTraceProbability_eventProb_forall_vecNorm2_rectMatMulVec_elementwiseTraceResidual_le_ge_one_sub_sum`
  and
  `sqMagTraceProbability_eventProb_forall_fl_vecNorm2_rectMatMulVec_elementwiseTraceResidual_le_ge_one_sub_sum`.
  These are one-step/fixed-vector/finite-test second-moment and Markov support
  results, not the CACM equation (2) uniform spectral concentration theorem.
- 2026-05-26 Algorithm 1 source-alignment continuation: formalized the
  Drineas--Zouzias hard-thresholding layer instead of treating the truncated
  source theorem as if it proved the untruncated `A_ij^2 / ||A||_F^2` law. New
  public theorems include `elementwiseTruncate`,
  `elementwiseTruncate_square_error_frobNormRect_le_half`,
  `elementwiseTruncate_square_error_rectOpNorm2Le_half`,
  `elementwiseTruncatedTraceResidual_square_rectOpNorm2Le_of_half`,
  `probability_algorithm1_exact_truncated_spectral_of_sampled_half`,
  `fl_elementwiseTruncatedTraceResidual_rectOpNorm2Le_of_truncated`, and
  `probability_algorithm1_fl_truncated_spectral_of_sampled_half`. These prove
  deterministic truncation cost and exact/FP transfer from a future half-budget
  theorem for sampling `\hat A`; they still do not prove the matrix-Bernstein
  half-budget event or close the untruncated equation (2) target.
- 2026-05-26 Algorithm 1 matrix-Bernstein prerequisite continuation: added
  product-law support and bounded-increment infrastructure for the truncated
  route. New public theorems include `entry_ne_zero_of_sqMagProb_pos`,
  `elementwiseTracePositiveProb`,
  `sqMagTraceProbability_eventProb_elementwiseTracePositiveProb`,
  `frobNormRect_elementwiseTruncate_le`,
  `frobNormRect_elementwiseSampleContribution_truncated_le`,
  `frobNormRect_elementwiseSampleResidualIncrement_truncated_le`,
  `rectOpNorm2Le_elementwiseSampleResidualIncrement_truncated`,
  `sqMagTraceProbability_eventProb_truncatedResidualIncrementsBoundedEvent_eq_one`,
  `finiteOpNorm2Le_rectSelfAdjointDilation_elementwiseSampleResidualIncrement_truncated`,
  and
  `sqMagTraceProbability_eventProb_truncatedDilationIncrementsBoundedEvent_eq_one`,
  plus the squared-Loewner versions
  `finiteLoewnerLe_rectSelfAdjointDilation_square_elementwiseSampleResidualIncrement_truncated`
  and
  `sqMagTraceProbability_eventProb_truncatedDilationIncrementSquaresBoundedEvent_eq_one`.
  These discharge support, bounded-matrix, and bounded-square side conditions
  only; the trace-exponential/largest-eigenvalue Bernstein tail remains open.
- 2026-05-26 tightened the same truncated Bernstein side-condition layer with
  two-sided Loewner boundedness.  Generic matrix algebra now includes
  `finiteLoewnerLe_smul_id_of_finiteOpNorm2Le` and
  `finiteLoewnerLe_neg_smul_id_of_finiteOpNorm2Le`; the truncated Algorithm 1
  route now exposes
  `finiteLoewnerLe_rectSelfAdjointDilation_elementwiseSampleResidualIncrement_truncated`,
  `finiteLoewnerLe_neg_rectSelfAdjointDilation_elementwiseSampleResidualIncrement_truncated`,
  `truncatedDilationIncrementLoewnerBoundedEvent`, and
  `sqMagTraceProbability_eventProb_truncatedDilationIncrementLoewnerBoundedEvent_eq_one`.
  The simultaneous `truncatedDilationBernsteinBoundedEvent` now packages
  bounded-operator, two-sided Loewner, and squared-Loewner side conditions with
  probability one.  This is still prerequisite infrastructure, not the
  trace-MGF domination theorem.
- 2026-05-26 added the deterministic scalar-CGF-to-trace-exponential step for
  the trace-MGF route.  `MatrixSpectral.lean` now proves
  `finiteQuadraticForm_finiteHermitianEigenvector_eq_eigenvalue_mul_norm_sq`,
  `finiteVecNorm2Sq_finiteHermitianEigenvector_eq_one`,
  `finiteHermitianEigenvalues_le_of_finiteLoewnerLe_smul_id`,
  `finiteTrace_finiteMatrixExp_le_card_mul_exp_of_finiteLoewnerLe_smul_id`,
  and
  `finiteTrace_finiteMatrixExp_neg_le_card_mul_exp_of_neg_finiteLoewnerLe_smul_id`.
  These turn a future scalar-identity Loewner matrix-CGF estimate into
  `tr(exp(M)) <= d exp(c)` and `tr(exp(-M)) <= d exp(c)`.  They still do not
  prove Golden-Thompson/Lieb trace domination or matrix Bernstein.

- 2026-05-26 continued the Algorithm 1 equation (2) concentration queue by
  adding the product-law expectation bridge.  `HitCountConcentration.lean` now
  has `sqMagTraceProbability_expectationReal_step_eq`, a generic adapter from
  one-step `sqMagProb` sums to expectations of a fixed coordinate in the
  independent trace law.  `ElementwiseSpectral.lean` uses it to prove
  trace-law zero mean for one-step dilation increments and the full dilation
  residual, plus product-law expected quadratic-form, Loewner, and PSD variance
  bounds:
  `sqMagTraceProbability_expectationReal_rectSelfAdjointDilation_elementwiseTraceResidual_eq_zero`,
  `sqMagTraceProbability_expectationReal_sum_finiteQuadraticForm_rectSelfAdjointDilation_sampleResidualIncrement_square_le`,
  `sqMagTraceProbability_sum_expectationReal_rectSelfAdjointDilation_square_loewnerLe_scalar_id`,
  and
  `sqMagTraceProbability_sum_expectationReal_rectSelfAdjointDilation_square_psd`.
  These close the expectation/variance packaging gap but not the
  trace-exponential/largest-eigenvalue Bernstein tail.
- 2026-05-26 also added
  `FiniteProbability.eventProb_inter_eq_one_of_eq_one` and the truncated
  simultaneous Bernstein side-condition package
  `truncatedDilationBernsteinBoundedEvent` with probability-one theorem
  `sqMagTraceProbability_eventProb_truncatedDilationBernsteinBoundedEvent_eq_one`.
  This now combines the bounded-dilation, two-sided Loewner, and bounded-square
  events; it remains prerequisite infrastructure only.

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

## 2026-05-26 RandNLA Full-Paper Continuation Note

- Continued the Algorithm 1 equation (2) concentration queue by adding generic
  product-law scalar MGF infrastructure in
  `HitCountConcentration.lean`: `exp_sum_stepFunction_eq_prod`,
  `sqMagTraceProbMass_exp_sum_stepFunction_eq`,
  `sqMagTraceProbability_expectationReal_exp_sum_stepFunction_eq`,
  `sqMagTraceProbability_eventProb_sum_stepFunction_ge_le_exp_mul_mgf`, and
  `sqMagTraceProbability_eventProb_sum_stepFunction_le_ge_one_sub_exp_mul_mgf`,
  plus the one-step-MGF-bound variants
  `sqMagTraceProbability_eventProb_sum_stepFunction_ge_le_exp_of_one_step_mgf_bound`
  and
  `sqMagTraceProbability_eventProb_sum_stepFunction_le_ge_one_sub_exp_of_one_step_mgf_bound`.
- These theorems factor the MGF of `sum_t f(X_t)` under the independent
  squared-magnitude trace law and provide scalar exponential-Markov tails.
  They are support infrastructure only: they do not prove trace-exponential
  domination, largest-eigenvalue tails, matrix Bernstein/Khintchine, or CACM
  equation (2).
- The same continuation added finite-family scalar MGF support and specialized
  it to self-adjoint-dilation quadratic forms:
  `sqMagTraceProbability_eventProb_forall_sum_stepFunction_le_ge_one_sub_sum_exp_of_one_step_mgf_bound`,
  `finiteQuadraticForm_rectSelfAdjointDilation_elementwiseTraceResidual_eq_sum_sampleResidualIncrement`,
  and
  `sqMagTraceProbability_eventProb_forall_finiteQuadraticForm_rectSelfAdjointDilation_elementwiseTraceResidual_le_ge_one_sub_sum_exp_of_one_step_mgf_bound`.
  These are finite-test support theorems only and still leave matrix
  Bernstein/equation (2) open.
- Added pointwise-bound variants
  `sqMagProb_sum_exp_stepFunction_le_exp_of_forall_le`,
  `sqMagTraceProbability_eventProb_forall_sum_stepFunction_le_ge_one_sub_sum_exp_of_pointwise_bound`,
  and
  `sqMagTraceProbability_eventProb_forall_finiteQuadraticForm_rectSelfAdjointDilation_elementwiseTraceResidual_le_ge_one_sub_sum_exp_of_pointwise_bound`.
  These remove explicit one-step MGF hypotheses when a pointwise statistic
  bound is available, but they are still weak finite-test support and not
  matrix Bernstein.
- Added support-aware pointwise variants
  `sqMagProb_sum_exp_stepFunction_le_exp_of_support_forall_le`,
  `sqMagTraceProbability_eventProb_forall_sum_stepFunction_le_ge_one_sub_sum_exp_of_support_pointwise_bound`,
  and
  `sqMagTraceProbability_eventProb_forall_finiteQuadraticForm_rectSelfAdjointDilation_elementwiseTraceResidual_le_ge_one_sub_sum_exp_of_support_pointwise_bound`.
  These only require the one-step pointwise bound on positive-probability
  samples, which avoids hidden retained-entry hypotheses for truncated
  sampling laws.
- Added matrix-algebra adapters
  `abs_finiteQuadraticForm_le_of_finiteOpNorm2Le` and
  `finiteQuadraticForm_le_of_finiteOpNorm2Le`, exposing the existing
  operator-to-inner-product control directly in `finiteQuadraticForm`
  notation for future pointwise MGF bounds.
- Specialized the support-aware MGF support to the Drineas--Zouzias truncated
  Algorithm 1 route with
  `finiteQuadraticForm_rectSelfAdjointDilation_elementwiseSampleResidualIncrement_truncated_le`
  and
  `sqMagTraceProbability_eventProb_forall_finiteQuadraticForm_rectSelfAdjointDilation_truncatedTraceResidual_le_ge_one_sub_sum_exp_of_support_bound`.
  This closes the zero-mass support bookkeeping for finite test vectors, but
  still does not prove trace-exponential/largest-eigenvalue or matrix
  Bernstein concentration.
- Added a one-sided self-adjoint-dilation Loewner adapter:
  `rectOpNorm2Le_of_selfAdjointDilation_loewnerLe_scalar_id`,
  `algorithm1ExactDilationUpperEvent_subset_exactSpectralEvent`,
  `probability_algorithm1_exact_spectral_of_dilation_upper`, and
  `probability_algorithm1_fl_spectral_of_exact_dilation_upper`.
  This lets a future largest-eigenvalue theorem proving `D(R) <= eps I`
  transfer to exact/FP rectangular residual events, but it is still only a
  deterministic/probability bridge and does not prove equation (2).
- Added a named eigenvalue form of that dilation upper event:
  `finiteScalarUpperDiffEigenvalues`,
  `finiteLoewnerLe_smul_id_iff_finiteScalarUpperDiffEigenvalues_nonneg`,
  `algorithm1ExactDilationEigenUpperEvent`,
  `algorithm1ExactDilationEigenUpperEvent_subset_exactDilationUpperEvent`,
  `algorithm1ExactDilationEigenUpperEvent_subset_exactSpectralEvent`,
  `probability_algorithm1_exact_spectral_of_dilation_eigen_upper`, and
  `probability_algorithm1_fl_spectral_of_exact_dilation_eigen_upper`.
  This exposes the future largest-eigenvalue tail target as nonnegativity of
  all eigenvalues of `eps I - D(R)`, but still does not prove that event with
  high probability.
- Added a finite union-bound adapter for supplied scalar eigenvalue events:
  `algorithm1ExactDilationEigenUpperIndexEvent`,
  `probability_algorithm1_exact_dilation_eigen_upper_of_index_bounds`,
  `probability_algorithm1_exact_spectral_of_dilation_eigen_upper_index_bounds`,
  and
  `probability_algorithm1_fl_spectral_of_exact_dilation_eigen_upper_index_bounds`.
  This is only a probability combiner for per-eigenvalue bounds; it still does
  not prove those bounds or a trace-exponential/largest-eigenvalue theorem.
- Added the matrix-exponential scalar-normalization bridge in
  `LeanFpAnalysis/FP/Analysis/MatrixSpectral.lean`:
  `finiteMatrixExp`, `finiteMatrixExp_smul_finiteIdMatrix`, and
  `finiteTrace_finiteMatrixExp_smul_finiteIdMatrix`, plus symmetry
  preservation `finiteMatrixExp_symmetric`. `MatrixAlgebra.lean` now has
  `finiteDiagonal`, and `MatrixSpectral.lean` proves
  `finiteMatrixExp_finiteDiagonal` and
  `finiteTrace_finiteMatrixExp_finiteDiagonal`.
  These provide the `tr(exp(L I)) = d exp(L)` and diagonal trace-exponential
  normalizations needed by a future trace-MGF proof, but they do not prove
  trace-exponential domination, matrix Bernstein/Khintchine, or CACM
  equation (2).
- Added the Hermitian spectral-calculus trace bridge in
  `LeanFpAnalysis/FP/Analysis/MatrixSpectral.lean`: `finiteHermitianCfcExp`
  and `finiteTrace_finiteHermitianCfcExp_eq_sum_exp_finiteHermitianEigenvalues`.
  This proves `tr(E_cfc(M)) = sum_i exp(lambda_i(M))` for local finite real
  symmetric matrices. The same file now also proves
  `finiteTrace_finiteMatrixExp_eq_sum_exp_finiteHermitianEigenvalues`, the
  repository-native power-series matrix-exponential trace identity
  `tr(exp(M)) = sum_i exp(lambda_i(M))` for local finite real symmetric
  matrices. This closes the trace-diagonalization dependency, but
  trace-exponential domination, largest-eigenvalue tails,
  matrix Bernstein/Khintchine, and CACM equation (2) remain open.
- Added `LeanFpAnalysis/FP/Analysis/MatrixConcentration.lean` with
  `exp_le_finiteTrace_finiteMatrixExp_of_finiteHermitianEigenvalue_ge`,
  `finiteTrace_finiteMatrixExp_nonneg`, and
  `FiniteProbability.eventProb_exists_finiteHermitianEigenvalue_ge_le_exp_neg_mul_expected_trace_exp`.
  This closes the MGF-to-eigenvalue Markov interface for a supplied random
  symmetric matrix family. It still requires a trace-MGF domination theorem for
  independent self-adjoint sums before matrix Bernstein/Khintchine or CACM
  equation (2) can close.
- Extended `MatrixConcentration.lean` with scalar-bound and high-probability
  complement forms:
  `FiniteProbability.eventProb_exists_finiteHermitianEigenvalue_ge_le_exp_neg_mul_trace_bound`,
  `FiniteProbability.eventProb_forall_finiteHermitianEigenvalue_lt_ge_one_sub_exp_neg_mul_expected_trace_exp`,
  and
  `FiniteProbability.eventProb_forall_finiteHermitianEigenvalue_lt_ge_one_sub_exp_neg_mul_trace_bound`.
  These make a future trace-MGF bound immediately usable as an eigenvalue
  tail or all-eigenvalues-below-threshold probability statement, but they still
  do not prove trace-MGF domination, matrix Bernstein/Khintchine, or CACM
  equation (2).
- Added the lower-tail companion for the trace-exponential/eigenvalue layer:
  `finiteTrace_finiteMatrixExp_neg_eq_sum_exp_neg_finiteHermitianEigenvalues`,
  `exp_neg_le_finiteTrace_finiteMatrixExp_neg_of_finiteHermitianEigenvalue_le`,
  `finiteTrace_finiteMatrixExp_neg_nonneg`,
  `FiniteProbability.eventProb_exists_finiteHermitianEigenvalue_le_le_exp_mul_expected_trace_exp_neg`,
  `FiniteProbability.eventProb_exists_finiteHermitianEigenvalue_le_le_exp_mul_trace_bound`,
  `FiniteProbability.eventProb_forall_finiteHermitianEigenvalue_gt_ge_one_sub_exp_mul_expected_trace_exp_neg`,
  and
  `FiniteProbability.eventProb_forall_finiteHermitianEigenvalue_gt_ge_one_sub_exp_mul_trace_bound`.
  These close the negative one-sided Markov interface for future two-sided
  self-adjoint concentration, but still leave trace-MGF domination,
  matrix Bernstein/Khintchine, and CACM equation (2) open.
- Added the two-sided trace-exponential/eigenvalue combiner
  `FiniteProbability.eventProb_forall_abs_finiteHermitianEigenvalue_lt_ge_one_sub_exp_neg_mul_expected_trace_exp_add`
  and
  `FiniteProbability.eventProb_forall_abs_finiteHermitianEigenvalue_lt_ge_one_sub_exp_neg_mul_trace_bound_add`.
  These combine positive and negative trace-MGF controls into an
  all-absolute-eigenvalues-below-threshold event, using existing finite
  probability intersection infrastructure. They still do not prove the
  trace-MGF controls themselves, matrix Bernstein/Khintchine, or CACM
  equation (2).
- Added the weak accumulated bounded-increment theorem for the truncated
  Algorithm 1 route:
  `truncatedDilationIncrementLoewnerBoundedEvent_subset_exactDilationUpperEvent_sum_bound`,
  `sqMagTraceProbability_eventProb_algorithm1ExactDilationUpperEvent_truncated_sum_bound_eq_one`,
  and
  `sqMagTraceProbability_eventProb_algorithm1ExactSpectralEvent_truncated_sum_bound_eq_one`.
  This proves the probability-one two-sided Loewner bounded-increment event
  composes to a probability-one exact truncated spectral event at scale `sL`.
  It is an audit/side-condition theorem only: it ignores zero mean and
  variance, so it does not prove the CACM equation (2) Bernstein rate.
- Added `Analysis/OperatorLog.lean` with `cstarMatrix_log_le_log`, a local
  wrapper around mathlib operator-log monotonicity for complex `CStarMatrix`.
  This closes one Tropp/Lieb functional-calculus prerequisite for the
  trace-MGF route, but it does not bridge finite real self-adjoint matrices to
  complex C-star matrix order and does not prove trace-MGF domination.
- Added `Analysis/CStarMatrixBridge.lean` with `finiteComplexCStarMatrix` and
  preservation lemmas for entries, subtraction, the finite identity, scalar
  identities, self-adjointness of symmetric finite real matrices, local PSD,
  and local finite Loewner inequalities into complex C-star spectral order.
  It now also proves strict positivity after positive scalar identity
  regularization and preservation of Loewner inequalities under the same
  regularization. `OperatorLog.lean` composes these with
  `cstarMatrix_log_le_log` as
  `finiteComplexCStarMatrix_regularized_log_le_log_of_finiteLoewnerLe`.
  This closes the algebraic/order/strict-positive-regularization part of the
  finite-real-to-complex-C-star bridge; Lieb/Tropp trace-MGF domination remains
  open.
- Added `Analysis/CStarMatrixTrace.lean` with `cstarMatrixTrace`, elementary
  additivity/scaling/subtraction/identity rules, cyclicity
  `cstarMatrixTrace_mul_comm`, real-part trace positivity/monotonicity for the
  C-star spectral order via `cstarMatrixTrace_re_nonneg_of_nonneg` and
  `cstarMatrixTrace_re_mono`, agreement with repository-native `finiteTrace`
  after embedding finite real matrices, and embedded real PSD/Loewner trace
  transfer lemmas.  It also proves scalar CFC-exponential trace
  normalization for complex and real scalar identities via
  `cstarMatrixTrace_cfc_exp_algebraMap` and
  `cstarMatrixTrace_cfc_exp_real_smul_one`.  This closes trace vocabulary for
  the Tropp/Lieb route, but it does not prove Lieb trace concavity, trace-MGF
  domination, matrix Bernstein/Khintchine, or CACM equation (2).
- Added `Analysis/CStarMatrixExpectation.lean` with
  `FiniteProbability.expectationComplex`,
  `FiniteProbability.expectationCStarMatrix`, complex linearity lemmas,
  `FiniteProbability.cstarMatrixTrace_expectationCStarMatrix`, and
  `FiniteProbability.expectationCStarMatrix_finiteComplexCStarMatrix`.  It
  now also proves `FiniteProbability.expectationCStarMatrix_eq_sum_smul`,
  `FiniteProbability.expectationCStarMatrix_eq_sum_real_smul`,
  `FiniteProbability.expectationComplex_re`,
  `FiniteProbability.expectationCStarMatrix_nonneg`,
  `FiniteProbability.expectationCStarMatrix_mono`, and
  `FiniteProbability.expectationCStarMatrix_add_pos_smul_one_isStrictlyPositive`.
  Together with the finite probability Jensen wrapper
  `FiniteProbability.expectationReal_le_of_concaveOn` and its C-star
  specialization
  `FiniteProbability.expectationReal_le_of_concaveOn_expectationCStarMatrix`,
  plus the conditional trace-exponential shape
  `FiniteProbability.expectationReal_trace_cfc_exp_add_log_le_of_concaveOn`,
  this closes the finite Jensen/expectation adapter needed after a future proof
  of Lieb trace concavity. The concavity hypothesis remains explicit and
  unproved locally. It is not trace-MGF domination, matrix Bernstein/Khintchine,
  or CACM equation (2).
  A follow-up locality pass confirmed that mathlib currently has
  `CFC.log_monotoneOn`, but `ExpLog.Order` still lists operator-log concavity
  as TODO and `Rpow.Order` lists operator concavity of `rpow` as TODO. The next
  proof frontier is therefore a genuine Lieb trace-concavity theorem or a
  deliberate route switch, not another local wrapper.
- Continued the Algorithm 1 equation (2) bottleneck by closing a covering-route
  dependency in `MatrixAlgebra.lean`: `abs_coord_le_vecNorm2`,
  `realUnitIntervalCover`, `rectUnitBallCover_product_grid`, and
  `fintype_card_product_grid_index`.  A one-dimensional interval grid for
  `[-1,1]` now induces an `n`-dimensional Euclidean unit-ball cover with radius
  loss `sqrt n`, and the product index type has cardinality `|grid|^n`.  This
  is deterministic cover geometry only; it does not prove sharp finite-net
  tails, matrix Bernstein/Khintchine, Lieb trace-MGF domination, or CACM
  equation (2).
- Updated the formalization automation workflow and the installed
  `lean-stability-formalizer` skill so incomplete paper proofs trigger a
  front-loaded proof-source acquisition phase before hard Lean proof work.
  Future runs must classify source proofs, search primary literature and
  citation chains, create a proof-source ledger with exact theorem/page/equation
  references and Lean targets, choose a route, and only then formalize. The
  exported Vershynin chapter skill was updated the same way and its archive was
  regenerated.
- Started the updated proof-source workflow for the CACM RandNLA paper by
  adding `docs/RANDNLA_CACM_PROOF_SOURCE_LEDGER.md`. The active Algorithm 1
  equation (2) bottleneck is now explicitly sourced through CACM ->
  Drineas--Zouzias Algorithm 1/Theorem 1/Lemmas 1--4 -> matrix-valued
  Bernstein -> Tropp Lieb/trace-MGF/matrix-Bernstein. Other open paper-level
  rows now have source queues before new infrastructure should be added.
- Added `LeanFpAnalysis/FP/Analysis/LiebTrace.lean` for the Algorithm 1
  equation (2) Tropp/Lieb route. It defines the strictly-positive complex
  `CStarMatrix` cone, proves positive/nonnegative real-scalar preservation and
  `strictPositiveCStarMatrixCone_convex`, and names `liebTraceFunctional` plus
  `liebTraceConcavityTarget`. This closes the domain-convexity/target-vocabulary
  dependency only; Lieb trace concavity, trace-MGF domination, matrix
  Bernstein/Khintchine, and CACM equation (2) remain open.
- Continued the active A1.5-B1 red-bottleneck pass by closing the local
  trace-exponential real-valuedness/positivity bridge: `cstarMatrixTrace_im_eq_zero_of_isSelfAdjoint`,
  `liebTraceCfcExp_nonneg`, `liebTraceFunctional_trace_im_eq_zero`, and
  `liebTraceFunctional_nonneg`. These are listed dependencies for the
  Tropp/Lieb route. They do not prove finite-dimensional Lieb concavity,
  trace-MGF domination, matrix Bernstein/Khintchine, or CACM equation (2).
- Tightened the automation workflow and installed `lean-stability-formalizer`
  skill after the Algorithm 1 equation (2) bottleneck exposed a process failure.
  Future runs must run a foundation feasibility gate before downstream theorem
  work. If a paper-level theorem depends on an unproved foundation, that
  foundation becomes the active Lean target. If the same row survives two
  focused passes with the same missing foundation, it becomes a red bottleneck:
  downstream adapters, transfer corollaries, PDF polish, and lookup prose no
  longer count as progress unless they close a listed dependency, rule out a
  listed route, or correct the theorem statement. The repository prompt playbook
  and exported Vershynin chapter skill now include this rule.
- Continued the active A1.5-B1 red-bottleneck pass by closing the
  log-exponential analytic bridge in `OperatorLog.lean`:
  `cstarMatrix_normedSpaceExp_isTopologicalRing`,
  `cstarMatrix_normedRingExp_isTopologicalRing`,
  `cstarMatrix_realContinuousFunctionalCalculus`,
  `cstarMatrix_log_normedSpace_exp_of_isSelfAdjoint`,
  `cstarMatrix_log_cfc_complex_exp_of_isSelfAdjoint`, and
  `cstarMatrix_log_cfc_real_exp_of_isSelfAdjoint`. These are deterministic
  C-star functional-calculus dependencies for the Tropp/Lieb route. They do not
  prove finite-dimensional Lieb concavity, trace-MGF domination, matrix
  Bernstein/Khintchine, or CACM equation (2).
- Continued the active A1.5-B1 red-bottleneck pass by closing the matching
  strictly-positive exponential-logarithm analytic bridge in `OperatorLog.lean`:
  `cstarMatrix_normedRingExp_nonnegSpectrumClass`,
  `cstarMatrix_normedSpace_exp_log_of_isStrictlyPositive`,
  `cstarMatrix_cfc_complex_exp_log_of_isStrictlyPositive`, and
  `cstarMatrix_cfc_real_exp_log_of_isStrictlyPositive`. These are
  deterministic C-star functional-calculus inverse dependencies for the
  Tropp/Lieb route. They do not prove finite-dimensional Lieb concavity,
  trace-MGF domination, matrix Bernstein/Khintchine, or CACM equation (2).
- Continued the active A1.5-B1 red-bottleneck pass by closing the local
  Lieb-functional normalization bridge in `LiebTrace.lean`:
  `liebTraceFunctional_eq_normedSpace_exp` identifies the CFC form of the local
  Lieb functional with the standard normed-algebra exponential
  `Re tr(exp(H + log A))`, and `liebTraceFunctional_zero_eq_trace` normalizes
  the `H = 0` case to `Re tr(A)` on the strictly positive cone. These are
  deterministic C-star functional-calculus/trace dependencies only. They do
  not prove finite-dimensional Lieb concavity, trace-MGF domination, matrix
  Bernstein/Khintchine, or CACM equation (2).
- Closed one sanity-check subcase of the Lieb target with
  `liebTraceConcavityTarget_zero`: for `H = 0`, the local Lieb functional is
  affine on the strictly positive cone, hence concave. This reduces the red
  bottleneck but does not prove the arbitrary self-adjoint-`H` Lieb theorem,
  trace-MGF domination, matrix Bernstein/Khintchine, or CACM equation (2).
- Continued the A1.5-B1 red-bottleneck pass by closing a finite-support
  strict-positivity domain dependency:
  `FiniteProbability.exists_prob_pos` and
  `FiniteProbability.expectationCStarMatrix_isStrictlyPositive`. This shows
  that finite C-star expectations preserve strict positivity when every sampled
  matrix is strictly positive, which is needed before future `log(E[exp X])`
  statements. It does not by itself prove strict positivity of matrix
  exponentials; that separate domain bridge is closed in the next bullet. It
  does not prove Lieb trace concavity, trace-MGF domination, matrix
  Bernstein/Khintchine, or CACM equation (2).
- Continued the A1.5-B1 red-bottleneck pass by closing the self-adjoint
  matrix-exponential strict-positivity bridge:
  `cstarMatrix_normedSpace_exp_isStrictlyPositive_of_isSelfAdjoint`,
  `cstarMatrix_cfc_complex_exp_isStrictlyPositive_of_isSelfAdjoint`,
  `cstarMatrix_cfc_real_exp_isStrictlyPositive_of_isSelfAdjoint`, and
  `liebTraceCfcExp_isStrictlyPositive`. This combines self-adjoint exponential
  nonnegativity with invertibility of the normed-algebra exponential and
  transfers the result to the CFC exponentials. It does not prove arbitrary
  self-adjoint-`H` Lieb concavity, trace-MGF domination, matrix
  Bernstein/Khintchine, or CACM equation (2).
- Continued the A1.5-B1 red-bottleneck pass by closing the conditional
  one-step Tropp/Jensen trace-MGF adapter:
  `FiniteProbability.expectationReal_trace_normed_exp_add_le_of_liebTraceConcavityTarget`.
  It proves `E Re tr exp(H + X) <= Re tr exp(H + log(E exp X))` for finite
  self-adjoint C-star matrix random variables from the explicit hypothesis
  `liebTraceConcavityTarget H`, using the local finite Jensen adapter plus
  `log(exp X)=X` and CFC-to-normed-exponential normalization. It does not prove
  arbitrary self-adjoint-`H` Lieb concavity, nonconditional trace-MGF
  domination, matrix Bernstein/Khintchine, or CACM equation (2).
- Continued the A1.5-B1 red-bottleneck pass by closing the first
  relative-entropy route dependency for the chosen Tropp monograph path:
  `cstarMatrixRelativeEntropy` and `cstarMatrixRelativeEntropy_self`.
  This names the finite complex C-star relative-entropy expression and proves
  the diagonal normalization `D(A;A)=0`. It does not prove matrix
  relative-entropy nonnegativity, joint convexity, the variational principle,
  arbitrary self-adjoint-`H` Lieb concavity, trace-MGF domination, matrix
  Bernstein/Khintchine, or CACM equation (2).
- Continued the A1.5-B1 red-bottleneck pass by closing the commutative
  relative-entropy nonnegativity dependency:
  `realRelativeEntropy_nonneg` proves
  `a * (log a - log b) - (a - b) >= 0` for positive real scalars, and
  `finiteRealRelativeEntropy_nonneg` sums it over coordinatewise-positive
  finite vectors. This does not prove matrix relative-entropy nonnegativity,
  joint convexity, the variational principle, arbitrary self-adjoint-`H` Lieb
  concavity, trace-MGF domination, matrix Bernstein/Khintchine, or CACM
  equation (2).
- Continued the A1.5-B1 red-bottleneck pass by closing the real
  scalar-identity matrix relative-entropy case:
  `cstarMatrixRelativeEntropy_algebraMap_real` proves
  `D(aI;bI) = dim * d(a;b)`, and
  `cstarMatrixRelativeEntropy_algebraMap_real_nonneg` proves nonnegativity for
  positive real scalars. This is a C-star matrix vocabulary sanity theorem
  only; it does not prove general matrix relative-entropy nonnegativity, joint
  convexity, the variational principle, arbitrary self-adjoint-`H` Lieb
  concavity, trace-MGF domination, matrix Bernstein/Khintchine, or CACM
  equation (2).
- A 2026-05-27 route-elimination pass for A1.5-B1 searched the repository,
  lookup files, and mathlib for Klein inequality, quantum/matrix
  relative-entropy joint convexity, arbitrary-`H` Lieb trace concavity, and
  matrix Bernstein. No reusable local theorem was found. Mathlib has scalar
  `convexOn_mul_log`, but its CFC order files still list operator-log
  concavity and operator convexity of `x * log x` as TODOs.
- Continued the A1.5-B1 red-bottleneck pass by closing the real diagonal
  matrix relative-entropy case:
  `cstarMatrixDiagonalStarAlgHom`,
  `cstarMatrixDiagonalStarAlgHom_continuous`, `cstarMatrixRealDiagonal`,
  `cstarMatrixTrace_realDiagonal`, `cstarMatrix_log_realDiagonal`,
  `cstarMatrixRelativeEntropy_realDiagonal`, and
  `cstarMatrixRelativeEntropy_realDiagonal_nonneg`. This proves that the
  diagonal C-star embedding is continuous, that nonzero real diagonal matrices
  have coordinatewise operator logarithms, and that C-star matrix relative
  entropy on real diagonal matrices reduces to finite-vector relative entropy.
  It does not prove general noncommutative matrix relative-entropy
  nonnegativity, joint convexity, the variational principle, arbitrary
  self-adjoint-`H` Lieb concavity, trace-MGF domination, matrix
  Bernstein/Khintchine, or CACM equation (2).
- Continued the A1.5-B1 red-bottleneck pass by closing the conditional
  Tropp relative-entropy route reduction:
  `cstarMatrixEntropyVariationalObjective`,
  `cstarMatrixRelativeEntropyJointConvexOnStrictPositive`,
  `cstarMatrixEntropyVariationalFormula`, and
  `liebTraceConcavityTarget_of_relativeEntropy_route`. A follow-up statement
  correction fixed the variational objective to include the `Re tr A` constant
  required by the local normalization
  `D(X;A)=Re tr(X(log X-log A)-(X-A))`. The same pass closed
  `cstarMatrixEntropyVariationalObjective_liebOptimizer`, the equality
  \(\Psi_H(\exp(H+\log A),A)=\Phi_H(A)\) for the normalized objective, and
  `cstarMatrixEntropyVariationalFormula_of_relativeEntropy_nonneg`, which
  reduces the normalized variational formula to
  `cstarMatrixRelativeEntropyNonnegOnStrictPositive`. This proves that joint
  convexity of local C-star matrix relative entropy on the strictly positive
  cone plus the normalized entropy variational formula imply the local Lieb
  trace-concavity target. It does not prove noncommutative relative-entropy
  nonnegativity or joint convexity, nonconditional trace-MGF domination, matrix
  Bernstein/Khintchine, or CACM equation (2); those are the next named
  foundations for this route.
- Continued the A1.5-B1 red-bottleneck pass by splitting the nonnegativity
  foundation further using the proof-source chain from Tropp's matrix
  concentration notes and 2012 relative-entropy/Lieb note.
  `cstarMatrixEntropyTraceFirstOrderConvexityOnStrictPositive` now names the
  generalized Klein first-order trace inequality for
  `Phi(X)=Re tr(X log X - X)`, and
  `cstarMatrixRelativeEntropyNonnegOnStrictPositive_of_entropyTraceFirstOrder`
  proves that this first-order trace inequality implies local C-star matrix
  relative-entropy nonnegativity. This is a source-aligned conditional
  reduction only: the generalized Klein first-order trace inequality and
  matrix relative-entropy joint convexity remain open, followed by
  nonconditional trace-MGF domination, matrix Bernstein/Khintchine, and CACM
  equation (2).
- Continued the same bottleneck with two source-aligned dependencies from
  Tropp Proposition 8.3.5. First,
  `cstarMatrixEntropyTraceFirstOrderConvexityOnStrictPositive_of_relativeEntropy_nonneg`
  and
  `cstarMatrixEntropyTraceFirstOrderConvexityOnStrictPositive_iff_relativeEntropy_nonneg`
  show that local generalized Klein first-order convexity and local
  relative-entropy nonnegativity are equivalent in the repository
  normalization. Second, the Hermitian spectral-overlap route is now local:
  `matrixTrace_diagonal_mul_mul_diagonal_mul_star`,
  `matrixTrace_sum_diagonal_mul_mul_diagonal_mul_star_re`,
  `matrixTrace_sum_hermitianCfc_mul_cfc_re`,
  `matrixTrace_sum_hermitianCfc_mul_cfc_nonneg_of_kernel_nonneg`,
  `matrixTrace_sum_hermitianCfc_mul_cfc_nonneg_of_eigen_kernel_nonneg`,
  `matrixTrace_hermitianCfc_firstOrderKernel_sum_nonneg`,
  `matrixTrace_hermitianCfc_firstOrderKernel_sum_nonneg_of_eigen`,
  `realEntropy_firstOrderKernel_nonneg`, and
  `matrixTrace_hermitianCfc_entropy_firstOrder_sum_nonneg` close the
  squared-overlap algebra and the positive-spectrum scalar entropy
  first-order specialization. The compact complex `CStarMatrix` logarithm
  bridge, relative-entropy joint convexity, Lieb concavity, trace-MGF
  domination, matrix Bernstein/Khintchine, and CACM equation (2) remain open.
- Continued A1.5-B1 by closing the compact Hermitian/C-star generalized Klein
  bridge. `matrixTrace_hermitianCfc_entropy_firstOrder_compact_nonneg`,
  `cstarMatrix_nonneg_to_matrix_posSemidef`,
  `cstarMatrix_isStrictlyPositive_to_matrix_posDef`,
  `cstarMatrixEntropyTraceFirstOrderConvexityOnStrictPositive_of_hermitianCfc`,
  `cstarMatrixRelativeEntropyNonnegOnStrictPositive_of_hermitianCfc`,
  `cstarMatrixEntropyVariationalFormula_of_hermitianCfc`, and
  `liebTraceConcavityTarget_of_relativeEntropy_jointConvex` now close
  generalized Klein, local relative-entropy nonnegativity, the normalized
  variational formula, and the reduction from joint convexity alone to the
  local Lieb target. The current A1.5-B1 frontier is
  `cstarMatrixRelativeEntropyJointConvexOnStrictPositive`, followed by
  nonconditional trace-MGF domination, matrix Bernstein/Khintchine, and CACM
  equation (2).
- Front-loaded source search for the next A1.5-B1 frontier identified
  Effros 2009 (matrix perspectives of operator convex functions) and Lindblad
  1975 (relative-entropy convexity/monotonicity lineage) as advisory primary
  sources for `cstarMatrixRelativeEntropyJointConvexOnStrictPositive`, in
  addition to Tropp's monograph Sections 8.6--8.8 and Tropp's 2012 note. These
  sources are recorded in the proof-source/theorem ledgers and are not used as
  Lean hypotheses.
- Continued A1.5-B1 by closing the commutative joint-convexity layer on the
  same Tropp/Effros route. `finite_log_sum_inequality` is now proved from
  mathlib's scalar convexity of `x * log x`; it feeds
  `realRelativeEntropy_jointConvex_of_pos_weights`,
  `realRelativeEntropy_jointConvex`, and
  `finiteRealRelativeEntropy_jointConvex`. The diagonal C-star bridge
  `cstarMatrixRealDiagonal_smul_add`, `positive_weighted_sum_pos`, and
  `cstarMatrixRelativeEntropy_realDiagonal_jointConvex` close the real
  diagonal subalgebra case. This is a route dependency/sanity subcase only:
  the current A1.5-B1 frontier remains the noncommutative theorem
  `cstarMatrixRelativeEntropyJointConvexOnStrictPositive`, followed by
  trace-MGF domination, matrix Bernstein/Khintchine, and CACM equation (2).
- 2026-05-27: A1.5-B1 Effros/Tropp perspective substrate advanced again.
  `LiebTrace.lean` now defines `cstarMatrixLeftMul` and
  `cstarMatrixRightMul`, proves their real weighted-sum affine laws, proves
  `cstarMatrixLeftRightMul_commute`, and proves left/right multiplication is
  a unit when the underlying matrix is a unit or strictly positive. This
  closes the algebraic \(L_A\), \(R_A\) layer needed before constructing
  \(L_X R_A^{-1}\); it still does not prove operator convexity, the perspective
  theorem, `cstarMatrixRelativeEntropyJointConvexOnStrictPositive`, Lieb
  concavity, trace-MGF domination, matrix Bernstein/Khintchine, or equation
  (2).
- 2026-05-27: A1.5-B1 Effros/Tropp perspective substrate advanced one step
  further. `LiebTrace.lean` now defines `cstarMatrixLeftRightRatio` for
  \(L_XR_A^{-1}\), proves its action formula, and proves the base-point
  normalization \((L_XR_A^{-1})(A)=X\) for unit and strictly positive `A`.
  This closes the explicit ratio-endomorphism layer only; the open frontier
  remains the finite operator-perspective theorem or relative-entropy trace
  representation, then `cstarMatrixRelativeEntropyJointConvexOnStrictPositive`.
- 2026-05-27: A1.5-B1 Effros/Tropp perspective substrate added the
  product/power algebra for the left/right multiplication endomorphisms:
  `cstarMatrixLeftMul_mul`, `cstarMatrixRightMul_mul`,
  `cstarMatrixLeftMul_pow`, and `cstarMatrixRightMul_pow`. This supports the
  future functional-calculus/trace-representation step for \(L_XR_A^{-1}\);
  it still does not prove the Effros perspective theorem or joint convexity.
- 2026-05-27: A1.5-B1 Effros/Tropp perspective substrate added the finite
  Kronecker lift layer: `matrix_kronecker_left_identity_real_smul_add`,
  `matrix_kronecker_right_identity_real_smul_add`,
  `matrix_kronecker_left_identity_mul_right_identity`,
  `matrix_kronecker_right_identity_mul_left_identity`,
  `matrix_kronecker_left_right_commute`,
  `matrix_kronecker_posDef_left_identity`, and
  `matrix_kronecker_posDef_right_identity`. This closes the affine,
  commutation, product, and positive-definiteness facts for \(A\otimes I\)
  and \(I\otimes H\); it still does not prove operator convexity, the Effros
  perspective theorem, relative-entropy joint convexity, Lieb concavity, or
  equation (2).
- 2026-05-27: A1.5-B1 Effros/Tropp perspective substrate added the finite
  Kronecker trace layer: `matrix_trace_kronecker`,
  `matrix_trace_kronecker_left_identity`, and
  `matrix_trace_kronecker_right_identity`. This closes
  \(\operatorname{tr}(A\otimes H)=\operatorname{tr}(A)\operatorname{tr}(H)\)
  plus identity-lift trace normalizations for the future trace-representation
  proof; it still does not prove operator convexity, the Effros perspective
  theorem, the representation itself, relative-entropy joint convexity, Lieb
  concavity, or equation (2).
- 2026-05-27: A1.5-B1 Hansen-Pedersen/Effros source route now has explicit
  Lean target names: `cstarMatrixHansenPedersenJensenTwoPointTarget`,
  `cstarMatrixHansenPedersenJensenTwoPointTarget_id`, and
  `cstarMatrixXLogXHansenPedersenJensenTarget`. The identity-function Jensen
  sanity case is proved; the nonlinear \(x\log x\) operator-Jensen theorem,
  Effros perspective theorem, relative-entropy trace representation, and
  `cstarMatrixRelativeEntropyJointConvexOnStrictPositive` remain open.
- 2026-05-27: The Hansen-Pedersen/Effros source route is now split more
  faithfully: `cstarMatrixPositiveOperatorConvexTarget`,
  `cstarMatrixPositiveOperatorConvexTarget_id`,
  `cstarMatrixPositiveHansenPedersenTransferTarget`,
  `cstarMatrixXLogXPositiveOperatorConvexTarget`, and
  `cstarMatrixXLogXHansenPedersenTransferTarget` distinguish ordinary
  positive-cone operator convexity from Hansen-Pedersen transfer before the
  assembled `cstarMatrixXLogXHansenPedersenJensenTarget`. Only the
  identity-function ordinary-convexity sanity theorem was proved in that pass;
  the later 2026-05-28 direct-kernel route closes nonlinear \(x\log x\)
  operator convexity, while the transfer theorem remains open.
- 2026-05-27: A1.5-B1 now has the assembly adapter
  `cstarMatrixXLogXHansenPedersenJensenTarget_of_positiveOperatorConvex_of_transfer`.
  It proves that the concrete \(x\log x\) Hansen-Pedersen Jensen target follows
  once the concrete operator-convexity target and concrete transfer target are
  locally proved. This is dependency wiring only; it does not prove either
  nonlinear input.
- 2026-05-28: Since ordinary positive-cone operator convexity of \(x\log x\)
  is now closed locally, A1.5-B1 also has the transfer-only bridge
  `cstarMatrixXLogXHansenPedersenJensenTarget_of_transfer`. That pass left the
  fixed-size transfer target as the visible blocker; the later all-finite
  correction below refines this to
  `cstarMatrixXLogXHansenPedersenTransferAllFiniteTarget` or a finite
  Effros perspective route that bypasses it, followed by relative-entropy joint
  convexity, Lieb trace concavity, trace-MGF domination, matrix
  Bernstein/Khintchine, and CACM equation (2).
- 2026-05-28: Corrected the Hansen-Pedersen source target to expose the
  all-finite-size hypothesis required by the standard block-matrix proof:
  `cstarMatrixPositiveOperatorConvexAllFiniteTarget`,
  `cstarMatrixPositiveHansenPedersenTransferAllFiniteTarget`,
  `cstarMatrixXLogXPositiveOperatorConvexAllFiniteTarget`, and
  `cstarMatrixXLogXHansenPedersenTransferAllFiniteTarget`. Also proved
  `cstarMatrixXLogXPositiveOperatorConvexAllFiniteTarget_of_unit_interval_kernel`
  and the adapter
  `cstarMatrixXLogXHansenPedersenJensenTarget_of_allFiniteTransfer`. The active
  red bottleneck is now the all-finite transfer theorem or a finite Effros
  perspective route that bypasses it.
- 2026-05-27: A Bendat-Sherman-route subdependency for A1.5-B1 is now closed:
  `cstarMatrix_cfc_one_add_log_eq_one_add_log`,
  `cstarMatrixXLogXDerivativeMonotoneTarget`, and
  `cstarMatrixXLogXDerivativeMonotoneTarget_of_log_monotone` prove operator
  monotonicity of the formal derivative `1 + log x` on the strictly positive
  finite C-star-matrix cone by reusing local `cstarMatrix_log_le_log`. This
  does not prove the Bendat-Sherman bridge or
  `cstarMatrixXLogXPositiveOperatorConvexTarget`.
- 2026-05-27: The same Bendat-Sherman route now has the exact missing bridge
  named as `cstarMatrixBendatShermanDerivativeBridgeTarget`.  The adapter
  `cstarMatrixXLogXPositiveOperatorConvexTarget_of_bendatShermanDerivativeBridge`
  shows that this bridge, together with the closed derivative-monotonicity
  theorem, would close the concrete `x log x` operator-convexity target.  The
  bridge itself remains open.
- 2026-05-27: The Bendat-Sherman route was corrected to the source-faithful
  first-divided-difference formulation.  New local names are
  `realXLogXDividedDifference`,
  `cstarMatrixXLogXDividedDifferenceMonotoneTarget`,
  `cstarMatrixBendatShermanDividedDifferenceBridgeTarget`, and
  `cstarMatrixXLogXPositiveOperatorConvexTarget_of_bendatShermanDividedDifferenceBridge`.
  The derivative-monotonicity theorem remains a closed sanity subdependency,
  not the full Bendat-Sherman bridge.
- 2026-05-27: The divided-difference route now has scalar normalization lemmas:
  `realXLogXDividedDifference_self`,
  `realXLogXDividedDifference_eq_log_add_ratio`, and
  `realXLogXDividedDifference_eq_log_add_normalized`.  These identify the
  off-diagonal kernel as `log c + (x / c) * log (x / c) / (x / c - 1)`;
  proving operator monotonicity of that normalized logarithmic kernel remains
  the next real Bendat-Sherman-route dependency.
- 2026-05-28: The logarithmic-kernel route now has a finite C-star spectrum
  wrapper and the first unital inverse-kernel monotonicity dependency:
  `cstarMatrix_spectrum_nonneg_of_nonneg`,
  `cstarMatrix_cfc_one_sub_one_add_inv_monotone`, and
  `cstarMatrix_cfc_pos_over_one_add_monotone`.  These prove operator
  monotonicity of `x ↦ 1 - (1 + x)⁻¹` and `x ↦ x/(1+x)` on the nonnegative
  cone in the same unital CFC vocabulary as the Lieb route.  They do not yet
  prove the integral lift to `x log x/(x-1)`, full divided-difference
  monotonicity, Bendat-Sherman, Lieb, matrix Bernstein, or equation (2).
- 2026-05-27: Local/mathlib reuse for the next nonlinear Hansen-Pedersen target
  was ruled out with evidence. Mathlib currently has operator-log monotonicity
  but its CFC exp/log order file lists operator-log concavity and operator
  convexity of `x => x * log x` as TODOs. The next real proof target remains
  `cstarMatrixXLogXHansenPedersenJensenTarget`, unless the source route changes.
- 2026-05-28: The Bendat-Sherman logarithmic-kernel route now also has the
  scaled fractional-kernel theorem
  `cstarMatrix_cfc_pos_over_pos_add_monotone`: for every `s > 0`,
  `x => x / (s + x)` is operator-monotone on the nonnegative finite complex
  C-star cone. This closes the scaling dependency after the unital
  `x/(1+x)` theorem, but the integral lift to the normalized logarithmic
  kernel, full divided-difference monotonicity, and the Bendat-Sherman bridge
  remain open.
- 2026-05-28: The same route now has the finite nonnegative-combination
  closure `cstarMatrix_cfc_finset_sum_nonneg_mul_pos_over_pos_add_monotone`
  for finite sums of scaled kernels `x => x / (sigma + x)` with nonnegative
  weights and positive `sigma`. This is a finite-sum precursor only; the
  Bochner/Riemann integral lift to the normalized logarithmic kernel remains
  open.
- 2026-05-28: The Bendat-Sherman route now has the generic CFC Bochner-integral
  order theorem `cfc_integral_mono_of_forall_of_bound`: pointwise CFC Loewner
  inequalities integrate to Loewner inequalities for the integrated kernel
  under the joint-continuity and finite-integral-bound hypotheses of
  `cfc_integral`. The scalar/logarithmic integral identity and concrete
  continuity/boundedness side conditions were handled by later route rows; the
  scalar-integral-to-CFC equality remains open.
- 2026-05-28: The scalar/logarithmic identity side of that route is now partly
  closed: `realNormalizedLogKernel` names the diagonal-normalized kernel,
  `realXLogXDividedDifference_eq_log_add_normalizedKernel` rewrites the scalar
  divided difference as `log c + realNormalizedLogKernel (x / c)`, and
  `real_normalizedLogKernel_offdiag_intervalIntegral` proves
  `∫ u in 0..1, t / (u + (1 - u) * t) = t * log t / (t - 1)` for
  `t > 0`, `t != 1`. The continuity and boundedness side conditions are now
  closed separately; scalar-integral-to-CFC equality and full
  divided-difference monotonicity remain open.
- 2026-05-28: The same scalar-integral route now has the interior pointwise
  operator-monotonicity theorem
  `cstarMatrix_cfc_unit_interval_fractional_kernel_monotone` for
  `x => x / (u + (1 - u) * x)` when `0 < u < 1`, proved by reducing to the
  scaled `x/(s+x)` theorem with `s = u/(1-u)`. The endpoint-inclusive theorem
  `cstarMatrix_cfc_unit_interval_fractional_kernel_monotone_of_mem_Icc` now
  handles all `u ∈ [0,1]` on the strictly positive cone (`u=0` is constant
  one, `u=1` is identity). The concrete `cfc_integral` side-condition
  discharge and scalar-integral-to-CFC equality remain the next frontier.
- 2026-05-28: The route now also closes the explicit boundedness side
  conditions for the unit-interval integrand. The scalar theorem
  `real_unit_interval_fractional_kernel_abs_le_max_of_le` proves
  `|z / (u + (1 - u) * z)| <= max 1 M` for `u ∈ [0,1]` and `0 < z <= M`;
  `real_unit_interval_fractional_kernel_spectrum_norm_le_max` specializes this
  to strictly positive C-star spectra. The a.e./finite-integral adapters
  `ae_unit_interval_fractional_kernel_spectrum_norm_le_max`,
  `hasFiniteIntegral_const_max_one_spectrum_bound`,
  `continuousOn_uncurry_unit_interval_subtype_fractional_kernel_spectrum`,
  `ae_unit_interval_subtype_fractional_kernel_spectrum_norm_le_max`, and
  `hasFiniteIntegral_unit_interval_subtype_const_max_one_spectrum_bound` give
  the interval-subtype shape expected by the future `cfc_integral` assembly.
  The scalar-integral-to-CFC equality for `realNormalizedLogKernel` and full
  divided-difference monotonicity remain open.
- 2026-05-28: The normalized logarithmic-kernel route now closes the
  scalar-integral-to-CFC equality and the normalized-kernel CFC monotonicity
  theorem. New names are `realNormalizedLogKernel_setIntegral`,
  `cstarMatrix_cfc_realNormalizedLogKernel_eq_unit_interval_integral`,
  `cstarMatrix_setIntegral_mono_on`,
  `cstarMatrix_cfc_realNormalizedLogKernel_monotone_of_spectrum_bound`, and
  `cstarMatrix_cfc_realNormalizedLogKernel_monotone`. The remaining
  Bendat-Sherman-route gap is no longer the scalar-integral-to-CFC equality;
  it is lifting normalized-kernel monotonicity through the base-point
  scaling/constant-shift CFC normalization for each
  `realXLogXDividedDifference c`, followed by the finite
  Bendat-Sherman divided-difference bridge.
- 2026-05-28: The Bendat-Sherman divided-difference route now closes that
  base-point normalization and the full divided-difference monotonicity target.
  New names are `realNormalizedLogKernel_eq_mul_dslope_log`,
  `continuousOn_realNormalizedLogKernel_Ioi`,
  `cstarMatrix_cfc_realXLogXDividedDifference_eq_log_add_scaled_normalizedKernel`,
  and `cstarMatrixXLogXDividedDifferenceMonotoneTarget_of_normalizedLogKernel`.
  The remaining Bendat-Sherman-route gap is the finite bridge
  `cstarMatrixBendatShermanDividedDifferenceBridgeTarget`; A1.5-B1 still does
  not prove operator convexity, Lieb concavity, trace-MGF domination, matrix
  Bernstein/Khintchine, or CACM equation (2).
- 2026-05-28: A direct integral-route dependency is now closed in
  `LiebTrace.lean`: `matrix_posDef_inverse_schur_block`,
  `matrix_weighted_inverse_schur_block`, `matrix_posDef_weighted_sum`, and
  `matrix_inv_convex_posDef` prove finite complex matrix inverse convexity on
  the positive-definite cone by a Schur-complement/arithmetic-harmonic mean
  argument. This is useful substrate for shifted inverse kernels, but at this
  stage A1.5-B1 still lacked the C-star/CFC inverse-kernel bridge, the
  integral representation of `x log x`, operator convexity, Lieb trace-MGF domination,
  matrix Bernstein/Khintchine, and CACM equation (2).
- 2026-05-28: The direct inverse-convexity route now also has the finite
  C-star/CFC bridge: `cstarMatrix_nonneg_of_matrix_posSemidef` and
  `cstarMatrix_le_of_matrix_le` lift ordinary matrix PSD/Loewner facts back to
  C-star order, and `cstarMatrix_cfc_inv_convex_isStrictlyPositive` states the
  inverse-kernel convexity theorem in the real CFC vocabulary on the strictly
  positive cone. At this stage it still did not prove the shifted-positive inverse-kernel
  family, the `x log x` integral representation, Bendat-Sherman, Lieb
  concavity, matrix Bernstein, or CACM equation (2).
- 2026-05-28: The direct inverse-convexity route now also closes the shifted
  inverse-kernel family: `cstarMatrix_cfc_shifted_inv_eq_cfc_inv_add_smul_one`
  reduces `x ↦ (s + x)⁻¹` to ordinary inverse CFC after adding `sI`, and
  `cstarMatrix_cfc_shifted_inv_convex_nonneg` proves shifted inverse-kernel
  convexity on the nonnegative finite C-star cone for every `s > 0`. The next
  direct-route target is the scalar/operator integral representation turning
  these kernels into operator convexity of `x log x`; A1.5-B1 still does not
  prove Lieb concavity, matrix Bernstein, or CACM equation (2).
- 2026-05-28: The scalar normalization layer for the direct `x log x` route is
  now closed: `real_xlog_eq_sub_one_mul_realNormalizedLogKernel` proves
  `(x - 1) * realNormalizedLogKernel x = x * Real.log x`, and
  `real_xlog_eq_sub_one_mul_normalizedKernel_setIntegral` combines this with
  the existing unit-interval integral for the normalized kernel. This is still
  scalar only; the open direct-route target is the operator integral assembly
  turning the scalar representation plus shifted inverse-kernel convexity into
  operator convexity of `x ↦ x log x`.
- 2026-05-28: A further scalar direct-route dependency is closed:
  `real_unit_interval_xlog_integrand_eq_affine_add_shifted_inv` rewrites the
  unit-interval integrand `(x - 1)^2 / (u + (1 - u) * x)` for `x > 0` and
  `0 <= u < 1` as an affine term plus a positive multiple of the shifted
  inverse kernel `(x + u / (1 - u))⁻¹`. The remaining direct-route target is
  the C-star/CFC fixed-`u` operator decomposition and then the operator
  integral assembly.
- 2026-05-28: The direct `x log x` route was corrected and the ordinary
  positive-cone operator-convexity dependency is now closed. The auxiliary
  `(x - 1)^2 / (u + (1 - u) * x)` integrand is true but is not the scalar
  reconstruction kernel; the correct source-aligned kernel is
  `x * (x - 1) / (u + (1 - u) * x)`. New closed names include
  `real_xlog_eq_unit_interval_xlog_kernel_integral`,
  `real_unit_interval_xlog_kernel_integrand_eq_affine_add_shifted_inv`,
  `cstarMatrix_cfc_unit_interval_xlog_kernel_integrand_eq_affine_add_shifted_inv`,
  `continuousOn_uncurry_unit_interval_xlog_kernel_spectrum`,
  `real_unit_interval_xlog_kernel_spectrum_norm_le_max_sq`,
  `ae_unit_interval_xlog_kernel_spectrum_norm_le_max_sq`,
  `hasFiniteIntegral_const_max_one_spectrum_bound_sq`,
  `cstarMatrix_cfc_xlog_eq_unit_interval_xlog_kernel_integral`,
  `cstarMatrix_cfc_unit_interval_xlog_kernel_integrand_convex_of_pos_lt_one`,
  and `cstarMatrixXLogXPositiveOperatorConvexTarget_of_unit_interval_kernel`.
  A1.5-B1 still does not prove Hansen-Pedersen transfer, Effros perspective or
  relative-entropy joint convexity, Lieb trace concavity, trace-MGF domination,
  matrix Bernstein/Khintchine, or CACM equation (2).
- 2026-05-28: The Hansen-Pedersen red bottleneck gained a real block-algebra
  dependency closure in `CStarMatrixBridge.lean`.  New definitions/theorems
  `cstarMatrixBlockDiagonal`, `cstarMatrixColumnPair`,
  `cstarMatrixColumnPair_conjTranspose_mul_columnPair`,
  `cstarMatrixColumnPair_conjTranspose_mul_self`,
  `cstarMatrixBlockDiagonal_mul_columnPair`,
  `cstarMatrixColumnPair_conjTranspose_mul_blockDiagonal_mul_columnPair`, and
  `cstarMatrixColumnPair_conjTranspose_mul_self_eq_one_of_sum` formalize
  \(V=[A;B]\), \(D=\operatorname{diag}(T_1,T_2)\), \(V^*V=A^*A+B^*B\), and
  \(V^*DV=A^*T_1A+B^*T_2B\).  This closes the entrywise block-compression
  substrate for the standard proof; the active red bottleneck remains the
  nonlinear CFC/Jensen transfer theorem
  `cstarMatrixXLogXHansenPedersenTransferAllFiniteTarget` or a finite Effros
  perspective theorem.
- 2026-05-28: The same red bottleneck gained the next block-diagonal substrate
  closure.  `CStarMatrixBridge.lean` now proves that
  `cstarMatrixBlockDiagonal` preserves zero, one, addition, negation,
  subtraction, star, multiplication, units, nonnegativity, and strict
  positivity through theorems including `cstarMatrixBlockDiagonal_star`,
  `cstarMatrixBlockDiagonal_mul`, `cstarMatrixBlockDiagonal_isUnit`,
  `cstarMatrixBlockDiagonal_nonneg`, and
  `cstarMatrixBlockDiagonal_isStrictlyPositive`.  This closes the
  star-algebra/order bookkeeping for \(D=\operatorname{diag}(T_1,T_2)\); the
  active red bottleneck remains the nonlinear CFC/Jensen transfer theorem
  `cstarMatrixXLogXHansenPedersenTransferAllFiniteTarget` or a finite Effros
  perspective theorem.
- 2026-05-28: The Hansen-Pedersen route now also has the block-diagonal CFC
  decomposition.  `CStarMatrixBridge.lean` provides the continuous star-algebra
  homomorphism `cstarMatrixBlockDiagonalStarAlgHom_continuous`, and
  `LiebTrace.lean` proves `cstarMatrixBlockDiagonal_cfc`:
  \(f(\operatorname{diag}(T_1,T_2))=\operatorname{diag}(f(T_1),f(T_2))\) for
  self-adjoint blocks and \(f\) continuous on the union of spectra.  This closes
  another listed red-bottleneck dependency; the active blocker is now the
  block-isometry compression/Jensen inequality or an Effros perspective theorem,
  not block-diagonal CFC.
- 2026-05-28: The next Hansen-Pedersen block-isometry dependency is closed:
  `CStarMatrixBridge.lean` now has rectangular multiplication helpers
  `cstarMatrix_mul_assoc_rect`, `cstarMatrix_mul_one_rect`, and
  `cstarMatrix_one_mul_rect`, plus the range projection
  `cstarMatrixColumnPairRangeProjection`.  Under \(V^*V=I\), it proves
  \(P=VV^*\) is self-adjoint/idempotent and absorbs \(V\) and \(V^*\) via
  `cstarMatrixColumnPairRangeProjection_mul_self_of_sum`,
  `cstarMatrixColumnPairRangeProjection_mul_columnPair_of_sum`, and
  `cstarMatrixColumnPair_conjTranspose_mul_rangeProjection_of_sum`.  The
  associated reflection \(R=2P-I\) is also formalized via
  `cstarMatrixProjectionReflection` and `cstarMatrixColumnPairRangeReflection`;
  it is self-adjoint, squares to identity, is a unitary unit, and fixes \(V\) through
  `cstarMatrixColumnPairRangeReflection_mul_self_of_sum`,
  `cstarMatrixColumnPairRangeReflection_isUnit_of_sum`,
  `cstarMatrixColumnPairRangeReflection_mem_unitary_of_sum`, and
  `cstarMatrixColumnPairRangeReflection_mul_columnPair_of_sum`.  The active
  CFC-conjugation substrate is also closed by `cstarMatrix_cfc_unitary_conj`,
  proving \(f(UTU^*)=Uf(T)U^*\) for unitary \(U\).  The strict-positive domain
  side condition for the same conjugation/reflection route is closed by
  `cstarMatrix_unitary_conj_isStrictlyPositive` and
  `cstarMatrixColumnPairRangeReflection_conj_isStrictlyPositive_of_sum`.  The
  block-compression domain side condition is closed too:
  `cstarMatrixColumnPair_mulVec_injective_of_sum`,
  `cstarMatrixColumnPair_compress_blockDiagonal_isStrictlyPositive_of_sum`, and
  `cstarMatrixHansenPedersenCompression_isStrictlyPositive_of_sum` prove
  \(V^*\operatorname{diag}(T_1,T_2)V=A^*T_1A+B^*T_2B\) is strictly positive
  when \(V^*V=I\) and \(T_1,T_2\) are.  The algebraic pinching-average
  compression identity is also closed by
  `cstarMatrixColumnPair_conjTranspose_mul_rangeReflection_of_sum` and
  `cstarMatrixColumnPair_reflectionAverage_compression_of_sum`, proving
  \(V^*R=V^*\) and \(V^*((D+RDR)/2)V=V^*DV\) for \(R=2VV^*-I\).  It also proves
  `cstarMatrixColumnPair_reflectionAverage_conj_rangeReflection_of_sum` and
  `cstarMatrixColumnPair_reflectionAverage_commute_rangeReflection_of_sum`, so
  the averaged block is invariant under and commutes with the reflection; and
  `cstarMatrixColumnPair_reflectionAverage_commute_rangeProjection_of_sum`, so
  it commutes with \(VV^*\).  Finally,
  `cstarMatrixColumnPair_reflectionAverage_mul_columnPair_of_sum` and
  `cstarMatrixColumnPair_conjTranspose_mul_reflectionAverage_of_sum` show the
  averaged block acts on \(V\) and \(V^*\) through the same compressed corner
  \(V^*DV\).  The active blocker is now the nonlinear CFC pinching/Jensen step
  or a finite Effros perspective theorem, not projection/reflection algebra,
  algebraic pinching-average compression/invariance/projection-commutation or
  range-reduction, unitary CFC conjugation, or strict-positive domain
  preservation.
- 2026-05-28: The reflection-average CFC pinching inequality is now closed.
  `LiebTrace.lean` proves `cstarMatrix_compression_nonneg` and
  `cstarMatrix_compression_mono`, showing rectangular C-star compression
  preserves nonnegativity and order.  It also proves
  `cstarMatrixColumnPair_reflectionAverage_cfc_le_average_of_sum` and
  `cstarMatrixColumnPair_reflectionAverage_compressed_cfc_le_compressed_of_sum`:
  ordinary all-finite operator convexity applied to \(D\) and \(RDR\), plus
  unitary CFC conjugation and compression by \(V=[A;B]\), yields
  \(V^*f((D+RDR)/2)V\le V^*f(D)V\).  The active red blocker has narrowed to the
  nonlinear corner functional-calculus identity
  \(V^*f((D+RDR)/2)V=f(V^*DV)\), or a source-faithful Effros/perspective route
  that bypasses that identity.  The full-paper gate is still FAIL.
- 2026-05-28: The Hansen-Pedersen red bottleneck now has the shifted-inverse
  nonlinear corner subcase closed.  `CStarMatrixBridge.lean` proves
  `cstarMatrix_units_inv_mul_rect_eq_mul_units_inv_of_mul_eq`, the rectangular
  unit-inverse adapter \(UV=VW \Rightarrow U^{-1}V=VW^{-1}\).  `LiebTrace.lean`
  proves `cstarMatrix_cfc_shifted_inv_mul_rect_eq_mul_cfc_shifted_inv_of_mul_eq`
  and `cstarMatrixColumnPair_reflectionAverage_shifted_inv_corner_of_sum`,
  giving \(V^*(sI+(D+RDR)/2)^{-1}V=(sI+V^*DV)^{-1}\) for \(s>0\).  This was
  an intermediate queue item; the following entry supersedes it by closing the
  full concrete \(x\log x\) corner/Jensen step.
- 2026-05-28: The concrete Hansen-Pedersen `x log x` corner/Jensen dependency is
  now closed.  `CStarMatrixBridge.lean` adds the finite-dimensional C-star
  instance and compression linearity/continuous-linear-map lemmas
  (`cstarMatrix_complex_finiteDimensional`, `cstarMatrixCompressionCLM`, and
  related add/sub/smul helpers).  `LiebTrace.lean` proves
  `cstarMatrix_compression_setIntegral`,
  `cstarMatrixColumnPair_reflectionAverage_xlog_kernel_corner_of_sum`,
  `cstarMatrixColumnPair_reflectionAverage_xlog_corner_of_sum`, and the concrete
  two-point Jensen theorem
  `cstarMatrixXLogXHansenPedersenJensenTarget_of_unit_interval_kernel`.  The
  affine-corrected normalized entropy-kernel dependency is also closed by
  `realEntropyKernel`, `cstarMatrix_cfc_realEntropyKernel_eq_xlog_sub_id_add_one`,
  `cstarMatrixEntropyKernelPositiveOperatorConvexTarget_of_unit_interval_kernel`,
  `cstarMatrixEntropyKernelPositiveOperatorConvexAllFiniteTarget_of_unit_interval_kernel`,
  and `cstarMatrixEntropyKernelHansenPedersenJensenTarget_of_unit_interval_kernel`.
  The finite perspective square-root substrate is now closed too:
  `cstarMatrixPositiveSqrt`, `cstarMatrixPositiveInvSqrt`,
  `cstarMatrixPositiveSqrt_mul_self`,
  `cstarMatrixPositiveInvSqrt_mul_sqrt`,
  `cstarMatrixPositiveSqrt_mul_invSqrt`,
  `cstarMatrixPositiveInvSqrt_isUnit`,
  `cstarMatrixPositiveInvSqrt_mul_self_mul`, and
  `cstarMatrixPositiveInvSqrt_conj_isStrictlyPositive` remove hidden
  \(A^{1/2}\)/\(A^{-1/2}\) algebraic side conditions from the next perspective
  statement.
  The
  full-paper gate is still FAIL, but the red blocker has advanced: the active
  foundation is now the source-faithful finite Effros superoperator
  perspective / Umegaki matrix relative-entropy trace representation, then
  `cstarMatrixRelativeEntropyJointConvexOnStrictPositive`,
  followed by arbitrary-\(H\) Lieb concavity, trace-MGF domination, and matrix
  Bernstein/Khintchine for CACM equation (2).
- 2026-05-28: The ordinary finite perspective theorem for the normalized
  entropy kernel is now closed.  `LiebTrace.lean` defines
  `cstarMatrixPerspective` and `cstarMatrixPerspectiveWeight`, proves the
  weight normalization/compression/uncompression lemmas, and closes
  `cstarMatrixEntropyKernelPerspective_jointConvex` for
  \(P_f(X,A)=A^{1/2}f(A^{-1/2}XA^{-1/2})A^{1/2}\) with
  \(f(x)=x\log x-(x-1)\).  This is a listed Effros-route dependency, but the
  full-paper gate remains FAIL: the still-open theorem is the source-faithful
  finite superoperator perspective/trace representation for Umegaki relative
  entropy and then `cstarMatrixRelativeEntropyJointConvexOnStrictPositive`.
- 2026-05-28: The superoperator trace-representation route now has finite
  vectorization and the vectorized-identity trace pairing closed.
  `LiebTrace.lean` defines `matrixVecId`, `matrixVec`, and
  `matrixComplexQuadraticForm`, proves `finset_sum_product_diagonal`, and
  closes `matrix_kronecker_transpose_mulVec_matrixVec` plus
  `matrixComplexQuadraticForm_vecId_kronecker_transpose`, i.e.
  \(A\otimes B^{\mathsf T}\) represents \(M\mapsto AMB\) and
  \(v_I^*(A\otimes B^{\mathsf T})v_I=\operatorname{tr}(AB)\).  These are real
  dependencies for translating Kronecker/superoperator perspective inequalities
  into trace formulas, but the red bottleneck remains the CFC/log
  superoperator ratio behavior and the full Umegaki relative-entropy trace
  representation.
- 2026-05-28: The same superoperator route now also has the polynomial
  vectorization/trace-pairing layer closed.  `LiebTrace.lean` proves
  `matrix_kronecker_transpose_pow`,
  `matrix_kronecker_transpose_pow_mulVec_matrixVec`, `matrixVec_one`, and
  `matrixComplexQuadraticForm_vecId_kronecker_transpose_pow`, giving
  \((A\otimes B^{\mathsf T})^k=A^k\otimes(B^k)^{\mathsf T}\),
  \((A\otimes B^{\mathsf T})^k\operatorname{vec}(M)=\operatorname{vec}(A^kMB^k)\),
  and \(v_I^*(A\otimes B^{\mathsf T})^k v_I=\operatorname{tr}(A^kB^k)\).
  The remaining red-bottleneck dependency is the CFC/log passage from these
  polynomial identities to the finite superoperator ratio and the full
  Umegaki relative-entropy trace formula.
- 2026-05-28: The finite-polynomial packaging of the superoperator
  trace-pairing layer is also closed.  `LiebTrace.lean` proves
  `matrixComplexQuadraticForm_sum`, `matrixComplexQuadraticForm_smul`, and
  `matrixComplexQuadraticForm_vecId_kronecker_transpose_polynomial`, giving
  \(v_I^*(\sum_{k\in S} c_k(A\otimes B^{\mathsf T})^k)v_I
    =\sum_{k\in S}c_k\operatorname{tr}(A^kB^k)\).  The active bottleneck is now
  the analytic CFC/log transfer to the finite superoperator ratio, then the
  Umegaki relative-entropy trace formula.
- 2026-05-28: The finite-polynomial trace identity is now also available in
  standard Lean polynomial-evaluation form via
  `matrixComplexQuadraticForm_vecId_kronecker_transpose_aeval`.  This closes an
  API bridge into `Polynomial.aeval`; the remaining active bottleneck is still
  the analytic CFC/log transfer for the finite superoperator ratio.
- 2026-05-28: The first analytic transfer hook for that route is closed:
  `continuous_matrixComplexQuadraticForm` proves continuity of
  \(M\mapsto v^*Mv\) for fixed finite \(v\).  This supports a later
  polynomial-to-CFC/log limit argument but does not yet prove the log transfer
  or Umegaki relative-entropy trace representation.
- 2026-05-28: Polynomial evaluation continuity on finite complex matrices is
  also closed by `continuous_matrix_polynomial_aeval`.  This removes another
  finite-dimensional continuity side condition before the actual CFC/log
  transfer theorem.
- 2026-05-29: The source-faithful superoperator polynomial perspective layer is
  now closed for the Effros/Umegaki route.  `LiebTrace.lean` proves the
  domain/CFC/approximation facts
  `matrixVecId_inner_matrixVec`,
  `matrix_transpose_conjTranspose_eq_self_of_isSelfAdjoint`,
  `matrix_kronecker_transpose_isSelfAdjoint_of_isSelfAdjoint`,
  `matrix_kronecker_transpose_posSemidef`,
  `matrix_kronecker_transpose_posDef`,
  `matrix_kronecker_inv_transpose_posDef`, `matrixSelfAdjointCfc`,
  `matrixSelfAdjointCfc_polynomial`,
  `exists_realPolynomial_near_log_on_Icc`,
  `exists_realPolynomial_near_xlog_on_Icc`, and
  `exists_realPolynomial_near_realEntropyKernel_on_Icc`, plus the right
  multiplication trace formulas
  `matrixComplexQuadraticForm_vecId_kronecker_transpose_pow_right`,
  `matrixComplexQuadraticForm_vecId_kronecker_transpose_polynomial_right`,
  `matrixComplexQuadraticForm_vecId_kronecker_transpose_aeval_right`,
  `matrixComplexQuadraticForm_vecId_matrixSelfAdjointCfc_kronecker_transpose_realPolynomial`,
  and
  `matrixComplexQuadraticForm_vecId_matrixSelfAdjointCfc_kronecker_inv_transpose_realPolynomial_right`.
  This proves the finite-polynomial identity for
  \(v_I^*p(L_XR_A^{-1})R_Av_I\).  The full-paper gate remains FAIL: the active
  red bottleneck is now the analytic logarithmic/entropy-kernel CFC transfer
  from these polynomial formulas and then the Umegaki relative-entropy trace
  representation.
- 2026-05-29: The analytic uniform-approximation transfer for the
  source-faithful Effros/Umegaki route is now closed by
  `tendsto_matrixComplexQuadraticForm_matrixSelfAdjointCfc_mul` and
  `tendsto_superoperator_entropyKernel_of_realPolynomial_uniform_approx`.
  These theorems prove that a supplied uniform real-polynomial approximation to
  \(x\log x-(x-1)\) on the spectrum of
  \(X\otimes(A^{-1})^{\mathsf T}\) transfers the finite-polynomial trace
  formula for \(p(L_XR_A^{-1})R_A\) to the entropy-kernel CFC trace term.  The
  full-paper gate remains FAIL: the active red bottleneck is reduced to the
  source-faithful Umegaki trace representation and noncommutative
  relative-entropy joint convexity.
- 2026-05-29: The supplied-approximation input in the previous item is now
  removed.  `matrix_posDef_spectrum_real_pos`,
  `matrix_posDef_spectrum_real_subset_Icc`,
  `exists_realPolynomial_tendstoUniformlyOn_realEntropyKernel_on_subset_Icc`,
  `exists_realPolynomial_tendstoUniformlyOn_realEntropyKernel_spectrum_of_posDef`,
  and `exists_realPolynomial_tendsto_superoperator_entropyKernel_trace_of_posDef`
  construct a real-polynomial approximating sequence on positive-definite
  spectra and specialize the convergence theorem to
  \(X\otimes(A^{-1})^{\mathsf T}\).  The full-paper gate remains FAIL because
  the source-faithful Umegaki trace representation and
  `cstarMatrixRelativeEntropyJointConvexOnStrictPositive` are still open.
- 2026-05-29: The remaining joint-convexity step is now corrected to the
  source-faithful superoperator target
  `cstarMatrixRelativeEntropyTraceRepresentationBySuperoperator`, stated in
  terms of \(L_XR_A^{-1}\) via \(X\otimes(A^{-1})^{\mathsf T}\) and right
  multiplication by \(A\).  The ordinary source-matrix perspective bridge was
  rejected as not source-faithful for Umegaki relative entropy.  The
  full-paper gate remains FAIL: this target and
  `cstarMatrixRelativeEntropyJointConvexOnStrictPositive` remain open.
- 2026-05-29: The compact relative-entropy trace side of the Umegaki route is
  now closed by `matrix_isHermitian_cfc_id`, `matrix_isHermitian_cfc_xlog`, and
  `matrixTrace_hermitianCfc_relativeEntropy_re_eq_sum`.  The active red
  bottleneck is now the matching spectral-overlap expansion for the
  superoperator CFC term \(v_I^*f(L_XR_A^{-1})R_Av_I\), then the transport to
  `cstarMatrixRelativeEntropyTraceRepresentationBySuperoperator`.
- 2026-05-29: The remaining superoperator-side theorem is now named as
  `matrixSuperoperatorEntropyKernelOverlapExpansion`, with
  `matrixSuperoperatorEntropyKernelTrace` packaging the finite Kronecker trace
  expression and `matrixRelativeEntropyTraceRepresentation_of_superoperator_overlap`
  proving that the overlap expansion would match the compact relative-entropy
  trace.  Do not reopen the ordinary source-matrix perspective route for this
  bottleneck; the next counted progress is proving this overlap expansion or a
  source-equivalent theorem.
- 2026-05-29: The finite-polynomial part of
  `matrixSuperoperatorEntropyKernelOverlapExpansion` is now closed.
  `matrix_isHermitian_cfc_congr_eigen`, `matrix_isHermitian_cfc_mul`,
  `matrix_isHermitian_cfc_fun_pow_nat`,
  `matrix_isHermitian_cfc_inv_of_posDef`,
  `matrix_posDef_mul_inv_pow_eq_cfc`,
  `matrixTrace_pow_mul_inv_pow_re_eq_sum`, and
  `matrixPolynomialTraceRatio_re_eq_sum` prove that
  \(\operatorname{tr}(X^kA(A^{-1})^k)\) and real-polynomial sums have the same
  eigenbasis-overlap weights as the compact relative-entropy trace.  The active
  bottleneck remains the limiting entropy-kernel CFC overlap expansion.
- 2026-05-29: The limiting entropy-kernel overlap expansion and the
  source-faithful Umegaki trace representation are now closed.  New theorem
  names: `realRelativeEntropy_eq_mul_realEntropyKernel_mul_inv`,
  `tendsto_matrixPolynomialTraceRatio_overlap_sum_of_uniform_approx`,
  `exists_realPolynomial_tendsto_superoperator_entropyKernel_trace_and_overlap_of_posDef`,
  `matrixSuperoperatorEntropyKernelOverlapExpansion_of_nonempty`,
  `matrixSuperoperatorEntropyKernelOverlapExpansion_of_isEmpty`,
  `matrixSuperoperatorEntropyKernelOverlapExpansion_all`, and
  `cstarMatrixRelativeEntropyTraceRepresentationBySuperoperator_all`.  The
  full-paper gate remains FAIL because the active A1.5-B1 red bottleneck is now
  `cstarMatrixRelativeEntropyJointConvexOnStrictPositive`, followed by
  arbitrary-\(H\) Lieb concavity, trace-MGF domination, matrix
  Bernstein/Khintchine, CACM equation (2), and downstream FP concentration.
- 2026-05-29: The joint-convexity bottleneck gained the product-index lift and
  scalar-extraction layer.  New theorem names:
  `matrix_kronecker_right_identity_transpose_real_smul_add`,
  `cstarMatrixSuperoperatorLeftLift`, `cstarMatrixSuperoperatorRightLift`,
  `cstarMatrixSuperoperatorLeftLift_real_smul_add`,
  `cstarMatrixSuperoperatorRightLift_real_smul_add`,
  `cstarMatrixSuperoperatorLeftLift_isStrictlyPositive`,
  `cstarMatrixSuperoperatorRightLift_isStrictlyPositive`,
  `matrixComplexQuadraticForm_re_nonneg_of_posSemidef`,
  `matrixComplexQuadraticForm_re_mono_of_posSemidef_sub`, and
  `matrixComplexQuadraticForm_re_mono_of_cstarMatrix_le`.  These are counted
  dependencies for `cstarMatrixRelativeEntropyJointConvexOnStrictPositive`, but
  the red bottleneck remains open at the finite superoperator perspective
  bridge \(v_I^*P_f(L_X,R_A)v_I = v_I^*f(L_XR_A^{-1})R_Av_I\).
- 2026-05-29: The same bottleneck gained the product-index ordinary
  perspective trace theorem.  New theorem names:
  `matrixComplexQuadraticForm_add`,
  `cstarMatrixSuperoperatorPerspectiveTrace`,
  `cstarMatrixSuperoperatorPerspectiveTrace_jointConvex`,
  `cstarMatrixRelativeEntropyPerspectiveTraceRepresentation`, and
  `cstarMatrixRelativeEntropyJointConvexOnStrictPositive_of_perspectiveTraceRepresentation`.
  This proves joint convexity of \(v_I^*P_f(L_X,R_A)v_I\) and reduces the red
  bottleneck to the exact equality bridge identifying that quantity with local
  relative entropy.  It does not yet prove
  `cstarMatrixRelativeEntropyJointConvexOnStrictPositive`.
- 2026-05-29: The equality bridge gained its first CFC commutation/reorder
  dependency.  New theorem names:
  `cstarMatrixSuperoperatorLeftLift_rightLift_commute`,
  `cstarMatrixSuperoperatorPositiveInvSqrtRightLift_commute_leftLift`, and
  `cstarMatrixSuperoperatorPerspective_normalizedArgument_reorder`.  The next
  dependency is the product-index right-lift identity
  \(R_A^{-1/2}R_A^{-1/2}=R_A^{-1}\) and the CFC transport that identifies the
  ordinary product-index perspective trace with
  `matrixSuperoperatorEntropyKernelTrace`.
- 2026-05-29: The right-lift inverse-square-root square dependency is closed.
  New theorem names: `cstarMatrixPositiveInvSqrt_mul_self_eq_unit_inv` and
  `cstarMatrixSuperoperatorPerspective_normalizedArgument_eq_leftLift_mul_rightLift_unit_inv`.
  The remaining equality-bridge target is now the outer CFC/square-root trace
  transport from \(R_A^{1/2}f(L_XR_A^{-1})R_A^{1/2}\) to
  \(f(L_XR_A^{-1})R_A\), then matching that expression with
  `matrixSuperoperatorEntropyKernelTrace`.
- 2026-05-29: The ratio/square-root commutation dependency is closed.  New
  theorem names: `cstarMatrixPositiveSqrt_commute_unit_inv`,
  `cstarMatrixSuperoperatorPositiveSqrtRightLift_commute_leftLift`, and
  `cstarMatrixSuperoperatorLeftLift_mul_rightLift_unit_inv_commute_positiveSqrtRightLift`.
  The next equality-bridge dependency is the CFC transport showing
  \(f(L_XR_A^{-1})\) commutes with \(R_A^{1/2}\), followed by the
  vectorized-identity quadratic-form product equality.
- 2026-05-29: The finite-dimensional relative-entropy/Lieb bottleneck is now
  closed.  New theorem names:
  `cstarMatrixSuperoperatorEntropyKernelCfc_ratio_commute_positiveSqrtRightLift`,
  `cstarMatrixSuperoperatorPerspective_outerSqrt_cfc_ratio_mul_outerSqrt`,
  `cstarMatrixSuperoperatorPerspective_eq_cfc_ratio_mul_rightLift`,
  `cstarMatrix_unit_inv_to_matrix`,
  `cstarMatrixSuperoperatorRightLift_unit_inv_to_matrix`,
  `cstarMatrixSuperoperatorPerspectiveTrace_eq_matrixSuperoperatorEntropyKernelTrace`,
  `cstarMatrixRelativeEntropyPerspectiveTraceRepresentation_all`,
  `cstarMatrixRelativeEntropyJointConvexOnStrictPositive_all`,
  `liebTraceConcavityTarget_all`, and
  `FiniteProbability.expectationReal_trace_normed_exp_add_le`.  The active
  A1.5-B1 red bottleneck has moved to Tropp's iterated independent-sum
  trace-MGF domination theorem and matrix Bernstein/Khintchine for CACM
  Algorithm 1 equation (2).
- 2026-05-29: The first Algorithm 1 product-law adapter for the new trace-MGF
  bottleneck is closed in `ElementwiseTraceMGF.lean`.  New theorem names:
  `sqMagSampleProbability`,
  `sqMagTraceProbability_expectationComplex_step_eq`,
  `sqMagTraceProbability_expectationCStarMatrix_step_eq`,
  `sqMagTraceProbability_expectationCStarMatrix_step_eq_sampleExpectation`, and
  `sqMagTraceProbability_expectationReal_trace_normed_exp_add_step_le`.  These
  specialize the no-hidden-Lieb one-step trace-MGF theorem to one coordinate of
  the canonical squared-magnitude Algorithm 1 product trace law; the remaining
  target is the independent-sum trace-MGF iteration and Bernstein/Khintchine
  instantiation.
- 2026-05-29: The Algorithm 1 iid trace-MGF iteration is now closed locally.
  New theorem names: `sqMagTraceProbMass_snoc`,
  `sqMagTraceProbability_expectationReal_succ_last_eq`,
  `cstarMatrix_finset_sum_isSelfAdjoint`, and
  `sqMagTraceProbability_expectationReal_trace_normed_exp_add_sum_le`.  The
  active red bottleneck has moved from product-law trace-MGF iteration to the
  matrix Bernstein/Khintchine tail conversion and downstream FP spectral
  concentration transfer for CACM equation (2).
- 2026-05-29: The finite-real trace-exponential adapter for the Algorithm 1
  trace-MGF route is now closed locally.  New theorem names:
  `finiteComplexCStarMatrix_zero`, `finiteComplexCStarMatrix_add`,
  `finiteComplexCStarMatrix_finset_sum`, `finiteComplexCStarMatrixRingHom`,
  `finiteComplexCStarMatrixRingHom_continuous`,
  `finiteComplexCStarMatrix_finiteMatrixExp`,
  `cstarMatrixTrace_normed_exp_finiteComplexCStarMatrix`,
  `cstarMatrixTrace_normed_exp_finiteComplexCStarMatrix_re`, and
  `sqMagTraceProbability_expectationReal_finiteTrace_finiteMatrixExp_add_sum_le`.
  The active red bottleneck is now the scalar matrix-CGF/log-MGF bound for the
  Algorithm 1 self-adjoint dilation increments, followed by the final
  Bernstein/Khintchine largest-eigenvalue tail conversion and FP spectral
  transfer.
- 2026-05-29: The Algorithm 1 self-adjoint dilation trace-MGF instantiation is
  now closed locally.  New theorem names:
  `sqMagTraceProbabilityFiniteRealTraceMGFLogBound`,
  `rectSelfAdjointDilation_elementwiseSampleResidualIncrement_smul_symmetric`,
  `sqMagTraceProbability_expectationReal_finiteTrace_finiteMatrixExp_sum_rectSelfAdjointDilation_sampleResidualIncrement_le`,
  and
  `sqMagTraceProbability_expectationReal_finiteTrace_finiteMatrixExp_rectSelfAdjointDilation_elementwiseTraceResidual_le`.
  The left side is now the exact finite-real trace exponential of
  \(\theta D(A-\widetilde A)\).  The next red-bottleneck dependency is the
  scalar matrix-CGF/log-MGF estimate for the one-sample logarithmic mean
  increment.
- 2026-05-29: The Algorithm 1 trace-exponential/eigenvalue Markov step is now
  specialized to the actual scaled self-adjoint dilation residual.  New theorem
  names:
  `sqMagTraceProbability_eventProb_exists_finiteHermitianEigenvalue_scaled_rectSelfAdjointDilation_elementwiseTraceResidual_ge_le`
  and
  `sqMagTraceProbability_eventProb_forall_abs_finiteHermitianEigenvalue_scaled_rectSelfAdjointDilation_elementwiseTraceResidual_lt_ge`.
  The remaining red bottleneck is the scalar matrix-CGF/log-MGF estimate and
  explicit Bernstein/Khintchine constants for CACM equation (2), not the
  Markov/eigenvalue conversion itself.
- 2026-05-29: The A1.5-B1 scalar-to-operator CFC Bernstein-parabola lift is
  closed in `LiebTrace.lean`.  New theorem names:
  `cstarMatrix_cfc_quadratic_eq` and
  `cstarMatrix_cfc_real_exp_mul_le_quadratic_of_spectrum`.  These lift a
  scalar pointwise bound \(e^{\theta x}\le 1+\theta x+\beta x^2\) on
  \(\sigma_{\mathbb R}(X)\) to
  \(\exp_{\mathrm{cfc},\mathbb R}(\theta X)\preceq I+\theta X+\beta X^2\).
  This left the scalar Bernstein parabola constants and one-sample
  matrix-CGF/log-MGF variance-proxy use open at that checkpoint; the scalar
  constants are closed in the next memory entry.
- 2026-05-29: The A1.5-B1 scalar Bernstein parabola with constants is now
  closed in `LiebTrace.lean`.  New theorem names:
  `real_exp_quadratic_remainder_monotone`,
  `real_exp_sub_self_sub_one_nonneg`,
  `real_sq_div_two_le_exp_sub_self_sub_one_of_nonneg`,
  `real_exp_le_one_add_self_add_sq_div_two_of_nonpos`,
  `real_exp_tail_two_hasSum`,
  `real_exp_mul_le_quadratic_of_nonneg_of_nonneg_of_le_one`,
  `real_exp_mul_le_quadratic_of_nonneg_of_le_one`,
  `real_exp_mul_le_quadratic_scaled_of_nonneg_of_pos_of_le`, and
  `cstarMatrix_cfc_real_exp_mul_le_bernstein_quadratic_of_spectrum_le`.  The
  remaining red bottleneck is the one-sample matrix-CGF/log-MGF variance-proxy
  instantiation and final Bernstein/Khintchine tail constants for CACM
  equation (2).
- 2026-05-29: The generic A1.5-B1 one-sample matrix-CGF/log-MGF variance
  proxy is now closed in `LiebTrace.lean`, with one real-scalar expectation
  helper in `CStarMatrixExpectation.lean`.  New theorem names:
  `FiniteProbability.expectationCStarMatrix_real_smul`,
  `cstarMatrix_real_smul_isSelfAdjoint`,
  `cstarMatrix_cfc_real_exp_mul_eq_normedSpace_exp_real_smul`,
  `cstarMatrix_selfAdjoint_mul_self_nonneg`,
  `cstarMatrix_one_add_le_normedSpace_exp_of_nonneg`,
  `cstarMatrix_log_one_add_le_self_of_nonneg`,
  `FiniteProbability.expectationCStarMatrix_cfc_real_exp_mul_le_bernstein_variance_proxy`,
  `FiniteProbability.cstarMatrix_log_expectationCStarMatrix_cfc_real_exp_mul_le_bernstein_variance_proxy`,
  and
  `FiniteProbability.cstarMatrix_log_expectationCStarMatrix_normed_exp_real_smul_le_bernstein_variance_proxy`.
  The remaining red bottleneck is now Algorithm 1 dilation-increment
  instantiation of that generic theorem, plus the final Bernstein/Khintchine
  tail constants and downstream FP spectral concentration.

- 2026-05-29: Closed the Algorithm 1 truncated one-sample log-CGF
  instantiation.  New shared support-aware wrappers:
  `FiniteProbability.expectationCStarMatrix_nonneg_of_prob_pos`,
  `FiniteProbability.expectationCStarMatrix_mono_of_prob_pos`, and
  `cstarMatrix_spectrum_le_of_le_real_smul_one`.  New Algorithm 1 theorems:
  `sqMagSampleProbability_expectationCStarMatrix_rectSelfAdjointDilation_sampleResidualIncrement_eq_zero`,
  `sqMagSampleProbability_finiteComplex_rectSelfAdjointDilation_sampleResidualIncrement_truncated_spectrum_le`,
  and
  `sqMagSampleProbability_cstarMatrix_log_expectationCStarMatrix_normed_exp_rectSelfAdjointDilation_truncated_sampleResidualIncrement_le`.
  The red bottleneck is now the Bernstein/Khintchine trace-MGF-to-tail
  constant optimization and downstream FP spectral concentration, not the
  one-sample Algorithm 1 CGF instantiation.

- 2026-05-29: Closed the Algorithm 1 parameterized two-sided Bernstein tail
  skeleton for the truncated self-adjoint dilation.  New theorem names:
  `sqMagSampleProbability_expectationCStarMatrix_rectSelfAdjointDilation_sampleResidualIncrement_square_le`,
  `sqMagSampleProbability_neg_finiteComplex_rectSelfAdjointDilation_sampleResidualIncrement_truncated_spectrum_le`,
  `sqMagTraceProbabilityFiniteRealTraceMGFLogBound_rectSelfAdjointDilation_truncated_sampleResidualIncrement_le`,
  `sqMagTraceProbability_eventProb_exists_finiteHermitianEigenvalue_scaled_rectSelfAdjointDilation_truncatedTraceResidual_ge_le_exp`,
  `sqMagTraceProbabilityFiniteRealTraceMGFLogBound_neg_rectSelfAdjointDilation_truncated_sampleResidualIncrement_le`,
  and
  `sqMagTraceProbability_eventProb_forall_abs_finiteHermitianEigenvalue_scaled_rectSelfAdjointDilation_truncatedTraceResidual_lt_ge_exp`.
  The red bottleneck is now theta optimization/final CACM equation (2)
  constants plus downstream floating-point spectral concentration transfer.

- 2026-05-29: Added the explicit `1-\delta` high-probability corollary for the
  Algorithm 1 truncated two-sided dilation eigenvalue theorem.  New theorem
  names: `real_exp_neg_log_two_mul_div_mul_self_add` and
  `sqMagTraceProbability_eventProb_forall_abs_finiteHermitianEigenvalue_scaled_rectSelfAdjointDilation_truncatedTraceResidual_lt_ge_one_sub_delta`.
  This chooses `T = log (2B/delta)` and proves the failure terms sum to
  `delta` locally.  The red bottleneck remains theta optimization, conversion
  from scaled eigenvalues to the final CACM equation (2) spectral-norm
  constants, and downstream FP transfer.

- 2026-05-29: Closed the deterministic scaled-eigenvalue to rectangular
  spectral-event conversion for Algorithm 1.  New shared theorems:
  `finiteLoewnerLe_of_smul_left_le_smul_id` and
  `finiteLoewnerLe_smul_id_of_finiteHermitianEigenvalues_le`.  New Algorithm
  1 event/corollaries:
  `algorithm1ScaledDilationAbsEigenvalueEvent`,
  `algorithm1ScaledDilationAbsEigenvalueEvent_subset_exactSpectralEvent`, and
  `sqMagTraceProbability_eventProb_algorithm1ExactSpectralEvent_truncatedTraceResidual_ge_one_sub_delta_scaled_radius`.
  The high-probability spectral radius is still
  `log (2B/delta) / theta`; the red bottleneck is now theta optimization and
  source-constant simplification to CACM equation (2), then downstream FP
  spectral transfer.

- 2026-05-29: Closed the scalar theta-optimization dependency for the
  truncated exact Algorithm 1 spectral route.  New shared theorem:
  `real_bernstein_exact_radius_le_of_log_le`.  New monotonicity helpers:
  `rectOpNorm2Le_mono` and `algorithm1ExactSpectralEvent_mono`.  New
  Algorithm 1 theorem:
  `sqMagTraceProbability_eventProb_algorithm1ExactSpectralEvent_truncatedTraceResidual_ge_one_sub_delta_bennett_radius`.
  This chooses `theta = log (1 + L*r/W) / L` and proves the spectral event at
  radius `r` under an explicit Bennett budget.  The remaining red bottleneck
  is source sample-complexity/final-constant simplification, truncation
  transfer at those constants, and downstream FP spectral transfer.

- 2026-05-29: Closed the source-sharp square variance dependency for the
  Drineas--Zouzias Algorithm 1 route.  New sharp vector/transpose-vector
  moment theorems feed
  `sqMagProb_sum_finiteQuadraticForm_rectSelfAdjointDilation_square_le_sharp_square`,
  `sqMagProb_sum_rectSelfAdjointDilation_square_loewnerLe_scalar_id_sharp_square`,
  and
  `sqMagSampleProbability_expectationCStarMatrix_rectSelfAdjointDilation_sampleResidualIncrement_square_le_sharp_square`.
  The truncated square trace-MGF/tail skeleton now has
  `sqMagTraceProbabilityFiniteRealTraceMGFLogBound_rectSelfAdjointDilation_truncated_sampleResidualIncrement_le_sharp_square`,
  `sqMagTraceProbabilityFiniteRealTraceMGFLogBound_neg_rectSelfAdjointDilation_truncated_sampleResidualIncrement_le_sharp_square`,
  and
  `sqMagTraceProbability_eventProb_forall_abs_finiteHermitianEigenvalue_scaled_rectSelfAdjointDilation_truncatedTraceResidual_lt_ge_one_sub_delta_sharp_square`.
  Remaining red bottleneck: source sample-complexity/final-constant
  simplification, final truncation transfer, and downstream FP spectral
  transfer.

- 2026-05-29: Closed the source-sharp square scaled-radius and Bennett-radius
  spectral conversion dependency for Algorithm 1.  New theorems:
  `sqMagTraceProbability_eventProb_algorithm1ExactSpectralEvent_truncatedTraceResidual_ge_one_sub_delta_scaled_radius_sharp_square`
  and
  `sqMagTraceProbability_eventProb_algorithm1ExactSpectralEvent_truncatedTraceResidual_ge_one_sub_delta_bennett_radius_sharp_square`.
  These use the source-aligned `V = n*||Ahat||_F^2/s^2` route and no-`sqrt 2`
  support radius.  Remaining red bottleneck: simplify the explicit Bennett
  budget to the Drineas--Zouzias/CACM sample-complexity constants, then
  perform truncation and FP spectral transfer at those constants.

- 2026-05-29: Closed a conservative denominator fallback for the Algorithm 1
  source-sharp Bennett route.  New scalar theorems:
  `real_bennett_transform_lower_bound_two_add` and
  `real_bennett_budget_of_quadratic_denominator_two_add`; new Algorithm 1
  corollary:
  `sqMagTraceProbability_eventProb_algorithm1ExactSpectralEvent_truncatedTraceResidual_ge_one_sub_delta_bernstein_denominator_sharp_square`.
  This proves the fully local `q <= r^2/(2W+L*r)` route.  It is weaker than
  the Drineas--Zouzias denominator `2W+(2/3)L*r`, so the final source-constant
  bottleneck remains open.

- 2026-05-29: Closed the sharper Algorithm 1 source denominator and sample
  budget route.  New scalar theorems:
  `real_bennett_transform_lower_bound_two_add_two_thirds` and
  `real_bennett_budget_of_quadratic_denominator_two_add_two_thirds`; new
  source sample/truncation/FP theorem family:
  `sqMagTraceProbability_eventProb_algorithm1ExactSpectralEvent_truncatedTraceResidual_ge_one_sub_delta_source_sample_budget_sharp_square`,
  `sqMagTraceProbability_eventProb_algorithm1ExactTruncatedSpectralEvent_ge_one_sub_delta_source_sample_budget_sharp_square`, and
  `sqMagTraceProbability_eventProb_algorithm1FlTruncatedSpectralEvent_ge_one_sub_delta_source_sample_budget_sharp_square`.
  The exact source-budget Algorithm 1 equation (2) route is now closed through
  deterministic truncation.

- 2026-05-29: Closed the Algorithm 1 source-budget floating-point gamma-budget
  row.  New sampling support lemmas:
  `hitCount_le_steps`, `hitCount_eq_zero_of_forall_not_hit`,
  `fl_elementwiseTraceSketch_zero_init_eq_zero_of_forall_not_hit`, and
  `sqMagTraceErrorBudget_nonneg`; new support-aware spectral theorem:
  `fl_elementwiseTraceSketch_zero_init_sqMag_error_bound_of_positiveProb`; new
  final FP source-budget theorem:
  `sqMagTraceProbability_eventProb_algorithm1FlTruncatedSpectralEvent_ge_one_sub_delta_source_sample_budget_gamma_square`.
  The theorem intersects the exact source-budget event with the sampler's
  probability-one positive-support event, derives the entrywise `gamma` budget
  locally with `Q=s`, and therefore no longer assumes an all-traces `hPoint`
  perturbation hypothesis.  The remaining Algorithm 1 gap is only the
  untruncated/general-rectangular CACM-prose variant, not the cited
  source-aligned square theorem.

- 2026-05-29: Advanced the equation (8) least-squares row after the Algorithm 1
  closure.  New bridge theorems:
  `rowSampleGramFullFpPerturbBudget_nonneg`,
  `eventProb_lsObjective_le_of_preserves`,
  `eventProb_lsObjective_le_one_add_eta_of_preserves`,
  `eventProb_lsObjective_le_one_add_eta_of_coordinate_quadratic_error`,
  `leverageTraceProbability_eventProb_lsObjective_le_one_add_eta_of_coordinate_quadratic_error`,
  and
  `leverageTraceProbability_eventProb_fl_lsObjective_le_one_add_eta_of_coordinate_quadratic_error`.
  These transfer the exact and fully floating-point leverage-score equation (7)
  operator events to the equation (8) sketched-minimizer objective guarantee,
  conditional on the residual-coordinate representation.  The paper-level
  equation (8) row remains open at the concrete sampled augmented-residual
  representation, sharper survey sample-complexity theorem, and downstream
  solver/preconditioner FP pipeline.

- 2026-05-29: Closed the concrete sampled-row algebra subrow for equation (8).
  New exact algebra/LS theorems:
  `vecNorm2Sq_add_quadraticForm_sub_id_eq_quadraticForm`,
  `vecNorm2Sq_rowSketch_linearCombination_eq_quadratic_rowSketchGram`,
  `vecNorm2Sq_rowSampleSketch_linearCombination_eq_quadratic_rowSampleGram`,
  `rowSampleLSMatrixWithBasisScale`, `rowSampleLSVectorWithBasisScale`,
  `rowSampleLSResidualWithBasisScale_eq_coord`,
  `rowSampleLSObjectiveWithBasisScale_eq_coordinate_quadratic_error`, and
  `leverageTraceProbability_eventProb_rowSampleLSObjective_le_one_add_eta_of_residual_coordinates`.
  These prove that the concrete Algorithm 2 sampled rows of `A` and `b`, scaled
  by leverage probabilities from `U`, have the expected coordinate quadratic
  objective whenever original residuals are represented in the rows of `U`.
  The equation (8) paper-level row remains open at constructing that
  residual-coordinate map from rectangular augmented-basis/rank/SVD/QR
  foundations, sharper survey sample complexity, and the FP solver pipeline.

- 2026-05-29: Advanced the equation (8) LS row one step further by replacing
  the arbitrary residual-coordinate map with canonical coordinates
  `U^T(Ax-b)` under an explicit column-space predicate.  New theorem names:
  `quadraticForm_idMatrix_eq_vecNorm2Sq`, `residualCoordinates`,
  `ResidualsInColumnSpace`,
  `lsObjective_eq_vecNorm2Sq_residualCoordinates_of_residualsInColumnSpace`,
  and
  `leverageTraceProbability_eventProb_rowSampleLSObjective_le_one_add_eta_of_residualsInColumnSpace`.
  This closes the objective identity from canonical residual coordinates.  The
  remaining LS foundation is now sharper and more honest: prove an orthonormal
  augmented residual basis that satisfies `ResidualsInColumnSpace`, then prove
  the sharper subspace-embedding/sample-complexity theorem and integrate the
  downstream FP solver/preconditioner pipeline.

- 2026-05-29: Closed the identity-basis fallback for equation (8).  New names:
  `hasOrthonormalColumns_idMatrix`, `residualCoordinates_idMatrix`,
  `residualsInColumnSpace_idMatrix`, and
  `leverageTraceProbability_eventProb_rowSampleLSObjective_le_one_add_eta_of_idBasis`.
  This gives a concrete equation (6) theorem with `U = I_m`, uniform row
  probabilities, and dimension parameter `d = m`.  It is a valid fallback and
  a regression guard against hidden residual-coordinate assumptions, but it is
  not the survey's sharp low-dimensional augmented residual basis.

- 2026-05-29: Closed the column/RHS representation adapter for equation (8).
  New names: `ColumnsAndRhsInColumnSpace`, `residualCoordinatesFromColumns`,
  `residualsInColumnSpace_of_residual_representation`,
  `lsResidual_eq_basis_sum_of_columnsAndRhsInColumnSpace`, and
  `residualsInColumnSpace_of_columnsAndRhsInColumnSpace`.  This reduces the
  remaining LS basis foundation to a precise linear-algebra target: construct
  a sharp low-dimensional orthonormal `U` and coordinates for the augmented
  data matrix `[A b]`.

- 2026-05-29: Closed the augmented-span basis dependency for equation (8) by
  reusing Mathlib's finite-dimensional orthonormal-basis API.  New names:
  `euclideanVec`, `augmentedDataVector`, `augmentedDataSpan`,
  `augmentedDataVector_mem_span`, `augmentedSpanBasisMatrix`,
  `augmentedSpanColumnCoords`, `augmentedSpanRhsCoords`,
  `hasOrthonormalColumns_augmentedSpanBasisMatrix`,
  `columnsAndRhsInColumnSpace_augmentedSpanBasisMatrix`,
  `residualsInColumnSpace_augmentedSpanBasisMatrix`, and
  `leverageTraceProbability_eventProb_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan`.
  The concrete leverage-score sampled LS theorem now uses dimension
  `finrank ℝ (augmentedDataSpan A b)` with the expected positive-dimension
  hypothesis. Remaining LS paper-level work: sharper survey
  subspace-embedding/sample-complexity constants and downstream FP
  solver/preconditioner composition.

- 2026-05-29: Added the fully floating-point rounded-Gram objective-transfer
  corollaries for equation (8) after the augmented-span closure.  New names:
  `leverageTraceProbability_eventProb_fl_lsObjective_le_one_add_eta_of_augmentedSpan`
  and `leverageTraceProbability_eventProb_fl_lsObjective_le_one_add_eta_of_idBasis`.
  These discharge the canonical residual-coordinate/original-objective side
  for the augmented-span and identity bases while keeping the rounded sketched
  objective representation explicit.  They do not close the sharper
  sample-complexity theorem or the implementation-backed FP solver pipeline.

- 2026-05-29: Advanced the source-sharp leverage-score equation (7) route by
  proving the one-step rank-one ingredients needed for an Oliveira/Tropp
  covariance concentration theorem.  New generic row-sampling names:
  `rowOuterGramSample_eq_zero_of_prob_zero`,
  `finiteQuadraticForm_rowOuterGramSample_eq_sq_div`, and
  `finitePSD_rowOuterGramSample`.  New leverage names:
  `leverage_rowOuterGramSample_finitePSD`,
  `leverage_rowOuterGramSample_mean_eq_id`, and
  `leverage_rowOuterGramSample_finiteLoewnerLe_nat`.  The sharp product-law
  concentration/sample-complexity theorem is still open and is the next
  leverage frontier.

- 2026-05-29: Added `RowSamplingTraceMGF.lean` for Algorithm 2 row-sampling
  product-law trace-MGF infrastructure.  New names include
  `rowSqNormSampleProbability`,
  `rowSqNormTraceProbability_expectationReal_trace_normed_exp_add_sum_le`,
  `rowSqNormTraceProbability_expectationReal_finiteTrace_finiteMatrixExp_add_sum_le`,
  `rowSqNormTraceProbabilityFiniteRealTraceMGFLogBound`, and
  `rowSqNormTraceProbabilityFiniteRealTraceMGFLogBound_zero_le_card_mul_exp_of_log_le_real_smul_one`.
  This closes the row-trace independence/MGF/scalarization dependency for the
  sharper leverage equation (7) route; the centered leverage covariance
  one-sample log-CGF and final rank-one concentration theorem remain open.

- 2026-05-29: Added `RowSamplingLeverageMGF.lean` to instantiate the local
  generic centered C-star Bernstein log-CGF theorem for Algorithm 2 leverage
  covariance increments `rowOuterGramSample U i - I`.  New names include
  `rowOuterGramSample_centered_symmetric`,
  `leverage_rowOuterGramSample_centered_expectationCStarMatrix_eq_zero`,
  `leverage_rowOuterGramSample_centered_spectrum_le_nat`, and
  `leverage_rowOuterGramSample_centered_log_cgf_le`.  This closes the
  centered one-sample log-CGF dependency without assuming concentration.  The
  active leverage frontier is now the product-law rank-one tail theorem and
  source sample-size simplification.

- 2026-05-29: Continued `RowSamplingLeverageMGF.lean` through the exact
  variance, two-sided row-trace tail, Bennett sample-budget, and sharper
  floating-point finite-Loewner transfer layer.  New public names include
  `rowSampleGram_sub_finiteIdMatrix_eq_centered_rowOuterGramSample_average`,
  `leverage_rowOuterGramSample_centered_square_expectationCStarMatrix_eq`,
  `leverage_rowOuterGramSample_neg_centered_log_cgf_le`,
  `leverage_rowSqNormTraceProbabilityFiniteRealTraceMGFLogBound_centered_le`,
  `leverage_rowSqNormTraceProbabilityFiniteRealTraceMGFLogBound_neg_centered_le`,
  `leverageTraceProbability_eventProb_rowSampleGram_finiteLoewnerLe_upper_lt_ge_one_sub_exp`,
  `leverageTraceProbability_eventProb_rowSampleGram_finiteLoewnerLe_lower_lt_ge_one_sub_exp`,
  `leverageTraceProbability_eventProb_rowSampleGram_two_sided_finiteLoewnerLe_ge_one_sub_exp`,
  and
  `leverageTraceProbability_eventProb_rowSampleGram_two_sided_finiteLoewnerLe_ge_one_sub_delta_of_tail_budget`,
  `real_bernstein_tail_le_half_delta_of_quadratic_budget`,
  `leverageTraceProbability_eventProb_rowSampleGram_finiteLoewnerLe_upper_ge_one_sub_delta_half_of_sample_budget`,
  `leverageTraceProbability_eventProb_rowSampleGram_finiteLoewnerLe_lower_ge_one_sub_delta_half_of_sample_budget`,
  `leverageTraceProbability_eventProb_rowSampleGram_two_sided_finiteLoewnerLe_ge_one_sub_delta_of_sample_budget`,
  and
  `leverageTraceProbability_eventProb_fl_rowSampleGramDot_two_sided_finiteLoewnerLe_ge_one_sub_delta_of_sample_budget`.
  The rank-one row-trace tail dependency, scalar Bennett sample-budget
  simplification, and sharper FP transfer are closed in finite-Loewner form.

- 2026-05-29: Continued equation (8) least-squares formalization by composing
  the new Algorithm 2 finite-Loewner Bennett sample-budget theorem with the
  sketched-minimizer objective bridge.  New public names include
  `preservesLSObjective_of_coordinate_finiteLoewner_error`,
  `eventProb_preservesLSObjective_of_coordinate_finiteLoewner_error`,
  `eventProb_lsObjective_le_one_add_eta_of_coordinate_finiteLoewner_error`,
  `leverageTraceProbability_eventProb_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget`,
  and
  `leverageTraceProbability_eventProb_fl_lsObjective_le_one_add_eta_of_augmentedSpan_sample_budget`.
  The exact Algorithm 2 leverage row-sampled LS theorem is closed in the
  source-aligned Bennett finite-Loewner sample-budget form; the FP theorem is a
  rounded-Gram transfer with an explicit `rowSampleGramFullFpPerturbBudget`
  radius and still requires a rounded sketched-objective representation.

- 2026-05-29: Added the first literal rounded sampled-row implementation
  foundation for equation (8) in `LeastSquaresSketch.lean`.  New public names
  include `fl_rowSampleLSMatrixWithBasisScale`,
  `fl_rowSampleLSVectorWithBasisScale`,
  `fl_rowSampleLSMatrixWithBasisScale_error_bound`,
  `fl_rowSampleLSVectorWithBasisScale_error_bound`,
  `fl_rowSampleLSResidualWithBasisScale_error_bound`, and
  `fl_rowSampleLSResidualWithBasisScale_error_bound_of_positiveProb`.  These
  model rounding the sampled/scaled entries of `A` and `b` by the local
  division FP primitive and prove the rowwise residual perturbation bound.

- 2026-05-29: Closed the deterministic objective-level lift for that literal
  rounded equation (8) construction.  New public names include shared vector
  lemmas `vecNorm2Sq_le_of_abs_le`, `vecNorm2_le_of_abs_le`, and
  `abs_vecNorm2Sq_add_sub_le`, plus LS bridges
  `lsObjective_residual_difference_bound`,
  `lsObjective_residual_budget_bound`, `rowSampleLSResidualFpBudget`,
  `rowSampleLSResidualFpBudget_nonneg`, and
  `fl_rowSampleLSObjectiveWithBasisScale_error_bound_of_positiveProb`.
  This was later closed under explicit objective-budget slack; the important
  guardrail remains that the concrete rounded `A,b` implementation is not
  claimed to automatically satisfy the older rounded-Gram representation.

- 2026-05-29: Closed the high-probability rounded-minimizer composition for
  the literal rounded sampled/scaled equation (8) construction under an
  explicit objective-budget slack condition.  New public names include
  `rowSampleLSObjectiveFpBudget`, `rowSampleLSObjectiveFpBudget_nonneg`,
  `fl_rowSampleLSObjectiveWithBasisScale_error_bound_of_positiveProb_budget`,
  `lsObjective_le_of_sketch_preserves_with_objective_error`,
  `lsObjective_le_one_add_eta_of_sketch_preserves_with_objective_error`,
  `eventProb_lsObjective_le_one_add_eta_of_preserves_with_objective_error`,
  `eventProb_lsObjective_le_one_add_eta_of_preserves_with_pointwise_objective_error`,
  `eventProb_lsObjective_le_one_add_eta_of_preserves_with_objective_error_on_event`,
  `eventProb_lsObjective_le_one_add_eta_of_coordinate_finiteLoewner_error_with_objective_error_on_event`,
  and
  `leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error`.
  This theorem reuses the exact finite-Loewner equation (7) concentration and
  the probability-one positive-support event; it still exposes the FP
  objective-budget slack as a hypothesis.  The remaining equation (8) work is
  downstream solver/preconditioner FP integration and random-projection
  variants.

- 2026-05-29: Closed the additive solver-objective-gap bridge for the same
  literal rounded sampled/scaled equation (8) construction.  New public names
  include `IsLeastSquaresApproxMinimizer`,
  `isLeastSquaresApproxMinimizer_of_minimizer`,
  `lsObjective_le_of_sketch_preserves_with_objective_error_and_solver_gap`,
  `lsObjective_le_one_add_eta_of_sketch_preserves_with_objective_error_and_solver_gap`,
  `eventProb_lsObjective_le_one_add_eta_of_preserves_with_objective_error_and_solver_gap_on_event`,
  `eventProb_lsObjective_le_one_add_eta_of_coordinate_finiteLoewner_error_with_objective_error_and_solver_gap_on_event`,
  and
  `leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_solver_gap`.
  This closes the composition theorem needed for approximate rounded solvers,
  but it deliberately keeps the solver objective gap explicit.  The next
  equation (8) frontier is deriving such a gap from a concrete QR,
  preconditioner, or iterative-solver FP theorem.

- 2026-05-29: Added the componentwise solver forward-error certificate bridge
  for the literal rounded sampled/scaled equation (8) construction.  New public
  names include `lsSolutionForwardResidualBudget`,
  `lsSolutionForwardObjectiveGap`,
  `lsResidual_difference_bound_of_solution_abs_le`,
  `lsObjective_solution_forward_error_bound`,
  `isLeastSquaresApproxMinimizer_of_solution_abs_le`, and
  `leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_forward_error`.
  A nonnegative componentwise certificate
  `|xHat samples j - xStar samples j| <= solverDx samples j` now induces an
  explicit additive rounded-objective gap and composes with the high-probability
  literal rounded sampled-row theorem.  The remaining equation (8) frontier is
  deriving that certificate, or an equivalent objective gap, from a concrete QR,
  preconditioner, or iterative-solver FP theorem.

- 2026-05-29: Added a perturbed-Gram-system solver certificate bridge for the
  same literal rounded sampled/scaled equation (8) construction.  New public
  names include `lsNormalMatrix`, `lsNormalRhs`, `gramForwardSolverDx`,
  `gramForwardSolverDx_nonneg`,
  `gram_forward_error_certificate_of_perturbed_gram_system`, and
  `leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_perturbed_gram_solver`.
  This reuses the local `gram_forward_error_normwise` theorem to turn explicit
  perturbations of the rounded normal equations into the `solverDx` certificate
  consumed by the high-probability theorem.  The remaining solver frontier is
  now specifically to derive those perturbed Gram equations and radii from a
  concrete QR, preconditioner, or iterative solver implementation.

- 2026-05-29: Added the QR least-squares backward-error-spec adapter for the
  same equation (8) solver frontier.  New public names include
  `abs_entry_le_frobNorm`, `lsQRSolveBackwardSolverDx`,
  `lsQRSolveBackwardSolverDx_nonneg`,
  `gram_forward_error_certificate_of_ls_qr_solve_backward_error`, and
  `leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_ls_qr_backward_error_solver`.
  This consumes the existing local `LSQRSolveBackwardError` structure, converts
  its Frobenius `ΔG` radius to entrywise control, and feeds the already proved
  solver-certificate transfer.  It is still a spec adapter, not a proof that a
  concrete QR/preconditioner implementation satisfies the spec.

- 2026-05-30: Added a concrete normal-equations/Cholesky solver route for the
  literal rounded sampled/scaled equation (8) construction.  New public names
  include `normalEqCholeskyXHat`, `normalEqCholeskyGramBound`,
  `normalEqCholeskyRhsBound`, `normalEqCholeskySolverDx`,
  `normalEqCholeskySolverDx_nonneg`,
  `normal_equations_cholesky_forward_error_certificate`, and
  `leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_normal_eq_cholesky_solver`.
  This reuses the local `ls_normal_equations_backward` and
  `ls_normal_equations_forward_error` theorems to produce the solver
  certificate.  It closes a concrete solver path, but not the separate
  rectangular QR/preconditioner implementation theorem.

- 2026-05-30: Recorded the remaining equation (8) solver item as red
  bottleneck `LS.8-rectangular-QR`.  Local search confirms that
  `LSQRSolveBackwardError` is a specification because the repository does not
  yet have a rectangular QR/Householder least-squares backward-error theorem.
  External proof-source acquisition points to Higham, *Accuracy and Stability
  of Numerical Algorithms*, chapters 19--20, and Cox--Higham's weighted least
  squares Householder QR analysis as the right mathematical route; these are
  sources to formalize from, not assumptions that close the theorem.

- 2026-05-30: Closed one dependency of `LS.8-rectangular-QR`:
  `rectLSNormalEquations_perturbed_to_gram_system` and
  `LSQRSolveBackwardError.of_rectangular_perturbed_normal_equations` now turn
  perturbed rectangular normal equations plus induced Gram/RHS radii into the
  local `LSQRSolveBackwardError` spec.  The remaining red dependency is the
  concrete rectangular Householder QR/preconditioner FP theorem itself.

- 2026-05-30: Closed another listed dependency of
  `LS.8-rectangular-QR`: `rectLSGramPerturbation_eq_sum`,
  `rectLSRhsPerturbation_eq_sum`,
  `rectLSGramPerturbation_abs_le_entryBudget`,
  `rectLSRhsPerturbation_abs_le_entryBudget`,
  `rectLSGramPerturbation_frobNorm_le_entryBudget`,
  `rectLSGramPerturbation_abs_le_normBudget`,
  `rectLSRhsPerturbation_abs_le_normBudget`, and
  `rectLSGramPerturbation_frobNorm_le_normBudget` expand the induced
  rectangular Gram/RHS perturbations and bound them from exact entry budgets
  or coarse data perturbation radii.  The red blocker is now specifically the
  concrete rectangular QR/preconditioner theorem supplying perturbed
  rectangular normal equations and rectangular data perturbation bounds.

- 2026-05-30: Added the norm-budget handoff theorem
  `LSQRSolveBackwardError.of_rectangular_perturbed_normal_equations_normBudget`.
  It packages perturbed rectangular normal equations, normwise data
  perturbation radii, and the induced Gram/RHS budget bounds into the local
  `LSQRSolveBackwardError` specification.  This closes the adapter layer; the
  remaining red dependency is still the concrete rectangular QR/preconditioner
  implementation theorem itself.

- 2026-05-30: Closed small route-A algebra dependencies for the rectangular
  QR bottleneck: `matMulRectLeft`, `matMulRectRight`,
  `frobNormSqRect_orthogonal_left`, `frobNormRect_orthogonal_left`,
  `frobNormSqRect_orthogonal_right`, and
  `frobNormRect_orthogonal_right` now prove that compatible orthogonal square
  left and right factors preserve the rectangular Frobenius norm.  The concrete
  rectangular Householder QR/preconditioner theorem is still open.

- 2026-05-30: Closed the companion rectangular Frobenius norm-growth
  dependency: `frobNormRect_eq_frobNormFn`,
  `frobNormRect_matMulRectLeft_le`, and
  `frobNormRect_matMulRectRight_le` reuse Mathlib's Frobenius
  submultiplicativity for compatible square left/right factors.  This is
  route-A substrate for a rectangular one-step Householder/orthogonal
  perturbation-accumulation proof, not the concrete QR theorem itself.

- 2026-05-30: Closed the rectangular square-left-action algebra dependency:
  `matMulRectLeft_id`, `matMulRectLeft_assoc`,
  `matMulRectLeft_add_left`, and `matMulRectLeft_add_right`.  These are the
  exact identity/associativity/additivity facts needed by the rectangular
  one-step orthogonal-transformation accumulation proof.

- 2026-05-30: Closed the rectangular one-step orthogonal-transformation
  accumulation theorem `rect_orthogonal_sequence_one_step` in
  `Algorithms/QR/HouseholderQR.lean`.  It generalizes the square
  Householder one-step proof to `m × n` data and gives the rectangular
  Frobenius growth bound.  The remaining red QR bottleneck is the multi-step
  rectangular Householder/preconditioner theorem and solve handoff, not this
  one-step algebra.

- 2026-05-30: Closed the supplied-transformation multi-step rectangular
  accumulation theorem `rect_orthogonal_sequence_geometric`.  It iterates the
  one-step theorem and proves the rigorous geometric radius
  `((1+c)^r - 1) ||A||_F`.  This is not yet a concrete `fl_householder_qr`
  implementation or rectangular solve theorem.

- 2026-05-30: Closed the orthogonal least-squares handoff:
  `rectLSGram_matMulRectLeft_orthogonal`,
  `rectLSRhs_matMulRectLeft_orthogonal`, and
  `RectLSNormalEquations.of_orthogonal_left`.  Orthogonal row transformations
  preserve the rectangular Gram matrix, RHS, and normal equations, so a future
  rectangular QR theorem can feed the existing `RectLSNormalEquations` bridge.

- 2026-05-30: Closed the vector/right-hand-side companion to the rectangular
  QR accumulation route.  `vecNorm2Sq_orthogonal`, `vecNorm2_orthogonal`,
  `matMulVec_id`, `matMulVec_add_left`, and `matMulVec_add_right` provide the
  shared vector algebra; `orthogonal_vector_sequence_one_step` and
  `orthogonal_vector_sequence_geometric` prove the supplied-transformation
  perturbation accumulation for `b` with radius
  `((1+c)^r - 1) ||b||_2`.  This closes the transformed-RHS dependency, but
  not the concrete rectangular `fl_householder_qr` / triangular solve theorem.

- 2026-05-30: Closed the exact top-block QR solve handoff:
  `RectLSNormalEquations.of_rowwise_normal` and
  `RectLSNormalEquations.of_top_solve_zero_bottom`.  If transformed QR data has
  top block `R`, zero lower matrix block, and the computed vector solves
  `R x = c`, then it satisfies the rectangular normal equations for the
  transformed problem; the lower transformed RHS is unrestricted.  This still
  leaves the concrete floating-point rectangular Householder/preconditioner
  implementation and rounded triangular solve theorem open.

- 2026-05-30: Closed the rounded top-block triangular solve handoff using the
  existing `backSub_backward_error` theorem.  `rectTopBlock` embeds an `n x n`
  top block into an `m x n` zero-lower matrix, and
  `RectLSNormalEquations.exists_topBlock_of_fl_backSub` proves that
  `fl_backSub fp n R c` satisfies rectangular normal equations for the
  perturbed top block `R + Delta R` with
  `|Delta R_ij| <= gamma fp n * |R_ij|`.  The red QR bottleneck is now the
  concrete rectangular Householder/preconditioner implementation and
  transformed-RHS/top-block shape theorem.

- 2026-05-30: Closed the common-orthogonal-factor accumulation substrate for
  the red rectangular QR bottleneck.  The new
  `rect_orthogonal_matrix_vector_sequence_one_step` and
  `rect_orthogonal_matrix_vector_sequence_geometric` theorems apply the same
  supplied perturbed orthogonal transformations to an `m x n` matrix and an
  `m`-vector, producing one shared orthogonal factor `Q` plus perturbations
  `Delta A`, `Delta b` with geometric radii.  This avoids combining unrelated
  existential `Q`s from separate matrix/vector accumulation theorems.  The
  remaining red dependency is the pulled-back top-block/triangular-solve QR
  theorem and then a concrete `fl_householder_qr`/preconditioner
  implementation.

- 2026-05-30: Closed the pulled-back top-block triangular-solve dependency.
  `RectLSNormalEquations.exists_original_perturbation_of_commonQ_topBlock_fl_backSub`
  combines common-`Q` transformed data, `[R;0]` top-block shape,
  `fl_backSub`, and the orthogonal normal-equation handoff.  It produces
  `Delta A_total = Delta A + Q [Delta R;0]`, proves rectangular normal
  equations for `(A+Delta A_total,b+Delta b)`, and bounds
  `||Delta A_total||_F` by `||Delta A||_F + ||[Delta R;0]||_F`.  The
  concrete rectangular Householder/preconditioner implementation remains open.

- 2026-05-30: Closed the embedded top-block norm-budget dependency.  Added
  `frobNormSqRect_abs` and `frobNormRect_abs` in `MatrixAlgebra.lean`, plus
  `rectTopBlock_frobNorm_perturb_bound`,
  `rectTopBlock_frobNorm_perturb_bound_of_gamma`, and
  `RectLSNormalEquations.exists_original_perturbation_of_commonQ_topBlock_fl_backSub_gamma_bound`
  in `LSQRSolve.lean`.  The strengthened pullback theorem now bounds
  `||Delta A_total||_F <= ||Delta A||_F + gamma fp n ||[R;0]||_F`, so the
  red QR bottleneck is narrowed to the concrete rectangular
  Householder/preconditioner implementation theorem.

- 2026-05-30: Closed the supplied-transform route into the local QR
  least-squares solver specification.  Added
  `LSQRSolveBackwardError.of_commonQ_topBlock_fl_backSub_gamma_bound_normBudget`
  and
  `LSQRSolveBackwardError.of_rect_orthogonal_sequence_topBlock_fl_backSub_gamma_bound_normBudget`.
  These compose the common-`Q` top-block pullback, rounded `fl_backSub`,
  gamma top-block norm budget, and rectangular induced Gram/RHS norm-budget
  adapter into `LSQRSolveBackwardError`.  This is still a supplied-transform
  theorem; a concrete `fl_householder_qr`/preconditioner implementation
  theorem remains the active red bottleneck.

- 2026-05-30: Closed the first exact embedded-reflector substrate for the
  concrete rectangular Householder QR route.  Added
  `householder_row_eq_id_of_zero_prefix`,
  `householder_col_eq_id_of_zero_prefix`,
  `matMulVec_householder_eq_self_of_zero_prefix`,
  `matMul_householder_eq_self_row_of_zero_prefix`, and
  `matMulRectLeft_householder_eq_self_row_of_zero_prefix` in
  `HouseholderSpec.lean`.  These prove that a full-size Householder reflector
  whose vector vanishes on a prefix acts as the identity on that prefix for
  rows, columns, vectors, and square/rectangular matrix rows.  Remaining
  route-A foundations are active-column zeroing for the constructed reflector
  and a common rounded panel/update theorem for applying the same reflector to
  both `A` and `b`.
- 2026-05-30: Closed the exact active-column Householder substrate for the
  concrete rectangular QR route.  Added `householderActiveVector`,
  `householderBeta`, `householderActiveVector_inner_x`,
  `householderActiveVector_inner_self`,
  `householderActiveVector_inner_self_eq_two_inner_x`,
  `householderBeta_mul_activeVector_inner_x`,
  `matMulVec_householder_activeVector_eq_alpha_basis`, and
  `matMulVec_householder_activeVector_eq_zero_of_ne`.  These prove that the
  exact reflector built from `v = x - alpha e_p` maps `x` to `alpha e_p`, and
  hence zeros off-pivot active-column entries, under explicit
  `alpha^2 = ||x||_2^2` and `v^T v != 0`.  The remaining route-A foundation is
  the common rounded panel/update theorem for applying the same reflector to
  both `A` and `b`, followed by concrete rectangular implementation assembly.
- 2026-05-30: Corrected and narrowed the common rounded panel/update interface
  for the rectangular QR route.  Added `HouseholderPanelAppError`, a stronger
  contract than vector-only `HouseholderAppError`, requiring one shared
  perturbation matrix `Delta P` for both the rectangular matrix-panel update
  and the right-hand-side update.  Added
  `householderPanelAppError_rect_orthogonal_matrix_vector_sequence_geometric`,
  which feeds a sequence of these contracts into the existing common-`Q`
  accumulation theorem.  The remaining red-bottleneck dependency is now the
  low-level floating-point Householder panel implementation proof that
  discharges `HouseholderPanelAppError`, then the final rectangular QR assembly.
- 2026-05-30: Corrected the active rectangular QR route after checking
  Higham's columnwise Householder QR proof source.  The shared-`Delta P`
  contract remains as a strong optional interface, but the source-faithful
  theorem permits a different perturbation matrix for each panel column.
  Added `HouseholderColumnwisePanelAppError`,
  `HouseholderColumnwisePanelAppError.of_vector_applications`,
  `orthogonal_vector_sequence_one_step_fixedQ`,
  `rect_orthogonal_columnwise_vector_sequence_geometric`, and
  `householderColumnwisePanelAppError_rect_orthogonal_columnwise_vector_sequence_geometric`.
  The active red-bottleneck dependency is now the low-level rounded
  Householder vector-application theorem proving `HouseholderAppError` for an
  actual `fl_householder_apply` primitive, then the final rectangular QR
  assembly.
- 2026-05-30: Closed the exact algebraic adapter dependency for the active
  rectangular QR bottleneck.  Added rank-one norm bridges
  `frobNormSq_rankOne`, `frobNorm_rankOne`, `frobNorm_rankOne_smul`, and
  `frobNorm_rankOne_div_vecNorm2Sq` in `MatrixAlgebra.lean`, plus
  `HouseholderAppError.of_forward_error` and
  `HouseholderColumnwisePanelAppError.of_forward_errors` in
  `HouseholderSpec.lean`.  This converts a future rounded Householder
  primitive forward-error theorem into the local backward-error contracts
  without a hidden nonzero-input hypothesis.  The active remaining dependency
  is now the actual rounded dot/scale/subtract primitive forward-error theorem,
  then final rectangular QR/preconditioner assembly.
- 2026-05-30: Closed a concrete explicit-matrix rounded Householder
  application route.  Added `vecNorm2Sq_abs` and `vecNorm2_abs` in
  `MatrixAlgebra.lean`, and created `Algorithms/QR/HouseholderApply.lean`
  with `fl_householderApplyExplicit`, `fl_householderApplyExplicitPanel`,
  `fl_householderApplyExplicit_forward_error_bound`,
  `fl_householderApplyExplicit_HouseholderAppError`, and
  `fl_householderApplyExplicitPanel_HouseholderColumnwisePanelAppError`.
  This route reuses `fl_matVec`/`matVec_error_bound` for an already formed
  reflector matrix and instantiates the vector and columnwise contracts.  The
  compact dot/scale/subtract Householder primitive and final rectangular QR
  assembly remain open.
- 2026-05-30: Closed the compact rounded Householder dot/scale/subtract vector
  primitive dependency.  `Algorithms/QR/HouseholderApply.lean` now contains
  `householderDot`, `householderAbsDotBudget`,
  `fl_householderApplyCompact`, `fl_householderApplyCompactPanel`,
  `householderCompactComponentBudget`, `matMulVec_householder_eq_compact`,
  `fl_householderApplyCompact_componentwise_error_bound`,
  `fl_householderApplyCompact_forward_error_bound`,
  `fl_householderApplyCompact_HouseholderAppError_of_budget`, and
  `fl_householderApplyCompactPanel_HouseholderColumnwisePanelAppError_of_budget`.
  The budget is explicit and deterministic; the relative contract uses a
  visible budget-domination condition, not a hidden concentration/stability
  hypothesis.  The active red bottleneck is now only the final rectangular
  Householder QR/preconditioner assembly: instantiate compact applications
  across the panel/RHS, prove transformed `[R;0]` and top-RHS linkage, and
  compose the pulled-back perturbation/triangular-solve handoff.
- 2026-05-30: Closed the compact sequence-glue dependency for the rectangular
  QR bottleneck.  `HouseholderQR.lean` now imports `HouseholderApply.lean` and
  proves
  `fl_householderApplyCompactPanel_rect_orthogonal_columnwise_vector_sequence_geometric`:
  any supplied sequence of compact rounded panel/RHS Householder updates whose
  explicit budgets are dominated by `c` feeds the existing source-faithful
  columnwise geometric accumulation theorem.  This supplies a common
  accumulated orthogonal factor and column/RHS perturbation radii, but still
  assumes the QR loop's concrete reflector sequence and transformed `[R;0]`
  shape/top-RHS invariants.
- 2026-05-30: Closed the compact sequence-to-solver-spec handoff dependency.
  `MatrixAlgebra.lean` now has
  `frobNormSqRect_eq_sum_vecNorm2Sq_cols` and
  `frobNormRect_le_of_col_vecNorm2_le`, converting columnwise Euclidean
  perturbation bounds into a rectangular Frobenius bound.  `LSQRSolve.lean`
  now proves
  `LSQRSolveBackwardError.of_compact_householder_sequence_topBlock_fl_backSub_gamma_bound_normBudget`,
  composing the compact Householder sequence theorem with the existing
  top-block `fl_backSub` pullback into the local `LSQRSolveBackwardError`
  interface.  The active red bottleneck is now narrowed to the concrete loop
  invariants that prove the final `[R;0]` shape, top-RHS linkage, and
  triangular/nonzero-diagonal facts for the actual rectangular Householder or
  preconditioner implementation.
- 2026-05-30: Closed the exact trailing Householder shape dependency for the
  rectangular QR bottleneck.  `HouseholderSpec.lean` now has
  `householderPrefixPart`, `householderTrailingPart`,
  `householderTrailingNorm2Sq`, `householderTrailingActiveVector`,
  support/split lemmas,
  `matMulVec_householder_eq_self_of_zero_prefix_support`,
  `matMulVec_householder_trailingActiveVector_eq_prefix_alpha_zero`, and
  `matMulVec_householder_trailingActiveVector_eq_zero_of_pivot_lt`.
  `HouseholderQR.lean` now proves
  `exact_trailing_householder_sequence_lower_zero` and
  `rectangular_topBlock_shape_facts_of_lower_zero`.  This corrects the exact
  QR shape route: the reflector vector is built from the trailing pivot
  segment with a zero prefix, preserving entries above the pivot and zeroing
  entries below it.  The remaining red dependency is the rounded stored-`R`/RHS
  compact loop assembly plus a formal nonzero-diagonal/rank or nonbreakdown
  condition.
- 2026-05-30: Closed the stored rounded QR shape dependency with
  `fl_householderStoredPanelStep`, `fl_householderStoredRhsStep`,
  `fl_householderStoredPanel_sequence_lower_zero`, and
  `fl_householderStoredPanel_sequence_topBlock_shape_facts`.  The stored panel
  step preserves completed columns and explicitly writes zeros below each pivot,
  so final `[R;0]`, `cTop`, and upper-triangular facts are now available for
  the rounded loop shape.  The remaining red dependency is the stored-step
  `HouseholderColumnwisePanelAppError` perturbation theorem plus
  nonzero-diagonal/rank or nonbreakdown.
- 2026-05-30: Closed the stored-step perturbation contract dependency with
  `householderCompactComponentBudget_nonneg`,
  `fl_householderStoredRhsStep_componentwise_error_bound`,
  `fl_householderStoredRhsStep_forward_error_bound`,
  `fl_householderStoredPanelStep_column_componentwise_error_bound`,
  `fl_householderStoredPanelStep_column_forward_error_bound`, and
  `fl_householderStoredPanelStep_HouseholderColumnwisePanelAppError_of_budget`.
  The theorem proves that the stored panel/RHS step satisfies the
  source-faithful columnwise Householder contract under explicit
  preservation, pivot-zeroing, RHS-prefix, and budget-domination hypotheses.
  The remaining red dependency is the concrete trailing-reflector loop theorem
  that discharges those hypotheses for each step, plus the nonzero
  diagonal/rank or nonbreakdown condition.
- 2026-05-30: Closed the one-step concrete trailing-reflector discharge
  dependency with
  `fl_householderStoredTrailingPanelStep_HouseholderColumnwisePanelAppError_of_budget`.
  The theorem uses the pre-step lower-zero invariant and the exact trailing
  Householder algebra to discharge completed-column preservation, RHS-prefix
  preservation, and pivot-column zeroing for one stored rounded QR step.  The
  remaining red dependency is the multi-step stored trailing loop theorem that
  invokes this step theorem at every pivot and the nonzero diagonal/rank or
  nonbreakdown condition.
- 2026-05-30: Closed the multi-step stored trailing Householder perturbation
  dependency with
  `fl_householderStoredTrailingPanel_rect_orthogonal_columnwise_vector_sequence_geometric`.
  The theorem maintains the stored lower-zero invariant, invokes the one-step
  trailing-reflector theorem at each pivot, and feeds the resulting
  columnwise contracts into the common-`Q` geometric accumulation theorem.  It
  yields one orthogonal factor, columnwise data perturbation radii
  `((1+c)^n-1)||A(:,j)||_2`, and RHS radius `((1+c)^n-1)||b||_2`.  The active
  red dependency is now the stored-loop solver-spec handoff into
  `LSQRSolveBackwardError`, plus the nonzero diagonal/rank or nonbreakdown
  condition.
- 2026-05-30: Closed the stored trailing Householder loop solver-spec handoff
  with
  `LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_normBudget`.
  The theorem reads the final `R` and `cTop` from `A_hat n` and `b_hat n`,
  reuses `fl_householderStoredPanel_sequence_topBlock_shape_facts` and
  `fl_householderStoredTrailingPanel_rect_orthogonal_columnwise_vector_sequence_geometric`,
  converts the columnwise data radii to Frobenius form, and invokes the
  existing common-`Q`/top-block `fl_backSub` pullback into
  `LSQRSolveBackwardError`.  The active red dependency is now exactly the
  nonzero diagonal/rank or nonbreakdown proof for the computed top block.
- 2026-05-30: Reduced the stored QR nonzero-diagonal bottleneck to a concrete
  per-pivot FP nonbreakdown condition with
  `fl_householderStoredTrailingPanelStep_diag_nonzero_of_budget_lt_abs_alpha`,
  `fl_householderStoredPanel_sequence_diag_nonzero_of_step_diag_nonzero`,
  `fl_householderStoredTrailingPanel_sequence_diag_nonzero_of_budget_lt_abs_alpha`,
  and
  `LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_normBudget_of_pivot_error_lt_abs_alpha`.
  The new route proves final top-block diagonal nonzeroness whenever each
  stored diagonal component budget is strictly smaller than `|alpha_k|`.  The
  active red dependency is now deriving those inequalities from a formal
  rank/conditioning/nonbreakdown invariant.
- 2026-05-30: Reduced the stored QR Householder denominator side condition
  `v^T v != 0` to the scalar pivot condition `A_hat[k,k] != alpha_k`.
  The new theorem
  `householderTrailingActiveVector_inner_self_ne_zero_of_pivot_ne_alpha`
  proves denominator nonzeroness for the trailing active vector; the stored QR
  theorem `fl_householderStoredTrailingPanel_sequence_diag_nonzero_of_pivot_ne_alpha`
  and the LSQRSolve wrapper
  `LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_normBudget_of_pivot_ne_alpha_and_pivot_error_lt_abs_alpha`
  compose it with the existing pivot-budget nonbreakdown bridge.  This is not
  a rank theorem; deriving `A_hat[k,k] != alpha_k` and
  `budget_k < |alpha_k|` from rank/conditioning remains open.
- 2026-05-30: Reduced the scalar stored QR pivot condition
  `A_hat[k,k] != alpha_k` to the standard Householder sign-choice facts.  New
  theorems
  `householder_pivot_ne_alpha_of_trailingNorm2Sq_pos_mul_nonpos` and
  `householderTrailingActiveVector_inner_self_ne_zero_of_trailingNorm2Sq_pos_mul_nonpos`
  prove denominator nonzeroness from
  `alpha_k^2 = ||A_hat_k(k:m,k)||_2^2`, positive trailing norm, and
  `alpha_k * A_hat[k,k] <= 0`; the stored QR theorem
  `fl_householderStoredTrailingPanel_sequence_diag_nonzero_of_trailingNorm_pos_mul_nonpos`
  and the LSQRSolve wrapper
  `LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_normBudget_of_trailingNorm_pos_mul_nonpos_and_pivot_error_lt_abs_alpha`
  compose this with the existing pivot-budget nonbreakdown bridge.  The active
  red dependency is now deriving positive trailing-column norms and
  `budget_k < |alpha_k|` from rank/conditioning/nonbreakdown.
- 2026-05-30: Added scalar lower-bound bridges for the remaining stored QR
  nonbreakdown route.  `householderTrailingNorm2Sq_pos_of_exists_ne` and
  `householderTrailingNorm2Sq_pos_of_pivot_ne_zero` reduce positive active
  trailing norm to a concrete nonzero trailing entry; `abs_alpha_eq_sqrt_trailingNorm2Sq`
  and `budget_lt_abs_alpha_of_lt_sqrt_trailingNorm2Sq` convert square-root
  trailing-norm lower bounds into the stored-loop condition
  `budget_k < |alpha_k|`.  The red dependency is now specifically a
  rank/conditioning/nonbreakdown invariant that supplies those two scalar
  facts for the computed loop.
- 2026-05-30: Added the first prefix-span bridge for the stored QR rank route.
  `qrColumnNotInPreviousSpan` plus
  `qrPrefixSupportSpannedByPreviousColumns` imply a nonzero active trailing
  entry by `exists_active_trailing_entry_ne_of_column_notInPreviousSpan`, hence
  positive trailing norm by
  `householderTrailingNorm2Sq_pos_of_column_notInPreviousSpan`.  The stored QR
  wrapper
  `fl_householderStoredTrailingPanel_sequence_diag_nonzero_of_span_nonbreakdown_sqrt_budget`
  combines prefix-span/column-independence, sign choice, and square-root budget
  into final nonzero diagonal entries.  Remaining QR rank work: prove the
  prefix-span and column-independence invariants, and budget lower bounds, from
  an invertible triangular/full-rank/nonbreakdown assumption.
- 2026-05-30: Added a prefix-span coefficient bridge for the stored QR rank
  route.  `qrPrefixBasisCoefficientMatrix` records concrete leading-block
  coefficients reproducing the prefix coordinate basis vectors, and
  `qrPrefixSupportSpannedByPreviousColumns_of_prefixBasisCoefficientMatrix`
  proves that this witness plus the QR lower-zero shape supplies
  `qrPrefixSupportSpannedByPreviousColumns`.  The remaining rank bottleneck is
  now producing those coefficient witnesses from a nonsingular/right-invertible
  leading block, proving current-column independence, and obtaining budget
  lower bounds.
- 2026-05-30: Added a leading-column left-inverse bridge for the same QR route.
  `qrLeadingColumnLeftInverse` records a dual coefficient family selecting the
  first `k+1` columns, and
  `qrColumnNotInPreviousSpan_of_leadingColumnLeftInverse` proves
  `qrColumnNotInPreviousSpan`.  Remaining QR rank work is producing the
  basis/left-inverse witnesses from a full-rank or triangular nonbreakdown
  invariant, plus quantitative budget lower bounds.
- 2026-05-30: Composed the QR coefficient and left-inverse witness bridges.
  `exists_active_trailing_entry_ne_of_leading_witnesses`,
  `householderTrailingNorm2Sq_pos_of_leading_witnesses`, and
  `fl_householderStoredTrailingPanel_sequence_diag_nonzero_of_leading_witnesses_sqrt_budget`
  prove active trailing nonbreakdown and stored-loop diagonal nonbreakdown from
  concrete leading witnesses plus the visible square-root budget.  This removes
  the abstract prefix-span/column-independence hypotheses from that stored-loop
  theorem but still does not derive the witnesses or the quantitative budget
  lower bound from full rank alone.
- 2026-05-30: Added the QR leading-block inverse orientation adapter.
  `qrPreviousLeadingBlockTranspose` names the transposed leading block and
  `qrPrefixBasisCoefficientMatrix_of_leftInverse_previousLeadingBlockTranspose`
  reuses the repository's `IsLeftInverse` predicate to produce the prefix
  coefficient witness.  This closes the coefficient-witness-from-inverse
  adapter but still does not prove existence of that inverse from rank or
  triangular nonbreakdown.
- 2026-05-30: Added the QR leading-block inverse padding adapter.
  `qrLeadingBlock` names the actual leading `(k+1) x (k+1)` block and
  `qrLeadingColumnLeftInverse_of_leftInverse_leadingBlock` pads a local
  `IsLeftInverse` witness by zeros outside the first `k+1` rows to produce
  the ambient `qrLeadingColumnLeftInverse` witness.  This closes the finite
  ambient-row bookkeeping for column independence, but still does not prove
  that the local leading block inverse exists from a rank/triangular invariant.
- 2026-05-30: Added the QR local-inverse composition bridge.
  `exists_active_trailing_entry_ne_of_leading_block_leftInverses`,
  `householderTrailingNorm2Sq_pos_of_leading_block_leftInverses`, and
  `fl_householderStoredTrailingPanel_sequence_diag_nonzero_of_leading_block_leftInverses_sqrt_budget`
  let the stored QR nonbreakdown route consume local `IsLeftInverse` witnesses
  for the previous and current leading blocks directly.  Remaining open
  dependencies are existence of those local inverses from a formal rank or
  triangular invariant and a square-root trailing-norm budget lower bound.
- 2026-05-30: Added the determinant/rank bridge for those QR local inverse
  witnesses.  `nonsingInv`, `isLeftInverse_nonsingInv_of_det_isUnit`, and
  `exists_isLeftInverse_of_det_ne_zero` wrap Mathlib's nonsingular inverse and
  convert nonzero determinants into the repository's `IsLeftInverse`
  predicate.  The QR wrappers
  `qrPrefixBasisCoefficientMatrix_of_det_ne_zero_previousLeadingBlockTranspose`,
  `qrLeadingColumnLeftInverse_of_det_ne_zero_leadingBlock`,
  `exists_active_trailing_entry_ne_of_leading_block_det_ne_zero`,
  `householderTrailingNorm2Sq_pos_of_leading_block_det_ne_zero`, and
  `fl_householderStoredTrailingPanel_sequence_diag_nonzero_of_leading_block_det_ne_zero_sqrt_budget`
  replace raw inverse-witness assumptions by nonzero determinants of the local
  leading blocks.  Remaining open dependencies are determinant/rank
  preservation for the computed leading blocks and the square-root
  trailing-norm budget lower bound.  The determinant/rank bridge itself has
  two weak-component passes.
- 2026-05-30: Added the triangular determinant route for QR local leading
  blocks.  `det_ne_zero_of_upper_triangular_diag_ne_zero` and
  `det_ne_zero_of_lower_triangular_diag_ne_zero` are shared MatrixAlgebra
  lemmas; `qrPreviousLeadingBlockTranspose_det_ne_zero_of_upper_triangular_diag_ne_zero`
  and `qrLeadingBlock_det_ne_zero_of_upper_triangular_diag_ne_zero` instantiate
  them for the QR blocks.  This is a visible principal-minor/nonzero-diagonal
  route, not a generic full-rank theorem.  It has two clean weak-component
  passes; the red QR bottleneck now needs either an explicit route choice to
  keep these local assumptions visible or a source-faithful prefix-span/full-rank
  invariant plus a square-root trailing-norm budget lower bound.
- 2026-05-30: Added a solver-facing nonsingular-leading-block QR wrapper:
  `LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_normBudget_of_leading_block_det_ne_zero_sqrt_budget`.
  It feeds nonzero local leading-block determinants, QR lower-zero shape, sign
  choice, square-root pivot budgets, compact panel/RHS budget domination, and
  final Gram/RHS norm budgets into the local `LSQRSolveBackwardError`
  certificate.  This dependency has two clean weak-component passes;
  determinant/rank facts and the square-root budget lower bound remain the
  active red bottleneck.
- 2026-05-30: Added and two-pass validated the triangular-leading-block QR solver wrapper:
  `LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_normBudget_of_triangular_leading_blocks_sqrt_budget`.
  It composes the triangular determinant adapters with the solver-facing
  nonsingular-leading-block certificate, so visible upper-triangular local
  shape plus nonzero previous/current leading diagonals can feed
  `LSQRSolveBackwardError` directly.  This is a domain theorem, not a generic
  full-rank result; the source-faithful rank/conditioning route and
  square-root budget lower bound remain open.  The second PDF validation used
  a Ghostscript-repaired exact-path PDF artifact because the raw pdfTeX output
  triggered Poppler page-tree warnings after page 79.
- 2026-05-30: Added and two-pass validated the active-entry square-root budget bridge in
  `HouseholderSpec.lean`: `abs_entry_le_sqrt_householderTrailingNorm2Sq_of_pivot_le`
  and `budget_lt_sqrt_householderTrailingNorm2Sq_of_lt_abs_active_entry`.
  These reuse the local coordinate-to-vector norm bound to show that
  `budget < |x_i|` for an active trailing entry implies the square-root
  trailing-norm budget.  This is progress on the QR red bottleneck, but it
  still leaves the source-faithful lower-bound derivation from rank,
  nonbreakdown, or conditioning open.
- 2026-05-30: Added the stored-loop active-entry-budget QR nonbreakdown wrapper
  `fl_householderStoredTrailingPanel_sequence_diag_nonzero_of_span_nonbreakdown_active_entry_budget`
  in `HouseholderQR.lean`.  It uses the active-entry scalar bridge to remove the
  square-root expression from the prefix-span stored-loop wrapper, while keeping
  the active-entry magnitude lower bound visible as a domain/nonbreakdown
  condition.  It now has two clean weak-component passes.
- 2026-05-30: Added the solver-facing active-entry-budget QR wrapper
  `LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_normBudget_of_span_nonbreakdown_active_entry_budget`
  in `LSQRSolve.lean`.  It feeds prefix-span nonbreakdown, sign choice,
  Householder normalization, compact panel/RHS budget domination, a visible
  active-entry magnitude budget, and final Gram/RHS budgets into the local
  `LSQRSolveBackwardError` certificate.  It now has two clean weak-component
  validation passes.  The remaining red bottleneck is the source-faithful
  derivation of the active-entry lower bound from rank, nonbreakdown, or
  conditioning, or an explicit route choice to keep that lower bound visible.
- 2026-05-30: Added and two-pass validated the dimensioned norm-square-budget
  bridge for the same QR bottleneck.  The lemma
  `exists_active_entry_budget_lt_abs_of_dim_mul_budget_sq_lt_trailingNorm2Sq`
  proves that `m * budget^2 < trailingNorm2Sq` gives an active entry with
  `budget < |x_i|`.  The stored-loop wrapper
  `fl_householderStoredTrailingPanel_sequence_diag_nonzero_of_span_nonbreakdown_trailingNorm2Sq_budget`
  and solver wrapper
  `LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_normBudget_of_span_nonbreakdown_trailingNorm2Sq_budget`
  use this to replace the raw active-entry witness by a dimensioned per-pivot
  norm-square margin.  This is not a conditioning theorem; the next red
  dependency is deriving that margin from a formal conditioning/nonbreakdown
  invariant, or explicitly keeping it as a domain assumption.
- 2026-05-30: Added and two-pass validated the leading-dual norm lower-bound
  route.  The lemma
  `householderTrailingNorm2Sq_ge_inv_leading_dual_norm_budget` proves that a
  prefix-span invariant plus a pivot-selecting leading dual row with
  `||L_last||_2^2 <= K` yields `1 / K <= trailingNorm2Sq`.  The stored-loop
  and solver wrappers
  `fl_householderStoredTrailingPanel_sequence_diag_nonzero_of_span_nonbreakdown_leading_dual_norm_budget`
  and
  `LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_normBudget_of_span_nonbreakdown_leading_dual_norm_budget`
  feed this into QR diagonal nonbreakdown and the local least-squares
  `LSQRSolveBackwardError` certificate under `m * budget_k^2 < 1 / K_k`.  This
  narrows the quantitative red bottleneck to constructing/bounding that dual
  from a concrete inverse/conditioning theorem, or keeping the dual-norm budget
  visible.
- 2026-05-30: Added and two-pass validated the local leading-block inverse
  row-norm route.  The new padding lemmas
  `vecNorm2Sq_qrLeadingRow_padded_eq` and
  `qrLeadingColumnLeftInverse_padded_row_norm_sq_eq` convert the last row of a
  local left inverse for `qrLeadingBlock` into the ambient dual row without
  changing squared norm.  The stored-loop wrapper
  `fl_householderStoredTrailingPanel_sequence_diag_nonzero_of_span_nonbreakdown_leadingBlock_leftInverse_norm_budget`
  and solver wrapper
  `LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_normBudget_of_span_nonbreakdown_leadingBlock_leftInverse_norm_budget`
  now feed the local inverse row budget into QR nonbreakdown and
  `LSQRSolveBackwardError`.  This still leaves deriving the inverse-row norm
  budget from determinant margins, SVD, condition number, or inverse-norm
  hypotheses as the active red-bottleneck dependency.
- 2026-05-30: Added and two-pass validated the local leading-block inverse
  Frobenius-norm route.  Shared matrix algebra now has
  `vecNorm2Sq_row_le_frobNormSq` and `vecNorm2Sq_row_le_frobNorm_sq`; QR/LS
  wrappers
  `fl_householderStoredTrailingPanel_sequence_diag_nonzero_of_span_nonbreakdown_leadingBlock_leftInverse_frobNorm_budget`
  and
  `LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_normBudget_of_span_nonbreakdown_leadingBlock_leftInverse_frobNorm_budget`
  use the local inverse Frobenius budget `||C_k||_F^2 <= K_k` plus
  `m * budget_k^2 < 1 / K_k`.  Validation used a targeted `LSQRSolve` build
  followed by full `lake build`, executable lookup, placeholder scan,
  `git diff --check`, axiom audit, and PDF compile/repair/text/render
  inspection.  This still does not derive the inverse Frobenius budget from
  determinant margin/SVD/condition number.
- 2026-05-30: Added and two-pass validated the local leading-block inverse
  infinity-norm route.  Shared matrix algebra now has
  `abs_coord_le_sum_abs`, `vecNorm2Sq_le_sum_abs_sq`,
  `frobNormSq_le_nat_mul_infNorm_sq`, and
  `frobNorm_sq_le_nat_mul_infNorm_sq`, proving
  `||C_k||_F^2 <= (k+1)||C_k||_\infty^2`.  QR/LS wrappers
  `fl_householderStoredTrailingPanel_sequence_diag_nonzero_of_span_nonbreakdown_leadingBlock_leftInverse_infNorm_budget`
  and
  `LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_normBudget_of_span_nonbreakdown_leadingBlock_leftInverse_infNorm_budget`
  use the visible local inverse infinity-norm budget
  `(k+1)||C_k||_\infty^2 <= K_k` plus `m * budget_k^2 < 1 / K_k`.
  Validation used a targeted `LSQRSolve` build followed by full `lake build`,
  executable lookup, placeholder scan, `git diff --check`, axiom audit, and
  PDF compile/repair/text/render inspection.  The next red-bottleneck
  dependency is deriving the inverse infinity-norm budget from triangular
  inverse estimates, determinant margin, SVD, condition number, or keeping that
  budget explicitly visible.
- 2026-05-30: Implemented the diagonal-dominant triangular inverse route for
  the QR local inverse budget.  `InverseBounds.lean` now has
  `triInv_infNorm_upperBound` and
  `triInv_infNorm_sq_budget_of_diagDominantUpper`, and `LSQRSolve.lean` has
  `LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_normBudget_of_span_nonbreakdown_diagDominant_leadingBlock_invNorm_budget`.
  Targeted builds for `InverseBounds` and `LSQRSolve` passed, followed by full
  `lake build`.  Two weak-component passes are now clean: lookup, placeholder
  scan, `git diff --check`, axiom audit, PDF compile/repair/text extraction,
  and rendered page inspection all succeeded.  This closes the
  diagonal-dominant triangular inverse route as a visible-domain theorem family;
  the remaining red-bottleneck work is to derive or choose the domain
  assumptions for computed QR leading blocks.
- 2026-05-30: Implemented the determinant-facing diagonal-dominant QR route.
  `MatrixAlgebra.lean` now proves determinant-to-`IsInverse` adapters for
  `nonsingInv`; `InverseBounds.lean` has
  `triInv_infNorm_sq_budget_of_diagDominantUpper_det_ne_zero`; and
  `LSQRSolve.lean` has
  `LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_normBudget_of_span_nonbreakdown_diagDominant_leadingBlock_det_ne_zero_invNorm_budget`.
  Two weak-component validation passes passed.  This closes the explicit
  inverse-witness dependency for the diagonal-dominant branch, while leaving
  diagonal dominance, determinant nonzero, and the diagonal-minimum budget as
  visible assumptions for the next red-bottleneck step.
- 2026-05-30: Implemented the determinant-facing inverse-norm QR route.
  `LSQRSolve.lean` now has
  `LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_normBudget_of_span_nonbreakdown_leadingBlock_det_ne_zero_infNorm_budget`,
  which uses `det S_k != 0` to instantiate the inverse-\(\infty\) route with
  `C_k = nonsingInv S_k` while keeping the inverse-norm budget visible.
  Targeted build and full-build validation now have two clean
  weak-component passes: executable lookup, placeholder scan,
  `git diff --check`, axiom audit, PDF compile/repair/text extraction, and
  rendered page inspection all succeeded.  The remaining red QR bottleneck is
  to derive the inverse-\(\infty\) budget from SVD, condition-number,
  determinant-margin, or computed-loop assumptions, or to keep that budget
  explicitly visible.
- 2026-05-30: Implemented the condition-number route for the local QR inverse
  budget.  `PerturbationTheory.lean` now proves
  `infNorm_eq_sup_row_sum`, `kappaInf_eq_infNorm_mul_infNorm`,
  `infNorm_inv_le_of_kappaInf_le_and_norm_lower`, and
  `infNorm_sq_budget_of_kappaInf_le_and_norm_lower`, and `LSQRSolve.lean` has
  `LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_normBudget_of_span_nonbreakdown_leadingBlock_det_ne_zero_kappaInf_budget`.
  The route derives `(k+1)||nonsingInv S_k||_\infty^2 <= K_k` from
  `0 < rho_k <= ||S_k||_\infty`, a visible
  `kappaInf S_k (nonsingInv S_k) <= kappa_k` bound, and
  `(k+1)(kappa_k/rho_k)^2 <= K_k`.  Two weak-component passes passed:
  targeted/full builds, executable lookup, placeholder scan, `git diff
  --check`, axiom audit, PDF compile/repair/text extraction, and rendered page
  inspection were clean.  This closes the condition-number route as a visible
  dependency; the remaining red-bottleneck work is deriving local `rho_k`,
  `kappa_k`, determinant, and QR-loop assumptions from SVD/determinant-margin
  or computed-loop invariants, or keeping them explicit.
- 2026-05-30: Implemented the self-norm specialization of the local QR
  condition-number route.  `MatrixAlgebra.lean` now proves
  `infNorm_pos_of_det_ne_zero`; `PerturbationTheory.lean` proves
  `infNorm_inv_le_of_kappaInf_le_and_det_ne_zero` and
  `infNorm_sq_budget_of_kappaInf_le_and_det_ne_zero`; and `LSQRSolve.lean`
  proves
  `LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_normBudget_of_span_nonbreakdown_leadingBlock_det_ne_zero_kappaInf_selfNorm_budget`.
  This removes the separate `rho_k` lower-bound hypothesis by taking
  `rho_k = ||S_k||_infty`.  Two weak-component passes passed: targeted/full
  builds, lookup, placeholder scan, `git diff --check`, axiom audit, PDF
  compile/repair/text extraction, and rendered page inspection were clean. This
  dependency is closed as a visible-domain route; the remaining red QR
  bottleneck is deriving the local determinant and `kappaInf` assumptions,
  plus prefix-span/compact-update/sign-choice/final solver budgets, from SVD,
  determinant-margin, or a computed-loop invariant, or keeping them explicit.
- 2026-05-30: Added the determinant-facing prefix-span bridge for the QR
  condition-number route.  `HouseholderQR.lean` now proves
  `qrPrefixSupportSpannedByPreviousColumns_of_det_ne_zero_previousLeadingBlockTranspose`,
  and `LSQRSolve.lean` proves
  `LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_normBudget_of_leading_blocks_det_ne_zero_kappaInf_selfNorm_budget`.
  This removes the abstract prefix-span hypothesis from the self-norm `κ∞`
  solver route under visible previous-leading-block determinant and lower-zero
  shape assumptions.  Two weak-component passes passed: targeted/full builds,
  lookup, placeholder scan, whitespace check, axiom audit, PDF
  compile/repair/text extraction, and rendered page inspection were clean.  This
  dependency is closed as a visible-domain route; the remaining red QR
  bottleneck is deriving previous/current determinant assumptions, local
  `kappaInf` bounds, sign choice, compact-update budgets, final solver budgets,
  and computed-loop lower-zero shape from SVD, determinant-margin, or a
  source-faithful computed-loop invariant, or keeping them explicit.
- 2026-05-30: Added the triangular-principal-minor self-norm condition-number
  route for stored QR least squares.  `LSQRSolve.lean` now proves
  `LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_normBudget_of_triangular_leading_blocks_kappaInf_selfNorm_budget`,
  deriving the previous/current determinant hypotheses and completed-column
  lower-zero shape from visible upper-triangular local shape plus nonzero
  previous/current leading diagonals, then applying the determinant-facing
  prefix-span self-norm route.  Two weak-component passes passed: targeted/full
  builds, lookup, placeholder scan, whitespace check, axiom audit, PDF
  compile/repair/text extraction, and rendered page inspection were clean.
  This closes the triangular self-norm dependency as a visible-domain route.
  The remaining red QR bottleneck is deriving the triangular/nonzero-diagonal
  computed-loop invariant, local `kappaInf` bounds, sign choice,
  compact-update budgets, and final solver budgets from source-faithful
  foundations, or explicitly keeping them visible.
- 2026-05-30: Added the computed-prefix-zero triangular self-norm
  condition-number route for stored QR least squares.  `HouseholderQR.lean` now
  exposes `fl_householderStoredPanel_sequence_prefix_lower_zero` and local
  leading-block determinant adapters; `LSQRSolve.lean` proves
  `LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_normBudget_of_prefix_lower_zero_triangular_leading_blocks_kappaInf_selfNorm_budget`.
  This removes the over-strong whole-panel triangular-shape assumption by
  deriving the needed leading-block triangular entries and completed-column
  lower-zero shape from the stored panel recurrence itself.  Two
  weak-component validation passes passed: targeted/full builds, lookup,
  placeholder scan, whitespace check, axiom audit, PDF compile/repair/text
  extraction, and rendered page inspection were clean.  This dependency is
  closed as a computed-loop shape route.  Remaining visible assumptions are
  nonzero local diagonals, local `kappaInf` bounds, sign choice,
  compact-update budgets, and final solver budgets.
- 2026-05-30: Added the concrete signed-alpha specialization for the stored QR
  route.  `HouseholderSpec.lean` now defines `signedHouseholderAlpha` and
  proves the scalar square/sign lemmas; `HouseholderQR.lean` proves
  `fl_householderStoredTrailingPanel_sequence_diag_nonzero_of_signed_alpha_trailingNorm_pos_sqrt_budget`;
  `LSQRSolve.lean` proves both
  `LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_normBudget_of_signed_alpha_trailingNorm_pos_and_sqrt_budget`
  and
  `LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_normBudget_of_signed_alpha_prefix_lower_zero_triangular_leading_blocks_kappaInf_selfNorm_budget`.
  This removes the independent sign-choice hypothesis whenever the loop states
  the standard signed trailing-norm alpha rule.  Remaining red QR dependencies:
  nonzero local diagonals/nonbreakdown, local `kappaInf` bounds,
  compact-update budgets, and final solver budgets.  Two weak-component
  validation passes passed: targeted/full builds, executable lookup,
  placeholder scan, whitespace check, axiom audit, PDF compile/repair/text
  extraction, and rendered page inspection were clean.
- 2026-05-30: Added the prefix-local previous-diagonal nonbreakdown route for
  the stored QR bottleneck.  `HouseholderQR.lean` now proves
  `fl_householderStoredPanel_sequence_prefix_diag_nonzero_of_step_diag_nonzero`
  and
  `fl_householderStoredTrailingPanel_sequence_prefix_diag_nonzero_of_signed_alpha_trailingNorm_pos_sqrt_budget`;
  `LSQRSolve.lean` proves
  `LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_normBudget_of_signed_alpha_prefix_lower_zero_pivot_nonzero_kappaInf_selfNorm_budget`.
  This derives all previous local diagonal nonzeros from the stored signed-alpha
  loop and leaves the current leading pivot nonzero condition visible.  Two-pass
  validation passed: targeted/full builds, executable lookup, placeholder scan,
  whitespace check, axiom audit, PDF compile/repair/text extraction, and
  rendered page inspection were clean, with one lookup rerun after a transient
  concurrent-build race.  Remaining red QR dependencies: current-pivot
  nonzero/nonbreakdown, local `kappaInf` bounds, compact-update budgets, and
  final solver budgets.
- 2026-05-30: Added explicit final Gram/RHS radii for the prefix-local stored QR
  route.  `LSQRSolve.lean` now defines
  `qrSolveFinalDataPerturbationBudget`, `qrSolveFinalRhsPerturbationBudget`,
  `qrSolveFinalGramBudget`, and `qrSolveFinalRhsBudget`, proves the required
  nonnegativity/RHS-sum adapters, and closes the solver wrapper
  `LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitNormBudget_of_signed_alpha_prefix_lower_zero_pivot_nonzero_kappaInf_selfNorm_budget`.
  Two-pass validation passed: targeted/full builds, executable lookup,
  placeholder scan, whitespace check, axiom audit, PDF compile/repair/text
  extraction, and rendered page inspection were clean.  The final Gram/RHS
  listed dependency of the red QR bottleneck is closed; remaining dependencies
  are current-pivot nonzero/nonbreakdown, local `kappaInf` bounds,
  compact-update budgets, and square-root/compact pivot-budget derivations.
- 2026-05-31: Added explicit compact-update budgets for the prefix-local stored
  QR route.  `HouseholderApply.lean` now defines one-vector and one-panel
  relative compact budgets, `HouseholderQR.lean` sums them into
  `storedQRCompactSequenceRelativeBudget`, and `LSQRSolve.lean` proves
  `LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_prefix_lower_zero_pivot_nonzero_kappaInf_selfNorm_budget`.
  This removes the separate compact-update domination constant from the
  prefix-local signed-alpha route by choosing a displayed repository budget and
  reusing the explicit final Gram/RHS radii.  Two-pass validation passed:
  targeted/full builds, executable lookup, placeholder scan, whitespace check,
  axiom audit, PDF compile/repair/text extraction, and rendered page inspection
  were clean.  The red QR bottleneck is now narrowed to current-pivot
  nonzero/nonbreakdown, local `kappaInf` bounds, and square-root/compact
  pivot-budget derivations.
- 2026-05-31: Added the scalar positive-trailing-norm bridge for the
  prefix-local stored QR route.  `HouseholderSpec.lean` now proves
  `householderTrailingNorm2Sq_pos_of_nonneg_budget_lt_sqrt`, and the explicit
  final-budget and explicit compact-budget LSQRSolve wrappers derive their
  positive-trailing-norm obligations internally from the square-root budget
  hypotheses.  Two-pass validation passed: targeted/full builds, executable
  lookup, placeholder scan, whitespace check, axiom audit, PDF
  compile/repair/text extraction, and rendered page inspection were clean.
  The red QR bottleneck is now narrowed to current-pivot nonzero/nonbreakdown,
  local `kappaInf` bounds, and square-root/compact pivot-budget derivations.
- 2026-05-31: Added the direct norm-square-to-square-root pivot-budget bridge
  for the stored QR route.  `HouseholderSpec.lean` now proves
  `budget_lt_sqrt_householderTrailingNorm2Sq_of_dim_mul_budget_sq_lt_trailingNorm2Sq`,
  and `HouseholderQR.lean` uses it directly in
  `fl_householderStoredTrailingPanel_sequence_diag_nonzero_of_span_nonbreakdown_trailingNorm2Sq_budget`
  instead of detouring through an active-entry witness.  Two-pass validation
  passed: targeted/full builds, executable lookup, placeholder scan, whitespace
  check, axiom audit, PDF compile/repair/text extraction, and rendered page
  inspection were clean.  The red QR bottleneck is now narrowed to
  current-pivot nonzero/nonbreakdown, local `kappaInf` bounds, and
  conditioning-to-norm-square compact pivot-budget derivations.
- 2026-05-31: Added the solver-facing explicit compact QR certificate with
  norm-square pivot margins.  `LSQRSolve.lean` now proves
  `LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_prefix_lower_zero_pivot_nonzero_kappaInf_selfNorm_normSqBudget`,
  which composes the direct scalar bridge with the explicit compact-update and
  final-radius QR solver wrapper.  The theorem accepts the dimensioned margin
  `m * budget_k^2 < ||A_k(k:m,k)||_2^2` directly rather than exposing a
  square-root pivot-budget hypothesis.  Two-pass validation passed:
  targeted/full builds, executable lookup, placeholder scan, whitespace check,
  axiom audit, PDF compile/repair/text extraction, and rendered page inspection
  were clean.  The red QR bottleneck is now narrowed to current-pivot
  nonzero/nonbreakdown, local `kappaInf` bounds, and deriving the norm-square
  margins from conditioning or a computed-loop invariant.
- 2026-05-31: Added a route-elimination counterexample for the rectangular QR
  bottleneck.  `HouseholderQR.lean` now defines the real `2 x 2` column-swap
  matrix `qrPivotCounterexample2` and proves
  `qrPivotCounterexample2_first_pivot_zero`,
  `qrPivotCounterexample2_det_ne_zero`, and
  `not_forall_det_ne_zero_implies_first_pivot_ne_zero`.  This formally rules
  out using ordinary nonsingularity/full rank alone to justify the first
  unpivoted Householder pivot.  Two-pass validation passed: targeted/full
  builds, executable lookup, placeholder scan, whitespace check, axiom audit,
  PDF compile/repair/text extraction, and rendered page inspection were clean.
  The red QR bottleneck is now narrowed to source-faithful pivoting,
  no-breakdown or structured current-pivot invariants, local `kappaInf` bounds,
  and deriving norm-square margins from conditioning or a computed-loop
  invariant.
- 2026-05-31: Closed the structured current-pivot route for the rectangular QR
  bottleneck.  `MatrixAlgebra.lean` now proves
  `diag_ne_zero_of_upper_triangular_det_ne_zero`; `HouseholderQR.lean` proves
  `qrLeadingBlock_current_pivot_ne_zero_of_local_upper_triangular_det_ne_zero`
  and
  `fl_householderStoredTrailingPanel_sequence_current_pivot_ne_zero_of_leadingBlock_det_ne_zero`;
  `LSQRSolve.lean` exposes the compact solver wrapper
  `LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_prefix_lower_zero_leadingBlock_det_ne_zero_kappaInf_selfNorm_normSqBudget`.
  Two-pass validation passed: targeted/full builds, executable lookup,
  placeholder scan, whitespace check, axiom audit, PDF compile/repair/text
  extraction, and rendered page inspection were clean.  The current-pivot
  dependency is now closed under the source-faithful structured local-leading
  determinant assumption; the red QR bottleneck remains local `kappaInf`
  bounds and conditioning-to-norm-square/dual compact pivot-budget derivations.
- 2026-05-31: Closed the structured norm-square margin route from local leading
  blocks and `kappaInf`/dual budgets.  `HouseholderQR.lean` now proves
  `qrPrefixSupportSpannedByPreviousColumns_of_leadingBlock_upper_det_ne_zero`,
  deriving prefix-span from stored lower-zero shape and nonsingular local
  leading blocks.  `LSQRSolve.lean` now proves
  `LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_prefix_lower_zero_leadingBlock_det_ne_zero_kappaInf_selfNorm_dualBudget`,
  which derives the dimensioned norm-square compact pivot margin internally
  from local `kappaInf`/`K_k` and dual compact-budget assumptions.  Two-pass
  validation passed: targeted/full builds, executable lookup, placeholder
  scan, whitespace check, axiom audit, PDF compile/repair/text extraction, and
  rendered page inspection were clean.  The red QR bottleneck is now narrowed
  to deriving or justifying local `kappaInf`, `K_k`, and dual compact-budget
  assumptions from conditioning or a computed-loop invariant.
- 2026-05-31: Closed the structured direct inverse-∞ budget route for the
  latest explicit compact QR certificate.  `LSQRSolve.lean` now proves
  `LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_prefix_lower_zero_leadingBlock_det_ne_zero_invNorm_dualBudget`,
  which removes the local `kappaInf` and self-norm hypotheses when the direct
  budget `(k+1)||nonsingInv(S_k)||_∞^2 <= K_k` is available.  The theorem
  still keeps local leading-block determinants and the dual compact-budget
  inequality visible.  Two-pass validation passed: targeted/full builds,
  executable lookup, placeholder scan, whitespace check, axiom audit, PDF
  compile/repair/text extraction, and rendered page inspection were clean.  The
  red QR bottleneck is now narrowed to deriving direct inverse-∞ and dual
  compact-budget assumptions from diagonal dominance, conditioning, or a
  computed-loop invariant, or keeping them as explicit triangular-solve domain
  assumptions.
- 2026-05-31: Closed the diagonal-dominant structured direct inverse-∞ route
  for the latest explicit compact QR certificate.  `LSQRSolve.lean` now proves
  `LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_prefix_lower_zero_diagDominant_leadingBlock_det_ne_zero_dualBudget`,
  which composes `triInv_infNorm_sq_budget_of_diagDominantUpper_det_ne_zero`
  with the direct inverse-budget wrapper.  Local diagonal dominance, nonzero
  leading-block determinant, and Higham's diagonal-minimum budget now derive
  `(k+1)||nonsingInv(S_k)||_∞^2 <= K_k` internally.  Two-pass validation
  passed: targeted/full builds, executable lookup, placeholder scan,
  whitespace check, axiom audit, PDF compile/repair/text extraction, and
  rendered page inspection were clean.  The red QR bottleneck is now narrowed
  to deriving local diagonal dominance and the dual compact-budget inequality
  from conditioning or a computed-loop invariant, or keeping them as visible
  source/domain assumptions.
- 2026-05-31: Closed a route-elimination dependency for the rectangular QR
  bottleneck: `TriangularForwardBound.lean` now proves
  `not_forall_upper_tri_diag_nonzero_implies_diagDominant` using the concrete
  `2 x 2` matrix `[[1,2],[0,1]]`.  It is upper triangular and has nonzero
  diagonal entries, but it is not diagonally dominant.  Two-pass validation
  passed: targeted/full builds, executable lookup, placeholder scan,
  whitespace check, axiom audit, PDF compile/repair/text extraction, and
  rendered page inspection were clean.  The red QR bottleneck is now narrowed
  to deriving local diagonal dominance from a stronger computed-loop or
  conditioning invariant, deriving the dual compact-budget inequality, or
  keeping those assumptions visible as source/domain hypotheses.
- 2026-05-31: Closed the concrete-dual diagonal-dominant compact QR dependency:
  `diagDominantUpperInvBudgetExpr`,
  `diagDominantUpperInvBudgetExpr_pos`,
  `triInv_infNorm_sq_budget_of_diagDominantUpper_det_ne_zero_twice_budget`, and
  `LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_prefix_lower_zero_diagDominant_leadingBlock_det_ne_zero_concreteDualBudget`
  remove the arbitrary auxiliary `K_k` from the latest diagonal-dominant
  certificate by choosing `K_k = 2D_k`.  Two-pass validation passed:
  targeted/full builds, executable lookup, placeholder scan, whitespace check,
  axiom audit, PDF compile/repair/text extraction, and rendered page
  inspection were clean.  The remaining red QR choice is to prove local
  diagonal dominance and the direct compact smallness condition from a stronger
  conditioning/computed-loop invariant, or keep them visible as domain
  assumptions.
- 2026-05-31: Closed the product-form concrete-dual compact QR dependency:
  `mul_sq_lt_inv_two_mul_of_two_mul_mul_sq_lt_one` and
  `LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_prefix_lower_zero_diagDominant_leadingBlock_det_ne_zero_concreteDualProductBudget`
  convert the concrete-dual smallness assumption from
  `m * budget_k^2 < 1/(2D_k)` to `2D_k * (m * budget_k^2) < 1`, with `D_k > 0`
  derived from the existing diagonal-dominance budget positivity theorem.
  Two-pass validation passed: targeted/full builds, executable lookup,
  placeholder scan, whitespace check, axiom audit, PDF compile/repair/text
  extraction, and rendered page inspection were clean.  The red QR bottleneck
  now has the product-shaped compact-smallness statement, but still requires
  deriving local diagonal dominance and product smallness from a stronger
  conditioning/computed-loop invariant, ruling out that route, or keeping the
  assumptions visible.
- 2026-05-31: Closed a route-elimination dependency for the product-form
  compact QR bottleneck: `InverseBounds.lean` now proves
  `not_forall_pos_implies_two_mul_mul_sq_lt_one`, showing with the scalar
  counterexample `D = 1`, `B = 1`, and `m = 1` that positivity of the inverse
  budget alone cannot imply `2D * (m * B^2) < 1`.  Two-pass validation passed:
  targeted/full builds, executable lookup, placeholder scan, whitespace check,
  axiom audit, PDF compile/repair/text extraction, and rendered page inspection
  were clean.  The active QR bottleneck is now narrowed to proving a genuine
  compact-update product bound from a computed-loop/conditioning invariant or
  keeping the product-smallness assumption visible.
- 2026-05-31: Strengthened the diagonal-dominance route elimination for the
  rectangular QR bottleneck.  `TriangularForwardBound.lean` now proves
  `diagDominanceCounterexample2_det_ne_zero` and
  `not_forall_upper_tri_det_ne_zero_implies_diagDominant`, showing that the
  concrete upper-triangular matrix `[[1,2],[0,1]]` has nonzero determinant but
  still is not diagonally dominant.  Two-pass validation passed:
  targeted/full builds, executable lookup, placeholder scan, whitespace check,
  axiom audit, PDF compile/repair/text extraction, and rendered page inspection
  were clean.  The active QR bottleneck can no longer use triangular
  determinant nonzeroness as a hidden diagonal-dominance proof; a positive
  route must derive diagonal dominance from a stronger computed-loop or
  conditioning invariant, or keep it visible.

- 2026-05-31: Added the conditioning-facing companion route elimination for
  the same QR bottleneck.  `TriangularForwardBound.lean` now proves
  `exists_upper_tri_det_ne_zero_kappaInf_bound_not_diagDominant` and
  `not_forall_upper_tri_det_ne_zero_kappaInf_bound_implies_diagDominant`.
  The same `[[1,2],[0,1]]` matrix has upper-triangular shape, nonzero
  determinant, and a finite local `kappaInf` certificate, but is not
  diagonally dominant.  This rules out using a generic finite condition-number
  certificate as the missing diagonal-dominance invariant; a positive route
  needs a stronger computed-loop/off-diagonal-control invariant or an explicit
  domain assumption.  Two weak-component passes completed: targeted/full
  builds, lookup, touched-Lean placeholder scan, whitespace check, axiom audit,
  PDF compile/text extraction, and rendered page inspection.

- 2026-05-31: Added source-faithful leading-dual budget instantiation wrappers
  for the rectangular QR bottleneck.  `LSQRSolve.lean` now proves
  `LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitNormBudget_of_span_nonbreakdown_leading_dual_norm_budget`
  and
  `LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_span_nonbreakdown_leading_dual_norm_budget`.
  These wrappers choose the repository final Gram/RHS budgets and, in the
  compact version, `storedQRCompactSequenceRelativeBudget` for the
  prefix-span plus leading-dual solver certificate.  They close a real
  budget-instantiation dependency while keeping the remaining obligations
  visible: construct the leading dual, prove prefix-span, and derive the dual
  compact-smallness condition from a computed-loop/conditioning invariant or
  keep them as explicit domain assumptions.  Two weak-component passes
  completed: targeted/full builds, lookup, touched-Lean placeholder scan,
  whitespace check, axiom audit, PDF compile/text extraction, and rendered
  page inspection.

- 2026-05-31: Added source-faithful local inverse row-budget wrappers with
  repository final and compact budgets.  `LSQRSolve.lean` now proves
  `LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitNormBudget_of_span_nonbreakdown_leadingBlock_leftInverse_norm_budget`
  and
  `LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_span_nonbreakdown_leadingBlock_leftInverse_norm_budget`.
  These construct the leading dual from a local leading-block left inverse,
  choose `qrSolveFinalGramBudget`/`qrSolveFinalRhsBudget`, and then choose
  `storedQRCompactSequenceRelativeBudget`.  This closes the local-dual
  construction plus budget-instantiation dependency under visible prefix-span,
  local row-norm, sign-choice, and compact-smallness hypotheses.  Two
  weak-component passes completed: targeted/full builds, lookup, touched-Lean
  placeholder scan, whitespace check, axiom audit, PDF compile/text extraction,
  and rendered page inspection.

- 2026-05-31: Added source-faithful local inverse Frobenius/infinity wrappers
  with repository final and compact budgets.  `LSQRSolve.lean` now proves the
  explicit norm-budget and explicit compact-budget variants ending in
  `leadingBlock_leftInverse_frobNorm_budget` and
  `leadingBlock_leftInverse_infNorm_budget`.  These compose the existing
  row-versus-Frobenius and infinity-versus-Frobenius bridges with
  `qrSolveFinalGramBudget`, `qrSolveFinalRhsBudget`, and
  `storedQRCompactSequenceRelativeBudget`.  Two weak-component passes
  completed: targeted/full builds, lookup, touched-Lean placeholder scan,
  whitespace check, axiom audit, PDF compile/text extraction, and rendered
  page inspection.

- 2026-05-31: Added the stored-prefix-span local-inverse row wrapper for the
  source-faithful rectangular QR route.  `HouseholderQR.lean` now proves
  `qrPrefixSupportSpannedByPreviousColumns_of_leftInverse_previousLeadingBlockTranspose`
  and
  `fl_householderStoredPanel_sequence_prefixSpan_of_leftInverse_previousLeadingBlockTranspose`,
  deriving prefix-span from the actual stored panel recurrence plus local
  left inverses for the previous transposed leading blocks.  `LSQRSolve.lean`
  now proves
  `LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_previousLeadingBlock_leftInverse_leadingBlock_leftInverse_norm_budget`,
  which feeds that derived prefix-span fact into the row-norm local-inverse
  compact-budget certificate.  This closes the separate prefix-span assumption
  for the row branch under visible previous/current local left inverses; local
  inverse existence, row-norm budget, sign choice, and compact-smallness remain
  explicit.  Two weak-component passes passed: targeted/full builds, lookup,
  placeholder scans, whitespace checks, repeated axiom audit, PDF text
  extraction, and rendered page inspection.
- 2026-05-31: Extended the stored-prefix-span source-faithful QR route to the
  Frobenius and infinity inverse-norm compact-budget branches.  `LSQRSolve.lean`
  now proves the `...previousLeadingBlock_leftInverse_leadingBlock_leftInverse_frobNorm_budget`
  and `...previousLeadingBlock_leftInverse_leadingBlock_leftInverse_infNorm_budget`
  wrappers, which derive prefix-span from the stored recurrence plus previous
  local left inverses and feed it into the repository-budgeted inverse-norm
  certificates.  Two weak-component passes passed: targeted/full builds,
  lookup, placeholder scans, whitespace checks, repeated axiom audit, PDF text
  extraction, and rendered page inspection.
- 2026-05-31: Added the signed-alpha stored-prefix-span local-inverse row
  wrapper for the source-faithful rectangular QR route.  `LSQRSolve.lean` now
  proves
  `LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_previousLeadingBlock_leftInverse_leadingBlock_leftInverse_norm_budget`,
  which derives the squared-alpha trailing-norm identity and sign-choice
  inequality from the repository `signedHouseholderAlpha` definition before
  applying the stored-prefix-span row certificate.  Two weak-component passes
  passed: targeted/full builds, lookup, placeholder scans, whitespace checks,
  repeated axiom audit, PDF text extraction, and rendered page inspection.
- 2026-05-31: Extended the signed-alpha stored-prefix-span local-inverse route
  to the Frobenius and infinity inverse-norm branches.  `LSQRSolve.lean` now
  proves the `...signed_alpha_previousLeadingBlock_leftInverse_leadingBlock_leftInverse_frobNorm_budget`
  and `...signed_alpha_previousLeadingBlock_leftInverse_leadingBlock_leftInverse_infNorm_budget`
  wrappers, which derive the squared-alpha identity and sign-choice inequality
  from `signedHouseholderAlpha` before applying the stored-prefix-span
  Frobenius/infinity certificates.  Two weak-component passes passed:
  targeted/full builds, lookup, placeholder scans, whitespace checks, repeated
  axiom audit, PDF text extraction, and rendered page inspection.
- 2026-05-31: Added the determinant-facing signed-alpha stored-prefix-span
  local-inverse wrappers.  `LSQRSolve.lean` now proves the
  `...signed_alpha_previousLeadingBlock_det_ne_zero_leadingBlock_det_ne_zero_norm_budget`,
  `...frobNorm_budget`, and `...infNorm_budget` certificates, instantiating
  previous/current local left inverses with `nonsingInv` from nonzero
  determinants while keeping the inverse-budget and compact-smallness
  inequalities visible.  Two weak-component passes passed: targeted/full
  builds, lookup, placeholder scans, whitespace checks, repeated axiom audit,
  PDF page-local text extraction, and rendered page inspection.
- 2026-05-31: Added the source-faithful signed-alpha determinant `κ∞`
  self-norm wrapper
  `...signed_alpha_previousLeadingBlock_det_ne_zero_leadingBlock_det_ne_zero_kappaInf_selfNorm_budget`.
  It derives the direct inverse-∞ budget from visible determinant, local
  `κ∞`, and self-norm squared-budget hypotheses using the repository
  `infNorm_sq_budget_of_kappaInf_le_and_det_ne_zero` bridge.  Two
  weak-component passes passed: targeted/full builds, lookup, placeholder
  scans, whitespace checks, repeated axiom audit, PDF page-local text
  extraction, and rendered page inspection.
- 2026-05-31: Added the source-faithful signed-alpha triangular leading-block
  `κ∞` wrapper
  `...signed_alpha_upperTriangular_leadingDiag_ne_zero_kappaInf_selfNorm_budget`.
  It derives the previous/current determinant facts from visible
  upper-triangular leading-block shape and nonzero displayed leading diagonal
  entries using the QR determinant bridges, then applies the signed-alpha
  determinant `κ∞` route.  Two weak-component passes passed: targeted/full
  builds, lookup, placeholder scans, whitespace checks, repeated axiom audit,
  PDF page-local text extraction, and rendered page inspection after replacing
  an overflowing inline Lean-name proof-idea sentence by math-level prose.
- 2026-05-31: Ruled out the false current-pivot route "positive active trailing
  norm implies current unpivoted pivot nonzero."  `HouseholderSpec.lean` now has
  the concrete `x = (0,1)` counterexample
  `householderTrailingPivotCounterexample2` with positive active trailing
  squared norm and zero pivot entry, plus
  `not_forall_trailingNorm2Sq_pos_implies_pivot_ne_zero`.  Two weak-component
  passes passed: targeted/full builds, lookup, placeholder scans, whitespace
  checks, repeated axiom audit, PDF page-local text extraction, and rendered
  page inspection.  This is route elimination only; the QR bottleneck must
  continue through pivoting, structured leading-block invariants, or visible
  domain assumptions for current-pivot nonzero.
- 2026-05-31: Ruled out the false product-smallness route "diagonal dominance
  and the displayed Higham inverse budget imply product compact smallness."
  `InverseBounds.lean` now has
  `not_forall_diagDominantUpper_implies_two_mul_budget_expr_mul_sq_lt_one`,
  using the scalar `1 x 1` identity block with compact budget `B = 1` and
  `m = 1`.  Two weak-component passes passed: targeted/full builds, lookup,
  placeholder scans, whitespace checks, repeated axiom audit, PDF page-local
  text extraction, and rendered page inspection.  This is route elimination
  only; the product compact-smallness inequality still needs a genuine
  computed-loop/conditioning invariant or must stay visible as a domain
  assumption.
- 2026-05-31: Re-audited the rectangular QR proof-source route after the
  product-smallness shortcut was ruled out.  The remaining QR work is now a
  genuine theorem-family choice: continue Higham's columnwise/normwise
  Householder QR Theorem 4.5 route, switch to Cox--Higham row-wise weighted-LS
  stability with pivoting/sorting/sign-choice hypotheses, or keep the remaining
  nonbreakdown/conditioning/product-smallness hypotheses visible.  Do not loop
  back into diagonal dominance/product smallness unless a real compact-update
  budget theorem is added.
- 2026-05-31: Chose the Higham columnwise route and closed the final stored QR
  factorization assembly.  `HouseholderQR.lean` now has
  `fl_householderStoredTrailingPanel_higham_columnwise_factorization`, combining
  the stored trailing columnwise perturbation theorem with the stored top-block
  shape theorem.  It yields one orthogonal `Q`, perturbations `DeltaA` and
  `Deltab`, columnwise/RHS geometric perturbation bounds, final `[R;0]` shape,
  top transformed RHS, and upper-triangular `R`.  This is not the final
  solver/preconditioner theorem: nonzero diagonal, conditioning/inverse-budget,
  and compact-smallness/product-budget obligations remain separate.
- 2026-05-31: Refactored the stored-loop LSQRSolve handoff
  `LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_normBudget`
  so it reuses
  `fl_householderStoredTrailingPanel_higham_columnwise_factorization` directly
  instead of rebuilding the sequence perturbation and shape facts internally.
  The cleanup has two weak-component passes (targeted/full builds, lookup,
  placeholder scan, diff check, axiom audit, PDF compile/text extraction, and
  rendered page inspection); this is a library-health/modularity improvement,
  not a new discharge of nonzero diagonal, conditioning, or compact-smallness.
- 2026-05-31: Strengthened the no-pivot QR route elimination:
  `qrPivotCounterexample2_first_leadingBlock_det_zero` and
  `not_forall_det_ne_zero_implies_all_leading_blocks_det_ne_zero` show that the
  nonsingular `2 x 2` column-swap matrix has zero determinant in its first
  unpivoted `1 x 1` leading QR block.  This rules out deriving the per-pivot
  leading-block determinant hypotheses from whole-matrix nonsingularity/full
  rank alone.  It is a theorem-statement correction/route elimination, not a
  positive nonbreakdown theorem.  Two weak-component passes validated the Lean
  facts, lookup references, axiom audit, PDF text extraction, and rendered PDF
  pages 120--121.
- 2026-05-31: Added the QR bottleneck cross-route elimination
  `not_forall_upper_tri_det_ne_zero_product_budget_implies_diagDominant`.
  The nonsingular upper-triangular block `[[1,2],[0,1]]` satisfies the displayed
  product compact-smallness inequality for a small budget `B = 1/8`, but still
  is not diagonally dominant.  This prevents collapsing the remaining
  diagonal-dominance and product-smallness assumptions into each other; both
  need a genuine invariant or must stay visible as domain assumptions.  Two
  weak-component passes validated the Lean theorem, lookup reference, axiom
  audit, PDF text extraction, and rendered PDF pages 124--125.
- 2026-05-31: Added the QR bottleneck stored-sequence compact-budget bridge:
  `storedQRCompactPivotBudget_le_sequence_column_norm`,
  `two_mul_mul_sq_lt_one_of_nonneg_le`, and
  `LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_prefix_lower_zero_diagDominant_leadingBlock_det_ne_zero_concreteDualProductSequenceBudget`.
  The raw pivot compact component is now bounded by the deterministic stored
  QR sequence budget times the current pivot-column norm before feeding the
  concrete-dual product certificate.  Two weak-component passes validated the
  Lean facts, lookup reference, axiom audit, PDF text extraction, and rendered
  PDF page 124.
- 2026-05-31: Added a QR bottleneck route elimination:
  `not_forall_upper_tri_det_ne_zero_kappaInf_bound_implies_two_mul_budget_expr_mul_sq_lt_one`.
  It shows that upper-triangular nonsingularity plus a finite local `κ∞` budget
  does not imply product compact-smallness; the compact-update budget still
  needs a genuine computed-loop/conditioning invariant or must stay visible.
  Two weak-component passes validated the Lean fact, lookup reference, axiom
  audit, PDF text extraction, and rendered PDF pages 125--126.
- 2026-05-31: Marked `LS.8-rectangular-QR` as an explicit route-choice
  checkpoint after the shortcut eliminations.  The generic implementation-backed
  equation (8) QR/preconditioner theorem remains open; the next valid progress
  must choose a stronger computed-loop/off-diagonal-control invariant, switch to
  a Cox--Higham pivoted/sorted row-wise theorem family, or keep the remaining
  nonbreakdown/conditioning/product-smallness assumptions visible as domain
  assumptions.  New adjacent adapters are frozen unless they close or rule out
  one of those listed routes.
- 2026-05-31: Narrowed the Cox--Higham option for `LS.8-rectangular-QR`.
  Source review confirmed it is not a drop-in closure for the current unpivoted
  stored-QR solver/preconditioner theorem: Cox--Higham requires column pivoting
  plus row pivoting or row sorting and the specified sign convention.  Treat it
  as a separate future theorem family.  For the current unpivoted theorem, the
  remaining honest choices are a stronger computed-loop/off-diagonal-control
  invariant or visible domain hypotheses.
- 2026-05-31: Added a Lean route elimination for the remaining unpivoted QR
  diagonal-dominance route.  The theorem
  `not_forall_orthogonal_upper_factorization_implies_diagDominant` shows that
  exact QR-shaped data `A = Q * R` with `Q` orthogonal, `R` upper triangular,
  and nonzero diagonal still does not imply diagonal dominance; the witness is
  `Q = I`, `R = [[1,2],[0,1]]`.  A positive unpivoted route must therefore use
  a genuine computed-loop/off-diagonal-control invariant, or keep diagonal
  dominance visible as a domain hypothesis.
- 2026-05-31: Strengthened the same route elimination with the actual exact
  no-pivot trailing Householder recurrence.  The theorem
  `not_forall_exact_trailing_householder_sequence_implies_diagDominant` proves
  that a valid two-step exact Householder sequence can start from
  `[[1,2],[0,1]]` and end at `[[-1,-2],[0,-1]]`, which is not diagonally
  dominant.  Do not try to close the QR/preconditioner bottleneck by claiming
  diagonal dominance is a generic consequence of the unpivoted Householder
  loop; it must be an explicit off-diagonal-control/pivoting hypothesis or a
  visible domain assumption.
- 2026-05-31: After the exact no-pivot recurrence route elimination, the
  equation (8) QR/preconditioner bottleneck is a theorem-scope choice rather
  than a local-adapter gap.  The next valid progress must choose one of:
  prove a stronger computed-loop/off-diagonal-control invariant, switch to a
  pivoted/sorted row-wise theorem family, or keep the remaining nonbreakdown,
  conditioning, diagonal-dominance, and compact-product assumptions visible as
  domain hypotheses.  Adjacent QR adapters are frozen until that choice is made.
- 2026-05-31: User chose the stronger computed-loop/off-diagonal-control route.
  `LSQRSolve.lean` now defines `StoredQROffDiagonalControlInvariant`, bundling
  local leading-block nonsingularity, local diagonal dominance, and product
  smallness for `storedQRCompactSequenceRelativeBudget * ||A_hat_k(:,k)||_2`.
  The wrapper
  `LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_offDiagonalControl`
  proves this invariant feeds the existing diagonal-dominant stored-sequence
  QR certificate and yields `LSQRSolveBackwardError` with the repository final
  Gram/RHS budgets.  This packages and consumes route 1; it does not prove the
  invariant from ordinary no-pivot QR.
- 2026-05-31: Reduced the route-1 invariant to source-shaped local fields.
  `StoredQRSourceOffDiagonalControl` assumes upper-triangular local leading
  blocks, nonzero local leading diagonals, row-wise off-diagonal domination,
  and the stored-sequence compact-product inequality.
  `StoredQROffDiagonalControlInvariant.of_sourceOffDiagonalControl` derives the
  packaged invariant using `det_ne_zero_of_upper_triangular_diag_ne_zero`, and
  `LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_sourceOffDiagonalControl`
  feeds those source-shaped assumptions to the existing solver certificate.
  The next QR bottleneck target is to prove `StoredQRSourceOffDiagonalControl`
  from a real pivoting/order/off-diagonal-growth theorem, or keep it visible as
  the theorem's domain condition.

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

## 2026-05-31 RandNLA CACM QR Bottleneck Frontier

- Route 1 for the rectangular QR/preconditioner bottleneck is reduced to
  `StoredQRSourceOffDiagonalControl`.  The source-shaped wrapper has two clean
  weak-component passes: full build, lookup, diff check, placeholder scan,
  axiom audit, PDF compile/text extraction, and rendered pages 128--129.  The
  remaining red dependency is not another adapter; it is proving the
  source-shaped local control data from source-specific pivoting, ordering, or
  off-diagonal-growth assumptions, or keeping those fields visible as domain
  hypotheses.
- The stored recurrence itself now supplies the triangular leading-block field:
  `StoredQRSourceOffDiagonalControl.of_stored_trailing_sequence_diag_offdiag_product`
  derives it from `fl_householderStoredPanel_sequence_prefix_lower_zero`, and
  the solver theorem
  `LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_diag_offdiag_product`
  leaves only nonzero displayed diagonals, row-wise off-diagonal domination,
  and compact-product smallness as the active red-bottleneck obligations.  This
  triangular-source reduction has two clean weak-component passes.
- The nonzero displayed diagonal obligation is now reduced using existing local
  QR infrastructure: `StoredQRSourceOffDiagonalControl.of_stored_trailing_sequence_pivot_sqrtBudget_offdiag_product`
  derives previously written diagonal entries from the signed-alpha stored
  prefix-diagonal theorem and square-root budget, while its solver wrapper
  keeps current pivot nonzero, square-root budget, row-wise off-diagonal
  domination, and compact-product smallness visible.  This reduction has two
  clean weak-component passes.
- The raw current pivot nonzero field is now reduced further to a structured
  local leading-block determinant hypothesis:
  `StoredQRSourceOffDiagonalControl.of_stored_trailing_sequence_leadingBlock_det_ne_zero_sqrtBudget_offdiag_product`
  reuses
  `fl_householderStoredTrailingPanel_sequence_current_pivot_ne_zero_of_leadingBlock_det_ne_zero`,
  and the solver wrapper
  `LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_leadingBlock_det_ne_zero_sqrtBudget_offdiag_product`
  feeds the reduced source-shaped data into `LSQRSolveBackwardError`.  This
  reduction has two clean weak-component passes.
- The square-root nonbreakdown budget in the same determinant-shaped
  source route is now reduced to the dimensioned norm-square margin:
  `StoredQRSourceOffDiagonalControl.of_stored_trailing_sequence_leadingBlock_det_ne_zero_normSqBudget_offdiag_product`
  applies
  `budget_lt_sqrt_householderTrailingNorm2Sq_of_dim_mul_budget_sq_lt_trailingNorm2Sq`,
  and the solver wrapper
  `LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_leadingBlock_det_ne_zero_normSqBudget_offdiag_product`
  feeds the result into the final QR certificate.  This reduction has two
  clean weak-component passes.
- The current QR red bottleneck is a genuine theorem-family route choice, not
  an API problem.  Existing local counterexamples rule out deriving the
  residual route-1 fields from ordinary unpivoted stored Householder QR, full
  rank, whole-matrix determinant nonzero, positive trailing norm, exact QR
  shape, finite conditioning, diagonal dominance alone, or product smallness
  alone.  Further progress needs one choice: keep the remaining fields as visible source/domain
  assumptions, switch to pivoted/sorted/off-diagonal-controlled QR, or provide
  an application-specific source theorem proving them.
- Current scoping choice: keep local leading-block nonsingularity, norm-square
  nonbreakdown margin, row-wise off-diagonal domination, and compact-product
  smallness visible for the existing
  unpivoted theorem family.  This closes the route-choice bookkeeping but not
  the generic paper-level QR/preconditioner claim.  Do not add adjacent
  unpivoted QR wrappers unless they close a listed dependency or the theorem
  family changes.
- 2026-05-31: Algorithm 3 SRHT route now has scalar signed-linear-form MGF
  infrastructure in `Preconditioning.lean`.
  `rademacherTraceProbability_expectationReal_exp_sum_mul_sign_eq_prod`
  factors the finite Rademacher MGF exactly, and
  `rademacherTraceProbability_eventProb_sum_mul_sign_le_ge_one_sub_exp_mul_prod`
  composes that factorization with the local exponential-Markov kernel.  The
  same file now also closes the scalar Hoeffding/two-sided-tail dependency and
  a weaker coordinate-Hoeffding all-row row-norm theorem
  `rademacherTraceProbability_eventProb_forall_rowNormSq_signedHadamard_le_ge_one_sub_sum_exp_sq_bound`.
  It also closes the scoped equation-(6) leverage-probability lift
  `rademacherTraceProbability_eventProb_forall_leverageScoreProb_signedHadamard_le_ge_one_sub_delta`.
  `UniformRowSampling.lean` now defines `uniformRowOuterGramSample` and proves
  the PSD, mean-identity, quadratic-form, and leverage-to-Loewner one-step
  facts for uniform row sampling after preconditioning.  `Preconditioning.lean`
  composes the coordinate-Hoeffding leverage event into
  `rademacherTraceProbability_eventProb_forall_uniformRowOuterGramSample_signedHadamard_finiteLoewnerLe_ge_one_sub_delta`.
  `UniformRowSamplingMGF.lean` now closes the deterministic-after-preconditioning
  iid uniform sample-average concentration route in tail-budget finite-Loewner
  form, ending with
  `uniformRowTraceProbability_eventProb_uniformRowSampleGram_two_sided_finiteLoewnerLe_ge_one_sub_delta_of_tail_budget`.
  `UniformRowSamplingComposition.lean` now composes the closed
  coordinate-Hoeffding preprocessing event with the closed uniform
  sample-average theorem on the product probability law, ending with
  `signedHadamardUniformRowTraceProbability_eventProb_uniformRowSampleGram_two_sided_finiteLoewnerLe_ge_one_sub_delta`.
  `UniformRowSamplingFP.lean` now closes the scoped floating-point uniform
  sketch transfer by proving `rowSketchGram_uniformRowSampleSketch_eq_uniformRowSampleGram`,
  `fl_uniformRowSampleGramDot_perturb_bound`, and
  `signedHadamardUniformRowTraceProbability_eventProb_fl_uniformRowSampleGramDot_two_sided_finiteLoewnerLe_ge_one_sub_delta`.
  This is a real high-probability auxiliary but not Tropp Lemma 3.3; remaining
  source-sharp work is Tropp row-norm/leverage uniformization.
- 2026-05-31: The scoped Algorithm 3 coordinate-Hoeffding route also has a
  deterministic FP-radius refinement in `UniformRowSamplingFP.lean`.
  `uniformRowSampleGramFullFpConstBudget` names a fixed row-scaling plus
  dot-product perturbation budget; the closed-form lemmas expose the Gram
  dimension factor; `uniformRowSampleGramFullFpPerturbBudget_le_const_of_sample_rowNormSq_le`
  proves that sampled-row norm caps bound the sample-dependent FP budget by
  the fixed budget with `C = m * R`; and
  `signedHadamardUniformRowTraceProbability_eventProb_fl_uniformRowSampleGramDot_two_sided_finiteLoewnerLe_ge_one_sub_delta_constBudget`
  gives the same joint probability lower bound with radius `epsilon + tau`
  whenever `tau` dominates the sample-dependent FP budget over all joint
  outcomes.  This closes the optional deterministic-radius refinement for the
  scoped route; it now has two clean weak-component passes.  It still does not
  prove Tropp's source-sharp SRHT row-norm theorem.
- 2026-05-31: The active Algorithm 3 source-sharp SRHT bottleneck has been
  narrowed by proof-source acquisition.  Tropp Lemma 3.3 depends on the
  Ledoux/Talagrand convex-Lipschitz Rademacher concentration theorem
  (Tropp Proposition 2.1), not on the scalar coordinate-Hoeffding theorem
  already formalized.  `Preconditioning.lean` now closes the expected
  Euclidean row-norm prelude step with
  `rademacherTraceProbability_expectationReal_sqrt_rowNormSq_signedHadamard_le`.
  `RowSamplingLeverage.lean`, `MatrixAlgebra.lean`, and `Preconditioning.lean`
  now also close the deterministic Lipschitz side with
  `hasOrthonormalColumns_vecNorm2Sq_mul_vec_eq`,
  `hasOrthonormalColumns_transpose_mul_vecNorm2Sq_le`,
  `abs_vecNorm2_sub_le_vecNorm2_sub`, and
  `signedHadamard_row_vecNorm2_lipschitz`.  `MatrixAlgebra.lean` and
  `Preconditioning.lean` now close the deterministic convexity side with
  `FiniteVecConvex`, `vecNorm2_linear_combination_convex`, and
  `signedHadamard_row_vecNorm2_convex`.  `MatrixAlgebra.lean` also records
  the deterministic Ledoux-to-Tropp affine scaling constants with
  `FiniteVecLipschitzWith`, `unitCubeToRademacherVec`,
  `finiteVecConvex_scaled_unitCubeToRademacher`, and
  `finiteVecLipschitzWith_scaled_unitCubeToRademacher`.  Ledoux's source
  statement is Corollary 1.3 from the log-Sobolev route: the \([0,1]^m\)
  upper tail has exponent `exp(-t^2/2)`, and Tropp's Rademacher
  `exp(-t^2/8)` follows from the factor-two affine map.  `FiniteProbability.lean` also
  closes the finite MGF/Herbst/Laplace algebraic substrate with
  `FiniteProbability.expectationReal_exp_pos`,
  `FiniteProbability.hasDerivAt_expectationReal_exp_mul`,
  `FiniteProbability.hasDerivAt_log_expectationReal_exp_mul`,
  `FiniteProbability.entropyReal`,
  `FiniteProbability.entropyReal_exp_mul_eq`,
  `FiniteProbability.boolUniformProbability`,
  `FiniteProbability.boolUniformProbability_prob`,
  `FiniteProbability.boolUniformProbability_expectationReal`,
  `FiniteProbability.entropyReal_boolUniformProbability_eq`,
  `FiniteProbability.twoPointEntropy_le_sq_sub_div_of_pos`,
  `FiniteProbability.entropyReal_boolUniformProbability_sq_le_sq_sub_of_pos`,
  `FiniteProbability.expectationReal_sq_nonneg`,
  `FiniteProbability.abs_expectationReal_mul_le_sqrt_mul_sqrt`,
  `FiniteProbability.sqrt_expectationReal_sq_add_le`,
  `FiniteProbability.abs_sqrt_expectationReal_sq_sub_le_sqrt_expectationReal_sub_sq`,
  `FiniteProbability.boolUniformProbability_abs_sqrt_expectationReal_sq_sub_le_sqrt_expectationReal_sub_sq`,
  `FiniteProbability.entropyReal_prod_boolUniformProbability_sq_le_coordinate_add_entropy`,
  `FiniteProbability.entropyReal_prod_boolUniformProbability_sq_le_lifted_diff_sum_add`,
  `FiniteProbability.prod_expectationReal_eq`,
  `FiniteProbability.prod_expectationReal_fst_eq`,
  `FiniteProbability.entropyReal_prod_eq_expectation_entropyReal_add_entropyReal_expectation`,
  `FiniteProbability.log_mgf_differential_le_of_entropyReal_exp_mul_le`,
  `FiniteProbability.log_mgf_div_sub_quadratic_antitoneOn_of_differential_le`,
  `FiniteProbability.tendsto_log_mgf_div_nhdsGT_zero`,
  `FiniteProbability.log_mgf_le_mean_add_quadratic_of_differential_le`,
  `FiniteProbability.log_mgf_le_mean_add_quadratic_of_entropyReal_exp_mul_le`,
  `FiniteProbability.expectationReal_exp_centered_le_exp_of_log_mgf_le`, and
  `FiniteProbability.eventProb_real_le_mean_add_ge_one_sub_exp_sq_of_log_mgf_bound`,
  `FiniteProbability.eventProb_real_le_mean_add_ge_one_sub_exp_sq_of_entropyReal_exp_mul_le`,
  and closes the generic Chernoff optimizer with
  `FiniteProbability.eventProb_real_le_ge_one_sub_exp_of_mgf_bound` and
  `FiniteProbability.eventProb_real_le_mean_add_ge_one_sub_exp_sq_of_subgaussian_mgf`,
  turning a centered subgaussian MGF bound into the one-sided
  `exp(-t^2/(2*sigma^2))` tail.  The unbiased Bernoulli coordinate law,
  coordinate expectation/entropy formulas, fair-Bernoulli coordinate
  log-Sobolev inequality, finite `L2` section-norm reverse-triangle bridge, the
  one-coordinate product peel-off, the abstract Bernoulli-product induction
  lift, the concrete `RademacherTrace m` cube entropy-gradient theorem
  `rademacherTraceProbability_entropyReal_sq_le_sum_flip`, the conditional
  exponential-tilt reduction
  `rademacherTraceProbability_entropyReal_exp_mul_le_of_flip_tilt_sq_sum_bound`,
  the conditional finite-cube Chernoff wrapper
  `rademacherTraceProbability_eventProb_real_le_mean_add_ge_one_sub_exp_sq_of_flip_tilt_sq_sum_bound`,
  product-law expectation Fubini, entropy chain-rule/tensorization algebra,
  scalar tilt inequalities `real_exp_sub_one_le_mul_exp`,
  `real_abs_exp_sub_exp_le_abs_sub_mul_exp_add_exp`,
  `real_exp_half_sub_sq_le_two_mul_half_diff_sq`, uniform Rademacher
  flip-invariance (`rademacherTraceFlip_involutive`,
  `rademacherTraceProbability_expectationReal_flip`), and the non-sharp
  finite-cube symmetrization bridges
  `rademacherTraceProbability_flip_tilt_sq_sum_bound_of_pointwise_halfdiff_sq_le`
  and
  `rademacherTraceProbability_flip_tilt_sq_sum_bound_of_pointwise_absdiff_le`
  are now closed locally.  `MatrixAlgebra.lean` also closes the unit-support
  lemmas `vecNorm2_inv_smul_self_of_pos`,
  `vecInnerProduct_inv_smul_self_eq_norm`, and
  `vecNorm2_sub_le_inner_unit_diff`; `Preconditioning.lean` closes the
  sign-flip algebra, `signedHadamard_row_vec_sub_flip`,
  `signedHadamard_row_inner_sq_sum_eq_inv_mul`, and the concrete
  signed-Hadamard row-norm positive-flip self-bound
  `signedHadamard_row_vecNorm2_positive_flip_sq_sum_le`.  The former
  exponential-tilt bottleneck is now closed in the specialized row-norm route:
  `real_exp_half_sub_sq_le_quarter_mul_sq_mul_exp_of_le`,
  `real_exp_half_sub_sq_le_lam_sq_quarter_pair_pos`,
  `rademacherTraceProbability_flip_tilt_sq_sum_bound_of_pointwise_posdiff_sq_sum_le`,
  and
  `rademacherTraceProbability_flip_tilt_sq_sum_bound_signedHadamard_row_vecNorm2`
  feed the finite-cube Herbst wrapper to prove the one-row
  `exp(-m*t^2/8)` tail and the all-row SRHT row-norm/leverage caps in
  `Preconditioning.lean`.  `UniformRowSamplingComposition.lean` also closes the
  exact source-sharp product-law composition
  `signedHadamardUniformRowTraceProbability_eventProb_uniformRowSampleGram_two_sided_finiteLoewnerLe_ge_one_sub_delta_srht`.
  The logarithmic preprocessing choice is also closed:
  `real_sqrt_eight_log_div_pos_of_pos_lt`,
  `real_mul_exp_neg_mul_sqrt_eight_log_div_sq_div_eight_eq`,
  `rademacherTraceProbability_eventProb_forall_rowNormSq_signedHadamard_le_log_delta_ge_one_sub_delta`,
  `rademacherTraceProbability_eventProb_forall_leverageScoreProb_signedHadamard_le_log_delta_ge_one_sub_delta`,
  and
  `signedHadamardUniformRowTraceProbability_eventProb_uniformRowSampleGram_two_sided_finiteLoewnerLe_ge_one_sub_delta_srht_log_preprocess`.
  The matching source-sharp floating-point constant-budget transfer is also
  closed by
  `signedHadamardUniformRowTraceProbability_eventProb_fl_uniformRowSampleGramDot_two_sided_finiteLoewnerLe_ge_one_sub_delta_constBudget_srht`
  and
  `signedHadamardUniformRowTraceProbability_eventProb_fl_uniformRowSampleGramDot_two_sided_finiteLoewnerLe_ge_one_sub_delta_constBudget_srht_log_preprocess`.
  The SRHT branch has two consecutive clean weak-component passes recorded in
  the not-proved ledger; non-SRHT Algorithm 3 distributions should use separate
  proof-source/bottleneck rows.
- 2026-05-31: Advanced the rectangular QR/preconditioner red bottleneck along
  the Cox--Higham pivoted/sorted weighted least-squares route.  The first local
  dependency, the signed Householder denominator bound
  `householderTrailingActiveVector_inner_self_ge_two_trailingNorm2Sq_of_mul_nonpos`
  and
  `householderTrailingActiveVector_inner_self_ge_two_trailingNorm2Sq_signed`, is
  now proved in `HouseholderSpec.lean` and has two weak-component passes.  It
  formalizes `2 ||x_tail||_2^2 <= v^T v`, the algebraic core of Cox--Higham
  Lemma 2.1 / equation (2.5).  The column-pivoting comparison also has two
  weak-component passes by `householderTrailingColumnNorm2Sq`,
  `exists_householderTrailingColumnNorm2Sq_active_max`,
  `abs_inner_householderTrailingActiveVector_trailingPart_le_vecNorm2_mul_sqrt`,
  and
  `abs_inner_householderTrailingActiveVector_column_le_vecNorm2_mul_sqrt_of_pivot_max`.
  The Cox--Higham scalar endpoint and first row-growth step are now proved by
  `abs_householderBeta_mul_inner_column_le_sqrt_two_of_signed_pivot_max` and
  `abs_householder_signed_pivot_update_entry_le_one_add_sqrt_two_mul_row_bound`;
  two weak-component passes for these theorems are clean.
  The row-sorting stage accumulation is now formalized by
  `scalar_growth_iterate_bound`,
  `coxHigham_rowSorting_active_entry_bound_of_prior_growth`, and
  `coxHigham_rowSorting_active_entry_bound_of_stage_growth`; two
  weak-component passes for these theorems are clean.
  The pivot-row active-tail norm step from Cox--Higham equations (4.4)--(4.5)
  is now formalized in ambient-dimension form by
  `vecNorm2_le_sqrt_card_mul_of_abs_le`,
  `coxHigham_pivot_row_entry_bound_of_active_tail_entry_bound`, and
  `coxHigham_pivot_row_entry_bound_of_stage_entry_bound`; two weak-component
  passes are clean for this dependency.
  The scalar row-wise accumulated perturbation dependency is now formalized by
  `scalarAffineGrowthBudget`, `scalar_affine_growth_iterate_bound`,
  `coxHigham_rowwise_error_accumulation_bound`, and
  `coxHigham_rowSorting_active_entry_bound_with_accumulated_error`; two
  weak-component passes for these theorems are clean.
  The concrete stored rounded panel per-step FP budget is now represented by
  `fl_householderStoredPanelStep_active_entry_componentwise_error_bound`,
  `coxHigham_storedPanelStep_row_error_recurrence_of_exact_lipschitz`, and
  `coxHigham_storedPanel_sequence_rowwise_error_accumulation_bound_of_exact_lipschitz`;
  two weak-component passes for these theorems are clean.  A direct
  row-magnitude adapter has also been added:
  `coxHigham_storedPanelStep_active_entry_bound_of_exact_growth` and
  `coxHigham_storedPanel_sequence_active_entry_bound_of_exact_growth`;
  two weak-component passes validate this route-shape correction as a scoped
  dependency, not as the final row-wise QR theorem.
  The non-pivot active-row exact same-reflector bridge is now formalized by
  `matMulVec_householder_signed_pivot_update_entry_eq` and
  `coxHigham_exact_same_reflector_row_growth_of_signed_pivot_row_bound`; two
  weak-component passes validate this one-step bridge as a scoped route
  dependency, not as the final row-wise QR theorem.
  The exact signed pivot-row same-reflector bridge is also now formalized by
  `householderBeta_mul_inner_self_eq_two`,
  `abs_matMulVec_householder_pivot_le_trailing_vecNorm2_of_zero_prefix_orthogonal`,
  `coxHigham_signed_pivot_row_update_abs_le_trailing_vecNorm2`, and
  `coxHigham_exact_signed_pivot_row_entry_bound_of_stage_entry_bound`; two
  weak-component passes validate this one-step pivot-row bridge as a scoped
  route dependency, not as the final row-wise QR theorem.
  The one-step active-row case split is now formalized by
  `coxHigham_exact_signed_pivot_active_row_entry_bound_of_stage_bounds`; two
  weak-component passes validate this combined one-step bridge as a scoped
  route dependency, not as the final row-wise QR theorem.
  The exact multi-stage loop bridge is now represented by the concrete
  `exactSignedPivotHouseholderPanelStep` and the sequence theorems
  `coxHigham_exactSignedPivotPanel_sequence_active_entry_bound_of_stage_budgets`
  and
  `coxHigham_exactSignedPivotPanel_sequence_active_entry_bound_of_geometric_stage_budgets`;
  two weak-component passes validate this stage-budget propagation dependency as
  a scoped exact loop theorem, not as the final row-wise QR theorem.  The
  exact-to-FP handoff for this honest active-row factor is now represented by
  `coxHigham_storedPanelStep_active_entry_bound_of_exact_growth_factor`,
  `coxHigham_storedPanel_sequence_active_entry_bound_of_exact_growth_factor`,
  and
  `coxHigham_storedPanel_sequence_active_entry_bound_of_exact_active_growth`;
  two weak-component passes validate this handoff dependency as a scoped
  exact-to-FP bridge, not as the final row-wise QR theorem.
  The source-shaped handoff has also been corrected to explicit stage budgets:
  `coxHigham_storedPanelStep_active_entry_bound_of_exact_stage_budget_factor`,
  `coxHigham_storedPanel_sequence_active_entry_bound_of_exact_stage_budgets_factor`,
  `coxHigham_storedPanel_sequence_active_entry_bound_of_exact_active_stage_budgets`,
  and
  `coxHigham_storedPanelStep_active_entry_bound_of_signed_pivot_stage_bounds`;
  two weak-component passes validate this stage-budget dependency as a scoped
  exact-to-FP bridge, not as the sorting-policy proof or final row-wise QR
  theorem.
  The one-step active-block sorting-field adapter
  `coxHigham_exactSignedPivotPanelStep_active_block_bound_of_stage_bound` has
  been added; two weak-component passes validate it as a scoped dependency. It
  closes only the conversion from one active-block bound to the row/column
  fields of the signed-pivot step, not multi-stage sorting-policy propagation.
  The exact sequence active-block wrappers
  `coxHigham_exactSignedPivotPanel_sequence_active_block_bound_of_stage_budgets`
  and
  `coxHigham_exactSignedPivotPanel_sequence_active_block_bound_of_geometric_stage_budgets`
  have been added; two weak-component passes validate them as scoped
  dependencies. They close only source-shaped field packaging for a visible
  active-block budget family.
  The exact active-block propagation theorem
  `coxHigham_exactSignedPivotPanel_sequence_active_block_bound_of_initial_block_bound`
  has been added and now has two weak-component passes clean. It derives the
  active-block family from an initial entrywise bound and monotone active
  windows, while leaving positive active norm and pivot-max fields visible.
  The positive active-norm field is now reduced to pivot maximality plus a
  nonzero remaining-active-block witness via
  `householderTrailingColumnNorm2Sq_pos_of_pivot_max_exists_active_entry_ne`
  and the sequence wrapper
  `coxHigham_exactSignedPivotPanel_sequence_active_block_bound_of_initial_block_bound_of_active_block_nonzero`.
  Two weak-component passes validate this reduction as a scoped dependency.
  The raw pivot-max inequality is now supplied by the finite active max-pivot
  selector `householderActiveMaxPivotColumn` and the sequence wrapper
  `coxHigham_exactSignedPivotPanel_sequence_active_block_bound_of_initial_block_bound_of_active_max_pivot`,
  replacing it by a visible pivot-policy equation. Two weak-component passes
  validate this finite-selector reduction as a scoped dependency.
  The active-nonzero witness is now reduced further to positive active-block
  mass via `householderActiveBlockNorm2Sq`,
  `exists_active_entry_ne_of_householderActiveBlockNorm2Sq_pos`, and
  `coxHigham_exactSignedPivotPanel_sequence_active_block_bound_of_initial_block_bound_of_active_block_norm_pos`.
  Two weak-component passes validate this positive-mass bridge as a scoped
  dependency. The active max-pivot policy for displayed sorted stages is now
  supplied by `householderSwapColumns_activeMaxPivotColumn_pivot_max` and
  `coxHigham_exactSignedPivotPanel_sequence_active_block_bound_of_initial_block_bound_of_swapped_active_max_pivot`;
  two weak-component passes validate this swapped-policy bridge as a scoped
  dependency.
  The raw-to-swapped active-block mass bridge is now validated:
  `householderActiveBlockNorm2Sq_pos_of_exists_active_entry_ne`,
  `householderActiveBlockNorm2Sq_swapColumns_pos_of_pos`, and
  `coxHigham_exactSignedPivotPanel_sequence_active_block_bound_of_initial_block_bound_of_swapped_active_max_pivot_of_raw_active_block_norm_pos`
  move the positive active-block mass assumption back to the raw pre-swap
  stage. Two weak-component passes validate this bridge as a scoped dependency.
  The rounded stored active-block budget recurrence has now been added:
  `signedPivotHouseholderVector`, `signedPivotHouseholderBeta`, and
  `coxHigham_storedPanel_sequence_active_block_bound_of_signed_pivot_stage_bounds`
  propagate rounded active-block budgets through the signed-pivot stored panel
  under visible nonbreakdown, pivot-maximality, storage, monotone active-window,
  and compact-budget recurrence fields. Two weak-component passes validate this
  theorem as a scoped dependency.  The QR-side raw-stage active-block
  nonbreakdown bridge is now added: the previous-span, leading-witness,
  local-left-inverse, and determinant routes each imply positive active-block
  mass, and `householderActiveBlockNorm2Sq_pos_sequence_of_leading_block_det_ne_zero`
  packages the determinant route for stored QR stages.  Two weak-component
  passes validate this as a scoped dependency.  The generic rectangular
  QR/preconditioner theorem remains open.  The new route-elimination theorem
  `not_forall_leadingBlock_upper_det_activeBlockPos_implies_offdiag_le_diag`
  shows that upper-triangular nonsingular leading blocks plus positive
  active-block mass still do not imply the row-wise off-diagonal domination
  field required by `StoredQRSourceOffDiagonalControl`.  The row-sorting
  invariance foundation is now added too: `vecPermute`, `rectPermuteRows`,
  `rectPermuteCols`, `vecNorm2Sq_permute`, `frobNormSqRect_permuteRows`,
  `frobNormSqRect_permuteCols`, `frobNormRect_permuteRows`,
  `frobNormRect_permuteCols`, `rectMatMulVec_permuteRows`,
  `rectLSGram_permuteRows`, `rectLSRhs_permuteRows`,
  `lsResidual_permuteRows`, and `lsObjective_permuteRows` prove that finite
  row sorting preserves rectangular least-squares objectives and
  normal-equation data.  The column-pivoting relabeling foundation is now added
  as well: `vecPermute_symm_vecPermute`, `vecPermute_vecPermute_symm`,
  `rectMatMulVec_permuteCols`, `rectLSGram_permuteCols`,
  `rectLSRhs_permuteCols`, `RectLSNormalEquations.of_permuteCols`,
  `lsResidual_permuteCols`, `lsObjective_permuteCols`, and
  `IsLeastSquaresMinimizer.of_permuteCols`; this foundation has two clean
  weak-component passes and is recorded as `LS.2g-dt`.  The unpivoted
  source-controlled solver handoff is now also composed into the Algorithm 2
  high-probability rounded objective theorem: `storedQRFinalR`,
  `storedQRFinalTopRhs`, `storedQRBackSubSolution`, and
  `leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_sourceOffDiagonalControl_solver`
  close the equation (8) handoff once `StoredQRSourceOffDiagonalControl` is
  supplied.  The row-budget decomposition is now added:
  `StoredQRSourceOffDiagonalControl.of_stored_trailing_sequence_leadingBlock_det_ne_zero_normSqBudget_rowBudget_product`
  and
  `LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_leadingBlock_det_ne_zero_normSqBudget_rowBudget_product`
  split the off-diagonal-control field into row-growth upper budgets and
  diagonal lower-bound obligations.  Two weak-component passes validate this
  row-budget decomposition as a scoped dependency.  Next progress must prove
  those fields for the concrete raw stages and connect the rounded sequence
  result to the QR/preconditioner solve theorem.  The next row-growth
  propagation bridge is now added in `HouseholderQR.lean`:
  `qrLeadingOffdiagStop`,
  `fl_householderStoredPanel_sequence_completed_column_eq_pivot_succ`, and
  `fl_householderStoredPanel_sequence_leadingBlock_offdiag_budget_of_exact_stage_budgets_factor`
  convert Cox--Higham stage budgets into displayed leading-block upper
  off-diagonal row budgets.  Two weak-component passes validate this bridge:
  focused `lake build LeanFpAnalysis.FP.Algorithms.QR.HouseholderQR`, executable
  lookup, `git diff --check`, touched-file marker scan, axiom audit, PDF
  compile/repair/text extraction, and rendered pages 172 and 203 all pass with
  only the pre-existing unused-variable warnings and standard axiom footprint.
  The least-squares stage-budget handoff is now added:
  `StoredQRSourceOffDiagonalControl.of_stored_trailing_sequence_leadingBlock_det_ne_zero_normSqBudget_stageBudget_rowBudget_product`
  and
  `LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_leadingBlock_det_ne_zero_normSqBudget_stageBudget_rowBudget_product`
  compose stage budgets plus diagonal lower bounds into the local source-control
  and QR solve certificates.  Two weak-component passes validate this handoff:
  focused `lake build LeanFpAnalysis.FP.Algorithms.LeastSquares.LSQRSolve`,
  executable lookup, `git diff --check`, touched-file marker scan, axiom audit,
  PDF compile/repair/text extraction, and rendered pages 173 and 203 all pass
  with only the pre-existing unused-variable warnings and standard axiom
  footprint.  Next progress must prove the diagonal lower-bound/nonbreakdown
  field or instantiate the remaining concrete stage-budget/pivot-zeroing
  fields.  The next scoped dependency has started: `HouseholderQR.lean` now
  defines `storedQRSignedStageVector`, `storedQRSignedStageBeta`, and proves
  `fl_householderStoredPanel_sequence_leadingBlock_offdiag_budget_of_signed_stage_budgets_factor`,
  specializing the displayed off-diagonal row-growth bridge to the actual
  signed stored-QR stages.  Focused build and two weak-component passes validate
  this specialization.  The least-squares layer now also proves the signed-stage
  source-control and solver handoff theorems
  `StoredQRSourceOffDiagonalControl.of_stored_trailing_sequence_leadingBlock_det_ne_zero_normSqBudget_signedStageBudget_rowBudget_product`
  and
  `LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_leadingBlock_det_ne_zero_normSqBudget_signedStageBudget_rowBudget_product`.
  Focused build and two weak-component passes validate this handoff.  The exact
  pivot-column zeroing field is now formalized by
  `storedQRSignedStage_pivot_column_zero_below_of_trailingNorm_pos` and
  `storedQRSignedStage_pivot_zeroing_field_of_trailingNorm_pos`.  Focused build
  and two weak-component passes validate this field.  The norm-square-budget
  adapter `storedQRSignedStage_pivot_zeroing_field_of_normSqBudget`, together
  with
  `StoredQRSourceOffDiagonalControl.of_stored_trailing_sequence_leadingBlock_det_ne_zero_normSqBudget_signedStageBudget_rowBudget_product_of_normSqBudget`
  and
  `LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_leadingBlock_det_ne_zero_normSqBudget_signedStageBudget_rowBudget_product_of_normSqBudget`,
  now removes the independent `hpivot` hypothesis from the signed-stage
  solver-facing route; focused build and two weak-component passes validate
  this adapter.  The uniform-stage-budget handoff
  `qrLeadingOffdiagStop_le`,
  `StoredQRSourceOffDiagonalControl.of_stored_trailing_sequence_leadingBlock_det_ne_zero_normSqBudget_signedStageUniformBudget_product_of_normSqBudget`,
  and
  `LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_leadingBlock_det_ne_zero_normSqBudget_signedStageUniformBudget_product_of_normSqBudget`
  now validates with two weak-component passes that monotone stage budgets
  remove the terminal row-budget-domination field.  The local exact
  same-reflector row split
  `storedQRSignedStage_exact_same_reflector_bound_of_prefix_or_active_stage_bounds`
  now has two clean weak-component passes: prefix rows use the zero-prefix
  Householder identity and active rows use the Cox--Higham signed-pivot
  active-row theorem.  The least-squares wrappers
  `StoredQRSourceOffDiagonalControl.of_stored_trailing_sequence_leadingBlock_det_ne_zero_normSqBudget_signedStageUniformBudget_product_of_normSqBudget_stage_entry_bounds`
  and
  `LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_leadingBlock_det_ne_zero_normSqBudget_signedStageUniformBudget_product_of_normSqBudget_stage_entry_bounds`
  now remove the abstract `hexact` field from the uniform-stage-budget route by
  deriving it from concrete stage row/column entry bounds, pivot maximality,
  and norm-square nonbreakdown; focused build and two weak-component passes
  validate this scoped handoff.  The next proof target is the diagonal
  lower-bound/nonbreakdown field or remaining concrete stage-entry recurrence.
  The row-budget diagonal-bound handoff now has the offdiag-row-only correction
  `StoredQRSourceOffDiagonalControl.of_stored_trailing_sequence_leadingBlock_det_ne_zero_normSqBudget_rowBudget_product_of_offdiag_rows`
  and
  `LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_leadingBlock_det_ne_zero_normSqBudget_rowBudget_product_of_offdiag_rows`,
  which require `rowBudget k i <= |S_k ii|` only for `i.val < k`.  Focused
  build and two weak-component passes validate this statement correction.
  The correction is now propagated through the stage-budget, signed-stage,
  norm-square-derived pivot-zeroing, uniform-stage-budget, and concrete
  stage-entry-bound LSQRSolve handoffs via the corresponding `_offdiag_rows`
  source-control and solver theorem families.  Focused LSQRSolve build passes
  with only the pre-existing HouseholderQR unused-variable warnings; two weak
  passes now close this checkpoint.  Next bottleneck progress should target
  either diagonal lower-bound/nonbreakdown for rows `i < k` or the remaining
  concrete stage-entry recurrence.
  The active/prefix stage-entry split was added next:
  `StoredQRSourceOffDiagonalControl.of_stored_trailing_sequence_leadingBlock_det_ne_zero_normSqBudget_signedStageUniformBudget_product_of_normSqBudget_activePrefix_stage_entry_bounds_offdiag_rows`
  and
  `LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_leadingBlock_det_ne_zero_normSqBudget_signedStageUniformBudget_product_of_normSqBudget_activePrefix_stage_entry_bounds_offdiag_rows`
  replace all-row stage-entry hypotheses by an active-suffix block budget plus a
  prefix displayed-row budget.  Focused LSQRSolve build passes, and two weak
  passes now validate this checkpoint.  The active-suffix recurrence handoff has
  since been added too:
  `StoredQRSourceOffDiagonalControl.of_stored_trailing_sequence_leadingBlock_det_ne_zero_normSqBudget_signedStageUniformBudget_product_of_normSqBudget_activePrefix_activeBlockRecurrence_offdiag_rows`
  and
  `LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_leadingBlock_det_ne_zero_normSqBudget_signedStageUniformBudget_product_of_normSqBudget_activePrefix_activeBlockRecurrence_offdiag_rows`
  instantiate the existing signed-pivot Cox--Higham active-block theorem for the
  stored QR pivot map.  Focused LSQRSolve build passes, and two weak-component
  passes now validate this checkpoint.  The prefix-row recurrence has now been
  added too: `storedQRSignedStage_active_block_bound_of_signed_stage_budget`
  exposes the active block as a reusable theorem,
  `storedQRSignedStage_prefix_row_bound_of_active_block_and_prefix_budget`
  proves displayed prefix-row bounds from a one-step prefix budget, and the
  source-control/solver wrappers with suffix
  `_activePrefix_activeBlockRecurrence_prefixRowRecurrence_offdiag_rows` remove
  the raw prefix-row-bound hypothesis.  Focused LSQRSolve build passes, and two
  weak-component passes now validate this checkpoint.  If resuming, target
  diagonal lower-bound/nonbreakdown, compact-product smallness, or concrete
  one-step active/prefix budget dependencies.
  The one-step budget dependency is now further packaged by a finite global
  compact-step budget: `storedQRSignedStageGlobalCompactBudget`,
  `storedQRSignedStage_compact_component_le_globalBudget`,
  `storedQRSignedStage_active_prefix_budgets_of_globalCompactBudget`, and the
  `_activePrefix_activeBlockRecurrence_globalCompactBudget_offdiag_rows`
  source-control/solver wrappers reduce displayed off-diagonal, active-block,
  and prefix-row one-step fields to one scalar recurrence.  Focused LSQRSolve
  build passes; two weak-component passes now validate this latest checkpoint.
  The completed-column preservation field has now been closed by
  `storedQRSignedStage_completed_column_preservation`, which derives old-column
  exact-reflector preservation from the stored prefix-lower-zero invariant and
  the zero-prefix Householder support lemma.  The completed-column global-budget
  source-control/solver wrappers build, and two weak-component passes are
  clean.  The per-pivot compact-product field is now packaged by
  `storedQRCompactSequenceProductBudget` and the
  `_globalCompactBudget_completedColumns_globalProduct_offdiag_rows`
  source-control/solver wrappers; two weak-component passes are clean.  The
  current RandNLA assembly theorem
  `leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_activePrefix_globalProduct_solver`
  has two clean weak-component passes.  If resuming, target diagonal
  lower-bound/nonbreakdown and global compact-product smallness from a concrete
  pivoted/sorted/off-diagonal-controlled loop.
  The global-product smallness bookkeeping now also has the converse finite
  maximum adapters:
  `storedQRCompactSequenceProductBudget_lt_one_of_forall_expr_lt` and
  `storedQRCompactSequenceProductBudget_lt_one_of_forall_pivot_product`.  These
  prove that `storedQRCompactSequenceProductBudget < 1` follows from the
  finite per-pivot product inequalities.  Two weak-component passes are clean.
  The active/prefix global-product route now also reuses the local
  leading-block inverse-budget infrastructure:
  `storedQRSignedStage_normSqBudget_of_leadingBlock_det_ne_zero_kappaInf_selfNorm_dualBudget`
  derives the raw norm-square nonbreakdown margin from local determinant,
  `κ∞`/self-norm, and dual compact-budget data.  The corresponding
  `kappaInf_dualBudget` source-control, solver, and equation (8) wrappers
  build and remove `hbudgetNormSq` from the newest route when those structured
  assumptions are supplied.  Two weak-component passes are clean for this
  checkpoint: focused build, executable lookup, `git diff --check`, marker
  scan, qualified axiom audit, PDF compile, text extraction, and rendered-page
  inspection.  Resume by targeting per-pivot product inequalities,
  offdiag-row diagonal lower bounds, and concrete-loop local
  determinant/conditioning budgets.
- 2026-06-01: Added the diagonal-dominant global-product branch for equation
  (8).  New theorem names:
  `StoredQRSourceOffDiagonalControl.of_stored_trailing_sequence_leadingBlock_det_ne_zero_normSqBudget_diagDominant_globalProduct`,
  `StoredQRSourceOffDiagonalControl.of_stored_trailing_sequence_leadingBlock_det_ne_zero_kappaInf_selfNorm_dualBudget_diagDominant_globalProduct`,
  `LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_leadingBlock_det_ne_zero_kappaInf_selfNorm_dualBudget_diagDominant_globalProduct`,
  and
  `leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_diagDominant_globalProduct_kappaInf_dualBudget_solver`.
  These reuse `IsDiagDominantUpper`, the finite global-product budget, and the
  `κ∞`/dual-budget norm-square adapter to close the offdiag-row diagonal
  lower-bound field under explicit diagonal-dominance assumptions.  This is a
  scoped dependency closure only; diagonal dominance, local
  determinant/conditioning budgets, and product smallness still need to be
  proved for a concrete QR loop or kept visible.  Two weak-component passes are
  clean: focused build, executable lookup, `git diff --check`, marker scan,
  qualified axiom audit, PDF compile, text extraction, and rendered page
  inspection.
- 2026-06-01: Added
  `storedQRCompactSequenceProductBudget_lt_one_of_diagDominant_factor_norm_bounds`.
  It proves `storedQRCompactSequenceProductBudget < 1` from global bounds
  `D_k <= Dmax`, `||A_k(:,k)||_2 <= Nmax`, local diagonal dominance, and the
  scalar inequality `2 * Dmax * (m * (c_seq * Nmax)^2) < 1`.  This reduces the
  red product-smallness dependency to concrete-loop proofs of those global
  factor/norm bounds plus the scalar inequality.  Two weak-component passes are
  clean: focused build, executable lookup, `git diff --check`, marker scan,
  qualified axiom audit, PDF compile, text extraction, and rendered page
  inspection.
- 2026-06-01: Added the canonical finite-max product-smallness adapter
  `storedQRCompactSequenceProductBudget_lt_one_of_diagDominant_finite_max_smallness`
  plus `storedQRDiagDominantInvFactorBudget`,
  `storedQRDiagDominantInvFactor_le_budget`,
  `storedQRDiagDominantInvFactorBudget_nonneg`,
  `storedQRPivotColumnNormBudget`, `storedQRPivotColumnNorm_le_budget`, and
  `storedQRPivotColumnNormBudget_nonneg`.  These choose finite maxima for the
  diagonal-dominant inverse factor and pivot-column norm, remove separate
  `Dmax`/`Nmax` bound hypotheses, and leave only the scalar smallness
  inequality for the canonical maxima.  Two weak-component passes are clean:
  focused build, executable lookup, `git diff --check`, marker scan, qualified
  axiom audit, PDF compile, text extraction, and rendered page inspection.
- 2026-06-01: Threaded the canonical finite-max product-smallness scalar into
  the diagonal-dominant equation (8) QR handoff.  New theorem names:
  `StoredQRSourceOffDiagonalControl.of_stored_trailing_sequence_leadingBlock_det_ne_zero_normSqBudget_diagDominant_finiteMaxSmallness`,
  `StoredQRSourceOffDiagonalControl.of_stored_trailing_sequence_leadingBlock_det_ne_zero_kappaInf_selfNorm_dualBudget_diagDominant_finiteMaxSmallness`,
  `LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_leadingBlock_det_ne_zero_kappaInf_selfNorm_dualBudget_diagDominant_finiteMaxSmallness`,
  and
  `leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_diagDominant_finiteMaxSmallness_kappaInf_dualBudget_solver`.
  This removes the raw `storedQRCompactSequenceProductBudget < 1` field from
  that theorem surface when the scalar inequality over
  `storedQRDiagDominantInvFactorBudget` and `storedQRPivotColumnNormBudget` is
  supplied.  Focused LSQRSolve and LeastSquaresSketch builds pass, and two
  weak-component passes are clean: `git diff --check`, marker scan, focused
  LeastSquaresSketch build, executable lookup, qualified axiom audit, PDF
  compile, text extraction, and rendered page inspection.  The axiom audit
  reports only standard `propext`, `Classical.choice`, and `Quot.sound`.
- 2026-06-01: Added the concrete-dual finite-max diagonal-dominant equation (8)
  handoff.  New theorem names:
  `LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_leadingBlock_det_ne_zero_diagDominant_finiteMaxSmallness_concreteDual`
  and
  `leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_diagDominant_finiteMaxSmallness_concreteDual_solver`.
  These reuse the local concrete diagonal-dominant inverse-budget theorem and
  the canonical finite-max product-smallness adapter, removing auxiliary `κ`,
  `K`, and dual compact-budget fields from the finite-max diagonal-dominant
  QR/equation (8) surface.  First weak-component validation is clean: focused
  build, executable lookup, `git diff --check`, marker scan, qualified axiom
  audit, PDF compile, text extraction, and rendered-page inspection all passed.
  The axiom audit reports only standard `propext`, `Classical.choice`, and
  `Quot.sound`.  The repeated pass is also clean, and the temporary axiom-audit
  file was deleted.  This checkpoint now has two consecutive clean passes.
- 2026-06-01: Added the determinant-free concrete-dual finite-max
  diagonal-dominant equation (8) handoff.  New theorem names:
  `det_ne_zero_of_diagDominantUpper`,
  `LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_diagDominant_finiteMaxSmallness_concreteDual`,
  and
  `leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_diagDominant_finiteMaxSmallness_concreteDual_solver_of_diagDominant`.
  The local determinant field is now derived from `IsDiagDominantUpper`; the
  finite-max concrete-dual branch no longer exposes local determinant,
  auxiliary `κ`, auxiliary `K`, or dual compact-budget hypotheses.  Two
  weak-component validation passes are clean: focused build, executable lookup,
  `git diff --check`, marker scan, qualified axiom audit, PDF compile, text
  extraction, and rendered-page inspection all passed twice.  The repeated
  axiom audit reports only standard `propext`, `Classical.choice`, and
  `Quot.sound`, and the temporary axiom-audit file was deleted.
- 2026-06-01: Added the direct packaged off-diagonal-control RandNLA equation
  (8) handoff.  New theorem name:
  `leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_offDiagonalControl_solver`.
  It consumes samplewise `StoredQROffDiagonalControlInvariant` and composes the
  local stored-QR backward-error certificate with the already proved
  high-probability finite-Loewner sampled-row objective theorem.  The existing
  source-shaped theorem
  `leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_sourceOffDiagonalControl_solver`
  now derives the packaged invariant via
  `StoredQROffDiagonalControlInvariant.of_sourceOffDiagonalControl` and reuses
  the direct theorem.  Two weak-component validation passes are clean: focused
  build, executable lookup, `git diff --check`, marker scan, qualified axiom
  audit, PDF compile, text extraction, and rendered-page inspection all passed
  twice.  The repeated axiom audit reports only standard `propext`,
  `Classical.choice`, and `Quot.sound`.  This closes the route-1
  solver-to-RandNLA handoff for the packaged invariant, not the proof that a
  concrete arbitrary no-pivot QR loop satisfies that invariant.
- 2026-06-01: Added the finite-max diagonal-dominant constructor for the
  packaged route-1 invariant.  New theorem name:
  `StoredQROffDiagonalControlInvariant.of_diagDominant_finiteMaxSmallness`.
  It derives `StoredQROffDiagonalControlInvariant` from local
  `IsDiagDominantUpper` leading blocks and the canonical scalar finite-max
  smallness inequality by reusing `det_ne_zero_of_diagDominantUpper` and
  `storedQRCompactSequenceProductBudget_lt_one_of_diagDominant_finite_max_smallness`.
  First weak-component validation is clean: focused LSQRSolve build,
  executable lookup, `git diff --check`, marker scan, qualified axiom audit,
  PDF compile, text extraction, and rendered page inspection all passed.  The
  axiom audit reports only standard `propext`, `Classical.choice`, and
  `Quot.sound`.  The remaining route-1 red dependencies are proving or
  classifying local diagonal dominance and the scalar finite-max smallness
  inequality for a concrete no-pivot stored QR loop.
  The repeated validation pass is also clean: focused LSQRSolve build,
  executable lookup, `git diff --check`, marker scan, qualified axiom audit,
  PDF compile, text extraction, and rendered page inspection passed again.
  This checkpoint now has two consecutive clean passes.
- 2026-06-01: Added the Cox--Higham row-budget diagonal-lower-bound route
  elimination.  New theorem name:
  `not_forall_leadingBlock_upper_det_activeBlockPos_offdiagBudget_implies_rowBudget_diag`.
  It uses the local `[[1,2],[0,1]]` witness with row budget `2` to show that
  upper-triangular nonsingular leading blocks, positive active-block mass, and
  a valid strict-upper-entry row budget do not imply the matching diagonal
  lower-bound field; the first displayed diagonal has magnitude `1`.  Two
  weak-component validation passes are clean: focused LSQRSolve build,
  executable lookup, `git diff --check`, touched Lean marker scan, qualified
  axiom audit, PDF compile, text extraction, and rendered page inspection
  passed twice.  This is route elimination only.  The next red-bottleneck
  progress must target a genuine diagonal lower-bound/nonbreakdown invariant,
  a stronger source theorem that supplies it, or a final solver-facing theorem
  that keeps the field explicit.
- 2026-06-01: Added the explicit-domain row-budget certificate
  `StoredQRDisplayedRowBudgetControl` and the wrapper theorems
  `StoredQRSourceOffDiagonalControl.of_stored_trailing_sequence_leadingBlock_det_ne_zero_normSqBudget_rowBudgetControl_product`
  and
  `LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_leadingBlock_det_ne_zero_normSqBudget_rowBudgetControl_product`.
  This packages the Cox--Higham displayed strict-upper row-budget field and
  the matching offdiag-row diagonal lower-bound/nonbreakdown field as a visible
  source/domain assumption.  Two weak-component validations are clean:
  focused LSQRSolve build, executable lookup, `git diff --check`, marker scan,
  qualified axiom audit, PDF compile, text extraction, and rendered-page
  inspection all passed twice; the axiom audit reports only standard
  `propext`, `Classical.choice`, and `Quot.sound`, and the temporary audit file
  was deleted after validation.  This is a theorem-statement correction, not a
  proof of the diagonal lower-bound invariant.
- 2026-06-01: Added the equation (8) probability-level row-budget-control
  handoff
  `leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_rowBudgetControl_solver`.
  It consumes samplewise `StoredQRDisplayedRowBudgetControl`, derives the
  source-shaped stored-QR certificate, and reuses the high-probability rounded
  sampled-row objective theorem.  Focused RandNLA least-squares build passed
  with only the pre-existing `HouseholderQR.lean` unused-variable warnings.
  Two weak-component validations are clean: executable lookup, `git
  diff --check`, marker scan, qualified axiom audit, PDF compile, text
  extraction, and rendered page inspection all passed twice; the axiom audit
  reports only standard `propext`, `Classical.choice`, and `Quot.sound`, and
  the temporary audit file was deleted after validation.
  This is a scoped theorem under visible domain assumptions, not a proof of
  the packaged row-budget certificate from a concrete loop.
- 2026-06-01: Added the `κ∞`/dual-budget equation (8) row-budget-control
  probability handoff
  `leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_rowBudgetControl_kappaInf_dualBudget_solver`.
  It reuses
  `storedQRSignedStage_normSqBudget_of_leadingBlock_det_ne_zero_kappaInf_selfNorm_dualBudget`
  to derive the norm-square nonbreakdown margin, then calls the existing
  row-budget-control solver theorem.  First weak-component validation is clean:
  focused RandNLA least-squares build, executable lookup, `git diff --check`,
  marker scan, qualified axiom audit, PDF compile, text extraction, and rendered
  page inspection passed; the repeated pass is also clean with the same standard
  axiom audit result.  This removes the raw norm-square
  nonbreakdown hypothesis from the row-budget probability handoff but leaves
  `StoredQRDisplayedRowBudgetControl`, local determinant/`κ∞`/dual-budget data,
  and compact-product smallness visible.
- 2026-06-01: Added
  `StoredQRDisplayedRowBudgetControl.of_signed_stage_budgets_factor_of_normSqBudget`
  in `LSQRSolve.lean`.  This builds the named row-budget control certificate
  from signed-stage Cox--Higham row-growth budgets, deriving pivot-column
  zeroing from the norm-square nonbreakdown budget and keeping the offdiag-row
  diagonal lower-bound field visible.  First weak-component validation is clean:
  focused LSQRSolve build, executable lookup, `git diff --check`, marker scan,
  qualified axiom audit, PDF compile/text/render checks all passed; the axiom
  audit reports only standard `propext`, `Classical.choice`, and `Quot.sound`.
  The repeated pass is also clean with the same standard axiom audit result and
  readable PDF pages 174--175.  The remaining package-producing dependencies are
  the offdiag-row diagonal lower-bound/nonbreakdown invariant and concrete
  stage-budget recurrence.
- 2026-06-01: Added
  `StoredQRDisplayedRowBudgetControl.of_signed_stage_uniformBudget_factor_of_normSqBudget`
  in `LSQRSolve.lean`.  This uniform-stage constructor sets
  `rowBudget k i = stageBudget k` and uses `qrLeadingOffdiagStop_le` plus
  monotonicity to discharge terminal row-budget domination.  First
  weak-component validation is clean: focused LSQRSolve build, executable
  lookup, `git diff --check`, marker scan, qualified axiom audit, PDF
  compile/text/render checks all passed; the axiom audit reports only standard
  `propext`, `Classical.choice`, and `Quot.sound`.  The repeated pass is also
  clean with the same standard axiom audit result and readable PDF pages
  174--175.
- 2026-06-01: Added
  `StoredQRDisplayedRowBudgetControl.of_signed_stage_uniformBudget_globalCompactBudget_of_normSqBudget`
  and
  `StoredQRDisplayedRowBudgetControl.of_signed_stage_uniformBudget_globalCompactBudget_kappaInf_dualBudget`
  in `LSQRSolve.lean`.  These constructors package the selected
  `κ∞`/dual-budget route: the norm-square version derives
  `StoredQRDisplayedRowBudgetControl` from monotone stage budgets,
  completed-column preservation, active-block recurrence, prefix-row
  recurrence, pivot maximality, finite global compact-step recurrence, and the
  norm-square nonbreakdown budget; the `κ∞`/dual-budget version derives that
  norm-square budget from the existing leading-block inverse-budget adapter.
  First weak-component validation is clean: `git diff --check`, touched Lean
  marker scan, focused LSQRSolve build, executable lookup, qualified axiom
  audit, PDF compile/text checks, and rendered page 175 passed; the axiom audit
  reports only standard `propext`, `Classical.choice`, and `Quot.sound`.  The
  repeated weak-component pass is also clean with the same standard axiom audit
  result and readable page 175.  This is a dependency closure, not a proof of
  the offdiag-row diagonal lower-bound/nonbreakdown invariant or final generic
  QR/preconditioner theorem.
- 2026-06-01: Added the canonical row-max row-budget bridge in
  `LSQRSolve.lean`: `qrLeadingStrictUpperRowMaxBudget`,
  `qrLeadingStrictUpperRowMaxBudget_entry_le`,
  `qrLeadingStrictUpperRowMaxBudget_le_diag_of_offdiag`, and
  `StoredQRDisplayedRowBudgetControl.of_sourceOffDiagonalControl_rowMaxBudget`.
  This packages an existing `StoredQRSourceOffDiagonalControl` field into
  `StoredQRDisplayedRowBudgetControl` by taking each row budget to be the finite
  maximum of strict-upper absolute values in the displayed row.  Focused build
  passed with only the pre-existing HouseholderQR warnings; first
  weak-component validation is clean: whitespace, marker, focused build,
  executable lookup, qualified axiom audit, PDF compile/text, and rendered page
  175 passed.  This is a safe-direction bridge, not a proof of source
  off-diagonal domination or generic QR/preconditioner closure.  The repeated
  weak-component pass is also clean with the same standard axiom audit result,
  executable lookup exposure, PDF text extraction, and readable rendered page
  175.
- 2026-06-01: Added the direct finite-max diagonal-dominant RandNLA equation
  (8) wrapper for the packaged route-1 invariant.  New theorem name:
  `leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_offDiagonalControl_solver_of_diagDominant_finiteMaxSmallness`.
  It applies
  `StoredQROffDiagonalControlInvariant.of_diagDominant_finiteMaxSmallness`
  samplewise, then reuses the direct packaged off-diagonal-control theorem
  `leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_offDiagonalControl_solver`.
  This removes the packaged-invariant hypothesis from the diagonal-dominant
  finite-max probability surface, while leaving local diagonal dominance and
  the canonical scalar finite-max smallness inequality visible.  First
  weak-component validation is clean: focused build, executable lookup, `git
  diff --check`, marker scan, qualified axiom audit, PDF compile/text, and
  rendered-page inspection passed; the axiom audit reports only standard
  `propext`, `Classical.choice`, and `Quot.sound`.
  The repeated weak-component pass is also clean with the same standard axiom
  audit result and readable rendered pages 115 and 186.  This checkpoint now
  has two consecutive clean passes.
- 2026-06-01: Added the stronger exact-no-pivot route-elimination theorem
  `not_forall_exact_trailing_householder_sequence_implies_diagDominant_and_property`
  in `LSQRSolve.lean`.  It reuses the existing exact two-step Householder
  counterexample to show that the standard no-pivot recurrence cannot
  universally imply diagonal dominance together with any final-block property
  `P`.  This directly rules out a hidden proof of the finite-max
  diagonal-dominant route from the exact recurrence alone; focused LSQRSolve
  build passed and first weak-component validation is clean (`git diff
  --check`, marker scan, focused build, executable lookup, qualified axiom
  audit, PDF compile/text extraction, and rendered page 168).  Repeated
  validation is also clean with the same standard axiom audit result and
  readable rendered page 168.  This closes the route-elimination dependency;
  positive completion still needs a stronger invariant, a pivoted/sorted
  theorem family, or visible scoped assumptions.
- 2026-06-01: Added active-max-pivot variants of the packaged global
  compact-step row-budget constructors in `LSQRSolve.lean`:
  `StoredQRDisplayedRowBudgetControl.of_signed_stage_uniformBudget_globalCompactBudget_activeMaxPivot_of_normSqBudget`
  and
  `StoredQRDisplayedRowBudgetControl.of_signed_stage_uniformBudget_globalCompactBudget_activeMaxPivot_kappaInf_dualBudget`.
  They derive the raw pivot-maximality field from
  `householderActiveMaxPivotColumn_pivot_max`, letting the row-budget package
  expose the algorithmic finite active max-pivot policy instead of a bare
  pivot inequality.  Focused LSQRSolve build passed; first weak-component
  validation is clean (`git diff --check`, marker scan, focused build,
  executable lookup, qualified axiom audit, PDF compile/text extraction, and
  rendered pages 175--176).  The repeated validation pass is also clean with
  the same standard axiom audit result and readable rendered pages 175--176.
  This checkpoint now has two consecutive clean passes.  It closes only the
  pivot-max field for the packaged row-budget route, not diagonal lower
  bounds/nonbreakdown, determinant/conditioning data, compact-product
  smallness, or final QR/preconditioner assembly.
- 2026-06-01: Added the probability-level active-max-pivot wrapper
  `leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_activePrefix_globalProduct_activeMaxPivot_kappaInf_dualBudget_solver`
  in `LeastSquaresSketch.lean`.  It replaces the raw samplewise pivot-max
  inequality in the active/prefix global-product `κ∞` equation (8) theorem
  surface by the policy equation choosing `householderActiveMaxPivotColumn` as
  the displayed pivot column, derives the raw field with
  `householderActiveMaxPivotColumn_pivot_max`, then applies the existing
  probability theorem.  First weak-component validation is clean: `git diff
  --check`, marker scan, focused RandNLA least-squares build, executable
  lookup, qualified axiom audit with only standard axioms, PDF compile/text
  extraction, and rendered page 185 passed.  Repeated validation is also clean
  with the same standard axiom audit result and readable rendered page 185.
  This checkpoint now has two consecutive clean passes.  It closes only the
  probability-layer pivot-max surface field; diagonal lower bounds,
  determinant/conditioning data, compact-product smallness, and the final
  generic QR/preconditioner theorem remain open or visible assumptions.
- 2026-06-01: Added the probability-level active-max-pivot row-budget
  global-product wrapper
  `leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_rowBudgetControl_globalProduct_activeMaxPivot_kappaInf_dualBudget_solver`
  in `LeastSquaresSketch.lean`.  It constructs samplewise
  `StoredQRDisplayedRowBudgetControl` from the active-max-pivot global
  compact-step constructor and then applies the finite global-product
  row-budget equation (8) theorem.  First weak-component validation is clean:
  `git diff --check`, marker scan, focused RandNLA least-squares build,
  executable lookup, qualified axiom audit with only standard axioms, PDF
  compile/text extraction, and rendered page 185 passed.  The repeated pass is
  also clean with the same standard axiom audit result and readable rendered
  page 185.  This checkpoint now has two consecutive clean passes.  It closes
  only a packaging/assembly edge; diagonal lower bounds, determinant or
  conditioning data, compact-product smallness, and the final generic
  QR/preconditioner theorem remain open or visible assumptions.
- 2026-06-01: Added the active-max-pivot row-budget diagonal route-elimination
  theorem in `LSQRSolve.lean`.  The new local witnesses
  `activeMaxPivotRowBudgetDiagCounterexampleA0` and
  `activeMaxPivotRowBudgetDiagCounterexampleSeq` show that a first stage with
  an active max-pivot column can be followed by the same row-budget diagonal
  failure stage `[[1,2],[0,1]]`.  The theorem
  `not_forall_leadingBlock_upper_det_activeBlockPos_activeMaxPivot_offdiagBudget_implies_rowBudget_diag`
  therefore rules out deriving the diagonal lower-bound/nonbreakdown field
  from active-block mass, active max-pivot selection, and row-growth upper
  budgets alone.  First weak-component validation is clean: `git diff
  --check`, touched Lean marker scan, focused LSQRSolve build, executable
  lookup, qualified axiom audit, PDF compile/text extraction, and rendered page
  169 passed.  The axiom audit reports only standard `propext`,
  `Classical.choice`, and `Quot.sound`.  The repeated weak-component pass is
  also clean with the same standard axiom audit result and readable rendered
  page 169.  This checkpoint now has two consecutive clean passes.  This is
  route elimination, not a positive diagonal lower-bound invariant.
- 2026-06-01: Added the active-block-budget strengthening
  `not_forall_leadingBlock_upper_det_activeBlockPos_activeMaxPivot_activeBlockBudget_offdiagBudget_implies_rowBudget_diag`
  in `LSQRSolve.lean`.  It reuses the two-stage active max-pivot witness and
  additionally assumes that the same nonnegative row budget bounds every active
  trailing-block entry at each displayed stage.  The witness satisfies that
  active-block magnitude budget with row budget `2`, but the second displayed
  stage still violates the diagonal lower-bound field because the relevant
  diagonal magnitude is `1`.  This red-bottleneck route-elimination dependency
  now has two clean weak-component passes: repeated `git diff --check`, touched
  Lean marker scan, focused `LSQRSolve` build, executable lookup, qualified
  axiom audit, PDF compile/text extraction, and rendered-page inspection passed.
  The axiom audit reports only standard `propext`, `Classical.choice`, and
  `Quot.sound`.  It is route elimination, not a positive diagonal lower-bound
  invariant.
- 2026-06-01: Added the meta-property strengthening
  `not_forall_leadingBlock_upper_det_activeBlockPos_activeMaxPivot_activeBlockBudget_offdiagBudget_property_implies_rowBudget_diag`
  in `LSQRSolve.lean`.  It shows that adding an arbitrary auxiliary side
  property `P A_hat rowBudget` to the active-block-budget row-budget route
  still cannot imply the diagonal lower-bound field; the proof chooses
  `P := True` and reuses the active-block-budget route-elimination theorem.
  This is a guardrail for the red bottleneck: unrelated scalar/product
  hypotheses cannot be treated as hidden diagonal nonbreakdown.  Two
  weak-component validation passes are clean: repeated `git diff --check`,
  touched Lean marker scan, focused `LSQRSolve` build, executable lookup,
  qualified axiom audit, PDF compile/text extraction, and rendered-page
  inspection passed.  The axiom audit reports only standard `propext`,
  `Classical.choice`, and `Quot.sound`.  The remaining valid progress routes
  are a genuine diagonal lower-bound/nonbreakdown invariant, determinant or
  conditioning field closure, compact-product smallness, or an explicit
  visible-assumption theorem surface.
- 2026-06-01: Added the solver-facing active-max-pivot wrapper for the
  active/prefix global-product `κ∞` QR route:
  `LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_leadingBlock_det_ne_zero_kappaInf_selfNorm_dualBudget_signedStageUniformBudget_globalCompactBudget_activeMaxPivot_completedColumns_globalProduct_offdiag_rows`.
  It derives the raw pivot-maximality inequality from the finite active pivot
  selector using `householderActiveMaxPivotColumn_pivot_max` and applies the
  existing raw-pivot solver theorem.  This closes only the local solver-layer
  pivot-policy dependency.  The remaining QR/preconditioner red-bottleneck
  dependencies are still the diagonal lower-bound/nonbreakdown invariant,
  local determinant/conditioning data, dual compact-budget assumptions,
  compact-product smallness, and final generic assembly.  Two weak-component
  passes are clean: whitespace, touched-source marker scan, focused LSQRSolve
  build, executable lookup, qualified axiom audit, PDF compile/text extraction,
  and rendered-page inspection of pages 184--185 passed, with only standard
  `propext`, `Classical.choice`, and `Quot.sound` in the axiom audit.
- 2026-06-01: Added the solver-facing row-budget-control finite-global-product
  wrappers:
  `LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_leadingBlock_det_ne_zero_normSqBudget_rowBudgetControl_globalProduct`
  and
  `LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_leadingBlock_det_ne_zero_kappaInf_selfNorm_dualBudget_rowBudgetControl_globalProduct`.
  These close the local solver-layer per-pivot compact-product family for the
  packaged row-budget route by reusing the existing source-control
  global-product certificate and the `κ∞`/dual-budget norm-square adapter.
  Two weak-component passes are clean: whitespace, touched-source marker scan,
  focused LSQRSolve build, executable lookup, qualified axiom audit, PDF
  compile/text extraction, and rendered-page inspection of pages 184--185
  passed.  The axiom audit reports only standard `propext`,
  `Classical.choice`, and `Quot.sound`.  Remaining QR/preconditioner
  red-bottleneck dependencies are still `StoredQRDisplayedRowBudgetControl`,
  local determinant/conditioning or dual-budget data, scalar compact-product
  smallness, and final generic assembly.
- 2026-06-01: Added the route-1 row-max contraction handoff for the
  rectangular QR/preconditioner bottleneck.  `LSQRSolve.lean` now proves
  `StoredQRDisplayedRowBudgetControl.of_rowMaxBudget_le_diag_factor`,
  `StoredQRSourceOffDiagonalControl.of_stored_trailing_sequence_leadingBlock_det_ne_zero_normSqBudget_rowMaxBudgetFactor_globalProduct`,
  and
  `LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_leadingBlock_det_ne_zero_normSqBudget_rowMaxBudgetFactor_globalProduct`.
  These theorem surfaces say that if a computed-loop invariant supplies a
  scalar `ρ <= 1` with every canonical displayed strict-upper row maximum below
  `ρ * |diag|`, then the packaged row-budget certificate and local solver
  handoff follow under the usual stored recurrence, determinant, norm-square,
  and global compact-product hypotheses.  This is a positive route-1 handoff,
  not a proof of the contraction invariant from generic no-pivot QR.
- 2026-06-01: Added the scalar row-max/diagonal defect handoff for the same
  rectangular QR/preconditioner route.  `LSQRSolve.lean` now defines
  `storedQRRowMaxDiagDefectBudget`, proves
  `storedQRRowMaxDiagDefect_le_budget`, and exposes
  `StoredQRDisplayedRowBudgetControl.of_rowMaxDiagDefectBudget_nonpos`,
  `StoredQRSourceOffDiagonalControl.of_stored_trailing_sequence_leadingBlock_det_ne_zero_normSqBudget_rowMaxDiagDefect_globalProduct`,
  and
  `LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_leadingBlock_det_ne_zero_normSqBudget_rowMaxDiagDefect_globalProduct`.
  The scalar condition `storedQRRowMaxDiagDefectBudget hmn A_hat <= 0`
  packages the `ρ = 1` row-max contraction branch as a finite maximum over
  displayed defects `rowMax - |diag|`.  Two weak-component validation passes
  are clean: repeated whitespace checks, touched-source marker scans, focused
  LSQRSolve builds, executable lookup, qualified axiom audits, PDF
  compile/text extraction, and rendered-page inspections passed; the axiom
  audit reports only standard `propext`, `Classical.choice`, and
  `Quot.sound`.  This reduces the shape of the
  row-budget dependency but does not prove the scalar defect condition,
  determinant/conditioning data, norm-square nonbreakdown, product smallness,
  or the final generic QR/preconditioner theorem from ordinary no-pivot QR.
- 2026-06-01: Added the scalar row-max defect route-elimination theorem pair
  for the rectangular QR/preconditioner bottleneck.  `LSQRSolve.lean` now
  proves
  `exactHouseholderQRDiagDominanceCounterexample_rowMaxDiagDefectBudget_pos`
  and
  `not_forall_exact_trailing_householder_sequence_implies_rowMaxDiagDefectBudget_nonpos`.
  The exact two-stage no-pivot Householder counterexample has positive
  `storedQRRowMaxDiagDefectBudget`, so exact recurrence plus valid squared-norm
  identities and nonzero denominators cannot universally imply the
  nonpositive scalar defect condition.  First weak-component validation is
  clean: whitespace, touched-source marker scan, focused LSQRSolve build,
  executable lookup, qualified axiom audit, PDF compile/text extraction, and
  rendered-page inspection of pages 177--179 passed; the axiom audit reports
  only standard `propext`, `Classical.choice`, and `Quot.sound`.  The repeated
  pass is also clean with the same standard axiom audit result, executable
  lookup exposure, PDF text extraction, and readable rendered pages 177--179.
  This is route elimination only, not a positive scalar defect invariant.
- 2026-06-01: Added the probability-level scalar row-max-defect global-product
  equation (8) wrapper
  `leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_rowMaxDiagDefect_globalProduct_solver`
  in `LeastSquaresSketch.lean`.  It builds the samplewise row-budget
  certificate from `storedQRRowMaxDiagDefectBudget <= 0`, derives per-pivot
  compact-product smallness from `storedQRCompactSequenceProductBudget < 1`,
  and reuses the row-budget-control high-probability objective theorem.  First
  weak-component validation is clean: whitespace, touched-source marker scan,
  focused LeastSquaresSketch build, executable lookup, qualified axiom audit,
  PDF compile/text extraction, and rendered-page inspection of pages 114--118
  passed; the axiom audit reports only standard `propext`, `Classical.choice`,
  and `Quot.sound`.  This is an assembly closure only; the scalar defect
  invariant and concrete-loop determinant/nonbreakdown/product-smallness fields
  remain open or visible.  Repeated validation is also clean with the same
  standard axiom audit result, executable lookup exposure, PDF text extraction,
  and readable rendered pages 114--118, giving this dependency two consecutive
  clean passes.
- 2026-06-01: Added the probability-level primitive
  norm-square/off-diagonal-product equation (8) wrapper
  `leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_leadingBlock_det_ne_zero_normSqBudget_offdiag_product_solver`
  in `LeastSquaresSketch.lean`.  It constructs
  `StoredQRSourceOffDiagonalControl` samplewise from leading-block determinant
  nonzeroness, dimensioned norm-square nonbreakdown, row-wise off-diagonal
  domination, and per-pivot compact-product smallness before applying the
  source-shaped high-probability objective theorem.  First weak-component
  validation is clean: whitespace, touched-source marker scan, focused
  LeastSquaresSketch build, executable lookup, qualified axiom audit, PDF
  compile/text extraction, and rendered-page inspection of pages 114--119
  passed; the axiom audit reports only standard `propext`, `Classical.choice`,
  and `Quot.sound`.  This is an assembly closure only; determinant/nonbreakdown,
  off-diagonal domination, product smallness, and the final generic QR theorem
  remain open or visible.  Repeated validation is also clean with the same
  standard axiom audit result, executable lookup exposure, PDF text extraction,
  and readable rendered pages 114--119, giving this dependency two consecutive
  clean passes.
- 2026-06-01: Added the diagonal-dominance to scalar row-max-defect bridge
  `storedQRRowMaxDiagDefectBudget_nonpos_of_diagDominant` and
  `StoredQRDisplayedRowBudgetControl.of_diagDominant` in `LSQRSolve.lean`.
  Local `IsDiagDominantUpper` displayed leading blocks now imply
  `storedQRRowMaxDiagDefectBudget <= 0`, and hence the packaged row-budget
  certificate, by taking the finite maximum of the row-wise strict-upper
  diagonal-dominance inequalities.  First weak-component validation is clean:
  whitespace, touched-source marker scan, focused LSQRSolve build, executable
  lookup, qualified axiom audit, PDF compile/text extraction, and rendered-page
  inspection of pages 177--179 passed; the axiom audit reports only standard
  `propext`, `Classical.choice`, and `Quot.sound`.  This is a bridge between
  visible route surfaces, not a proof that generic no-pivot QR is diagonally
  dominant.  Repeated validation is also clean with the same standard axiom
  audit result, executable lookup exposure, PDF text extraction, and readable
  rendered pages 177--179, giving this dependency two consecutive clean passes.
- 2026-06-02: Added the exact/zero-compact compact-product endpoint
  `storedQRCompactSequenceProductBudget_lt_one_of_relativeBudget_eq_zero` in
  `LSQRSolve.lean`.  If
  `storedQRCompactSequenceRelativeBudget hmn fp A_hat b_hat alpha = 0`, then
  the stored compact-product budget is automatically below one.  This closes
  only the exact/zero-compact product-smallness dependency for the
  rectangular QR/preconditioner bottleneck; positive floating-point
  compact-product smallness, local diagonal dominance/off-diagonal control,
  determinant/conditioning fields, norm-square nonbreakdown, and the final
  generic equation (8) QR/preconditioner theorem remain open.  Two
  weak-component passes are clean: focused LSQRSolve build, executable lookup,
  `git diff --check`, touched Lean marker scan, qualified axiom audit, PDF
  compile/text extraction, and rendered-page inspection of page 186 passed.
  The axiom audit reports only standard `propext`, `Classical.choice`, and
  `Quot.sound`.
- 2026-06-02: Added the positive relative-budget cap theorem
  `storedQRCompactSequenceProductBudget_lt_one_of_diagDominant_finite_max_relativeBudget_le`
  in `LSQRSolve.lean`.  Under local diagonal dominance, if the stored compact
  sequence relative budget is bounded by a nonnegative scalar `cmax`, then the
  canonical finite-max product smallness condition may be checked with `cmax`
  in place of the exact relative budget.  This reduces the positive-budget
  compact-product blocker to proving the cap and scalar inequality; it does not
  prove local diagonal dominance/off-diagonal control, determinant/conditioning
  fields, norm-square nonbreakdown, or the final generic equation (8)
  QR/preconditioner theorem.  First weak-component validation is clean:
  focused LSQRSolve build, executable lookup, `git diff --check`, touched Lean
  marker scan, qualified axiom audit, PDF compile/text extraction, and
  rendered-page inspection of pages 187--188 passed.  The axiom audit reports
  only standard `propext`, `Classical.choice`, and `Quot.sound`.  Repeated
  weak-component validation is also clean with the same standard axiom audit
  result, executable lookup exposure, PDF text extraction, and readable
  rendered pages 187--188, giving this dependency two consecutive clean passes.
- 2026-06-02: Added the uniform per-step compact-panel cap reduction for the
  positive-budget compact-product route.  `HouseholderQR.lean` now proves
  `storedQRCompactSequenceRelativeBudget_le_mul_of_step_le`, and
  `LSQRSolve.lean` now proves
  `storedQRCompactSequenceProductBudget_lt_one_of_diagDominant_finite_max_stepBudget_le`.
  A uniform one-step relative budget cap `cStep` gives the sequence cap
  `n * cStep`, which is then fed into the canonical finite-max product
  threshold.  This reduces the route-1 blocker to proving the one-step cap and
  scalar inequality, while local diagonal dominance/off-diagonal control,
  determinant/conditioning/nonbreakdown, and the final generic equation (8)
  QR/preconditioner theorem remain open.  Two weak-component passes are clean:
  focused LSQRSolve build, executable lookup, `git diff --check`, touched Lean
  marker scan, qualified axiom audit, PDF compile/text extraction, and
  rendered-page inspection of pages 187--188 passed.  The axiom audit reports
  only standard `propext`, `Classical.choice`, and `Quot.sound`.
- 2026-06-02: Added the vector-level compact column/RHS cap reduction for the
  same route.  `HouseholderApply.lean` proves
  `householderCompactPanelRelativeBudget_le_mul_add_of_column_rhs_le`;
  `HouseholderQR.lean` proves
  `storedQRCompactStepRelativeBudget_le_mul_add_of_column_rhs_le`; and
  `LSQRSolve.lean` proves
  `storedQRCompactSequenceProductBudget_lt_one_of_diagDominant_finite_max_columnRhsBudget_le`.
  The product-smallness chain now has an explicit local reduction
  `cCol,cRhs -> n * cCol + cRhs -> n * (n * cCol + cRhs)`.  This still leaves
  vector-level compact caps, the scalar smallness inequality, local diagonal
  dominance/off-diagonal control, determinant/conditioning/nonbreakdown, and
  the final generic equation (8) QR/preconditioner theorem as open
  red-bottleneck dependencies.  Two weak-component passes were clean, with only
  pre-existing HouseholderQR unused-variable warnings and standard axioms in
  the audit.
- 2026-06-02: Added the primitive norm-budget compact column/RHS cap reduction.
  `HouseholderApply.lean` proves
  `householderCompactRelativeBudget_le_of_normBudget_le_mul` and
  `householderCompactPanelRelativeBudget_le_mul_add_of_normBudget_le_mul`;
  `HouseholderQR.lean` proves
  `storedQRCompactStepRelativeBudget_le_mul_add_of_normBudget_le_mul`; and
  `LSQRSolve.lean` proves
  `storedQRCompactSequenceProductBudget_lt_one_of_diagDominant_finite_max_columnRhsNormBudget_le`.
  The positive-budget compact-product chain can now start from primitive
  `householderCompactNormBudget <= c * vecNorm2` hypotheses and still uses
  the cap chain `cCol,cRhs -> n * cCol + cRhs -> n * (n * cCol + cRhs)`.
  This narrows the next route-1 target to deriving those primitive norm-budget
  inequalities from the local FP dot/scale/subtract model, or to scalar
  smallness/local off-diagonal-control work.  Two weak-component passes are
  clean: repeated whitespace checks, touched Lean marker scans, focused
  HouseholderApply/HouseholderQR/LSQRSolve builds, executable lookup, qualified
  axiom audits, theorem PDF compile/text extraction, and rendered inspection of
  pages 187--190 all passed with only pre-existing HouseholderQR unused-variable
  warnings and standard axioms.
- 2026-06-02: Added the componentwise compact column/RHS cap reduction below
  the primitive norm-budget bridge.  `HouseholderApply.lean` proves
  `householderCompactNormBudget_le_mul_of_componentBudget_le_mul_abs`,
  `householderCompactRelativeBudget_le_of_componentBudget_le_mul_abs`, and
  `householderCompactPanelRelativeBudget_le_mul_add_of_componentBudget_le_mul_abs`;
  `HouseholderQR.lean` proves
  `storedQRCompactStepRelativeBudget_le_mul_add_of_componentBudget_le_mul_abs`;
  and `LSQRSolve.lean` proves
  `storedQRCompactSequenceProductBudget_lt_one_of_diagDominant_finite_max_columnRhsComponentBudget_le`.
  This lowers the positive-budget compact-product chain to entrywise
  `householderCompactComponentBudget_i <= c * |input_i|` hypotheses, then
  reuses the same `cCol,cRhs -> n * cCol + cRhs -> n * (n * cCol + cRhs)` cap
  chain.  Two weak-component validations are clean: repeated whitespace
  checks, touched Lean marker scans, focused LSQRSolve builds, executable
  lookup, qualified axiom audits, theorem PDF compile/text extraction, and
  rendered inspection of pages 188--190 passed with only pre-existing
  HouseholderQR unused-variable warnings and standard axioms.  The next route-1
  targets are proving those entrywise FP inequalities, scalar smallness, or
  local off-diagonal-control/diagonal dominance fields.
- 2026-06-02: Added the explicit compact Householder norm-coefficient route for
  the equation (8) QR/preconditioner compact-product bottleneck.  The local
  Householder file now proves `householderAbsDotBudget_le_vecNorm2_mul`,
  defines `householderCompactUpdateCoeff` and
  `householderCompactNormBudgetCoeff`, proves
  `householderCompactComponentBudget_le_updateCoeff_mul_norm`,
  `householderCompactNormBudget_le_normBudgetCoeff_mul`,
  `householderCompactRelativeBudget_le_normBudgetCoeff`, and
  `householderCompactPanelRelativeBudget_le_mul_add_normBudgetCoeff`.  The QR
  file adds `storedQRCompactStepNormBudgetCoeff` and
  `storedQRCompactStepRelativeBudget_le_mul_add_normBudgetCoeff`; the LS file
  adds
  `storedQRCompactSequenceProductBudget_lt_one_of_diagDominant_finite_max_normBudgetCoeff_le`.
  This is the valid primitive FP reduction: it charges the nonlocal compact
  update to `||input||_2 * |v_i|` and the final subtraction to `|input_i|`,
  rather than requiring the generally false cap `budget_i <= c * |input_i|`.
  Two weak-component validation passes are clean: focused builds, repeated
  `git diff --check`, touched-file marker scan, executable lookup, qualified
  axiom audit, PDF compile, targeted `pdftotext`, and rendered pages 188--192
  all passed.
- 2026-06-02: Added the canonical finite maximum for the compact Householder
  norm-coefficient route.  `HouseholderQR.lean` proves
  `storedQRCompactStepNormBudgetCoeff_nonneg`; `LSQRSolve.lean` defines
  `storedQRCompactStepNormBudgetCoeffBudget`, proves
  `storedQRCompactStepNormBudgetCoeff_le_budget` and
  `storedQRCompactStepNormBudgetCoeffBudget_nonneg`, and proves
  `storedQRCompactSequenceProductBudget_lt_one_of_diagDominant_finite_max_normBudgetCoeffBudget`.
  This removes the arbitrary `cHH` field from the product theorem by choosing
  the finite max of the actual stored-stage coefficients.  Two
  weak-component validation passes are clean: repeated `git diff --check`,
  touched-file marker scans, focused LSQRSolve build, executable lookup,
  qualified axiom audits, PDF compile/text extraction, and rendered pages
  188--193 all passed.  Scalar smallness for the displayed max and local
  diagonal/off-diagonal or determinant/conditioning fields remain.
- 2026-06-02: Added the coefficient-maximum equation (8) handoff.  The
  least-squares layer proves
  `StoredQROffDiagonalControlInvariant.of_diagDominant_finiteMaxNormBudgetCoeffSmallness`,
  deriving the route-1 package from local diagonal dominance and the canonical
  `storedQRCompactStepNormBudgetCoeffBudget` scalar inequality.  The RandNLA
  layer proves
  `leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_offDiagonalControl_solver_of_diagDominant_finiteMaxNormBudgetCoeffSmallness`,
  composing that package into the high-probability sampled least-squares
  objective theorem.  Two weak-component validation passes are clean (repeated
  `git diff --check`, touched-file marker scans, focused RandNLA build,
  executable lookup, qualified axiom audits, PDF compile/text extraction, and
  rendered pages 190--192); scalar smallness for the displayed max and local
  diagonal/off-diagonal or determinant/conditioning fields remain.
- 2026-06-02: Added the bounded scalar-smallness certificate for the
  coefficient-maximum route.  `LSQRSolve.lean` proves
  `storedQRCompactNormBudgetCoeffSmallness_of_bounds`,
  `storedQRCompactSequenceProductBudget_lt_one_of_diagDominant_finite_max_normBudgetCoeffBudget_bounds`,
  and
  `StoredQROffDiagonalControlInvariant.of_diagDominant_finiteMaxNormBudgetCoeffBoundedSmallness`.
  These reduce the exact canonical scalar condition to route constants
  `Dmax`, `Cmax`, and `Nmax` that dominate the canonical diagonal-dominant
  inverse budget, compact Householder coefficient maximum, and pivot-column
  norm budget; nonnegativity of those constants is derived from domination.
  Two weak-component validation passes are clean (`git diff --check`, touched
  Lean marker scans, focused LSQRSolve builds, executable lookup, qualified
  axiom audits, PDF compile/text extraction, and rendered pages 190--193).
- 2026-06-02: Added pointwise route-bound certificates for the
  coefficient-maximum scalar route.  `LSQRSolve.lean` proves
  `storedQRDiagDominantInvFactorBudget_le_of_forall_le`,
  `storedQRPivotColumnNormBudget_le_of_forall_le`,
  `storedQRCompactStepNormBudgetCoeffBudget_le_of_forall_le`,
  `storedQRCompactNormBudgetCoeffSmallness_of_pointwise_bounds`,
  `storedQRCompactSequenceProductBudget_lt_one_of_diagDominant_finite_max_normBudgetCoeffBudget_pointwise_bounds`,
  and
  `StoredQROffDiagonalControlInvariant.of_diagDominant_finiteMaxNormBudgetCoeffPointwiseBounds`.
  These reduce the displayed-upper-bound obligations to per-pivot route
  estimates plus nonnegativity of the displayed constants in the zero-pivot
  case.  Two weak-component validation passes are clean: repeated touched Lean
  marker scans, focused LSQRSolve builds, executable lookup, qualified axiom
  audits, PDF compile/text extraction, and rendered pages 190--194 passed.
- 2026-06-02: Added the solver-facing pointwise coefficient-maximum handoff.
  `LSQRSolve.lean` proves
  `LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_leadingBlock_det_ne_zero_diagDominant_finiteMaxNormBudgetCoeffPointwiseBounds_concreteDual`
  and
  `LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_diagDominant_finiteMaxNormBudgetCoeffPointwiseBounds_concreteDual`.
  These wrappers compose the pointwise product-budget route into the
  concrete-dual QR solve certificate; the second derives leading-block
  determinant nonzeroness from local diagonal dominance.  Two weak-component
  validation passes are clean: repeated `git diff --check`, touched Lean marker
  scans, focused LSQRSolve builds, executable lookup, qualified axiom audits,
  PDF compile/text extraction, and rendered pages 191--195 passed.  This remains a solver-surface composition step only:
  the pointwise estimates, scalar inequality, local diagonal/off-diagonal
  control, and final generic equation (8) QR/preconditioner theorem remain open.
- 2026-06-02: Added the per-pivot beta-norm coefficient reduction for the
  compact Householder route.  `HouseholderApply.lean` proves
  `householderCompactNormBudgetCoeff_eq_u_add_abs_beta_norm_sq_mul_factor`,
  `householderCompactNormBudgetCoeffFactor_nonneg`, and
  `householderCompactNormBudgetCoeff_le_of_abs_beta_norm_sq_le`; `HouseholderQR.lean`
  proves `storedQRCompactStepNormBudgetCoeff_le_of_abs_beta_norm_sq_le` and
  `storedQRCompactStepNormBudgetCoeff_le_of_forall_abs_beta_norm_sq_le`;
  `LSQRSolve.lean` proves
  `storedQRCompactStepNormBudgetCoeffBudget_le_of_forall_abs_beta_norm_sq_le`,
  `storedQRCompactNormBudgetCoeffSmallness_of_pointwise_absBetaNormSq_bounds`,
  `storedQRCompactSequenceProductBudget_lt_one_of_diagDominant_finite_max_absBetaNormSqPointwiseBounds`,
  and
  `StoredQROffDiagonalControlInvariant.of_diagDominant_finiteMaxAbsBetaNormSqPointwiseBounds`.
  This specializes the coefficient-max route to
  `Cmax = u + Bmax * householderCompactNormBudgetCoeffFactor fp m` when each
  signed stage has `|beta_k| * ||v_k||_2^2 <= Bmax`.  Focused LSQRSolve build
  passes; two weak-component validation passes are clean (`git diff --check`,
  touched-source marker scans, focused LSQRSolve builds, executable lookup,
  qualified axiom audits, PDF compile/text extraction, and rendered page
  inspections).  The `Bmax` estimate, scalar inequality, local
  diagonal/off-diagonal control, and final generic equation (8)
  QR/preconditioner theorem remain open.
- 2026-06-02: Added the exact Householder-normalization coefficient branch.
  `HouseholderSpec.lean` proves `abs_householderBeta_mul_vecNorm2_sq_eq_two`
  and `abs_householderBeta_mul_vecNorm2_sq_le_two`, reusing
  `householderBeta_mul_inner_self_eq_two` to show
  `|beta| * ||v||_2^2 = 2` from a nonzero denominator.  `HouseholderQR.lean`
  lifts this to stored signed stages and the source-shaped QR-loop
  nonbreakdown hypothesis; `LSQRSolve.lean` proves
  `storedQRCompactStepNormBudgetCoeffBudget_le_of_forall_source_den_ne_zero`,
  `storedQRCompactNormBudgetCoeffSmallness_of_pointwise_source_den_ne_zero_bounds`,
  `storedQRCompactSequenceProductBudget_lt_one_of_diagDominant_finite_max_sourceDenPointwiseBounds`,
  and
  `StoredQROffDiagonalControlInvariant.of_diagDominant_finiteMaxSourceDenPointwiseBounds`.
  This closes the coefficient-route `Bmax` estimate with concrete `Bmax = 2`
  under visible source nonbreakdown.  Focused LSQRSolve build passes, and two
  weak-component passes are clean: repeated `git diff --check`, touched Lean
  marker scans, focused
  `lake build LeanFpAnalysis.FP.Algorithms.LeastSquares.LSQRSolve`, executable
  lookup, qualified axiom audit for the eleven new theorem names, theorem PDF
  compile, targeted `pdftotext`, and rendered pages 190--193 passed.  The axiom
  audit reported only standard `propext`, `Classical.choice`, and
  `Quot.sound`, and the temporary axiom-audit file was deleted.

- 2026-06-02: Added the LS.2g-fi source-facing scalar-smallness normalization.
  `LSQRSolve.lean` now proves
  `storedQRCompactNormBudgetCoeffSmallness_of_pointwise_source_den_ne_zero_simple_bounds`,
  `storedQRCompactSequenceProductBudget_lt_one_of_diagDominant_finite_max_sourceDenSimpleBounds`,
  and
  `StoredQROffDiagonalControlInvariant.of_diagDominant_finiteMaxSourceDenSimpleBounds`.
  These siblings rewrite the expanded exact-normalization condition with
  `Cmax = fp.u + 2 * householderCompactNormBudgetCoeffFactor fp m` into the
  compact route certificate
  `2 * Dmax * (m * ((n * (n + 1) * Cmax * Nmax)^2)) < 1`, then reuse the
  source-denominator `Bmax = 2` branch.  Focused LSQRSolve build passes, and
  two weak-component passes are clean: repeated `git diff --check`, touched
  Lean marker scans, focused LSQRSolve builds, executable lookup, qualified
  axiom audit for the three new theorem names, theorem PDF compile, targeted
  `pdftotext`, and rendered pages 192--193 passed.  The axiom audit reported
  only standard `propext`, `Classical.choice`, and `Quot.sound`, and the
  temporary axiom-audit file was deleted.

- 2026-06-02: Added the LS.2g-fj source-denominator scalar cap bridge.
  `LSQRSolve.lean` now proves
  `storedQRCompactNormBudgetCoeffSmallness_of_pointwise_source_den_ne_zero_cap_bounds`,
  `storedQRCompactSequenceProductBudget_lt_one_of_diagDominant_finite_max_sourceDenCapBounds`,
  and
  `StoredQROffDiagonalControlInvariant.of_diagDominant_finiteMaxSourceDenCapBounds`.
  These theorems reduce the source-facing scalar condition with
  `fp.u + 2 * householderCompactNormBudgetCoeffFactor fp m` to visible caps
  `fp.u <= Ucap` and
  `householderCompactNormBudgetCoeffFactor fp m <= Fcap`, plus the displayed
  inequality with `Ucap + 2 * Fcap`.  This is a scalar-smallness dependency
  reduction only: cap estimates, local diagonal dominance/off-diagonal control,
  inverse-factor and pivot-column pointwise bounds, source nonbreakdown,
  determinant/conditioning fields, and the final generic equation (8)
  QR/preconditioner theorem remain open or visible.  Focused LSQRSolve build
  passed, and two weak-component passes are clean: repeated `git diff --check`,
  production Lean marker scans, focused LSQRSolve builds, executable lookup,
  qualified axiom audits, theorem PDF compile, targeted `pdftotext`, and
  rendered pages 192--195 passed.  The axiom audit reported only standard
  `propext`, `Classical.choice`, and `Quot.sound`, and the temporary audit file
  was deleted.

- 2026-06-02: Added the LS.2g-fk Householder coefficient-factor cap.
  `HouseholderApply.lean` now proves
  `householderCompactNormBudgetCoeffFactor_le_of_u_gamma_le`, bounding
  `householderCompactNormBudgetCoeffFactor fp m` by the explicit polynomial in
  caps `Ucap` and `Gcap` whenever `fp.u <= Ucap`,
  `gamma fp m <= Gcap`, and the caps are nonnegative.  This is a cap-estimate
  dependency for the LS.2g-fj scalar cap bridge only: primitive `u`/`gamma`
  caps, scalar cap smallness, local diagonal dominance/off-diagonal control,
  inverse-factor and pivot-column pointwise bounds, source nonbreakdown,
  determinant/conditioning fields, and the final generic equation (8)
  QR/preconditioner theorem remain open.  Two weak-component passes are clean:
  repeated `git diff --check`, production Lean marker scans, focused
  HouseholderApply and LSQRSolve builds, executable lookup, qualified axiom
  audit, theorem PDF compile, targeted `pdftotext`, and rendered pages 192--193
  passed.  The axiom audit reported only standard `propext`,
  `Classical.choice`, and `Quot.sound`.

- 2026-06-02: Added the LS.2g-fl gamma cap from a unit-roundoff cap.
  `Rounding.lean` now proves `gamma_le_of_u_le_cap` and
  `gamma_le_Gcap_of_u_le_cap`, bounding `gamma fp m` by
  `m*Ucap/(1-m*Ucap)` from `fp.u <= Ucap` and `(m : ℝ) * Ucap < 1`, and then
  by any displayed `Gcap` dominating that expression.  This is a primitive
  cap-estimate dependency for the LS.2g-fk factor cap only: the actual
  unit-roundoff cap, scalar cap smallness, local diagonal dominance/off-diagonal
  control, inverse-factor and pivot-column pointwise bounds, source
  nonbreakdown, determinant/conditioning fields, and final generic equation (8)
  QR/preconditioner theorem remain open.  Two weak-component passes are clean:
  repeated `git diff --check`, production marker scans, focused
  Rounding/HouseholderApply/LSQRSolve builds, executable lookup, qualified
  axiom audit, theorem PDF compile, targeted `pdftotext`, and rendered pages
  193--194 passed.  The axiom audit reported only standard `propext`,
  `Classical.choice`, and `Quot.sound`.

- 2026-06-02: Added the LS.2g-fm composed coefficient-factor cap from a
  unit-roundoff cap.  `HouseholderApply.lean` now proves
  `householderCompactNormBudgetCoeffFactor_le_of_u_cap_gamma_cap`, composing
  the LS.2g-fk factor cap with the LS.2g-fl gamma cap so the route derives
  `householderCompactNormBudgetCoeffFactor fp m <= polynomial(Ucap,Gcap)`
  from `fp.u <= Ucap`, `(m : ℝ) * Ucap < 1`, and the rational domination by
  `Gcap`, without a separate `gamma fp m <= Gcap` field.  Two weak-component
  passes are clean: repeated `git diff --check`, production marker scans,
  focused HouseholderApply/LSQRSolve builds, executable lookup, qualified axiom
  audit, theorem PDF compile, targeted `pdftotext`, and rendered pages 193--194
  passed.  The axiom audit reported only standard `propext`,
  `Classical.choice`, and `Quot.sound`.

- 2026-06-02: Added the LS.2g-fn source-denominator cap route from
  unit-roundoff/gamma caps.  `LSQRSolve.lean` now proves
  `storedQRCompactNormBudgetCoeffSmallness_of_pointwise_source_den_ne_zero_uGammaCapBounds`,
  `storedQRCompactSequenceProductBudget_lt_one_of_diagDominant_finite_max_sourceDenUGammaCapBounds`,
  and
  `StoredQROffDiagonalControlInvariant.of_diagDominant_finiteMaxSourceDenUGammaCapBounds`,
  composing the LS.2g-fm displayed Householder factor cap into the
  scalar-smallness, compact-product, and packaged invariant surfaces.  Two
  weak-component passes are clean: repeated `git diff --check`, production Lean
  marker scans, focused LSQRSolve builds, executable lookup, qualified axiom
  audits, theorem PDF compile, targeted `pdftotext`, and rendered pages 193--195
  passed.  The axiom audit reported only standard `propext`,
  `Classical.choice`, and `Quot.sound`; the temporary audit file was deleted.

- 2026-06-02: Added the LS.2g-fo unit-roundoff-cap route elimination.
  `Model.lean` now defines `FPModel.exactWithUnitRoundoff` and proves
  `FPModel.not_forall_u_le_cap`, showing that no fixed cap `fp.u <= Ucap`
  follows from the abstract `FPModel` alone.  This is a theorem-statement
  correction for the LS.2g cap route: primitive unit-roundoff caps must remain
  visible domain assumptions unless a concrete machine model is formalized.
  Two weak-component passes are clean: repeated `git diff --check`, production
  Lean marker scans, focused Model builds, executable lookup, qualified axiom
  audits, theorem PDF compile, targeted `pdftotext`, and rendered page 194
  passed.  The axiom audit reported only standard `propext`,
  `Classical.choice`, and `Quot.sound`.

- 2026-06-02: Added the LS.2g-fp rational gamma cap specialization.
  `LSQRSolve.lean` now proves
  `storedQRCompactNormBudgetCoeffSmallness_of_pointwise_source_den_ne_zero_uRationalGammaCapBounds`,
  `storedQRCompactSequenceProductBudget_lt_one_of_diagDominant_finite_max_sourceDenURationalGammaCapBounds`,
  and
  `StoredQROffDiagonalControlInvariant.of_diagDominant_finiteMaxSourceDenURationalGammaCapBounds`,
  specializing `Gcap` to `(m * Ucap)/(1 - m * Ucap)` so the separate
  rational-domination proof field closes by reflexivity.  Two weak-component
  passes are clean: repeated `git diff --check`, production Lean marker scans,
  focused LSQRSolve builds, executable lookup, qualified axiom audits, theorem
  PDF compile, targeted `pdftotext`, and rendered pages 194--195 passed.  The
  axiom audit reported only standard `propext`, `Classical.choice`, and
  `Quot.sound`.

- 2026-06-02: Added the LS.2g-fq canonical finite-max rational gamma cap route.
  `LSQRSolve.lean` now proves
  `storedQRCompactNormBudgetCoeffSmallness_of_source_den_ne_zero_uRationalGammaCanonicalBounds`,
  `storedQRCompactSequenceProductBudget_lt_one_of_diagDominant_finite_max_sourceDenURationalGammaCanonicalBounds`,
  and
  `StoredQROffDiagonalControlInvariant.of_diagDominant_finiteMaxSourceDenURationalGammaCanonicalBounds`,
  choosing `Dcap` and `Ncap` as the repository's canonical finite maxima and
  removing the separate pointwise inverse-factor and pivot-column domination
  proof fields from the rational-gamma source-denominator route.  Two
  weak-component passes are clean: repeated `git diff --check`, production
  Lean marker scans, focused LSQRSolve builds, executable lookup, qualified
  axiom audits, theorem PDF compile, targeted `pdftotext`, and rendered pages
  194--196 passed.  The axiom audit reported only standard `propext`,
  `Classical.choice`, and `Quot.sound`.

- 2026-06-02: Added the LS.2g-fr solver/probability handoff for the canonical
  finite-max rational gamma cap route.  `LSQRSolve.lean` now proves
  `LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_diagDominant_finiteMaxSourceDenURationalGammaCanonicalBounds`,
  and `LeastSquaresSketch.lean` now proves
  `leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_diagDominant_finiteMaxSourceDenURationalGammaCanonicalBounds_solver`.
  Two weak-component passes are clean: repeated `git diff --check`, production
  Lean marker scans, focused LSQRSolve and LeastSquaresSketch builds,
  executable lookup, qualified axiom audits, theorem PDF compile, targeted
  `pdftotext`, and rendered pages 195--201 passed.  The axiom audit reported
  only standard `propext`, `Classical.choice`, and `Quot.sound`.

- 2026-06-02: Added the LS.2g-fs canonical scalar-smallness route-elimination
  theorem.  `LSQRSolve.lean` now proves
  `not_forall_diagDominant_sourceDen_uCap_implies_uRationalGammaCanonicalSmallness`,
  a `1 x 1` exact-with-unit-roundoff witness showing that local diagonal
  dominance, source denominator nonbreakdown, `fp.u <= Ucap`, and
  `(m : ℝ) * Ucap < 1` do not imply the displayed canonical finite-max scalar
  smallness inequality.  Two weak-component passes are clean: repeated
  `git diff --check`, production Lean marker scans, focused LSQRSolve builds,
  executable lookup, qualified axiom audits, theorem PDF compile, targeted
  `pdftotext`, and rendered pages 198--199 passed.  The axiom audit reported
  only standard `propext`, `Classical.choice`, and `Quot.sound`.

- 2026-06-02: Added the actual-unit-roundoff companion to the LS.2g-fs
  scalar-smallness route elimination.  `LSQRSolve.lean` now proves
  `not_forall_diagDominant_sourceDen_actualU_implies_uRationalGammaCanonicalSmallness`,
  showing that even substituting the actual `fp.u` into the rational-gamma
  expression does not make the canonical finite-max scalar smallness inequality
  automatic from diagonal dominance, source nonbreakdown, and `m * fp.u < 1`.
  This rules out the `Ucap = fp.u` shortcut and keeps scalar smallness as a
  genuine positive proof obligation.

- 2026-06-02: Added the LS.2g-ft source nonbreakdown reduction for the
  canonical rational-gamma route.  `LSQRSolve.lean` now proves
  `storedQRSourceDenominator_ne_zero_of_trailingNorm2Sq_pos_mul_nonpos`,
  `StoredQROffDiagonalControlInvariant.of_diagDominant_trailingNormPos_finiteMaxSourceDenURationalGammaCanonicalBounds`,
  and
  `LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_diagDominant_trailingNormPos_finiteMaxSourceDenURationalGammaCanonicalBounds`;
  `LeastSquaresSketch.lean` now proves
  `leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_diagDominant_trailingNormPos_finiteMaxSourceDenURationalGammaCanonicalBounds_solver`.
  These derive raw source denominator nonbreakdown from signed-alpha source
  facts and positive trailing norm squares, then reuse the existing canonical
  route.  Two weak-component passes are now clean: focused LSQRSolve and
  LeastSquaresSketch builds, executable lookup, `git diff --check`, touched
  marker scan, qualified axiom audit, theorem PDF compile, `pdftotext`
  inspection, and rendered page inspection passed.  The temporary axiom-audit
  file was deleted.

- 2026-06-02: Added the Algorithm 1 explicit FP scalar-radius correction after
  PDF review.  `ElementwiseSpectral.lean` now proves
  `sqMagTraceErrorBudget_zero_init_truncated_le_const`,
  `frobNormRect_sqMagTraceErrorBudget_zero_init_truncated_le_const_square`,
  `sqMagTraceProbability_eventProb_algorithm1FlTruncatedSpectralRadius_ge_one_sub_delta_source_sample_budget_gamma_square`,
  and
  `sqMagTraceProbability_eventProb_algorithm1FlTruncatedSpectralRadius_ge_one_sub_delta_source_sample_budget_explicit_gamma_square`.
  The user-facing Algorithm 1 equation (2) FP corollary should now advertise
  the displayed radius
  `eps + (2*n^2*||A||_F^2/eps)*gamma fp (s+1)` for `tau=eps/(2n)`, not only
  the internal budget-matrix theorem `eps + ||B||_F`.  Two weak-component
  passes are clean for this correction: repeated diff checks, marker scans,
  focused ElementwiseSpectral builds, executable lookup, axiom audit, PDF
  compile/text inspection, and rendered page checks.

- 2026-06-02: Fixed the follow-up Algorithm 1 PDF presentation regression.
  Theorem 142 in `docs/RandNLA_CACM_Formalization_Summary.tex` is now
  exact-only and explicitly labelled as an entrywise union-bound fallback, not
  equation (2).  The final end-of-Algorithm-1 corollary immediately before
  Algorithm 2 is the equation (2) citation target; it states the rounded
  source-aligned square truncated result with the explicit radius
  `eps + (2*n^2*||A||_F^2/eps)*gamma fp (s+1)` and no hidden budget matrix.
  Older fallback Markov/net/Frobenius prose was also rewritten so generic
  perturbation matrices do not look like advertised Algorithm 1 endpoints.

- 2026-06-02: Made the final Algorithm 1 equation (2) PDF corollary
  self-contained.  Corollary 143 now restates the hard-thresholding definition
  of `trunc_tau(A)` entrywise and explains why `tau = eps/(2*n)` is used:
  deterministic truncation costs at most `eps/2` in Frobenius/operator norm for
  an `n x n` matrix, while retained sampled entries have magnitude at least
  `tau`, giving the denominator lower bound behind the explicit FP
  `gamma fp (s+1)` radius.

- 2026-06-02: Corrected the Algorithm 1 theorem-scope mistake after user
  review.  Hard-thresholding is not part of the literal CACM Algorithm 1
  sampler with `p_ij = A_ij^2 / ||A||_F^2`; it is a modified/truncated
  element-wise sampler.  The theorem PDF now retitles the former final
  Algorithm 1 corollary as a truncated element-wise sampler theorem and states
  explicitly that the sharp literal untruncated equation (2) matrix-Bernstein
  theorem remains open.
  Do not cite the truncated theorem as closing CACM Algorithm 1.

- 2026-06-02: Added the faithful nontruncated Algorithm 1 FP corollary after
  the truncation correction.  `ElementwiseSpectral.lean` proves
  `sqMagTraceErrorBudget_zero_init_le_const_of_entry_abs_ge`,
  `frobNormRect_sqMagTraceErrorBudget_zero_init_le_const_square_of_entry_abs_ge`,
  and
  `sqMagTraceProbability_eventProb_algorithm1FlSpectralRadius_ge_one_sub_delta_frob_explicit_gamma_square`.
  This result uses the literal law `p_ij = A_ij^2 / ||A||_F^2`, no
  `trunc_tau(A)`, and a visible nonzero-entry floor `alpha <= |A_ij|` to expand
  the rounded radius to `eps + n*(||A||_F^2/alpha)*gamma fp (s+1)`.  It is a
  weaker Frobenius/Markov corollary, not the sharp CACM equation (2)
  matrix-Bernstein/Khintchine theorem.

- 2026-06-02: Added the literal Algorithm 1 source-rate specialization under a
  visible no-small-entry condition.  `ElementwiseSpectral.lean` proves
  `elementwiseTruncate_eq_self_of_forall_nonzero_entry_abs_ge`,
  `sqMagTraceProbability_eventProb_algorithm1ExactSpectralEvent_ge_one_sub_delta_source_sample_budget_no_small_entries_square`,
  and
  `sqMagTraceProbability_eventProb_algorithm1FlSpectralRadius_ge_one_sub_delta_source_sample_budget_no_small_entries_square`.
  These use the literal law `p_ij = A_ij^2 / ||A||_F^2` and the source-rate
  sample budget `14*n*||A||_F^2*log(2(2n)/delta) <= s*eps^2`, but require
  `eps/(2n) <= |A_ij|` for every nonzero entry so the source truncation is the
  identity.  The FP radius is
  `eps + (2*n^2*||A||_F^2/eps)*gamma fp (s+1)`.  This is not the fully
  unconditional literal CACM equation (2) theorem for arbitrarily small
  nonzero entries.

- 2026-06-02: Clarified Algorithm 2 equation (5) FP scope.  The theorem
  `rowSqNormTraceProbability_eventProb_fl_rowSampleGram_frob_error_le_epsilon_add_scaling_budget`
  is the scaling-only model: sampled/scaled rows are rounded, then the Gram
  matrix is formed as a mathematical object.  Its radius is
  `eps * D(A) + n*(2*u+u^2)*D(A)` and it has no `tau_dot` and no `gammaValid`
  hypothesis.  Use the `fl_rowSampleGramDot` theorem only for implementations
  that actually compute Gram entries by rounded dot products.

- 2026-06-02: Added the LS.2g-fu determinant-facing source-nonbreakdown
  reduction for the canonical rational-gamma QR route.  `LSQRSolve.lean` now
  proves
  `StoredQROffDiagonalControlInvariant.of_diagDominant_leadingBlock_det_ne_zero_finiteMaxSourceDenURationalGammaCanonicalBounds`
  and
  `LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_diagDominant_leadingBlock_det_ne_zero_finiteMaxSourceDenURationalGammaCanonicalBounds`;
  `LeastSquaresSketch.lean` proves
  `leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_diagDominant_leadingBlock_det_ne_zero_finiteMaxSourceDenURationalGammaCanonicalBounds_solver`.
  This replaces the positive trailing-norm hypothesis in the LS.2g-ft branch
  by nonzero previous/current leading-block determinants plus the stored
  lower-zero shape, then reuses the signed-alpha source-nonbreakdown route.
  Two weak-component passes are clean: focused LSQRSolve and
  LeastSquaresSketch builds, executable lookup, `git diff --check`, production
  marker scans, qualified axiom audits, theorem PDF compile, targeted
  `pdftotext`, and rendered pages 203--204 passed.  The axiom audits reported
  only standard `propext`, `Classical.choice`, and `Quot.sound`, and the
  temporary audit file was deleted.  The final generic rectangular
  QR/preconditioner theorem remains open on determinant/nonzero fields, local
  diagonal-dominance/off-diagonal control, scalar smallness, primitive
  unit-roundoff caps, and conditioning assumptions.

- 2026-06-02: Added the LS.2g-fv signed-alpha-definition invariant-surface
  reduction for the determinant-facing canonical rational-gamma QR route.
  `LSQRSolve.lean` proves
  `StoredQROffDiagonalControlInvariant.of_diagDominant_signedAlphaDef_leadingBlock_det_ne_zero_finiteMaxSourceDenURationalGammaCanonicalBounds`,
  which derives the squared-alpha identity and sign-choice inequality directly
  from the concrete `signedHouseholderAlpha` definition before reusing the
  determinant-facing source-nonbreakdown route.  This is a theorem-surface
  reduction only; determinant nonzeroness, local diagonal dominance/off-diagonal
  control, scalar smallness, primitive unit-roundoff caps, conditioning fields,
  and the final rectangular QR/preconditioner theorem remain open or visible.
  The determinant-facing solver theorem now syntactically consumes this
  packaged invariant through the generic off-diagonal-control handoff.  Two
  focused weak-component passes after this proof rewrite are clean: repeated
  focused LSQRSolve builds, executable lookup, `git diff --check`, production
  marker scans, qualified axiom audits for both the invariant and consuming
  solver theorem, theorem PDF compiles, targeted `pdftotext`, and rendered pages
  203--204 passed.  The axiom audits reported only standard `propext`,
  `Classical.choice`, and `Quot.sound`, and the temporary axiom-audit file was
  deleted after the second pass.

- 2026-06-02: Added the LS.2g-fw current-determinant reduction for the
  determinant-facing canonical rational-gamma QR route.  `LSQRSolve.lean`
  proves
  `StoredQROffDiagonalControlInvariant.of_diagDominant_signedAlphaDef_previousLeadingBlock_det_ne_zero_finiteMaxSourceDenURationalGammaCanonicalBounds`
  and
  `LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_diagDominant_previousLeadingBlock_det_ne_zero_finiteMaxSourceDenURationalGammaCanonicalBounds`;
  `LeastSquaresSketch.lean` proves
  `leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_diagDominant_previousLeadingBlock_det_ne_zero_finiteMaxSourceDenURationalGammaCanonicalBounds_solver`.
  These wrappers derive the current leading-block determinant from
  `IsDiagDominantUpper` via `det_ne_zero_of_diagDominantUpper`.  The previous
  transposed leading-block determinant, local diagonal dominance/off-diagonal
  control, scalar smallness, primitive unit-roundoff caps, conditioning fields,
  and final rectangular QR/preconditioner theorem remain open or visible.
  Two focused weak-component passes are clean: focused LSQRSolve and
  LeastSquaresSketch builds, executable lookup, `git diff --check`, production
  marker scans, qualified axiom audits, theorem PDF compile, targeted
  `pdftotext`, and rendered page 204 passed.  The axiom audits reported only
  standard `propext`, `Classical.choice`, and `Quot.sound`, and the temporary
  audit file was deleted.

- 2026-06-02: Added the LS.2g-fx previous-determinant reduction for the
  determinant-facing canonical rational-gamma QR route.  `LSQRSolve.lean`
  proves `qrPreviousLeadingBlockTranspose_det_ne_zero_of_diagDominant_leadingBlock`,
  `StoredQROffDiagonalControlInvariant.of_diagDominant_signedAlphaDef_lowerPrev_finiteMaxSourceDenURationalGammaCanonicalBounds`,
  and
  `LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_diagDominant_lowerPrev_finiteMaxSourceDenURationalGammaCanonicalBounds`;
  `LeastSquaresSketch.lean` proves
  `leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_diagDominant_lowerPrev_finiteMaxSourceDenURationalGammaCanonicalBounds_solver`.
  These wrappers derive the previous transposed leading-block determinant from
  the same `IsDiagDominantUpper` leading-block hypothesis, leaving the previous
  lower-zero shape, diagonal dominance/off-diagonal control, scalar smallness,
  primitive unit-roundoff caps, conditioning fields, and final rectangular
  QR/preconditioner theorem open or visible.  Two focused weak-component passes
  are clean: repeated LSQRSolve and LeastSquaresSketch builds, executable
  lookup, `git diff --check`, production marker scans, qualified axiom audits,
  theorem PDF compile, targeted `pdftotext`, and rendered pages 205--206
  passed.  The axiom audits reported only standard `propext`,
  `Classical.choice`, and `Quot.sound`, and the temporary audit file was deleted
  after validation.

- 2026-06-02: Added the LS.2g-fy stored-lower-zero reduction for the
  determinant-facing canonical rational-gamma QR route.  `LSQRSolve.lean`
  proves `storedQRPreviousColumnLowerZero_of_stored_trailing_householder_sequence`
  and
  `LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_diagDominant_storedLower_finiteMaxSourceDenURationalGammaCanonicalBounds`;
  `LeastSquaresSketch.lean` proves
  `leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_diagDominant_storedLower_finiteMaxSourceDenURationalGammaCanonicalBounds_solver`.
  These wrappers derive the previous-column lower-zero field from the stored
  Householder panel recurrence via
  `fl_householderStoredPanel_sequence_prefix_lower_zero`, leaving diagonal
  dominance/off-diagonal control, scalar smallness, primitive unit-roundoff
  caps, conditioning fields, and the final rectangular QR/preconditioner theorem
  open or visible.  Two focused weak-component passes are clean: focused
  LSQRSolve and LeastSquaresSketch builds, executable lookup, `git diff --check`,
  production marker scans, qualified axiom audits, theorem PDF compile,
  targeted `pdftotext`, and rendered pages 205--206 passed.  The axiom audits
  reported only standard `propext`, `Classical.choice`, and `Quot.sound`.

- 2026-06-02: Added the LS.2g-fz unit-roundoff-cap nonnegativity reduction for
  the stored-lower canonical rational-gamma QR route.  `LSQRSolve.lean` proves
  `LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_diagDominant_storedLower_finiteMaxSourceDenURationalGammaCanonicalBounds_of_uCap`;
  `LeastSquaresSketch.lean` proves
  `leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_diagDominant_storedLower_finiteMaxSourceDenURationalGammaCanonicalBounds_solver_of_uCap`.
  These wrappers derive the former explicit `0 <= Ucap` hypothesis from
  `FPModel.u_nonneg` and `fp.u <= Ucap`, leaving the primitive unit-roundoff cap
  itself, scalar smallness, local diagonal dominance/off-diagonal control,
  conditioning fields, and the final QR/preconditioner theorem open or visible.
  Two focused weak-component passes are clean: focused LSQRSolve and
  LeastSquaresSketch builds, executable lookup, `git diff --check`, production
  marker scans, qualified axiom audit, theorem PDF compile, targeted
  `pdftotext`, and rendered pages 205--207 passed.  The axiom audit reported
  only standard `propext`, `Classical.choice`, and `Quot.sound`.

- 2026-06-02: Added the LS.2g-ga cap-derived gamma-validity reduction for the
  stored-lower canonical rational-gamma QR route.  `Rounding.lean` proves
  `gammaValid_of_u_le_cap`.  `LSQRSolve.lean` proves
  `LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_diagDominant_storedLower_finiteMaxSourceDenURationalGammaCanonicalBounds_of_uCap_no_gammaValid`,
  and `LeastSquaresSketch.lean` proves
  `leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_diagDominant_storedLower_finiteMaxSourceDenURationalGammaCanonicalBounds_solver_of_uCap_no_gammaValid`.
  These wrappers derive the former `gammaValid fp m`/`gammaValid fp s` guard
  from `fp.u <= Ucap` and the displayed cap smallness, then derive the
  triangular-dimension guard with `gammaValid_mono`.  This removes a redundant
  FP validity field from the cap-based QR/probability surface; it does not
  prove the primitive cap itself, scalar smallness, local diagonal
  dominance/off-diagonal control, conditioning fields, or the final generic
  QR/preconditioner theorem.  Two focused weak-component passes are clean:
  Rounding, LSQRSolve, and LeastSquaresSketch builds; executable lookup;
  `git diff --check`; touched-source marker scan; qualified axiom audit;
  theorem PDF compile; targeted `pdftotext`; and rendered pages 206--207
  passed.  The only Lean warnings were the pre-existing `HouseholderQR`
  unused-variable warnings, and the axiom audit reported only standard
  `propext`, `Classical.choice`, and `Quot.sound`.

- 2026-06-02: Added the LS.2g-gb actual-unit-roundoff stored-lower
  specialization.  `LSQRSolve.lean` proves
  `LSQRSolveBackwardError.of_stored_trailing_householder_sequence_topBlock_fl_backSub_gamma_bound_explicitCompactBudget_of_signed_alpha_diagDominant_storedLower_finiteMaxSourceDenURationalGammaCanonicalBounds_of_actualUnitRoundoff`,
  and `LeastSquaresSketch.lean` proves
  `leverageTraceProbability_eventProb_fl_rowSampleLSObjective_le_one_add_eta_of_augmentedSpan_sample_budget_of_objective_error_and_stored_qr_diagDominant_storedLower_finiteMaxSourceDenURationalGammaCanonicalBounds_solver_of_actualUnitRoundoff`.
  These wrappers choose `Ucap = fp.u`, discharge `fp.u <= Ucap` by
  reflexivity, and write the canonical finite-max scalar smallness condition
  directly with the actual unit roundoff.  The ordinary `gammaValid fp m` or
  `gammaValid fp s` guard remains visible.  This removes a primitive cap
  parameter and cap notation from the stored-lower solver/probability surface;
  it does not prove scalar smallness, local diagonal dominance/off-diagonal
  control, conditioning fields, or the final generic QR/preconditioner theorem.
  Two weak-component passes are clean: focused LSQRSolve and
  LeastSquaresSketch builds; executable lookup; `git diff --check`;
  touched Lean-source marker scan; qualified axiom audit; theorem PDF compile;
  targeted `pdftotext` over pages 206--208; and rendered pages 206--208
  passed.  The only Lean warnings were the pre-existing `HouseholderQR`
  unused-variable warnings, and the axiom audit reported only standard
  `propext`, `Classical.choice`, and `Quot.sound`.

- 2026-06-05: Added LR.1ds for the RandNLA CACM equation-(9) low-rank
  bottleneck.  `LowRankApprox.lean` proves
  `exists_columnSketchGramInverseProjector_sourceHeadTail_sourceSVDTailRankResidualSurface_of_rectRightGramOrdered_replacement_tail_left_of_last_pos`,
  composing the constructed ordered replacement-tail block certificate with the
  exact block-certificate rank/residual surface.  The theorem exposes exact
  `det(V_ord^T Z) != 0` and cross-term hypotheses and gives rank at most `k`
  plus residual radius `2 * sqrt(1 + eps^2) * ||Sigma_tail||_F`; sampling
  probabilities and laws remain exact mathematical inputs.  It does not prove
  the relative/Eckart--Young conclusion, randomness-derived cross-term
  certificates, or computed non-probability SVD/singular-vector/projector/Gram/
  inverse/sketch/product routines.  Focused Lean, focused Lake build after one
  stale-artifact rerun, lookup, aggregate RandNLA build, full Lake build,
  marker scan, axiom audit, PDF compile/text/render checks, and root/docs PDF
  sync passed; the axiom audit reported only `propext`, `Classical.choice`, and
  `Quot.sound`.

- 2026-06-05: Added and fully validated LR.1dt for the RandNLA CACM
  equation-(9) low-rank bottleneck.  `LowRankApprox.lean` proves
  `exists_columnSketchGramInverseProjector_sourceHeadTail_sourceSVDTailRelativeResidualSurface_of_rectRightGramOrdered_replacement_tail_left_of_last_pos`,
  composing the same constructed ordered replacement-tail block certificate
  with the exact block-certificate sigma-tail relative surface.  The theorem
  exposes exact `det(V_ord^T Z) != 0`, exact cross-term, exact tail-optimality
  for every rank-at-most-`k` competitor, and scalar comparison hypotheses, then
  returns the best-rank certificate for the constructed ordered source head and
  the relative residual bound for the exact Gram-inverse column-sketch
  projector.  Focused Lean, focused Lake build, lookup, aggregate RandNLA
  build, full Lake build, `git diff --check`, marker scan, axiom audit, PDF
  compile/text/render checks, and root/docs PDF sync passed; the axiom audit
  reported only `propext`, `Classical.choice`, and `Quot.sound`.  Remaining
  obligations are the Eckart--Young tail-optimality proof for the constructed
  ordered source split, randomness-derived cross-term certificates, and
  computed non-probability SVD/singular-vector/projector/Gram/inverse/sketch/
  product routine certificates.  Sampling probabilities and laws remain exact
  mathematical inputs.

- 2026-06-05: Added and fully validated LR.1du for the RandNLA CACM
  equation-(9) low-rank bottleneck.  `LowRankApprox.lean` now proves the
  generic exact diagonal identities `frobNormSq_diagonal_eq_sum` and
  `frobNorm_diagonal_eq_sqrt_sum`, plus the constructed ordered-tail
  specializations `frobNormSq_rectRightGramOrderedTailSingularDiagonal_eq_sum`
  and `frobNorm_rectRightGramOrderedTailSingularDiagonal_eq_sqrt_sum`.  The
  result rewrites `||rectRightGramOrderedTailSingularDiagonal A hk||_F` as the
  square root of the complement singular-square sum needed for the LR.1dt
  tail-optimality discharge.  Focused Lean, lookup, aggregate RandNLA build,
  full Lake build, `git diff --check`, marker scan, axiom audit, PDF
  compile/text/render checks, and root/docs PDF sync passed; the axiom audit
  reported only `propext`, `Classical.choice`, and `Quot.sound`.  Remaining
  obligations are the residual lower-bound transport, randomness-derived
  cross-term certificates, and computed non-probability SVD/singular-vector/
  projector/Gram/inverse/sketch/product routine certificates.  Sampling
  probabilities and laws remain exact mathematical inputs.

- 2026-06-05: Added and fully validated LR.1dv for the RandNLA CACM
  equation-(9) low-rank bottleneck.  `LowRankApprox.lean` now proves
  `rectRightGramSelectedIndexSet_card_add_compl_card` and
  `rectRightGramOrderedTailIndex_card_add`, giving the exact finite-cardinality
  bridge `k + |S^c| = n` and its constructed ordered-tail specialization
  `k + q = n`.  Focused Lean, focused LowRankApprox build, lookup, full Lake
  build, `git diff --check`, marker scan, axiom audit, PDF compile/text/render
  checks, and root/docs PDF sync passed; the axiom audit reported only
  `propext`, `Classical.choice`, and `Quot.sound`.  Remaining obligations are
  column-reindexing/equivalence transport, the residual lower-bound discharge
  for LR.1dt's tail-optimality hypothesis, randomness-derived cross-term
  certificates, and computed non-probability SVD/singular-vector/projector/
  Gram/inverse/sketch/product routine certificates.  Sampling probabilities
  and laws remain exact mathematical inputs.

- 2026-06-06: Added LR.1dw for the RandNLA CACM equation-(9) low-rank
  bottleneck.  `LowRankApprox.lean` now proves
  `sum_vecNorm2Sq_sourceSVDFactorMatrix_ge_tail_sq_of_orthonormal_gap`,
  `rectRankAtMost_lowRankResidualFrob_sq_ge_tail_sum_of_sourceSVDFactorMatrix_gap`,
  and `sqrt_tail_sum_le_lowRankResidualFrob_of_sourceSVDFactorMatrix_gap`.
  The route transports the diagonal head-tail gap theorem through exact
  `U diag(sigma) V^T` and composes it with the q-dimensional residual-side
  right-kernel theorem.  This avoids assuming that a constructed complement-tail
  enumeration is sorted: it only needs a visible separator `eta` with head
  squares above and tail squares below.  Focused Lean, focused LowRankApprox
  build, lookup, full Lake build, `git diff --check`, marker scan, axiom audit,
  PDF compile/text/render checks, and root/docs PDF sync passed; the axiom
  audit reported only `propext`, `Classical.choice`, and `Quot.sound`.  The
  summary PDF now contains Corollary 605, "Source-factor gap lower-bound bridge
  for equation (9)", with the three LR.1dw theorem names.  The remaining
  low-rank proof still needs the constructed gap instantiation, original-column
  reindexing/equivalence transport, LR.1dt tail-optimality discharge,
  randomness-derived cross-term certificates, and computed non-probability
  SVD/singular-vector/projector/Gram/inverse/sketch/product routine
  certificates.  Sampling probabilities and laws remain exact mathematical
  inputs.

- 2026-06-06: Added LR.1dx for the RandNLA CACM equation-(9) low-rank
  bottleneck.  `LowRankApprox.lean` now proves
  `rectRightGramOrdered_head_tail_square_gap`: for `0 < k`, the last selected
  top singular square is a separator `eta` such that every constructed selected
  head square is at least `eta` and every constructed complement-tail singular
  square is at most `eta`.  The proof uses selected-square equality plus
  antitonicity of ordered right-Gram singular-value squares for the head side,
  and the complement-versus-selected comparison plus nonnegativity and
  `sq_le_sq` for the tail side.  Focused Lean, focused LowRankApprox build,
  lookup, full Lake build, `git diff --check`, marker scan, axiom audit, PDF
  compile/text/render checks, and root/docs PDF sync passed; the axiom audit
  reported only `propext`, `Classical.choice`, and `Quot.sound`.  The summary
  PDF now contains Corollary 588, "Constructed ordered head-tail square gap",
  with the LR.1dx theorem name and the displayed separator inequalities.  The
  remaining low-rank proof still needs original-column reindexing/equivalence
  transport, the LR.1dt tail-optimality discharge, randomness-derived cross-term
  certificates, and computed non-probability SVD/singular-vector/projector/Gram/
  inverse/sketch/product routine certificates.  Sampling probabilities and laws
  remain exact mathematical inputs.

- 2026-06-06: Added LR.1dy for the RandNLA CACM equation-(9) low-rank
  bottleneck.  `LowRankApprox.lean` now defines
  `RectRankFactorization.permuteCols` and proves
  `RectRankAtMost.permuteCols`, `RectRankAtMost.of_permuteCols`, and
  `lowRankResidualFrob_permuteCols`.  This gives the exact generic
  column-reindexing transport: explicit rank factorizations transport by
  composing the right factor with the column equivalence, rank-at-most
  certificates transport both directions, and Frobenius residuals are invariant
  when source and competitor are permuted together.  Focused Lean, focused
  LowRankApprox build, lookup, full Lake build, marker scan, axiom audit, PDF
  compile/text/render checks, and root/docs PDF sync passed.  The PDF records
  this as Corollary 589 on pages 394--395.  This clears the LowRank parse
  blocker noted in not-proved ledger row 1451.  The next low-rank target is the
  constructed head-plus-complement-tail equivalence
  `Fin (k+q) ≃ Fin n`, followed by the LR.1dt tail-optimality discharge.
  Sampling probabilities and laws remain exact mathematical inputs.

- 2026-06-06: Added LR.1dz for the RandNLA CACM equation-(9) low-rank
  bottleneck.  `LowRankApprox.lean` now defines
  `rectRightGramOrderedHeadTailColumnMap`, proves its injectivity and
  surjectivity, packages `rectRightGramOrderedHeadTailColumnSumEquiv`, and
  composes with `finSumFinEquiv` to obtain
  `rectRightGramOrderedHeadTailColumnEquiv : Fin (k+q) ≃ Fin n` for the
  constructed ordered top block plus complement-tail enumeration.  Focused
  Lean, focused LowRankApprox build, lookup, full Lake build, marker scan,
  axiom audit, PDF compile/text/render checks, and root/docs PDF sync passed.
  The PDF records this as Corollary 590 on pages 396--397.  The next low-rank
  target is the LR.1dt tail-optimality discharge using the constructed gap,
  diagonal-tail norm, and column-equivalence transport.  Sampling probabilities
  and laws remain exact mathematical inputs.

- 2026-06-06: Added LR.1ea for the RandNLA CACM equation-(9) low-rank
  bottleneck.  `LowRankApprox.lean` now defines `rectReindexCols` for exact
  cross-domain column equivalences `Fin p ≃ Fin n`, transports explicit rank
  factorizations and rank-at-most certificates through the equivalence, proves
  `frobNormSqRect_reindexCols`, `frobNormRect_reindexCols`, and
  `lowRankResidualFrob_reindexCols`, and specializes the result to
  `rectRightGramOrderedHeadTailColumnEquiv hk`.  Focused Lean, focused
  LowRankApprox build, lookup, full Lake build, marker scan, axiom audit, PDF
  compile/text/render, and root/docs PDF sync passed.  The PDF records this as
  Corollary 591 on pages 397--398.  The next low-rank target remains the
  LR.1dt tail-optimality discharge.  Sampling probabilities and laws remain
  exact mathematical inputs.

- 2026-06-06: Added and fully validated LR.1eb for the RandNLA CACM
  equation-(9) low-rank bottleneck.  `LowRankApprox.lean` now assembles the
  constructed ordered head-plus-tail `Fin(k+q)` source blocks, proves the left
  block and pulled-back right block orthonormal/orthogonal facts, proves the
  source factor equals `rectReindexCols (rectRightGramOrderedHeadTailColumnEquiv hk) A`,
  and discharges the constructed tail-optimality inequality
  `frobNorm (rectRightGramOrderedTailSingularDiagonal A hk) <=
  lowRankResidualFrob A B` for every exact rank-at-most-`k` competitor.  The
  wrapper
  `exists_columnSketchGramInverseProjector_sourceHeadTail_sourceSVDTailRelativeResidualSurface_of_rectRightGramOrdered_replacement_tail_left_of_last_pos_tailOptimal`
  feeds this into LR.1dt without a supplied `hopt`.  Focused Lean, focused
  LowRankApprox build, lookup, full Lake build, marker scan, axiom audit, PDF
  compile/text/render, and root/docs PDF sync passed.  The PDF records this as
  Corollary 592 on pages 399--400.  The next low-rank targets are
  randomness-derived cross-term certificates, scalar relative comparison, and
  computed non-probability SVD/singular-vector/projector/Gram/inverse/sketch/
  product routine certificates.  Sampling probabilities and laws remain exact
  mathematical inputs.

- 2026-06-06: Added and fully validated LR.1ec for the RandNLA CACM
  equation-(9) low-rank bottleneck.  `LowRankApprox.lean` now proves
  `two_sqrt_one_add_sq_mul_tail_le_of_scalar` and the wrapper
  `exists_columnSketchGramInverseProjector_sourceHeadTail_sourceSVDTailRelativeResidualSurface_of_rectRightGramOrdered_replacement_tail_left_of_last_pos_tailOptimal_of_scalarRelative`.
  The theorem surface now accepts the coefficient condition
  `2 * sqrt (1 + eps^2) <= rho`; Lean derives the product-form scalar
  comparison by multiplying by the nonnegative constructed tail Frobenius norm.
  During validation a local proof-focus issue in
  `rademacherTraceProbability_expectationReal_eq_zero_of_flip_neg` was made
  robust by proving the function equality explicitly.  Focused Lean, focused
  Preconditioning build, focused LowRankApprox build, lookup, full Lake build,
  marker scan, axiom audit, PDF compile/text/render, and root/docs PDF sync
  passed.  The PDF records this as Corollary 593 on page 401.  Remaining
  low-rank targets are randomness-derived cross-term certificates and computed
  non-probability SVD/singular-vector/projector/Gram/inverse/sketch/product
  routine certificates.  Sampling probabilities and laws remain exact
  mathematical inputs.
