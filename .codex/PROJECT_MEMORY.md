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
- RandNLA Algorithm 1 now builds as:
  `ElementwiseSampling` for squared-magnitude probabilities, deterministic
  sampled-entry updates, traces, hit counts, and entrywise stability events;
  `Analysis/FiniteProbability` for generic probability kernels; and
  `HitCountConcentration` for Markov, pairwise-Chebyshev, and canonical
  product-law Chernoff concentration plus high-probability stability.
- RandNLA Algorithm 2 row sampling builds in `Algorithms/RandNLA/RowSampling.lean`
  and `Algorithms/RandNLA/RowSamplingGram.lean`: equation (4) norm-squared row
  probabilities, literal sampled rows, local one-division FP stability,
  elementwise unbiasedness of `Atildeᵀ Atilde`, the iid variance calculation,
  high-probability equation (5), the probability-one support theorem for
  positive-probability row traces, and explicit FP perturbation/bias theorems
  for the Gram matrix.
  Do not cite any grouped row-hit or Chernoff-count theorem for Algorithm 2;
  Algorithm 2 does not accumulate repeated sampled rows.

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
