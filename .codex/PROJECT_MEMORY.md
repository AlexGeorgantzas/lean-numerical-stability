# Codex Project Memory

Project: `LeanFpAnalysis`, a Lean 4 library for floating-point arithmetic and
automatic stability analysis. The model is axiomatic and intentionally not tied
to IEEE 754. All core results should be stated over `FPModel` and `Real`.

Last review by Codex: 2026-04-26.
Current main commit after integrity fixes: `015d6c4`.

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
  `015d6c4`; `.vscode/extensions.json` remains an unrelated untracked file.

## Claude Context Found

- `.claude/settings.json` and `.claude/settings.local.json` contain tool
  permission/settings only.
- `benchmark/condition_c/.claude/CLAUDE.md` is the only substantive Claude
  memory. It is benchmark-specific and describes Condition C as full-library
  access, with a high-level module map and Lean proof hints.
- Additional Claude project memory exists outside the repo at
  `/Users/georgiosalexandrosgeorgantzas/.claude/projects/-Users-georgiosalexandrosgeorgantzas-Documents-GitHub-lean-fp-analysis/memory/MEMORY.md`.
  It frames the project as a VSCL/Thrust A thesis library for compositional
  stability-carrying foundations, not as a goal to formalize all of Higham.
- Durable user/project preferences from Claude memory: formalize only reusable
  stepping stones for future stability proofs; always search the existing
  codebase before claiming a theorem or definition is missing; put proof
  sketches in docstrings; keep Higham constants exact.

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

- `Model.lean`: `FPModel` with `u`, `u_nonneg`, `fl_add/sub/mul/div`, exact
  `fl_add_zero`, and standard relative-error axioms for each operation.
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
- `Analysis/MatrixAlgebra.lean`: exact matrix operations, inverses, norms,
  transpose, Frobenius algebra, orthogonal matrices, Neumann-series style
  bounds. This is foundational but very large and could eventually be split.
- `Analysis/PerturbationTheory.lean`: residual, normwise/componentwise
  perturbation, Oettli-Prager, Rigal-Gaches, Skeel condition definitions.

## Strong Reuse Chain

- `Rounding` supports `Summation` and `SubtractionFold`.
- `Summation` supports `DotProduct`.
- `DotProduct` supports `MatVec`.
- `MatVec` supports `MatMul` and matrix inversion residual results.
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
- The benchmark tree is currently incomplete in the working copy: the new
  `benchmark/condition_a` and `benchmark/condition_c` directories have config
  files only and no Lean exercise files.

## Benchmark Context

Claude memory says the thesis benchmark is designed as `10 tasks × 3
conditions`, with three difficulty tiers.  Research question: does access to
`LeanFpAnalysis` help LLMs prove FP stability results they otherwise cannot?

Conditions:

- **A: Bare**: Mathlib only; the agent must invent the FP model, gamma
  calculus, algorithm definitions, intermediate lemmas, and proof.
- **B: Axioms only**: provide only `FPModel`, `gamma`, and `gammaValid`; the
  agent still has to build all intermediate algorithm lemmas.
- **C: Full library**: provide full `LeanFpAnalysis` imports and task theorem;
  the agent should compose existing library results.

Intended task list from Claude traces:

- Tier 1 direct application:
  `T01_SymmetricMatVec`, `T02_UnitTriangularForwardSub`, and `T03` either
  `NormwiseMatVecBound` in older generated task files or
  `ResidualStoppingCriterion` in later README/file-history traces. Resolve this
  before regenerating benchmark files; the later thesis README-style design
  appears to prefer `ResidualStoppingCriterion`.
- Tier 2 composition:
  `T04_PLUSolve`, `T05_TwoStepRefinement`, `T06_LDLtSolve`.
- Tier 3 novel reasoning:
  `T07_ScaledMatVec`, `T08_GEMV`, `T09_BlockTriangularSolve`,
  `T10_StationaryInexactSolve`.

Metrics from Claude benchmark design: `pass@1`, `pass@5`, remaining `sorry`
count in best attempt, human edit distance/lines, proof validity via
`lake build`, and response/proof lines of code.

Current repo state: tracked benchmark files are only
`benchmark/condition_a/{lakefile.toml,lean-toolchain,.claude/settings.json}`
and `benchmark/condition_c/{lakefile.toml,lean-toolchain,.claude/settings.json,
.claude/CLAUDE.md}`.  There is no tracked `condition_b`, no tracked task Lean
files, and no tracked benchmark runner/validator scripts.  Claude session
history shows older task files once lived under `LeanFpAnalysis/FP/Benchmark`
and/or `benchmark/tasks`, then were removed/moved; regenerate cleanly rather
than relying on the old tree.

Condition C Claude prompt file: `benchmark/condition_c/.claude/CLAUDE.md`
describes full-library access, tells agents to replace `sorry` in
`ConditionC/` exercises, and lists key library modules and Lean 4 proof
patterns.

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
