# Codex Project Memory

Project: `LeanFpAnalysis`, a Lean 4 library for floating-point arithmetic and
automatic stability analysis. The model is axiomatic and intentionally not tied
to IEEE 754. All core results should be stated over `FPModel` and `Real`.

Last review by Codex: 2026-04-28.
Current branch `benchmark` contains the benchmark harness and T01
workspace-generator pass.  `main` is kept as the core-library branch.

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
  `015d6c4`.  Benchmark setup commits through `f54206d` live on branch
  `benchmark`.
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
- The benchmark tree now has canonical task specs, a neutral unsolved T01 task,
  and a first generated-workspace harness.  The harness copies the same
  `Task.lean` into both conditions, then satisfies `import LeanFpAnalysis.FP`
  with either a task-local bare stub (Condition A) or the real library
  (Condition C).

## Benchmark Context

Revised user decision on 2026-04-27: skip the old Condition B.  The thesis
benchmark should be `10 tasks × 2 conditions`, with tasks in increasing
difficulty.  Research question: does access to `LeanFpAnalysis` help Codex
prove FP stability-analysis results it otherwise cannot?

Conditions:

- **A: Bare**: Mathlib only; the agent must invent the FP model, gamma
  calculus, algorithm definitions, intermediate lemmas, and proof.  Condition A
  should still include the bare minimum definitions needed to state exactly the
  same theorem target as Condition C.  Generated A/C workspaces should use
  byte-identical task files; Condition A satisfies `import LeanFpAnalysis.FP`
  with generated bare stubs, while Condition C uses the real library.
- **C: Full library**: provide full `LeanFpAnalysis` imports and task theorem;
  the agent should use the repository as a first-time user of the library.
  Condition C should not provide agent memory files, private notes, or
  task-specific proof hints. Its help should come from the library itself:
  module organization, theorem names, docstrings, comments, and public
  orientation material describing what the library contains.

Execution note: Codex will be the evaluated solver, so the benchmark must be
mostly automatic and must avoid condition leakage.  Condition A should run in an
isolated project/worktree that does not expose `LeanFpAnalysis`; otherwise the
agent could inspect the parent repository.  Final task files should avoid proof
hints or expected-approach comments.

Task difficulty rule: the exercises should not be exact theorem lookups or
one-line lemma chaining, especially in the first five tasks.  Early tasks should
still require the agent to instantiate algorithm definitions, bridge notation,
perform small algebraic rewrites, or combine a local statement with a library
contract.  Later tasks should become progressively more compositional and may
require substantial new glue lemmas or algorithm variants, while remaining true
statements over the stated model.

Condition C documentation surface: the public library guide should be
`docs/LIBRARY_LOOKUP.md`, linked from `README.md`, with a companion exploratory
Lean file at `examples/LibraryLookup.lean`.  This guide is acceptable help for
Condition C because it is normal repository documentation and is not
agent-specific.  It should remain free of benchmark task names, expected proof
routes, and task-specific hints.

Project-wide decision notes now live in `thesis/DECISION_LOG.md`.  This
file is intentionally solver-invisible material: it records why choices were
made, rejected alternatives, benchmark task ordering, expected difficulty, and
automation policy.  Do not copy it into Condition A or Condition C solver
workspaces.

Earlier generated task list considered:

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

Metrics from earlier benchmark design: `pass@1`, `pass@5`, remaining `sorry`
count in best attempt, human edit distance/lines, proof validity via
`lake build`, and response/proof lines of code.

Current benchmark source state: `benchmark/tasks/T01_ScaledDot/Task.lean` is
the canonical unsolved task file; `benchmark/stubs/T01_ScaledDot/` supplies the
Condition A import provider; `benchmark/scripts/generate_task_workspace.sh`
creates paired generated workspaces.  Tool-specific benchmark settings and
prompt/memory files were removed because Condition C should use public library
docs rather than hidden guidance.  Older generated task files that once lived
under `LeanFpAnalysis/FP/Benchmark` or earlier benchmark folders should not be
trusted; regenerate cleanly from the current benchmark tree.

Task-selection rule: hard is fine, but invalid/unprovable statements are not a
useful benchmark.  If a task needs extra exactness assumptions or a slightly
different algorithm variant, state those assumptions or define that variant
explicitly.  Every task should be stability analysis for an algorithm.
Do not restrict task discovery to Higham statements: use the current library's
formal theorem surface to design new algorithm-composition and certificate
tasks.  The hardest tasks should be true under clear assumptions and grounded in
existing internal theorem chains, while leaving the actual solver success/fail
outcome open.

Benchmark task theorem shapes are being drafted in
`benchmark/tasks/TASK_SPECS.md`.  This is benchmark-source/planning material,
not solver-facing input.  Generated Condition A/C workspaces should receive
only the current task file and the allowed condition environment.
Generated-workspace rules live in `benchmark/RUN_PROTOCOL.md`.
Do not pre-solve benchmark tasks with Codex before evaluation.  Since Codex is
the evaluated solver, repository reference proofs or same-conversation proofs
create avoidable contamination risk.  Generate theorem statements with `sorry`,
run fresh isolated solver attempts, then add hidden reference proofs or
post-hoc validation artifacts only after evaluation if needed.

T01 experiment status on 2026-04-28: the generated Condition A workspace builds
with only the bare `LeanFpAnalysis.FP` stub and the expected `sorry` warning;
the generated Condition C workspace builds with the real library and the same
expected `sorry` warning.  Validate generated workspaces with
`lake build BenchmarkTask`, not direct `lake env lean BenchmarkTask.lean`,
because the generated local import provider must first be built into `.olean`
files.

Draft task ladder proposed 2026-04-27, not yet finalized:

1. Scaled dot product backward stability: define a task-local algorithm that
   computes `fl_mul alpha (fl_dotProduct x y)` and prove a gamma-composed
   componentwise backward-error statement.
2. Shifted dot product forward stability: define a task-local algorithm that
   computes `fl_add c (fl_dotProduct x y)` and prove an absolute forward-error
   bound involving `|c| + sum |x_i||y_i|`.
3. Residual stopping certificate: use `fl_residual` and prove that a small
   computed residual implies a bound on the exact residual after accounting for
   residual-computation error.
4. Triangular solve residual certificate: derive a componentwise residual bound
   for `fl_forwardSub` or `fl_backSub` from the triangular backward-error
   theorem.
5. BLAS GEMV stability: define a task-local `alpha*A*x + beta*y` algorithm
   using `fl_matVec`, scalar multiplications, and additions, and prove a
   componentwise forward-error bound with an absorbed gamma constant.
6. Combined triangular solve as a backward-stable solve for `A = L*U`: expand
   `(L+DeltaL)(U+DeltaU)` from `triangularSolve_backward_error` to a single
   perturbation bound of size about `2*gamma + gamma^2`.
7. LU solve with growth-scaled relative backward error: combine
   `lu_solve_backward_error` with a componentwise growth hypothesis
   `|L||U| <= rho |A|`.
8. Cholesky solve with growth-scaled relative backward error: combine
   `cholesky_solve_backward_error` with a factor-product growth hypothesis.
9. One-step iterative refinement with conventional residual and a
   backward-stable correction solve: combine residual computation with the
   one-step refinement residual bound.
10. Stationary iteration with inexact triangular local solves: derive or
    instantiate `ComputedIteration`/local-error hypotheses for a concrete
    splitting step and then prove a normwise residual or forward-error bound.

Avoid old generated tasks as-is: symmetric matvec is likely false without a
symmetry-preserving perturbation theorem; unit triangular solve with zero
diagonal perturbation needs an explicit unit-diagonal algorithm variant; LDLT
currently leans on abstract interfaces; old block triangular solve was too
partial unless reformulated as a full residual/backward-error statement.

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
