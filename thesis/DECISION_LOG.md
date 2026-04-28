# Project Decision Log

This file records design decisions for the LeanFpAnalysis project.  It is
intended as thesis source material and durable project memory.

The log is project-wide, not only a benchmark log.  It should record decisions
about library design, proof organization, documentation, branches, benchmark
methodology, and thesis-facing rationale.  Benchmarking is the current active
work on this branch, so the benchmark sections below are detailed.

Important: do not include this file in solver-facing benchmark workspaces.  It
may contain benchmark intent, task ordering, expected difficulty, and reasons
for choosing particular tasks.  Condition C should expose the public library,
source comments, `README.md`, `docs/LIBRARY_LOOKUP.md`, and examples, but not
project decision notes like this file.

## Branch Policy

### Decision: Keep Benchmark Work On A Dedicated Branch

Benchmark artifacts live on branch `benchmark`.

This includes:

- benchmark task files;
- condition-specific stubs;
- generated-workspace scripts;
- run protocols;
- task-selection rationale;
- contamination checks;
- solver-attempt logs, when added.

Reason: benchmark design is exploratory and has different risks from the core
library.  It may need several iterations, and it must avoid accidentally mixing
solver-facing material with private design rationale.  Keeping it on its own
branch lets the core library remain stable while benchmark infrastructure
evolves.

`main` is the core-library branch.  It may keep project-wide thesis notes and
reusable public documentation, but benchmark harness files should not live on
`main` unless explicitly merged later.

## Core Library Decisions

### Decision: Use An Axiomatic Floating-Point Model

The library is built around `FPModel`, an axiomatic model over `Real`, rather
than a specific IEEE 754 formalization.

Reason: the goal is automatic stability analysis in a general mathematical
floating-point model.  The core theorem statements should be reusable across
formats and rounding implementations, as long as they satisfy the model
axioms.

Consequence: avoid adding IEEE-specific assumptions to core modules.  If they
are ever needed, they should belong in a separate optional module.

### Decision: Build Stability Proofs Compositionally

New results should reuse existing lower-level contracts whenever possible:
rounding lemmas support summation, summation supports dot products, dot
products support matvec/matmul, and triangular solve contracts support
higher-level solve analyses.

Reason: the thesis goal is not only to formalize isolated theorems, but to test
whether a library of reusable stability components helps future analyses.

### Decision: Mark Abstract Interfaces Honestly

Some high-level results are specification-transfer theorems: they take an
external or abstract hypothesis that is already close to the desired numerical
contract, then package the consequence.

Reason: these are useful named interfaces, but they should not be advertised as
fully derived floating-point analyses from `FPModel`.

Consequence: wrappers around external assumptions should be documented as
abstract/specification-transfer results.

### Decision: Keep Public Lookup Documentation

The files `docs/LIBRARY_LOOKUP.md` and `examples/LibraryLookup.lean` are public
library documentation.

Reason: the library is large.  A central lookup guide helps humans and tools
discover relevant definitions and theorem families without relying on private
agent memory.

These files are allowed on `main` because they describe the library generally.
They should avoid task-specific proof scripts.

## Benchmark Design Rationale

### Benchmark Goal

The benchmark asks whether access to a formal floating-point stability library
helps an AI agent prove stability-analysis theorems in Lean.

The benchmark is not meant to test ordinary theorem proving in isolation.  It
is meant to test whether the library changes the agent's ability to reason
compositionally about floating-point algorithms:

- identify the relevant FP model and gamma assumptions;
- use reusable local stability contracts;
- compose forward-error, backward-error, and residual-error results;
- avoid reproving a full floating-point analysis from first principles.

The target solver is Codex.  The benchmark should therefore be mostly
automatic, repeatable, and protected against leakage between conditions.

### Decision: Two Conditions Instead Of Three

Earlier benchmark notes considered three conditions:

- Condition A: bare environment;
- Condition B: FP axioms only;
- Condition C: full library access.

The current design uses only two conditions:

- **Condition A: Bare/isolated.**  The solver gets Mathlib plus only the
  minimum definitions needed to state the theorem target.
- **Condition C: Full library.**  The solver gets the LeanFpAnalysis library as
  a normal user would: public source files, comments/docstrings, README,
  lookup guide, and examples.

The reason for dropping Condition B is that it is less directly aligned with
the thesis question.  Condition B would measure whether the agent can rebuild a
large amount of intermediate floating-point infrastructure after being given
only the axioms.  That is interesting, but it weakens the main comparison:
whether a reusable stability library changes what can be proved.

The two-condition setup is cleaner:

- Condition A measures what the model can do without the library.
- Condition C measures what the model can do with the library as a public
  mathematical artifact.

This also reduces benchmark cost and makes the results easier to explain:
each task has exactly one control environment and one library environment.

### Decision: Condition A Must Be Isolated

Condition A must be run in an isolated project/workspace, not merely in a
subdirectory of the repository.  Otherwise the solver could inspect
`LeanFpAnalysis` or public lookup documentation and silently convert Condition
A into Condition C.

Condition A should contain:

- Mathlib and the Lean toolchain;
- the task file;
- the bare definitions required to state exactly the same theorem target as in
  Condition C.

Condition A should not contain:

- `LeanFpAnalysis`;
- library documentation;
- benchmark rationale files;
- previous solver attempts;
- memory files.

The theorem statement should be syntactically and semantically the same target
as in Condition C wherever possible.  The point is not to give Condition A a
different problem; the point is to remove the library support.

The preferred implementation is to copy the exact same task file into both
generated workspaces.  The task file imports `LeanFpAnalysis.FP` in both
conditions.  In Condition A that import is satisfied by a generated bare stub
with only the definitions required to state the theorem; in Condition C it is
satisfied by the actual library.

### Decision: Condition C Should Be Fresh But Documented

Condition C should model a realistic first encounter with the library.  The
agent should not receive agent memory files, old benchmark notes, or a
task-specific proof strategy.  However, it should be allowed to read normal
public documentation and comments.

Allowed Condition C material:

- `LeanFpAnalysis` source files;
- theorem names and docstrings;
- `README.md`;
- `docs/LIBRARY_LOOKUP.md`;
- `examples/LibraryLookup.lean`;
- task statement.

Disallowed Condition C material:

- agent memory directories;
- benchmark design notes;
- task-specific proof hints;
- previous attempts or expected proof scripts.

This distinction matters.  The thesis should measure the value of the library,
not the value of private agent memory.

### Decision: Public Lookup Guide Instead Of Hidden Memory

A lookup guide was chosen over an agent-specific memory file.

Rejected option: hidden agent memory.

Reason rejected: it would make Condition C depend on private prompt state rather
than the library.  It would also be difficult to reproduce across agents or
future versions of Codex.

Rejected option: only source comments, no central guide.

Reason rejected: the library is large.  A fresh agent or human user may spend a
large part of the benchmark simply rediscovering names and module organization.
That would measure navigation friction more than mathematical reuse.

Chosen option: public lookup documentation.

Files:

- `docs/LIBRARY_LOOKUP.md`
- `examples/LibraryLookup.lean`

Reason chosen: this is normal library documentation.  It tells users where
definitions and theorem families live without giving benchmark-specific proof
scripts.  It is reusable for humans, agents, and thesis readers.

The lookup guide must remain benchmark-neutral.  It may list theorem names,
files, assumptions, and caveats.  It should not mention task names, expected
solutions, or "for task N use theorem X".

### Task-Selection Principles

Every task must be a stability-analysis task for an algorithm.  The benchmark
should not drift into pure algebra, pure matrix theory, or generic Lean puzzles.
The tasks also should not be restricted to statements appearing verbatim in
Higham.  Much of the point of the library is that Higham-style infrastructure
has already been formalized; the benchmark should test whether an agent can use
that infrastructure to perform new stability analyses for composed algorithms,
certificates, and task-local variants.

A good task has the following properties:

- The statement is true under the given assumptions.
- Condition A and Condition C attempt the same theorem target.
- Condition C has a plausible route using the library.
- The proof is not merely an exact restatement of an existing theorem.
- The proof requires some stability reasoning: unpacking a contract,
  composing local errors, converting backward error to residual error, or
  absorbing gamma constants.
- The task is grounded in a real stability-analysis pattern: an internal
  library theorem chain, a standard numerical analysis result, or an explicitly
  defined algorithm variant whose assumptions match the model.
- The task is not a known textbook theorem copied verbatim with a common Lean
  formalization available online.

Hard tasks are allowed to require extra assumptions or task-local algorithm
variants.  That is acceptable if the assumptions are explicit and mathematically
defensible.  What should be avoided is a false theorem or an underspecified
algorithm.

For the final task or final two tasks, the desired outcome is asymmetric:
Condition A should plausibly fail because it lacks the formal FP/gamma/matrix
infrastructure, while Condition C should have a plausible path through the
library.  It is acceptable to leave the actual solver outcome open.  What is not
acceptable is leaving the theorem truth open.  The theorem statement must be
grounded before the run by conservative assumptions and a clear library theorem
chain, even if no Codex-written proof is produced before evaluation.

### Proposed Task Ladder

The current draft is a sequence of ten tasks in increasing difficulty.  The
names below are descriptive, not final theorem names.

The working task-spec source is `benchmark/tasks/TASK_SPECS.md`.  It is used to
develop exact theorem shapes before generating Condition A and Condition C
workspaces.  It is not solver-facing material and should not be copied into
generated benchmark runs.

The generated-workspace protocol is tracked in `benchmark/RUN_PROTOCOL.md`.
That file describes what is copied into Condition A and Condition C and what
must be excluded.

Because Codex is the evaluated solver, benchmark tasks should not be pre-solved
by Codex in the repository before evaluation.  Pre-solving would create
unnecessary contamination risk, especially if the same conversation or files are
available to the evaluated run.  The safer protocol is:

- write theorem statements and task-local definitions;
- generate Condition A and Condition C workspaces with byte-identical task
  files containing `sorry`;
- run fresh solver attempts;
- only after solver runs, add hidden reference proofs or post-hoc validation
  artifacts if needed to diagnose failures.

#### 1. Scaled Dot Product Backward Stability

Algorithm: compute `alpha * (x^T y)` by first computing a floating-point dot
product and then one rounded multiplication by `alpha`.

Reason for selection:

- It is the smallest nontrivial composition beyond an existing theorem.
- The library gives dot-product backward stability, but the task must account
  for the extra scalar multiplication.
- It tests whether the solver can combine a local stability theorem with one
  additional FP operation.

Expected Condition A difficulty:

- Rebuilding dot-product backward error and gamma composition from scratch is
  already substantial.

Expected Condition C route:

- Use `dotProduct_backward_error` or `dotProduct_backward_stable_x`.
- Use the FP multiplication model.
- Combine the errors with gamma arithmetic.

#### 2. Shifted Dot Product Forward Stability

Algorithm: compute `c + x^T y` by computing the floating-point dot product and
then one rounded addition with `c`.

Reason for selection:

- It is a realistic kernel: affine dot products occur in residual updates,
  Krylov methods, and BLAS-like routines.
- It tests forward-error reasoning rather than only backward-error reasoning.
- It forces the proof to carry both the dot-product contribution and the shift
  contribution.

Expected Condition A difficulty:

- The agent must reconstruct the dot-product forward bound and one-step
  addition error.

Expected Condition C route:

- Use `dotProduct_error_bound`.
- Use `FPModel.model_add`.
- Bound the combined absolute error in terms of `|c|` and
  `sum |x_i| |y_i|`.

#### 3. Residual Stopping Certificate

Algorithm: compute the residual `r_hat = fl(b - A*x_hat)`.

The theorem should say that if the computed residual is small, then the exact
residual is small up to the residual-computation error bound.

Reason for selection:

- Residual stopping tests are central in numerical linear algebra.
- This is a stability-analysis result with direct algorithmic meaning.
- The task uses the library's residual computation theorem, but the target
  should be a certificate-style statement rather than an exact theorem lookup.

Expected Condition A difficulty:

- The agent must define residual computation, matvec error, and subtraction
  error from scratch.

Expected Condition C route:

- Use `fl_residual`.
- Use `conventional_residual_error`.
- Apply triangle inequality to transfer a bound on `|r_hat|` to a bound on the
  exact residual.

#### 4. Triangular Solve Residual Certificate

Algorithm: solve a triangular system by forward or back substitution.

The theorem should convert the triangular backward-error theorem into a
componentwise residual bound for the original triangular matrix.

Reason for selection:

- It checks whether the solver understands the meaning of backward error:
  `(T + DeltaT)x_hat = b` implies a residual bound for `T*x_hat - b`.
- It is not just applying `forwardSub_backward_error` or
  `backSub_backward_error`; the proof must unpack the perturbation and derive a
  residual inequality.

Expected Condition A difficulty:

- The triangular solve analysis is long and depends on subtraction-fold
  infrastructure.

Expected Condition C route:

- Use `forwardSub_backward_error` or `backSub_backward_error`.
- Rearrange the exact perturbed system.
- Bound the residual by `gamma * |T| * |x_hat|`.

#### 5. BLAS GEMV Stability

Algorithm: compute `alpha * A*x + beta * y` using a floating-point matvec,
rounded scalar multiplications, and rounded additions.

Reason for selection:

- GEMV is a canonical BLAS operation and a natural real-world benchmark.
- The library has matvec results, but not this full BLAS-style operation.
- The task forces the solver to combine rowwise matvec error with scalar
  operations and addition.

Expected Condition A difficulty:

- The agent must reconstruct matvec stability and then extend it.

Expected Condition C route:

- Use `matVec_error_bound` or `matVec_backward_error`.
- Use `FPModel.model_mul` and `FPModel.model_add`.
- Produce a componentwise forward-error bound with an explicit or absorbed
  gamma-style coefficient.

#### 6. Combined Triangular Solve As One Backward Error

Algorithm: solve `A x = b` with `A = L*U` by forward substitution followed by
back substitution.

The theorem should convert the library's two-factor result
`(L+DeltaL)(U+DeltaU)x_hat = b` into a single perturbation result for
`A + DeltaA`.

Reason for selection:

- It tests composition of two backward-error statements.
- It requires expanding matrix products and bounding
  `L*DeltaU + DeltaL*U + DeltaL*DeltaU`.
- It is a useful bridge between triangular solve analysis and LU solve
  analysis.

Expected Condition A difficulty:

- Reproving both triangular solve theorems is likely out of reach.

Expected Condition C route:

- Use `triangularSolve_backward_error`.
- Define `DeltaA`.
- Prove a bound of the form `(2*gamma + gamma^2) * |L||U|`.

#### 7. LU Solve With Growth-Scaled Backward Error

Algorithm: solve `A x = b` via computed LU factors.

The theorem should combine LU solve backward error with a growth hypothesis
`|L_hat| |U_hat| <= rho * |A|` to obtain a relative componentwise backward
error for `A`.

Reason for selection:

- This is a realistic stability-analysis step: convert a factor-product bound
  into a user-facing bound relative to the input matrix.
- It is harder than applying `lu_solve_backward_error` directly.

Expected Condition A difficulty:

- The full LU solve theorem and triangular infrastructure are missing.

Expected Condition C route:

- Use `lu_solve_backward_error`.
- Apply the growth hypothesis componentwise.
- Manage nonnegativity and scalar multiplication inequalities.

#### 8. Cholesky Solve With Growth-Scaled Backward Error

Algorithm: solve an SPD system via Cholesky factorization and triangular solves.

The theorem should convert the Cholesky solve bound involving
`|R_hat^T| |R_hat|` into a relative matrix perturbation bound under a
factor-product growth hypothesis.

Reason for selection:

- It parallels Task 7 but uses a different algorithmic path and a different
  constant structure.
- It tests whether the solver can transfer a known composition pattern to
  another factorization.

Expected Condition A difficulty:

- Requires Cholesky factorization contracts, triangular solves, and gamma
  absorption.

Expected Condition C route:

- Use `cholesky_solve_backward_error` or
  `cholesky_solve_backward_error_expanded`.
- Apply the factor-product growth hypothesis.

#### 9. One-Step Iterative Refinement

Algorithm: compute a conventional residual, approximately solve the correction
equation, and update the iterate once.

The theorem should prove a residual or backward-error bound for the updated
iterate from:

- conventional residual computation error;
- a backward-stable correction solve;
- the exact one-step refinement identity.

Reason for selection:

- Iterative refinement is a genuine compositional stability analysis.
- The proof requires coordinating several library contracts.
- It is a good second-to-last task because Condition A should lack too much
  infrastructure, while Condition C has a plausible path.

Expected Condition A difficulty:

- The agent must rebuild matvec residual analysis, solver backward error, and
  the one-step refinement algebra.

Expected Condition C route:

- Use `conventional_residual_error`.
- Use `one_step_residual_bound`,
  `solver_perturbation_to_residual`, or related iterative-refinement lemmas.
- Perform task-specific substitutions.

#### 10. Stationary Iteration With Inexact Triangular Local Solves

Algorithm: perform a stationary iteration step where the local solve with `M`
is carried out inexactly, for example by a triangular solve in a Jacobi,
Gauss-Seidel, or SOR-style splitting.

The theorem should connect the local solve error to a `ComputedIteration` or
local-error hypothesis and then prove a normwise forward-error or residual
bound after several iterations.

Reason for selection:

- This is the hardest task because it requires building the bridge from a
  concrete inexact local solve to the abstract stationary-iteration framework.
- It is still a stability-analysis task for an algorithm.
- It tests whether the library supports multi-level composition, not just local
  kernel reuse.

Expected Condition A difficulty:

- Very high.  The agent would need matrix norm infrastructure, splitting
  identities, residual recurrences, and triangular solve error analysis.

Expected Condition C route:

- Use triangular solve backward/residual bounds to justify local error.
- Instantiate `ComputedIteration` or `LocalErrorBound`.
- Use `normwise_forward_bound` or `normwise_residual_bound`.

### Rejected Or Revised Earlier Tasks

Some earlier generated task ideas should not be used as-is.

#### Symmetric Matrix-Vector Product

Problem: the current matvec theorem gives a rowwise perturbation.  It does not
provide a single symmetric perturbation `DeltaA` preserving
`y_hat = (A + DeltaA)x`.

Possible revised version: prove an ordinary matvec bound under the additional
assumption that `A` is symmetric, without requiring the perturbation to be
symmetric.  But that would not test a genuinely new stability phenomenon.

#### Unit Triangular Forward Substitution With Zero Diagonal Perturbation

Problem: the current `fl_forwardSub` algorithm performs divisions by the
diagonal.  Even if the diagonal entries are mathematically one, the current
model does not automatically say the corresponding division is exact.

Possible revised version: define a task-local unit-triangular algorithm that
skips diagonal division.  Then a zero-diagonal perturbation theorem may be
reasonable.

#### LDLT Solve

Problem: the existing indefinite Cholesky/LDLT area contains abstract
interfaces.  It can be made into a hard task, but only after the exact
algorithmic assumptions are stated carefully.

#### Old Block Triangular Solve

Problem: earlier traces suggested a block triangular task that only proved a
partial block residual.  That is too weak or misleading for a stability
benchmark.

Possible revised version: formulate a full residual/backward-error theorem for
the block solve.

### Contamination Policy

After exact theorem statements are chosen, perform contamination checks before
freezing the benchmark.

Search for:

- final theorem names;
- distinctive theorem statement fragments;
- uncommon combinations of constants and assumptions;
- task descriptions.

Do not claim that a task is uncontaminated until this check has been performed.
The current task ladder is designed to reduce contamination risk by using
task-local algorithm combinations rather than directly asking for textbook
theorems.

### Automation Plan

Each task should be generated in two solver workspaces:

- Condition A: isolated project containing Mathlib plus the bare definitions
  needed to state the theorem.
- Condition C: full library project containing public library documentation but
  excluding benchmark meta-notes and agent memory files.

The runner should:

- insert exactly one theorem with `sorry`;
- invoke the solver with a fixed prompt;
- prevent cross-condition file access;
- run `lake build`;
- reject solutions containing `sorry`, `admit`, new axioms, or weakened theorem
  statements;
- record pass/fail, proof length, diff size, build output, and remaining
  obligations.

Suggested metrics:

- pass@1;
- pass@5;
- best-attempt build status;
- remaining `sorry` count;
- lines changed;
- human edit distance to a reference proof, if reference proofs are created;
- qualitative failure reason.

### Decision: Separate Preflight Build From Post-Attempt Validation

A generated task should first be checked with `sorry` allowed.  This confirms
that the theorem statement, imports, and condition-specific environment are
coherent.  It does not count as solving the theorem.

After a solver attempt, validation is stricter: only the theorem proof body may
change, `lake build BenchmarkTask` must succeed, and the workspace must not
contain `sorry`, `admit`, new `axiom`, `opaque`, or `unsafe` declarations.

Reason: the benchmark needs both checks.  Preflight build catches bad task
statements before wasting solver runs.  Post-attempt validation catches invalid
or weakened solver outputs, including changes to imports, task-local
definitions, namespaces, or theorem statements.

Current scripts:

- `benchmark/scripts/prepare_solver_run.sh`
- `benchmark/scripts/run_codex_attempt.sh`
- `benchmark/scripts/validate_attempt.sh`

### Decision: Archive Solver Results Inside The Repository

Generated solver workspaces should remain outside the repository, normally
under `/tmp`, so the solver does not see benchmark design notes or previous
attempts.  However, the results of each attempt should be copied back to
`benchmark/results/<run-id>/<condition>/`.

Archived result material should include the solver prompt, final
`BenchmarkTask.lean`, diff against the canonical task, validation log, exit
codes, and metadata.  This prevents loss when temporary workspaces are cleaned
up while keeping solver-facing workspaces isolated.

### Decision: Use A Clean Dependency Copy, Not A Repo Symlink

For real runs, generated workspaces should not use symlinks into the project
repository's `.lake/packages`, because that creates a filesystem path back to
the source repository.

The current harness instead lets Condition A clone/build third-party Lake
packages, then copies that dependency package directory into Condition C before
the Condition C preflight.  This copies Mathlib and related third-party
dependencies only.  It does not copy `LeanFpAnalysis` from Condition C into
Condition A, and it does not copy benchmark notes, thesis notes, memory files,
or previous attempts into either solver workspace.

Reason: full no-cache builds are too slow for repeated runs, but repository
symlinks are a contamination risk.

### Decision: Run Solvers With An Auth-Only Temporary Codex Home

Solver attempts should not inherit Codex memories, prior sessions, project
rules, user configuration, or global plugins from the orchestration machine.

`benchmark/scripts/run_codex_attempt.sh` now creates a temporary `CODEX_HOME`
containing only `auth.json`, runs `codex exec` with ephemeral session storage,
`--ignore-user-config`, `--ignore-rules`, `--disable plugins`, and
`--disable memories`, then deletes the temporary home after the attempt.

Reason: `--ignore-user-config` alone still allowed the installed Codex CLI to
touch global plugin metadata.  The benchmark requires a fresh solver process
whose useful information comes from the generated workspace, the task prompt,
and, in Condition C, the library itself.

### Current Open Decisions

- Exact theorem statements for all ten tasks.
- Whether Task 10 should target forward error or residual error.
- Whether the Condition C solver workspace should be a filtered copy of the
  repository or a normal dependency project pointing to a library checkout.
- The final contamination-search protocol and log format.
