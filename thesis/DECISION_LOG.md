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

In concrete terms, there are two different kinds of theorem in the library:

- fully derived floating-point analyses, where the theorem starts from
  `FPModel`, algorithm definitions, and structural assumptions, then proves the
  error bound;
- abstract interfaces, where the theorem assumes a contract such as "this
  solver returns `xhat` satisfying `(A + DeltaA)xhat = b` with
  `|DeltaA| <= mu |A|`", then derives a consequence from that contract.

The second kind is still useful.  It lets later proofs be written against a
clean solver or factorization contract before every possible implementation of
that contract has been formalized.  But it is not the same achievement as
proving the contract from floating-point operations.

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

Each task should have explicit source material.  In practice this means:

- the algorithmic pattern should be traceable to a standard stability-analysis
  source, usually Higham's *Accuracy and Stability of Numerical Algorithms*;
- the bound should be justified by a named theorem chain in LeanFpAnalysis or
  by a documented local composition of such theorems;
- if the task introduces an extra assumption, such as a growth hypothesis, the
  assumption must be stated in the theorem and explained in the task notes.

The task-source record is `benchmark/tasks/TASK_DERIVATION.md`.

For the final task or final two tasks, the desired outcome is asymmetric:
Condition A should plausibly fail because it lacks the formal FP/gamma/matrix
infrastructure, while Condition C should have a plausible path through the
library.  It is acceptable to leave the actual solver outcome open.  What is not
acceptable is leaving the theorem truth open.  The theorem statement must be
grounded before the run by conservative assumptions and a clear library theorem
chain, even if no Codex-written proof is produced before evaluation.

### Proposed Task Ladder

The current benchmark suite is a sequence of ten tasks in increasing
composition depth.  It should not be described as empirically increasing
difficulty if the evidence is solver runtime, because elapsed time is not
monotone: a later task can be quick in Condition C when the right library
theorem is discovered early.  The intended ordering is a composition ladder:
early tasks compose one local theorem with one FP operation, while later tasks
compose multiple contracts or bridge concrete algorithms to abstract iterative
frameworks.

The solver-facing files are:

- `benchmark/tasks/T01_ScaledDot/Task.lean`
- `benchmark/tasks/T02_ShiftedDot/Task.lean`
- `benchmark/tasks/T03_ResidualCertificate/Task.lean`
- `benchmark/tasks/T04_ForwardSubResidual/Task.lean`
- `benchmark/tasks/T05_Gemv/Task.lean`
- `benchmark/tasks/T06_TriangularSolveSingle/Task.lean`
- `benchmark/tasks/T07_LUSolveGrowth/Task.lean`
- `benchmark/tasks/T08_CholeskySolveGrowth/Task.lean`
- `benchmark/tasks/T09_OneStepRefinement/Task.lean`
- `benchmark/tasks/T10_StationaryForwardSub/Task.lean`

The working task-spec source is `benchmark/tasks/TASK_SPECS.md`.  It is used to
develop exact theorem shapes before generating Condition A and Condition C
workspaces.  It is not solver-facing material and should not be copied into
generated benchmark runs.

The task-source and composition-depth record is
`benchmark/tasks/TASK_DERIVATION.md`.  It is also not solver-facing material.

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

All ten current task files have passed preflight builds with `sorry` allowed in
both Condition A and Condition C.  This establishes that the Lean statements
and generated environments are coherent enough to compile.  It does not
establish that the theorems have been proved, and it should not be reported as
a solver success.

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

- `benchmark/scripts/setup_shared_lake_packages.sh`
- `benchmark/scripts/setup_condition_c_snapshot.sh`
- `benchmark/scripts/prepare_solver_run.sh`
- `benchmark/scripts/run_task_once.sh`
- `benchmark/scripts/run_codex_attempt.sh`
- `benchmark/scripts/validate_attempt.sh`
- `benchmark/scripts/analyze_run.sh`
- `benchmark/scripts/archive_preflight_run.sh`
- `benchmark/scripts/cleanup_run_workspaces.sh`

### Decision: Use A Common Bare Stub For Condition A

Condition A now has a default stub module at
`benchmark/stubs/common/LeanFpAnalysis/FP.lean`.  A task may still receive a
task-specific stub later if its statement needs a narrower surface, but the
common stub is the default.

Reason: the benchmark has ten tasks sharing the same public import
`LeanFpAnalysis.FP`.  Maintaining ten nearly identical stubs would be noisy and
would create unnecessary opportunities for accidental differences between
tasks.  A common stub keeps Condition A consistent: it exposes only bare
definitions and abstract contracts needed for the theorem statements to parse,
without proved stability theorems, gamma calculus, lookup documentation, or
examples.

Consequence: Condition A can define the same theorem targets as Condition C,
but it should not have the reusable proof infrastructure that the thesis is
trying to evaluate.

### Decision: Bare Stubs Must Use Faithful Definitions

Condition A stubs may omit proved stability theorems, gamma-calculus lemmas,
lookup documentation, and examples.  They should not replace real definitions
with degenerate placeholders when those definitions appear in the theorem
target.

This was discovered during the first pass@1 run on May 5, 2026.  The initial
common stub defined `infNormVec` and `infNorm` as `0`.  That allowed
Condition A to prove Task 10 by `simp [infNormVec, infNorm]`, making the
control theorem trivial.  That result was invalid as a benchmark datapoint.

The stub was corrected so `infNormVec` and `infNorm` use the same finite
supremum definitions as the public library.  Task 10 was then rerun.  Under
the corrected stub, Condition A failed and Condition C passed.

A second stub issue was found in the same audit.  The initial common stub
defined `fl_forwardSub` and `fl_backSub` as zero-valued placeholders, while
Tasks 4, 6, 7, 8, and 10 mention those algorithms in their theorem targets.
That changed the meaning of the control condition.  The stub now copies the
same fold-based algorithm definitions from the public library, while still
omitting the associated stability theorems.  The affected tasks were rerun
under this audited stub.

Reason: the benchmark should remove reusable proof infrastructure from
Condition A, not change the mathematical meaning of the task.  A bare
definition is acceptable; a degenerate replacement that weakens the theorem is
not.

The current audit is recorded in
`benchmark/stubs/CONDITION_A_STUB_AUDIT.md`.

### Decision: Reject Lean Placeholder Escape Hatches

Post-attempt validation rejects `sorry`, `admit`, `sorryAx`, and new
`axiom`/`opaque`/`unsafe` declarations.

Reason: a first T07 rerun produced `exact sorryAx _ true` in Condition A.  This
is semantically the same problem as leaving a `sorry`: Lean accepts the file,
but the theorem has not actually been proved.  The validator and run analyzer
now treat `sorryAx` as a forbidden placeholder, and T07 was rerun with that
rule in place.

### Decision: Condition C Keeps The Whole Public Library

Condition C should not import or expose only task-specific modules.  The goal
is to test whether a fresh solver can discover and use the library as a whole,
as a user would after loading the project for the first time.

The task file remains neutral and contains no task-specific proof guidance.
Condition C receives access to the full public library, README, docs, and
examples through a shared read-only snapshot.  Each solver attempt still runs
in a fresh task workspace containing only the task file, prompt, Lake config,
and symlinks/dependency paths to the snapshot.  It does not receive benchmark
meta-notes, thesis notes, memory files, previous attempts, or solution
sketches.

Reason: narrowing imports per task would turn the benchmark into a directed
lemma-lookup exercise.  The intended measurement is broader: whether the
library is organized and documented well enough for the solver to find the
right concepts without private help.  A shared snapshot avoids recopying and
rebuilding the library for every attempt while preventing one run from building
on edits made by a previous run.

### Decision: Archive Solver Results Inside The Repository

Generated solver workspaces should remain outside the repository, normally
under `/tmp`, so the solver does not see benchmark design notes or previous
attempts.  However, the results of each attempt should be copied back to
`benchmark/results/<task>/<timestamp>/<condition>/`.

Archived result material should include the solver prompt, final
`BenchmarkTask.lean`, diff against the canonical task, validation log, exit
codes, and metadata.  This prevents loss when temporary workspaces are cleaned
up while keeping solver-facing workspaces isolated.  Results are grouped by
task first so repeated attempts for one task can be compared without mixing
them with other benchmark exercises.

### Decision: Use A Shared Third-Party Lake Package Cache

Generated benchmark workspaces should not reclone or rebuild Mathlib for every
run.  They also should not use symlinks into the project repository's
`.lake/packages`, because that creates a filesystem path back to the source
repository.

The current harness keeps third-party Lake packages in a shared cache under
`~/.cache/lean-fp-analysis/lake-packages/...`.  The repository's
`.lake/packages` and generated benchmark workspaces point to that cache.

The shared Lake package cache contains Mathlib and related third-party
dependencies only.  It does not contain `LeanFpAnalysis` source, benchmark
notes, thesis notes, memory files, previous attempts, or task solutions.
Condition A still receives only the generated stubs plus the byte-identical
task file.  Condition C receives a dependency path and inspection symlinks to a
separate shared read-only `LeanFpAnalysis` snapshot.

Reason: full no-cache builds are too slow and disk-heavy for repeated runs.
The benchmark needs fresh solver memory and isolated task workspaces, not a
fresh clone of public third-party dependencies for every attempt.

### Decision: Run Expensive Benchmark Infrastructure In The Cloud

The first build of the shared Condition C snapshot compiles the whole public
library and is too CPU/RAM-heavy to run repeatedly on the laptop used for
writing.  Expensive benchmark infrastructure should therefore run on a cloud
runner.

The repository now has a manual GitHub Actions workflow for benchmark
preflight: it checks out the branch, prepares the shared Lake package cache,
builds or restores the Condition C snapshot, generates fresh task workspaces,
runs preflight builds for both conditions, archives metadata, and uploads the
archive as an artifact.

Reason: GitHub Actions gives reproducible logs and downloadable artifacts
without consuming local laptop resources.  Solver attempts are not added to
this workflow yet because Codex authentication on a non-local runner must be
chosen explicitly; the workflow currently covers the heavy Lean/snapshot side
of the benchmark.

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

### Decision: Use An Explicit Solver Timeout

Solver attempts should have a fixed wall-clock timeout.  The current harness
uses `BENCHMARK_CODEX_TIMEOUT_SECONDS`, defaulting to 1200 seconds, and
archives a timeout marker when the Codex process is stopped.

Reason: benchmark runs must be reproducible and bounded.  Open-ended attempts
make results hard to compare and can waste compute time even when disk usage is
controlled.

The timeout was increased from 900 seconds to 1200 seconds because a
20-minute attempt is a better compromise for this benchmark: short enough to
run repeated trials, but long enough that Condition C has time to inspect the
large library and attempt a genuine proof rather than failing due to navigation
latency.

### Decision: Produce An Analysis After Every Run

Each official run should produce `RUN_ANALYSIS.md` and `metrics.tsv` in the
archived result directory.

Reason: raw Codex logs, Lean logs, diffs, and validation files are necessary
for auditability but are too scattered for thesis analysis.  A compact analysis
file makes every run immediately interpretable while preserving the raw
artifacts for later inspection.

The metrics currently recorded per condition are:

- Codex exit code;
- validation exit code;
- timeout marker;
- start and finish timestamps;
- Codex event-log line count;
- diff line count;
- proof-line count;
- remaining placeholder count;
- forbidden declaration count.

The analysis also records a mechanical validation classification, such as
"proof placeholder remained", "task interface changed", or "final Lean file did
not build".

These metrics are deliberately mechanical.  They do not replace human
classification of failure modes, but they make it easier to compare runs and to
identify cases where a condition timed out, left placeholders, changed too much
code, or failed validation despite Codex exiting normally.

### Decision: Audit Condition A Failures, Not Just Pass/Fail

Condition A failures should be auditable from the archived artifacts.  The
harness saves the final `BenchmarkTask.after.lean`, diff, validation log,
solver event log, extracted public solver messages, final solver message,
metadata, `RUN_ANALYSIS.md`, and `metrics.tsv` for every task and condition.

Reason: the thesis claim should not rest on a closed-minded rejection rule.
If Condition A fails, we need to know whether it left `sorry`, used a forbidden
escape hatch, changed the theorem, or attempted a proof that Lean rejected.

The extracted public solver messages are saved as audit context, not as hidden
chain-of-thought.  They can show, for example, that the solver identified a
missing residual-error lemma or tried a natural perturbation witness, but the
formal result is still determined by the archived Lean artifact and validator.

The corrected 2026-05-05 pass@1 run has a separate failure audit at
`benchmark/results/CONDITION_A_FAILURE_AUDIT_20260505.md`.  Its conclusion is
that the Condition A attempts are valid pass@1 failures under the protocol, but
not proof that Condition A is impossible in principle.  Repeated attempts,
larger timeouts, or different prompts remain separate measurements.

### Decision: Require Exact Source Anchors For Benchmark Bounds

Every benchmark task must identify the exact source of its target bound.  A
valid source record must include both the external numerical-analysis anchor
such as a Higham theorem, equation, algorithm, or BLAS operation, and the
LeanFpAnalysis definitions/theorems that formally justify the exact task
statement.

Reason: "stability analysis task inspired by Higham" is too vague for thesis
work.  The target theorem includes a specific bound, so the benchmark must say
where that bound comes from and which local theorem chain supports it.

Consequence: tasks may be derived compositions rather than verbatim textbook
theorems, but this must be documented honestly.  The source document
`benchmark/tasks/TASK_DERIVATION.md` now distinguishes textbook anchors,
formal Lean anchors, and task-local composition steps for every task.

### Decision: Treat The Current Task Set As Prototype, Not Final Evidence

The current ten benchmark tasks are too Higham-centered.  Since
LeanFpAnalysis formalizes a large amount of Higham-style floating-point
stability analysis, a successful Condition C run on those tasks may partly
measure access to a formalized version of the same source material.

Reason: the thesis benchmark should test whether the library helps an agent
perform stability analysis on algorithms and contracts that are not merely
restatements of the book the library follows most closely.

Consequence: the existing pass@1 results are retained as harness diagnostics:
they validate workspace isolation, artifact capture, and the broad Condition
A/C gap mechanism.  They should not be presented as the final benchmark claim.
The final task set must use a diversified source mix, recorded in
`benchmark/tasks/TASK_SOURCE_STRATEGY.md`, with substantial non-Higham sources
such as LAPACK error-bound documentation, Netlib Templates stopping criteria,
Wilkinson-style growth-factor analysis, fast-matrix-multiplication stability
papers, and least-squares references.

The external-source survey is tracked in
`benchmark/tasks/EXTERNAL_STABILITY_SOURCE_SURVEY.md`.  It distinguishes
algorithm/API sources, such as BLAS `DGEMV`, from actual stability-bound
sources.  This prevents using an external algorithm name while silently deriving
the bound from Higham-only material.

### Decision: Keep Benchmark-Specific Algorithms Inline

Paper-derived benchmark tasks should not be supported by adding
task-specific algorithm definitions or source-bound predicates to the public
library immediately before evaluation.

Reason: if the public library contains exactly the paper-specific definitions
needed by a benchmark task, Condition C may be helped by benchmark scaffolding
rather than by the reusable floating-point stability library.  The task file is
the artifact copied byte-identically into both Condition A and Condition C, so
task-local algorithms should live there unless they are genuine permanent
library features.

Consequence: definitions such as compensated `TwoSum`/`TwoProduct`, `SumK`,
`DotK`, and DDHK paper-specific coefficients should be inlined in the relevant
solver-facing task file.  The public library should provide reusable
infrastructure, such as `FPModel`, `gamma`, matrix algebra, residual theory,
summation/dot-product primitives, and perturbation theory.

### Decision: Benchmark Tasks Must Be Stability Proofs

The final benchmark should contain only tasks whose conclusion is a stability
bound for an algorithm: forward error, backward error, residual error, or a
certified conversion between these notions for a computed quantity.

Reason: proving a corollary from a hypothesis that already states the source
error bound is too weak for this benchmark.  It may be mathematically useful,
but it does not test whether the agent can perform automatic stability
analysis.

Consequence: candidate tasks that merely assume the paper's final absolute
bound and derive a relative-error restatement are not accepted as final tasks.
Acceptable extra assumptions are structural or model assumptions that the
library deliberately does not provide, such as no-underflow hypotheses or
error-free transformation contracts, provided the theorem still proves the
algorithm's error bound rather than assuming it.

The first stability-only pilot is
`benchmark/tasks/E01_LapackBerrBackward/Task.lean`.  It uses a LAPACK/Oettli-
Prager style residual certificate: if the computed residual is small enough
after accounting for floating-point residual-computation error, then the
approximate vector is an exact solution of a componentwise perturbed linear
system.

Two additional stability-only pilots were added:

- `benchmark/tasks/E02_TemplatesResidualStop/Task.lean`, a Netlib Templates
  residual-stopping criterion proving a forward-error bound.
- `benchmark/tasks/E03_LapackFerrForward/Task.lean`, a LAPACK `FERR`-style
  forward-error certificate from the computed residual plus residual-rounding
  allowance.

Seven more external-source pilot tasks were then added to cover matrix
multiplication, triangular solves, least squares, stationary iterations, and a
paper-derived compensated summation certificate:

- `benchmark/tasks/E04_LapackLevel3Matmul/Task.lean`, a LAPACK Level 3
  BLAS-style normwise forward-error bound for matrix multiplication.
- `benchmark/tasks/E05_LapackTriangularResidual/Task.lean`, a LAPACK Level 3
  BLAS-style residual bound for triangular solve.
- `benchmark/tasks/E06_OettliPragerForward/Task.lean`, a componentwise
  backward-to-forward error conversion based on Oettli-Prager/LAPACK
  componentwise conditioning.
- `benchmark/tasks/E07_TemplatesStationaryResidual/Task.lean`, a Netlib
  Templates-style residual bound for inexact stationary iteration.
- `benchmark/tasks/E08_LapackLSQRForward/Task.lean`, a QR least-squares
  perturbation certificate converted into a forward-error bound.
- `benchmark/tasks/E09_LapackNormalEquations/Task.lean`, a normal-equations
  perturbation certificate converted into a forward-error bound.
- `benchmark/tasks/E10_OgitaSumKCertificate/Task.lean`, an
  Ogita-Rump-Oishi `SumK` certificate proving an absolute error bound from
  sourced distillation assumptions.

This E01-E10 set is a source-backed pilot set, not yet a frozen thesis
benchmark.  E08-E10 are intentionally documented as specification-transfer or
certificate-level tasks because the public library does not currently
formalize full rectangular QR, IEEE error-free transformations, or the full
paper algorithms from raw `FPModel`.

The derivation record for these external-source tasks is
`benchmark/tasks/EXTERNAL_TASK_DERIVATION.md`.

An initial contamination screen is tracked in
`benchmark/tasks/CONTAMINATION_CHECKS.md`.  It records exact-name searches for
the E01-E10 theorem names and task-local definitions.  This is a development
screen, not a final thesis audit; official runs still require a final
contamination check after theorem names and prompts are frozen.

The theorem-truth audit is tracked in
`benchmark/tasks/THEOREM_TRUTH_AUDIT.md`.  It records which E01-E10 statements
are supported by existing library theorem chains, which are too direct as
benchmark tasks, and which are certificate-level rather than full algorithm
analyses.

Current audit conclusion after revising E07 and E08:

- E01-E09 are suitable serious candidates.
- E07 now requires a bridge from a task-local stationary-iteration local-error
  definition to the library's abstract `ComputedIteration` contract.
- E08 now requires unpacking a QR least-squares backward-error certificate
  before applying the forward-error infrastructure, but it remains a
  specification-transfer theorem rather than a full rectangular QR algorithm
  proof.
- E10 is a valid certificate-level paper task, but not a full formalization of
  Ogita-Rump-Oishi `SumK` from raw floating-point operations.

The external-source suite file is
`benchmark/suites/external_stability.tsv`.  It is used by plotting/reporting
tools to avoid hardcoding the old prototype `T01`-`T10` task list.  The
plotting script now accepts `--task-list` and can therefore plot either the
prototype suite or the external-source suite without changing source code.

A generated-workspace preflight was run for `E01_LapackBerrBackward` after the
suite/script changes.  Both Condition A and Condition C built
`BenchmarkTask` with `sorry` allowed, confirming that the actual harness path
works for the new external task naming scheme.  No Codex solver attempt was
run in this preflight.

The first controlled external-source solver run was then executed for
`E01_LapackBerrBackward` with a 1200-second timeout per condition.  Condition A
failed validation without timing out and left the original `sorry`.  Its public
solver messages identified the missing residual-error theorem for
`fl_residual` as the blocker.  Condition C passed validation using
`conventional_residual_error` and `oettli_prager_sufficient`.  The run is
recorded in `benchmark/results/EXTERNAL_PILOT_20260507.md`.

An E02 pilot run also separated the conditions qualitatively: Condition A left
`sorry` and Condition C passed.  However, it exposed a timeout-enforcement
problem.  Condition A recorded `timeout_seconds = 1200` but ran much longer
than 1200 seconds and did not produce `timeout.txt`.  This E02 result should
not be treated as an official timing-valid datapoint.

The runner was updated to use `benchmark/scripts/run_with_timeout.py`, a
Python process-group timeout wrapper.  It starts the solver in a new process
group, writes a timeout marker, sends `SIGTERM`, and escalates to `SIGKILL`
after a grace period.  A local test confirmed that a command sleeping for
5 seconds is terminated after a 1-second timeout with exit code 124.

E02 was rerun after the timeout fix.  The timing-valid rerun is
`benchmark/results/E02_TemplatesResidualStop/20260507-201754`: Condition A
failed validation in about 5.5 minutes with the original `sorry` still present,
while Condition C passed validation in about 4.5 minutes.  This is now the E02
pilot datapoint to cite; the earlier E02 run remains only as evidence for the
timeout bug and the qualitative failure mode.

E03 was then run with the fixed timeout wrapper:
`benchmark/results/E03_LapackFerrForward/20260507-202911`.  Condition A failed
validation without timing out and left `sorry`; its public messages again
identified the missing floating residual error lemma as the blocker.  Condition
C passed validation by using the residual-error and forward-error
infrastructure plus norm/supremum reasoning.

E04 was run next:
`benchmark/results/E04_LapackLevel3Matmul/20260507-204055`.  Condition A failed
validation without timing out and left the original `sorry`.  Its public
messages identified the missing dot-product/matrix-multiplication error theorem
as the blocker.  Condition C passed validation by using the library theorem
`matMul_error_bound`, then proving the rectangular infinity-norm row-sum bound
locally inside the task file.  This is an important pilot datapoint because it
shows the A/C gap is not limited to residual-certificate tasks.

E05 was then run:
`benchmark/results/E05_LapackTriangularResidual/20260507-205025`.  Condition A
failed validation without timing out, while Condition C passed.  However, this
run exposed an isolation weakness.  The Condition A attempted proof called
`backSub_backward_error`, which is correctly unavailable from the Condition A
stub and was rejected by validation.  The public solver messages say the solver
had discovered a compiled companion library in a local cache and manually
tested with an extra search path.  Therefore this E05 attempt is useful as a
harness diagnostic but should not be cited as an isolation-clean datapoint.

The harness was hardened in response.  The neutral solver prompt now explicitly
treats the current workspace as the whole benchmark environment, forbids
inspection of the original repository, user home directories, global caches,
previous results, and manually discovered external paths, and forbids manual
`LEAN_PATH` or `--root` additions.  `benchmark/scripts/run_codex_attempt.sh`
also now runs Codex with a temporary `HOME` and `XDG_CACHE_HOME`, in addition
to the existing temporary auth-only `CODEX_HOME`.  The first hardened rerun
showed that this prevented the earlier Condition A cache-theorem attempt, but
it also made solver-side `lake build` try to fetch dependencies because the
build sandbox could not use the shared Lake package cache cleanly.  The runner
was therefore updated again to add only the shared third-party Lake package
cache as a Codex `--add-dir`.  That cache contains Mathlib-style dependencies,
not the full `LeanFpAnalysis` snapshot, so it should support solver-side builds
without giving Condition A the library being benchmarked.  This does not by
itself prove OS-level noninterference, but it removes the obvious
cache-discovery path and makes future Condition A runs cleaner.

A further cause of the solver-side build artifact was identified: setting
`HOME` to a temporary directory also made Elan search for the Lean toolchain in
that temporary home, so `lean` and `lake` attempted to download the toolchain
from GitHub.  The runner now passes the host `ELAN_HOME` explicitly while still
keeping `HOME` and `XDG_CACHE_HOME` temporary.  This exposes the installed Lean
toolchain, not benchmark memory or the FP library.

E05 was rerun after the prompt and `ELAN_HOME` fixes:
`benchmark/results/E05_LapackTriangularResidual/20260507-214953`.  This is the
E05 datapoint to cite.  Condition A failed validation without timing out and
left the original `sorry`; its public messages stayed within the local stub and
reported that no triangular-solve residual theorem was available.  Condition C
passed validation by finding `backSub_backward_error`, rewriting the residual
as a perturbation matrix-vector product, and using `infNormVec_matMulVec_le`.
The only remaining nuisance is that solver-side `lake build BenchmarkTask`
still reports an external Mathlib lock-file sandbox error.  The post-run
validator then builds the archived final file successfully, so validation
remains the authoritative pass/fail check.

E06 was run next:
`benchmark/results/E06_OettliPragerForward/20260507-215812`.  Both conditions
failed validation.  This is not evidence that the theorem is false: the theorem
truth route is still `componentwise_forward_error_standard` after unpacking
the task-local `opBackwardCompatible` hypothesis.  The Condition C attempt
instead wrote a large local finite-sum proof and failed on Lean details.  The
failure exposed a public-documentation gap: `docs/LIBRARY_LOOKUP.md` listed
`componentwise_forward_error` but not the standard specialization
`componentwise_forward_error_standard`, even though this is the theorem users
need for the common `|DeltaA| <= eps*|A|`, `|Deltab| <= eps*|b|` form.  The
lookup table and `examples/LibraryLookup.lean` were updated to include
`componentwise_forward_error_standard` and `normwise_perturbation_bound`.

E06 was rerun after rebuilding the Condition C snapshot with the updated
lookup table:
`benchmark/results/E06_OettliPragerForward/20260507-220547`.  Both conditions
still failed validation.  Condition C again wrote a local finite-sum proof and
failed on Lean details instead of applying
`componentwise_forward_error_standard`.  This is an important benchmark design
signal: merely listing the theorem name was not enough for Codex to use it in
this task.  E06 should either be placed later in the difficulty ordering, or
the public library guide should gain a general perturbation-transfer pattern
section that explains how to use specification-transfer theorems without
mentioning benchmark tasks.

E07 was run next:
`benchmark/results/E07_TemplatesStationaryResidual/20260507-221510`.  Both
conditions passed.  Condition A produced a long local derivation of the
stationary residual recurrence and scalar contraction from the task-visible
definitions.  Condition C produced a much shorter proof by constructing the
`ComputedIteration` bridge and applying `normwise_residual_bound`.  This means
E07 is not a good pass/fail separation task in its current form.  It may still
serve as an efficiency-gap example, but if the benchmark's criterion is
"Condition A fails, Condition C succeeds", E07 should be redesigned or replaced.

E08 was then run:
`benchmark/results/E08_LapackLSQRForward/20260507-222525`.  Condition A failed
validation after attempting a long local least-squares perturbation proof.
Condition C passed validation with a short proof: it extracted `DeltaG` and
`Deltag` from `LSQRSolveBackwardError` and applied `ls_qr_forward_error`.  This
is a clean pass/fail separation, with the caveat already recorded in the task
audit that E08 is a specification-transfer certificate rather than a full QR
algorithm analysis from raw floating-point operations.

E09 was run next:
`benchmark/results/E09_LapackNormalEquations/20260507-223046`.  Both
conditions failed validation.  Condition A attempted to rebuild a local
normal-equations perturbation proof and failed on ordinary Lean details.
Condition C found the intended public theorem,
`ls_normal_equations_forward_error`, but failed on a small finite-sum
normalization step in the wrapper inequality.  This should be read as an
informative C failure, not as a false-theorem signal.  It also makes the
remaining solver-side Lake lock-file artifact more important: the validator
reached and archived the true Lean error, but the solver itself reported that
its `lake build BenchmarkTask` command was blocked before useful compiler
feedback by an external Mathlib lock-file write.  Fixing that solver-feedback
artifact is now a benchmark-harness priority before drawing strong conclusions
from C failures.

The solver-side Lake lock-file artifact was diagnosed after E09.  The
generated workspaces symlink `.lake/packages` to a shared package cache under
`~/.cache`; Codex can read enough of that cache to use prebuilt dependencies,
but its workspace sandbox cannot write through that external symlink to
Lake's package-configuration lock files.  Granting the shared cache with
`--add-dir` was not sufficient on this machine.  The chosen fix is a
workspace-local `lake` wrapper installed by `run_codex_attempt.sh` and placed
first on `PATH` only for the solver process.  For the benchmark-required
command `lake build BenchmarkTask`, the wrapper invokes `lean` directly using
the `LEAN_PATH` computed by the real Lake preflight.  This gives the solver
actual Lean elaboration errors for the task file while keeping post-run
validation authoritative: `validate_attempt.sh` still runs the real Lake build
outside the solver sandbox.  This is a harness fix, not solver guidance about
how to prove any task.

E10 was run after the solver-side Lake wrapper fix:
`benchmark/results/E10_OgitaSumKCertificate/20260507-224508`.  Both conditions
passed quickly.  This is an important negative task-design result.  Although
E10 is sourced from a real compensated-summation stability-certificate
pattern, the theorem as stated exposes the hard numerical-analysis facts as
task-local certificate assumptions.  The proof left to the solver is mostly
real arithmetic: use the final-rounding assumption, use the stage bound at
`K - 2`, and combine powers/nonnegativity.  Condition A can do that without
the library.  Therefore E10 should not be used as the final hard
library-separation task in its current form.  It may remain as a
certificate-arithmetic sanity check, but a replacement final task should force
the solver to derive or compose a stability bound from library contracts that
are absent in Condition A.

The May 7 external-suite pilot plots were generated at
`benchmark/results/plots/pass_at_1_20260507_external/`.  Using the latest run
for each E01-E10 task on that date, the pass/fail pattern is:

- A-fail/C-pass: E01, E02, E03, E04, E05, E08.
- both fail: E06, E09.
- both pass: E07, E10.

Decision consequence: the external-source suite is a successful pilot of the
harness and task-sourcing method, but not a frozen thesis benchmark.  The
final benchmark should keep or adapt the clean separation tasks, redesign or
replace E07 and E10, and decide whether E06/E09 need better public
perturbation-transfer guidance or should be replaced by tasks whose Condition
C route is more discoverable.

### Decision: Add A Separate Persistence Prompt Benchmark

The May 7 pass@1 runs remain valid standard-prompt evidence.  They show what
Codex did when asked normally to prove the theorem and rejected by validation
if it left `sorry` or produced a non-building proof.  A Condition A attempt
that stops with `sorry` should be interpreted as "the standard prompt did not
make the model persist to a proof", not as a mathematical impossibility
result.

A separate persistence experiment is now allowed through
`BENCHMARK_SOLVER_PROMPT_VARIANT=persistent`.  This prompt explicitly tells the
solver not to stop after one failed proof route, to keep running
`lake build BenchmarkTask`, and to continue revising until the external
timeout or a local build success.

Reason: this tests a different question from the original pass@1 benchmark.
The standard benchmark asks whether the library helps under an ordinary
one-shot proof prompt.  The persistence benchmark asks whether extra pressure
and more wall-clock time let Condition A overcome the absence of the library.

Consequence: persistent-prompt runs must be archived separately and should not
replace or invalidate standard-prompt runs.  The prompt variant is recorded in
run metadata and attempt metadata.

The first persistent-prompt pilot was run on E01:
`benchmark/results/E01_LapackBerrBackward_persistent/20260508-014020`.
The timeout was increased to 3600 seconds per condition.  Condition A still
failed and Condition C passed.  The important difference is the failure mode:
Condition A no longer left the original `sorry`; it produced a long
constructive perturbation proof and failed at the exact residual-rounding
estimate that the bare Condition A stub does not provide.  This supports a
two-benchmark story: standard prompting tests ordinary one-shot use, while
persistent prompting tests whether pressure and more time let Condition A
reconstruct missing stability infrastructure.  For E01, the answer was still
no, although the model did useful additional work before failing.

### Decision: Pin Model And Effort For Persistent Runs

The earlier benchmark harness used `codex exec` with `--ignore-user-config`,
but did not pass an explicit model or reasoning effort.  That makes the runs
useful as pilots but not precise enough for thesis-quality reproduction.

The runner now accepts:

- `BENCHMARK_CODEX_MODEL`;
- `BENCHMARK_CODEX_REASONING_EFFORT`.

The current stronger persistence protocol is:

- `BENCHMARK_CODEX_MODEL=gpt-5.5`;
- `BENCHMARK_CODEX_REASONING_EFFORT=xhigh`;
- `BENCHMARK_SOLVER_PROMPT_VARIANT=persistent`;
- `BENCHMARK_CODEX_TIMEOUT_SECONDS=1200`.

Reason: if the thesis compares conditions A and C, the solver identity and
reasoning budget must be part of the experimental treatment, not an implicit
desktop-app default.

Consequence: every official run must record the model and effort in both run
metadata and attempt metadata.  Unpinned earlier runs should be described as
pilots unless they are rerun under pinned settings.

Two pinned GPT-5.5 xhigh persistent runs were performed:

- E01:
  `benchmark/results/E01_LapackBerrBackward_gpt55_xhigh_persistent/20260508-021347`.
- E06:
  `benchmark/results/E06_OettliPragerForward_gpt55_xhigh_persistent/20260508-024006`.

E01 is a clean separation result under the stronger protocol: Condition A
timed out after 1200 seconds with the original `sorry` still present, while
Condition C passed in about five minutes.

E06 is not a clean separation task under the stronger protocol: both
conditions passed.  Condition C used the library theorem
`componentwise_forward_error_standard` in a very short proof, while Condition
A rederived the Oettli-Prager finite-sum algebra directly.  This is evidence
that E06 is too abstract and self-contained to serve as a hard
library-necessity task for GPT-5.5 xhigh persistence, even though it remains a
valid stability theorem.

The full E01-E10 external suite was then rerun with a 40-minute timeout per
condition under the pinned GPT-5.5 xhigh persistent protocol:
`benchmark/results/PERSISTENT40_XHIGH_SUITE_20260508.md`.

Result: all ten tasks passed in both Condition A and Condition C.  This is a
major benchmark-design finding.  The current E-suite does not separate the
conditions by pass/fail once the solver is given GPT-5.5 xhigh, persistent
instructions, and 40 minutes per condition.

However, the run still shows an efficiency gap.  Across E01-E10, Condition A
used 155.84 total solver minutes, while Condition C used 25.71.  Condition A
averaged 254.4 proof-body lines, while Condition C averaged 47.5.

Consequence: the current external-source tasks are valid stability tasks, but
they are not hard enough for the intended final pass/fail benchmark under the
strong persistent protocol.  They can support an efficiency-gap story, but the
final benchmark needs harder tasks whose theorem statements do not expose the
key numerical-analysis facts as local assumptions and whose Condition C proofs
must compose nontrivial library stability contracts unavailable to Condition A.

### Current Open Decisions

- The final contamination-search protocol and publication-grade audit.
- Number of repeated attempts per task and per condition.
- Whether to add hidden reference proofs after the first solver evaluation
  round for diagnostic purposes.
