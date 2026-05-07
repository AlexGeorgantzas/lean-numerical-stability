# Benchmark Task Source Strategy

Draft status: benchmark-design material. Do not copy this file into generated
solver workspaces.

## Problem

The current ten-task benchmark set is too Higham-centered. Since
LeanFpAnalysis formalizes a large amount of Higham-style floating-point
stability infrastructure, a pass/fail gap on tasks sourced mainly from Higham
is useful as a harness check, but it is not strong evidence that the library
helps an agent transfer stability-analysis knowledge to new material.

The current results should therefore be described as prototype diagnostics, not
as final thesis evidence.

## Final Source-Mix Rule

The final ten-task benchmark should satisfy all of the following:

- At most four tasks may have Higham's book as the primary stability source.
- At least five tasks must have a primary non-Higham stability source.
- At least two tasks should be grounded in software specifications or software
  accuracy documentation, such as BLAS, LAPACK, or Netlib Templates.
- At least two tasks should come from papers or books other than Higham's book.
- A task may use LeanFpAnalysis theorems in its proof, but the source record
  must distinguish:
  - external algorithm source;
  - external stability/bound source, if present;
  - Lean theorem chain used to prove the exact formal statement.
- If the external source specifies only the algorithm and the bound is derived
  from LeanFpAnalysis infrastructure, the task must be labelled
  "externally specified algorithm, library-derived bound."

This distinction matters because an externally specified algorithm alone is not
enough to avoid Higham leakage if the stability bound is still copied from a
formalized Higham theorem.

## Acceptance Criteria For Each Task

Before a task becomes part of the final benchmark, its derivation record must
answer these questions:

- What exact algorithm is analyzed?
- Where is that algorithm specified?
- What exact stability claim or bound is the task asking the solver to prove?
- Where does that bound come from?
- Which Lean definitions and theorems make the formal statement true?
- Is the theorem a direct wrapper around an existing Lean theorem, or does it
  require task-local composition?
- What contamination search was performed for this exact theorem shape?

Final benchmark tasks must be stability proofs.  The conclusion should be a
forward-error, backward-error, residual-error, or stability-conversion bound for
an algorithm or computed certificate.  A theorem that assumes the source's final
error bound and merely restates it is not a final benchmark task.

Task-specific algorithm definitions should be in the solver-facing task file
itself.  This keeps the algorithm identical in Condition A and Condition C and
prevents the public library from becoming benchmark-specific scaffolding.

The external-source pilot derivations are tracked in
`benchmark/tasks/EXTERNAL_TASK_DERIVATION.md`.

## Current External Pilot Set

The current source-backed pilot set is E01-E10:

| Task | Primary source family | Stability target | Status |
| --- | --- | --- | --- |
| E01 | LAPACK linear-solve `BERR`; Oettli-Prager compatibility | Componentwise backward perturbation from a computed residual certificate | Good near-term task. |
| E02 | Netlib Templates stopping criteria | Forward-error guarantee from a residual stopping test | Good near-term task. |
| E03 | LAPACK linear-solve `FERR` | Forward-error certificate from computed residual plus residual rounding allowance | Good near-term task. |
| E04 | LAPACK fast Level 3 BLAS | Normwise matrix-product forward-error bound | Gamma-version of the LAPACK first-order contract. |
| E05 | LAPACK fast Level 3 BLAS | Normwise triangular-solve residual bound | Gamma-version of the LAPACK first-order contract. |
| E06 | Oettli-Prager; LAPACK componentwise conditioning | Forward-error consequence of componentwise backward compatibility | Good stability-conversion task. |
| E07 | Netlib Templates stationary methods/stopping criteria | Residual bound for inexact stationary iteration | Good residual-stability task; source is less formula-specific than E01-E05. |
| E08 | LAPACK/Björck least squares | Forward-error consequence of a QR least-squares perturbation certificate | Abstract/specification-transfer task. |
| E09 | LAPACK least-squares normal-equations discussion | Forward-error consequence of perturbed normal equations | Abstract/specification-transfer task. |
| E10 | Ogita-Rump-Oishi `SumK` | Absolute error bound from a compensated-summation distillation certificate | Hard paper-derived certificate task. |

This set is intended for statement design and harness experimentation.  Before
official thesis runs, each task still needs a final contamination-search
record.  The current theorem-truth audit is tracked in
`benchmark/tasks/THEOREM_TRUTH_AUDIT.md`; it should be rerun after any task
statement changes.

## Candidate Non-Higham Source Pool

The following sources are candidates for replacing the prototype tasks. They
are not yet final task statements.  A more detailed survey is maintained in
`benchmark/tasks/EXTERNAL_STABILITY_SOURCE_SURVEY.md`.

| Candidate | Source anchor | Candidate task shape | Lean support | Current status |
| --- | --- | --- | --- | --- |
| BLAS matrix-vector product | Netlib `DGEMV` documentation, which specifies `y := alpha*A*x + beta*y`: <https://www.netlib.org/lapack/explore-html/d7/dda/group__gemv.html> | Prove a componentwise backward-error certificate for a Lean model of GEMV. | `MatVec.lean`, `FPModel.model_mul`, `FPModel.model_add`, gamma algebra. | Externally specified algorithm, library-derived bound. Current T05 can remain only with this label. |
| LAPACK componentwise backward error | LAPACK Users' Guide, "Further Details: Error Bounds for Linear Equation Solving": <https://www.netlib.org/lapack/lug/node81.html> | Given a residual bound in the LAPACK `BERR` denominator, prove existence of componentwise perturbations `E` and `f` such that `(A+E)xhat = b+f`. | `IterativeRefinement.lean`, `PerturbationTheory.lean`, residual infrastructure. | Strong replacement candidate for a residual-certificate task. |
| LAPACK least-squares error bounds | LAPACK Users' Guide, "Error Bounds for Linear Least Squares Problems" and further details: <https://www.netlib.org/lapack/lug/node82.html>, <https://www.netlib.org/lapack/lug/node83.html> | Convert a small normwise least-squares backward error into an `ERRBD`-style forward-error bound involving conditioning and residual angle hypotheses. | `LeastSquares/LSQRSolve.lean`, `LeastSquares/LSNormalEquations.lean`, perturbation structures. | Candidate; exact theorem shape must avoid being only an abstract wrapper. |
| Netlib Templates stopping criterion | Netlib Templates, stopping criteria for iterative methods: <https://netlib.org/templates/templates.html> and <https://netlib.org/linalg/old_html_templates/section2.8.2.html> | Prove that a residual stopping criterion implies a relative forward-error target under an explicit `A^{-1}` or condition-number hypothesis. | `StationaryIteration.lean`, `PerturbationTheory.lean`, residual bounds. | Strong replacement candidate for the stationary-iteration task. |
| Wilkinson growth-factor analysis | Wilkinson's Gaussian-elimination backward-error tradition; local source should be pinned to a book/page before use. | Use a growth-factor hypothesis to derive a normwise backward-error bound for LU solve. | `LU/GrowthFactor.lean`, `LU/LUSolve.lean`. | Candidate, but needs exact source anchor beyond secondary summaries. |
| Fast matrix multiplication stability | Demmel-Dumitriu-Holtz-Kleinberg, "Fast Matrix Multiplication is Stable": <https://arxiv.org/abs/math/0603207> | From a recursive fast-matrix-multiply error interface, prove a normwise forward-error certificate for a blocked algorithm. | `FastMatMul.lean`, `MatMul.lean`, norm infrastructure. | Hard candidate; likely late benchmark task. |
| Block algorithms with fast BLAS | Demmel and Higham, "Stability of Block Algorithms with Fast Level 3 BLAS": <https://www2.eecs.berkeley.edu/Pubs/TechRpts/1990/5472.html>; LAPACK Users' Guide fast BLAS section: <https://www.netlib.org/lapack/lug/node108.html> | Show that a block algorithm inherits a bound when the underlying matrix multiply and triangular solve satisfy specified normwise BLAS3 bounds. | `FastMatMul.lean`, triangular-solve and LU modules. | Useful, but because Higham is a coauthor it should not be counted as a fully non-Higham source. |
| Accurate summation/dot product | Ogita, Rump, and Oishi, "Accurate Sum and Dot Product", SIAM J. Sci. Comput. 26(6), 1955-1988, DOI 10.1137/030601818. | Prove a small certified error bound for a compensated sum or dot-product kernel. | Current library has standard sum/dot-product infrastructure but not full EFT/compensated algorithms. | Good hard-task candidate only if we add or task-localize the needed algorithm definitions. |

## Proposed Revision Direction

Do not keep the current ten tasks as the final benchmark. Instead:

1. Archive the current pass@1 result as a prototype harness validation.
2. Replace several Higham-derived tasks with LAPACK, Netlib Templates,
   Wilkinson, fast-matrix-multiplication, and least-squares tasks.
3. Keep only a small number of Higham-derived tasks where they test basic
   library navigation or low-level gamma composition.
4. For every selected task, write a source record before writing the Lean task.
5. Run contamination searches on the exact natural-language theorem shape and
   theorem name before official solver attempts.
