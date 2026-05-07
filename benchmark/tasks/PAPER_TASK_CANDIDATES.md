# Paper-Derived Stability Task Candidates

Draft status: benchmark-design material. Do not copy this file into generated
solver workspaces.

This file tracks paper-derived candidates that can become benchmark tasks only
if the solver-facing theorem is a genuine stability proof: the conclusion must
be a forward-error, backward-error, residual-error, or stability-conversion
bound for a computed algorithm.

## Acceptance Rule

A candidate is accepted only if:

- the task file defines the algorithm or computed quantity inline;
- the conclusion is an error/stability bound;
- the paper source states the target bound or a very close equivalent;
- the theorem does not assume the same bound it is meant to prove;
- extra assumptions are structural/model assumptions, not hidden final
  stability conclusions.

Examples of acceptable extra assumptions:

- no-overflow/no-underflow side conditions;
- exactness contracts for arithmetic features outside generic `FPModel`, such
  as error-free transformations;
- matrix structural hypotheses, conditioning hypotheses, or residual stopping
  hypotheses.

Examples of rejected task shapes:

- assume `|res - exact| <= ...` and prove the same bound;
- assume the paper's absolute error bound and merely restate it as a relative
  error;
- add benchmark-specific paper helper definitions to the public library and ask
  the solver to apply them directly.

## P1: Ogita-Rump-Oishi `SumK`

Source:
Ogita, Rump, and Oishi, "Accurate Sum and Dot Product", SIAM J. Sci. Comput.
26(6), 1955-1988, 2005, Proposition 4.10 and Corollary 4.11, DOI
10.1137/030601818:
<https://ogilab.w.waseda.jp/ogita/math/doc/2005_OgRuOi.pdf>

Target source bound:

```text
|res - s|
  <= (eps + 3*gamma_{n-1}^2) * |s|
     + gamma_{2n-2}^K * sum_i |p_i|
```

Status:
good hard candidate.  The current pilot
`benchmark/tasks/E10_OgitaSumKCertificate/Task.lean` formalizes a
certificate-level version: it assumes the sourced intermediate distillation
facts from Lemma 4.9 and asks for the Proposition 4.10-style absolute error
bound.  A stronger final version could define `TwoSum`, `VecSum`, and `SumK`
inline and prove those intermediate facts from error-free-transformation
assumptions.  A relative-error corollary from an assumed absolute bound is not
accepted as a final benchmark task.

## P2: Ogita-Rump-Oishi `DotK`

Source:
Ogita-Rump-Oishi Proposition 5.11.

Target source bound:

```text
|res - x^T y|
  <= (eps + 2*gamma_{4n-2}^2) * |x^T y|
     + gamma_{4n-2}^K * |x|^T |y|
```

with side conditions including `K >= 3` and `8*n*eps <= 1`.

Status:
excellent final-hard-task candidate, but likely too large until the task-local
`TwoProduct`, `TwoSum`, `SumK`, and `DotK` algorithm definitions and exactness
assumptions are carefully designed.  The task should prove the absolute error
bound, not assume it.

## P3: DDHK Fast Matrix Multiplication

Source:
Demmel, Dumitriu, Holtz, and Kleinberg, "Fast Matrix Multiplication is Stable",
Numerische Mathematik 106 (2007), Theorem 3.1 and equation (4):
<https://arxiv.org/abs/math/0603207>

Target source bound:

```text
||Ccomp - C|| <= mu(n) * eps * ||A|| * ||B|| + O(eps^2)
```

For stationary partitioning, Theorem 3.1 gives:

```text
mu(n) =
  (1 + max_{r,s}(alpha_s + beta_s + gamma_r + 3) * log_k n)
  * (e_max * ||U|| * ||V|| * ||W||)^(log_k n)
```

Status:
very hard candidate.  A valid task should inline the coefficient definitions
and a sufficiently concrete recursive/bilinear algorithm interface, then prove
a normwise forward-error bound.  A task that assumes a final
`DDHKStationaryStable` bound is rejected as too close to the conclusion.

## P4: Rump Computable Matrix-Product Bound

Source:
Rump, "Computable backward error bounds for basic algorithms in linear algebra",
NOLTA 6(3), 2015, Corollary 1:
<https://www.tuhh.de/ti3/paper/rump/Ru14c.pdf>

Target source bound:

```text
|P_hat - A*B|
  <= k*u*(1+u)*(Q_hat + (k-1)*u*ufp(Q_hat))
```

where `Q_hat` is the floating-point computation of `|A|*|B|`.

Status:
interesting but currently outside the intentionally general `FPModel`, because
the result uses IEEE-style `ufp` reasoning and sharper `k*u` bounds.  It should
not be a near-term task unless we intentionally add a task-local `ufp` model and
accept that it goes beyond the current library's general assumptions.

## Recommended Next Pilot

Do not start with the hardest paper tasks.  Start with an external-source task
that is clearly a stability proof and already matches the existing library's
strength:

1. LAPACK/Oettli-Prager componentwise residual to backward perturbation.
2. Netlib Templates residual stopping criterion to relative forward-error
   certificate.
3. LAPACK normwise residual/condition-number forward-error bound.

These are still stability proofs, but they do not require formalizing
error-free transformations, `ufp`, or a recursive fast-matrix-multiplication
algorithm before the benchmark machinery can be tested.

Initial pilot:
`benchmark/tasks/E01_LapackBerrBackward/Task.lean`.

The theorem conclusion is a componentwise backward-compatibility statement:
there exist bounded perturbations `DeltaA` and `Deltab` such that the
approximate vector is an exact solution of the perturbed linear system.

Additional stability-only pilots:

- `benchmark/tasks/E02_TemplatesResidualStop/Task.lean`
- `benchmark/tasks/E03_LapackFerrForward/Task.lean`
- `benchmark/tasks/E04_LapackLevel3Matmul/Task.lean`
- `benchmark/tasks/E05_LapackTriangularResidual/Task.lean`
- `benchmark/tasks/E06_OettliPragerForward/Task.lean`
- `benchmark/tasks/E07_TemplatesStationaryResidual/Task.lean`
- `benchmark/tasks/E08_LapackLSQRForward/Task.lean`
- `benchmark/tasks/E09_LapackNormalEquations/Task.lean`
- `benchmark/tasks/E10_OgitaSumKCertificate/Task.lean`

Their source derivations are recorded in
`benchmark/tasks/EXTERNAL_TASK_DERIVATION.md`.
