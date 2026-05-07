# Benchmark Contamination Checks

Draft status: benchmark-design material. Do not copy this file into generated
solver workspaces.

This file records contamination checks for solver-facing theorem statements.
The purpose is to avoid benchmarking Codex on tasks whose exact Lean statement,
theorem name, or distinctive proof target is already available online or in
solver-visible files.

## Policy

Before official solver runs:

- search exact Lean theorem names;
- search exact task-local definition names;
- search distinctive statement fragments in natural-language form;
- search local repository files, excluding generated benchmark results;
- record whether hits are public source material, private benchmark design
  material, or direct theorem/proof contamination;
- rerun this check after renaming or changing theorem statements.

Allowed hits:

- the solver-facing task file itself;
- private benchmark-source notes that are excluded from generated workspaces;
- external numerical-analysis source material used to justify the task.

Disallowed hits:

- a public Lean proof of the same theorem;
- a solver-facing guide saying which library theorem solves the task;
- prior generated attempts copied into a future solver workspace;
- task-specific reference proofs visible to Condition A or Condition C.

## Initial E01-E10 Screen

Date: May 7, 2026.

Scope:

- local repository search excluding `benchmark/results/**`, `thesis/main.*`,
  and `error.log`;
- web search for exact theorem names and task-local names;
- web search for distinctive source-level bound phrases.

Local exact-name search:

| Name | Local hits outside generated results |
| --- | --- |
| `lapack_level3_matmul_forward_error` | `benchmark/tasks/E04_LapackLevel3Matmul/Task.lean` only |
| `lapack_level3_triangular_solve_residual` | `benchmark/tasks/E05_LapackTriangularResidual/Task.lean` only |
| `oettli_prager_backward_to_forward_error` | `benchmark/tasks/E06_OettliPragerForward/Task.lean` only |
| `templates_stationary_iteration_residual_bound` | `benchmark/tasks/E07_TemplatesStationaryResidual/Task.lean` only |
| `lapack_ls_qr_forward_error_certificate` | `benchmark/tasks/E08_LapackLSQRForward/Task.lean` only |
| `lapack_normal_equations_forward_error_certificate` | `benchmark/tasks/E09_LapackNormalEquations/Task.lean` only |
| `ogita_sumK_absolute_error_certificate` | `benchmark/tasks/E10_OgitaSumKCertificate/Task.lean` only |
| `lapackBerrDenom` | `benchmark/tasks/E01_LapackBerrBackward/Task.lean` only |
| `templatesResidualAllowance` | `benchmark/tasks/E02_TemplatesResidualStop/Task.lean` only |
| `lapackFerrBound` | `benchmark/tasks/E03_LapackFerrForward/Task.lean` and private derivation notes |

Web exact-name search:

No substantive web hits were found for the exact Lean theorem names above or
for task-local names such as `lapackBerrDenom`,
`templatesResidualAllowance`, `lapackFerrBound`, or
`SumKDistillationCertificate`.

Web source-fragment search:

| Fragment searched | Result |
| --- | --- |
| `|res - s| <= (eps + 3*gamma` with `SumK` | Points to the Ogita-Rump-Oishi source family, not a Lean formalization. |
| `omega_c`, `|A|`, `|xhat|`, `|b|` | Mostly unrelated `omega_c` hits unless constrained to LAPACK/Oettli-Prager; the intended hit is LAPACK source material. |
| `||Chat - AB||`, `c1(m,n,p)`, `epsilon` | LAPACK Level 3 BLAS source material. |
| `||T Xhat - B||`, `c2(m,p)` | LAPACK Level 3 BLAS source material. |

Interpretation:

The first screen found no direct public Lean proof contamination for E01-E10.
The source-level formulas are intentionally present in LAPACK, Netlib
Templates, Oettli-Prager, and Ogita-Rump-Oishi material; those are not
contamination because the benchmark is explicitly source-backed.

## Remaining Caveats

This is not yet a final contamination audit.

Remaining checks before official thesis runs:

- search GitHub code search manually for exact theorem names and distinctive
  Lean fragments;
- search generated result directories after any solver dry run and ensure they
  are never copied into later workspaces;
- check the final solver prompt does not include this file, task derivation
  notes, or expected theorem routes;
- rerun exact-name searches after any theorem renaming.

The current status is suitable for continued benchmark development, but not
yet for final thesis claims.
