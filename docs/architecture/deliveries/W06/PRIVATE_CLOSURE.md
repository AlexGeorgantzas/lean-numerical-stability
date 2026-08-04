# W06 private-declaration and retention closure

The frozen P0007 selection contains 3,512 declarations in 3,450 complete Lean
commands. Exactly 94 declarations are private. Lean encodes each private
declaration's defining module in its generated name, so no private declaration
is moved or renamed.

## Graph closure

`PRIVATE_CLOSURE_PLAN.py` starts with the 94 private declarations and reverse-
closes every P0007 signature and body/proof dependency at command granularity.
The deterministic graph floor is:

| Quantity | Count |
| --- | ---: |
| Private seeds | 94 |
| Transitively pinned public declarations | 674 |
| Graph-retained declarations/commands | 768 |
| Graph-free declarations | 2,744 |
| Graph-free commands | 2,682 |

The hash-pinned ledger is `PRIVATE_CLOSURE.tsv`, SHA-256
`5391A2EAED68263FE9EE2B38D35F79A1660BF06728580D37485286CC115B0E64`.
It records every C0005 source blob, exact `.ilean` hash, half-open command span,
private seed, closure depth, and typed witness edge.

The replay command, run while holding
`Local\lean-reorganization-2026-08`, is:

```text
python docs/architecture/deliveries/W06/PRIVATE_CLOSURE_PLAN.py --repo-root . --control-root C:\Users\qed_s\higham-worktrees\final-main-audit --ilean-root C:\Users\qed_s\higham-worktrees\final-main-audit\.lake\build\lib\lean --check
```

It exits zero with 3,450 selected commands, 768 graph-retained declarations,
2,744 graph-free declarations, and 768 retained commands.

## Required ambient-context retention

The graph format does not encode file-local instances and section state. The
second block of `Higham16Problem16_2` depends on two local finite-dimensional
instances that are not re-exported by importing the first block. Seven otherwise
graph-free public commands therefore remain with that historical owner:

- `NumStability.Higham16LyapunovSemigroupIntegrable`
- `NumStability.higham16CMatrixFiniteDimensionalComplex`
- `NumStability.higham16CMatrixFiniteDimensionalReal`
- `NumStability.higham16Problem16_2LyapunovKernel`
- `NumStability.higham16Problem16_2LyapunovIntegral`
- `NumStability.higham16_problem16_2_generalIntegral_neg_eq_lyapunovIntegral`
- `NumStability.higham16_problem16_2_lyapunovKernel_posDef`

The final worker retention closure is therefore 775 declarations: 94 private
and 681 public. The other 2,737 declarations relocate. `RETENTION.tsv` records
the exact per-owner partition and identifies 23 declaration-bearing facades and
44 pure import shims.

## Non-P0007 physical and notation boundaries

C0005 contains one stale physical copy of `NumStability.infNorm_add_le` in
`Algorithms/MatrixPowers.lean`. The declaration is not selected by P0007 because
the combined C0005 environment attributes the canonical declaration to
`NumStability.Algorithms.PolynomialEvaluation.MatrixNorms`. The generator blanks
the unique old command span (from its triangle-inequality docstring through the
next command marker), imports that accepted canonical module in the historical
facade, and tests `#check NumStability.infNorm_add_le`.

Five `local notation` commands generate private syntax names. Those commands
stay historical. Four owners have movable commands that use the notation, so
the generator performs the only intentional command-text substitutions in the
delivery:

- 37 uses of `𝔼` become `(EuclideanSpace ℂ (Fin n))`: 7 in
  `BergerInequality`, 10 in `BergerResolvent`, and 20 in `NumericalRadius`;
- 9 uses of `↑ₐ` become `(algebraMap 𝕜 A)` in
  `PseudospectralResolvent`.

`BergerGeneral` and its private notation remain wholly historical. The P0007
candidate comparison is the final proof that these syntax expansions preserve
the same public declaration identities, statements, kinds, visibility, and all
typed incident edges.
