# W05 private-declaration retention closure

The hash-pinned planner in `PRIVATE_CLOSURE_PLAN.py` reads C0004 source blobs,
C0004 `.ilean` command spans, and P0006 typed edges.  Its complete
machine-readable result is `PRIVATE_CLOSURE.tsv`.

## Result

- P0006 declarations: 921.
- Atomic declaration commands after recovering source aliases: 921.
- Genuine-private seeds: 3, all in
  `NumStability.Algorithms.Sylvester.Higham16`.
- Retained reverse closure: 138 declarations/commands.
- Retained visibility: 3 private and 135 public.
- Relocation candidates: 783.
- Maximum witness depth: 9.
- Closure leaks: 0.

The private seeds are:

1. `rectMatMul_left_right_sub`, source lines 3684–3708;
2. `sylvesterVecCoeff_det_ne_zero_of_sepLowerBound`, lines 5747–5795;
3. `sylvesterVecCoeff_det_ne_zero_of_pos_le_sylvesterSepInf`, lines 5797–5804.

Lean encodes the defining module in a private declaration's generated name,
so moving any seed would change declaration identity.  Every transitive user
must therefore remain in the same historical module.

## Exact closure partition

The `rectMatMul_left_right_sub` reverse closure has 64 declarations: the seed
and 63 public users.  It consists of every declaration whose defining command
starts in Higham16 lines 3684–5238 except these four independently movable
commands:

- `rectMatMul_schur_coords_cancel`, bytes `[180017,181564)`;
- `rectMatMul_schur_coords_expand`, bytes `[181565,183114)`;
- `sylvesterSchurDiagonalSolution`, bytes `[211144,211472)`;
- `sylvesterSchurDiagonalSolution_zero`, bytes `[211637,212122)`.

It also retains the twelve source aliases starting at lines 7031–7086.

The `sylvesterVecCoeff_det_ne_zero_of_sepLowerBound` reverse closure has 74
declarations and contains the 37-declaration closure of the third seed.  It
consists of every declaration whose defining command starts in lines
5747–6861 plus the 32 aliases at lines 7091–7254.

The two top-level closures are disjoint, so their union is exactly 138.

## Reconstruction rule

`Higham16.lean` is intentionally a declaration-bearing historical facade.
The generator copies all 138 retained commands from the frozen C0004 blob,
preserves the historical namespace/import context, and imports every leaf
holding a relocated dependency.  No movable canonical or source command has
a typed dependency on this retained closure.  P0006 is the final identity and
incident-edge check.
