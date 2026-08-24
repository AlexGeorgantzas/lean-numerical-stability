# C0006 acceptance evidence

Checkpoint code commit: `fda296b2079acae3bf1d3565b2dc6e45dc8f6ef5`

Acceptance status: **accepted** by `primary-human` at `2026-08-24T00:01:01Z`.

This report records the primary-human acceptance of checkpoint C0006 for the
integrated R07 matrix-powers epoch at exact code commit
`fda296b2079acae3bf1d3565b2dc6e45dc8f6ef5` on `main`. It accepts milestone
M07, applies shared request R0011 with its reviewed four-path supplemental
correction, retires baseline projection P0010, and moves branch B0010 to
`accepted` with retirement due. Branch retirement, remote-ref deletion, and
worker-worktree removal remain a later separate control; the exact
acceptance-control commit SHA and its CI run are intentionally deferred to
that separate control's hash-pinned attestation record.

## Exact green code runs

The integrated code was proved by
[GitHub Lean CI run 32616508317 (job 97138028649)](https://github.com/AlexGeorgantzas/lean-numerical-stability/actions/runs/32616508317),
which completed successfully for integration control
`b2b9ab9057deda15c3fcf27745b76dcc49d3a1a5` on `main`, and the checkpoint code
commit itself passed
[GitHub Lean CI run 32636790741](https://github.com/AlexGeorgantzas/lean-numerical-stability/actions/runs/32636790741)
(success at 2026-08-23T11:40:46Z for exact
`fda296b2079acae3bf1d3565b2dc6e45dc8f6ef5`). Both runs are recorded in the
hash-pinned attestation records
`reviews/R07-integration-control-ci.json` and the acceptance-control
attestation to follow.

## Delivery ancestry

Immutable R07 delivery `2f55e0aa5687829ca3a7dd54d5f90663ec4293cc` (sole
parent: exact C0005 code `ad92bbfae62d538f3e52829a269a846688a8e213`) was
preserved by true merge `4e298a102c6f914b42581492152ab9eea1cd0edf`, integrated
under exact R0011 and its reviewed correction at
`b2b9ab9057deda15c3fcf27745b76dcc49d3a1a5`, closed out at
`6867ea68774f1ca250191fa0f2c549ec0227b10d`, and refreshed at the checkpoint
code commit. The integration ledger below records the exact 57-path
merge-to-checkpoint range.

## Generated evidence

| Artifact | SHA-256 |
| --- | --- |
| `C0006-combined.json` | `5F61A60D5743E507D5DE4D82852DFA551861E1CAECD8610D8F345CC942DB1C76` |
| `C0006-combined.md` | `D417B835CC5A1ACAFCAD3FCE725CCE7163604623CD21819F5E6BA1004730E8E5` |
| raw `benchmark-results/C0006-combined.tsv` | `55EAFED7B5AA556A918128BFA32CEC44608A377449031795D2F68306FF8EF0D6` |
| `C0006-inventory.tsv` | `FCAAD0014B1614CFE419F9945F2A6F508217BE576628D6274C3774AD81A2E993` |
| `C0006-integrator-paths.tsv` | `94938AF9856BB941DD597490E6797018DB8BCA3C44F4FE4D8D2E91659EEAB8E1` |

The baseline records 2,860 production modules: 2,770 classified, 90
unclassified, and 0 mixed, with 72 noncanonical names, one declaration-bearing
umbrella, zero missing module docstrings, and zero unsorted aggregate imports.
The inventory has 2,860 unique sorted rows: 2,758 already complete and 102
still in scope, with exactly 91 debt rows. The remaining queue is exactly
I01=12, R09=72 and R10=18. The integrator ledger records the exact 57-path
(42 modified, 15 added) integration range from the R07 merge to the
checkpoint code commit.

## Acceptance gates

All twelve acceptance gates PASS at the exact code commit: architecture,
canonical_import, combined_baseline, compatibility, focused_build, full_build,
full_tests, layout, old_import, provenance, scope, and strict_source. The
full build and test gates are carried by the green integrated-code CI runs
above; the static architecture, layout, compatibility, provenance,
strict-source, and baseline gates were rerun locally against this exact tree
during acceptance preparation, all exiting zero.

## Lifecycle

M07 is accepted at C0006. B0010 is accepted with retirement due. P0010 is
retired and R0011 is applied with the reviewed supplemental correction. M09,
M10, and M13 remain planned. Subsequent waves must reduce the remaining 90
unclassified modules (R09=72 and R10=18) to zero under the same contract.
