# C0008 acceptance evidence

Checkpoint code commit: `897557779a2102aa0e23b0b2f63edeb35b06bc68`

Acceptance status: **accepted** by `primary-human` at `2026-08-31T04:10:00Z`.

This report records the primary-human acceptance of checkpoint C0008 for the
M13/I01 wave at exact code commit `897557779a2102aa0e23b0b2f63edeb35b06bc68`
on `main`. It accepts milestone M13, closing the phase's last in-scope wave,
and it is the evidence checkpoint for bounded-phase completion. Repository-wide
completion remains `incomplete` with null evidence: the repository-wide gate
set (build profiles, documentation currency, entrypoint reachability, outlier
review, and the rest) is not proved here, and C0008 must not be cited as its
proof.

## Exact green code runs

The checkpoint code commit was proved by
[GitHub Lean CI run 33354902730 (job 99375060412)](https://github.com/AlexGeorgantzas/lean-numerical-stability/actions/runs/33354902730),
which completed successfully for exact
`897557779a2102aa0e23b0b2f63edeb35b06bc68` on `main` (attempt 1, run number
8965, check suite 90378441233, runner `GitHub Actions 1000009011`, started
`2026-08-31T03:46:14Z`, completed `2026-08-31T03:55:44Z`). Its complete job log
is 157,342,571 bytes with SHA-256
`FEEB92A24CBCFBCEE86FC75A735549CE92DE23A6315C26AC0A8B0431A7482DF1`.

That run is the first in repository history to carry a distinct test-driver
step. Its seven steps all concluded `success`:

| Step | Name | Start | End |
| ---: | --- | --- | --- |
| 1 | Set up job | `2026-08-31T03:46:19Z` | `2026-08-31T03:46:20Z` |
| 2 | Run actions/checkout@v5 | `2026-08-31T03:46:20Z` | `2026-08-31T03:46:46Z` |
| 3 | Check architecture source graph and Python tooling | `2026-08-31T03:46:46Z` | `2026-08-31T03:50:49Z` |
| 4 | Build library and smoke tests | `2026-08-31T03:50:49Z` | `2026-08-31T03:55:13Z` |
| 5 | Run lake test | `2026-08-31T03:55:13Z` | `2026-08-31T03:55:38Z` |
| 10 | Post Run actions/checkout@v5 | `2026-08-31T03:55:38Z` | `2026-08-31T03:55:38Z` |
| 11 | Complete job | `2026-08-31T03:55:38Z` | `2026-08-31T03:55:38Z` |

The `full_build` gate is carried by step 4, whose literal command is
`lake build NumStability NumStabilityTest`. The `full_tests` gate is carried by
step 5, whose literal command is exactly `lake test`. These are distinct steps
with distinct conclusions: no build target, action input, or inferred command
stands in for the test-driver claim. The predecessor checkpoint's `full_tests`
label did not have this property, and the append-only correction record
`reviews/C0007-full-tests-evidence-correction.json` states so; that record must
not be reused as test-driver proof, and this checkpoint does not rely on it.

## Epoch content

C0008 accepts the reviewed R0014/R0015 implementation union applied at
`9fbb1e36bcc85f866893e902cbe206ba468a65b0`, together with the process
transition at `cca0621da6c2b0f19836aec67aa736ef9a06a838`, the governance
reconciliation at `543b64df93daff49b123e6b1b4252f3c9b4d3d55`, and the
test-contract repair at the code commit itself. The bounded P/A/T/I/V lifecycle
that had been prepared for this wave was retired by the primary human's
2026-08-30 decision before its second activation candidate could pass CI; the
bounded branch `codex/reorg-closeout-2026-08-m13-i01` remains immutable history
at `46c42a339b59a08cec3cbc439a929c3707447229`, and the same reviewed postimages
landed by the ordinary gated route recorded in `docs/architecture/PROCESS.md`.
Every one of the fourteen R0014/R0015 postimages was verified byte-exact
against the SHA-256 values frozen in `requests/R0014-postimages.tsv` and
`requests/R0015-postimages.tsv` at planned commit `1d454ecb8`, and every
preimage was verified byte-identical at the C0007 code commit before
application.

The changed-path ledger `C0008-integration-paths.tsv` records the exact 48-path
range from the C0007 code commit to this checkpoint code commit, categorized by
the landing that introduced each path.

## Generated evidence

| Artifact | SHA-256 |
| --- | --- |
| `C0008-combined.json` | `F46630771D68B4A7CD602580F9AF116F9C93E2CD3B79B206E1E7BB054F6856B1` |
| `C0008-combined.md` | `E6106C42CED68BBCFC628D74139B968EBD0EF7FEA0503C89A84662D24C885480` |
| raw `benchmark-results/C0008-combined.tsv` | `B73F43B1F90684A81831290FCC6D00AE0A87E19D77889AACCC89190ADBA688A9` |
| `C0008-inventory.tsv` | `FADDC6529266357C836BC0DBD99CF8151C2DC75D3B16D64B4D8AB383F996EF73` |
| `C0008-integration-paths.tsv` | `7B140432E55D8B2E77FBC3B3A045BBA8937B795BFB79BB6EF31D2B23CB92EBC3` |

The baseline records 2,928 production modules: 2,928 classified, 0
unclassified, and 0 mixed, with 0 noncanonical names, **zero**
declaration-bearing umbrellas, zero missing module docstrings, and zero
unsorted aggregate imports. The single declaration-bearing umbrella carried by
C0007 was the Chapter 2 Problem 9 double-rounding counterexample parent; the
I01 split retired it, so this is the first checkpoint at which the
declaration-bearing umbrella count is zero. Tier separation is complete with
zero reusable-to-source and zero reusable-to-mixed reachable pairs. The tier
audit's `source`-to-`compatibility` edge count falls from 2 to 0: the two
retained Chapter 19 production compatibility imports are gone, and with them
the retained-boundary exception mechanism itself. The inventory has 2,928
unique sorted rows, all `already_complete`, with zero debt rows; the in-scope
queue is empty.

## Declaration graph

The I01 epoch is declaration-preserving in both directions. Against the C0007
combined baseline the elaborated declaration count is unchanged at 56,913, the
public count is unchanged at 55,219, the private count is unchanged at 1,690,
theorems at 43,179, definitions at 11,982, and cross-module union edges at
262,888. The three-path counterexample split moved declarations between modules
without adding, removing, or changing the visibility of any of them, and the
Chapter 19 import retarget changed no declaration at all. Source line count
falls from 3,982,215 to 3,981,679 and direct imports rise from 31,329 to
31,331, both accounted for entirely by the reviewed postimages.

## Acceptance gates

All twelve acceptance gates PASS at the exact code commit: architecture,
canonical_import, combined_baseline, compatibility, focused_build, full_build,
full_tests, layout, old_import, provenance, scope, and strict_source. The
`full_build` and `full_tests` gates are carried by the two distinct CI steps
recorded above. The static architecture, layout, compatibility, provenance,
strict-source, and baseline gates were run against this exact tree during
acceptance preparation, all exiting zero, and the same architecture step was
independently re-run by CI in step 3 of the same run. The `focused_build` gate
is the exact twelve-row focused build sequence from the acceptance packet,
run against this tree: the twelve I01 modules together, then
`Counterexample.Inputs`, `Counterexample.Results`, `Analysis.DoubleRounding`,
and `DoubleRounding.All` independently, then the parent entrypoints
(`Chapter02`, `Source`, `Chapter19.Core`, `All`, `NumStability`), then each of
the five new I01 test leaves independently, and finally the `I01.All`
aggregate. Every command exited zero; each new test leaf was built in isolation
before its aggregate, so no broad test-root import stands in for isolation.

## Lifecycle

M13 is accepted at C0008 and its I01 wave is complete: the twelve reserved
modules are no longer in scope, and the inventory carries no in-scope row.
B0011 and B0012 remain accepted with retirement due, P0011 and P0012 remain
retired, and R0012 and R0013 remain applied; no branch or request is open.
Bounded-phase completion becomes `complete` with `evidence_checkpoint_id`
C0008 on this record. Repository-wide completion stays `incomplete` with null
evidence and is not implied, inferred, or partially proved by this checkpoint;
branch retirement remains a separate later control.
