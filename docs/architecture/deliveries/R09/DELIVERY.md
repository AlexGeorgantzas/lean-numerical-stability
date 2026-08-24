# R09 worker delivery

This directory is the immutable-worker evidence packet for R09, Higham Chapter 28 gallery of test matrices. It is based on checkpoint C0006 and code commit
`fda296b2079acae3bf1d3565b2dc6e45dc8f6ef5`. The activated planning control is B0011 at control commit `ac2253a514ee2ad25c763f1ee5a6365061f42146`.

The materialized worker result has 72 historical owners. 68 declaration-bearing owners are import-only compatibility wrappers after
relocation; 4 zero-declaration owners remain byte-identical to C0006. The 570 declarations (405 public and 165 private)
are routed to 41 semantic destinations. The isolated test plan contains 115 test modules: 114 isolated targets and one
aggregate.

`MATERIALIZATION.json` binds all 224 worker-rendered postimages at SHA-256
`54AB3DA3F3C9ECE1D4D62CC44FFBDF8D2FCBD839D500EA8897ECDB39337FA8B4`.
Its deterministic verifier has SHA-256
`CA072ED2A92F7999E697FA4236C32FCE0A33A469FBE222CD36CCA43A41334D6D`.
The copied TSV ledgers bind the reviewed planning inputs byte-for-byte.
`RETENTION.tsv` records each historical owner, and `CHANGED_PATHS.md` records
the complete 240-path delivery set: 109 production paths, 115 test paths, and
16 delivery-evidence paths. The shipped checkers are read-only in the worker tree.

## Disclosed deviations from R07's mechanics

0. **This package ships 16 of R07's 20 evidence artifacts, and carries no executable verification.** All four checker scripts are absent. `CHECK_SCOPE.py` and `CHECK_STATIC.py` generate cleanly but exit 1 on first run against B0011-module-routes.tsv, B0011-inventory.tsv, B0011-destinations.tsv and the six-column wrapper-imports form, none of which this control has; shipping them would read as verification that was performed. `CHECK_REQUEST_REPLAY.py` cannot be built for R09: it reads R0012-import-manifest.tsv, R0012-request-plan.tsv, B0011-shared-request-paths.txt, B0011-module-routes.tsv, B0011-destinations.tsv, reviews/R09-COMPATIBILITY-postimage.md and reviews/R09-planned-control-contract.json, none of which the C0006 planned control landed. `CHECK_PROJECTION.py` pins a four-root extraction census, while the generated candidate graph is a single-root extraction and so cannot supply the counts it would pin. The integrator must treat both verifications as not performed.
1. R09 has no mid-wave correction patch: nothing in the reviewed inputs records one, so there is no analogue of R07's `R0011-CORRECTION.patch`.
2. The R09 planning control carries no source-command (ilean span) ledger, so `auditors/materialize_worker.py` verifies the postimages by SHA-256 and
   re-derives every import surface, instead of re-rendering bodies the way R07's materializer did.
3. 0 anonymous `local instance` declarations are restated as `private local instance`; one proof lost a redundant tactic step; 11
   compiler-named instances were placed by a documented replication / dominant-destination rule. All three are detailed in `ROUTING.md`.

All required worker gates are green. `GATE_RESULTS.tsv` records each gate invocation or artifact-bound exact roster, exit code, transcript SHA-256, and
bound artifact or checker SHA-256, for 6 green gates out of 6 recorded rows.

This delivery does not integrate R0012, edit shared files, accept R09, accept a checkpoint, retire the branch, or push main.
