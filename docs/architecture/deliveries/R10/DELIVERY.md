# R10 worker delivery

This directory is the immutable-worker evidence packet for R10, Drineas-Mahoney RandNLA 2016 randomized linear algebra. It is based on checkpoint C0006 and code commit
`fda296b2079acae3bf1d3565b2dc6e45dc8f6ef5`. The activated planning control is B0012 at control commit `ac2253a514ee2ad25c763f1ee5a6365061f42146`.

The materialized worker result has 18 historical owners. 9 declaration-bearing owners are import-only compatibility wrappers after
relocation; 9 zero-declaration owners remain byte-identical to C0006. The 225 declarations (222 public and 3 private)
are routed to 17 semantic destinations. The isolated test plan contains 38 test modules: 37 isolated targets and one
aggregate.

`MATERIALIZATION.json` binds all 64 worker-rendered postimages at SHA-256
`F187FA0AE20E1A266C8D1A8FE62F539E0FB37825FB2CDCF824D6D8DA3B1B33D6`.
Its deterministic verifier has SHA-256
`980C2C4DF0CC42086CD1B1D4C0F02DE9B1F742E764D59FAF55D4ECDD4B1673C2`.
The copied TSV ledgers bind the reviewed planning inputs byte-for-byte.
`RETENTION.tsv` records each historical owner, and `CHANGED_PATHS.md` records
the complete 80-path delivery set: 26 production paths, 38 test paths, and
16 delivery-evidence paths. The shipped checkers are read-only in the worker tree.

## Disclosed deviations from R07's mechanics

0. **This package ships 16 of R07's 20 evidence artifacts, and carries no executable verification.** All four checker scripts are absent. `CHECK_SCOPE.py` and `CHECK_STATIC.py` generate cleanly but exit 1 on first run against B0012-module-routes.tsv, B0012-inventory.tsv, B0012-destinations.tsv and the six-column wrapper-imports form, none of which this control has; shipping them would read as verification that was performed. `CHECK_REQUEST_REPLAY.py` cannot be built for R10: it reads R0013-import-manifest.tsv, R0013-request-plan.tsv, B0012-shared-request-paths.txt, B0012-module-routes.tsv, B0012-destinations.tsv, reviews/R10-COMPATIBILITY-postimage.md and reviews/R10-planned-control-contract.json, none of which the C0006 planned control landed. `CHECK_PROJECTION.py` pins a four-root extraction census, while the generated candidate graph is a single-root extraction and so cannot supply the counts it would pin. The integrator must treat both verifications as not performed.
1. R10 has no mid-wave correction patch: nothing in the reviewed inputs records one, so there is no analogue of R07's `R0011-CORRECTION.patch`.
2. The R10 planning control carries no source-command (ilean span) ledger, so `auditors/materialize_worker.py` verifies the postimages by SHA-256 and
   re-derives every import surface, instead of re-rendering bodies the way R07's materializer did.
3. 0 anonymous `local instance` declarations are restated as `private local instance`; one proof lost a redundant tactic step; 0
   compiler-named instances were placed by a documented replication / dominant-destination rule. All three are detailed in `ROUTING.md`.

All required worker gates are green. `GATE_RESULTS.tsv` records each gate invocation or artifact-bound exact roster, exit code, transcript SHA-256, and
bound artifact or checker SHA-256, for 6 green gates out of 6 recorded rows.

This delivery does not integrate R0013, edit shared files, accept R10, accept a checkpoint, retire the branch, or push main.
