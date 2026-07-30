# Integrator handoff: 2026-07-29

This checkpoint was pushed because the current machine had to be shut down.
It intentionally records both completed evidence and remaining integrator gates.

## Included work

- QR Chapter 19 Householder Wave 1 and Q2A are integrated. Q2A passed a
  5,706-job combined build and the cumulative semantic stage gate: 18
  destinations, 17 wrappers, 1,501 command groups, 22 private rewrites,
  25,540 signature edges, and 35,878 body/proof edges.
- Chapter 9 is physically split in full: 20 canonical destinations, 4,420
  declarations, 4,108 command groups, 28 private declarations, and 11
  declaration-free historical facades. The cumulative static reconciliation,
  layout, compatibility, provenance, and strict-source gates pass.
- Claude's complete LSQ/Chapter 20 delivery branch is merged through delivery
  commit `ce5a2e153fa2fbf8da0536842ac164741f3b3e52`. It contains all 16 lane
  commits, 41 migrated historical owners, 73 destinations, isolated tests,
  axiom probes, the ownership checker, and the delivery report. The lane's own
  full build passed 5,449 jobs before integration.
- The integration retargets completed QR compatibility imports to canonical
  paths and makes the delivered LSQ test surface reachable from
  `NumStabilityTest` through `NumStabilityTest.Worker.LsqCh20`.

## Verified at this checkpoint

- `check_layout.py`: pass; 1,270 Lean modules, 564 unclassified, 0 mixed,
  0 unsorted aggregates.
- `check_compatibility.py`: pass; 147 forwarding modules and 266 targets.
- `check_provenance.py`: pass.
- strict source/import graph: pass; no cycles or classified
  reusable-to-source/mixed reachable pairs.
- Python compilation and `git diff --check`: pass.

`NumStability.Analysis.Perturbation.LeastSquares.Conditioning` is explicitly
classified as source at this checkpoint because its preserved proof imports
the Chapter 21 source chain. The lane proposal called it reusable; resolving
that semantic mismatch requires either moving the source-dependent theorem or
reclassifying its destination, not weakening the strict-source gate.

## Resume gates

1. Run the combined `lake build NumStability NumStabilityTest` under
   `Local\LeanNumericalStabilityLargeBuild`. The QR and LSQ lane builds passed
   separately, but the final Chapter 9 + LSQ merge was not rebuilt before the
   shutdown deadline.
2. Generate a fresh format-2 dependency stream and run the three Chapter 9
   semantic stage gates. The complete closure-tail static checker passes; the
   first layers checker needs a cumulative-mode adjustment because its old
   materialization check expects the pre-Wave-A residual giant owner.
3. Apply and verify the remaining exact LSQ shared registrations from
   `docs/architecture/declaration-ownership/lsq-ch20-coordinator-patches.tsv`.
   Physical migration and tests are present; full historical-wrapper tier and
   compatibility-map registration remains coordinator work.
4. LSQ post mode still requires the authoritative 69-row QR owner/carrier
   handoff. Q2B supplies 14 of those identities when it is completed.
5. The local `codex/org-qr-ch19-q2b` branch was interrupted during preparation
   and was not merged; restart Q2B from the pushed checkpoint rather than
   treating that partial local branch as a delivery.

The authoritative LSQ details are in
`worker-lsq-ch20-delivery.md`; Chapter 9 wave reports and frozen ownership
artifacts are committed beside this note.
