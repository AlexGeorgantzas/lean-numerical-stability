# C0000 acceptance evidence

Checkpoint commit: `7930cca4f6c45ccbe0dc23e40480fabec4993f5b`

Accepted at: `2026-08-01T10:41:11Z`

## Remote gate

[GitHub Lean CI run 30695846088](https://github.com/AlexGeorgantzas/lean-numerical-stability/actions/runs/30695846088)
completed successfully at the checkpoint commit. Its single `build` job passed:

- checkout;
- Python compilation and the architecture, compatibility, provenance, and
  strict source-graph checks; and
- `lake build NumStability NumStabilityTest` through the tracked Lean action.

The job ran from `2026-08-01T10:30:39Z` to `2026-08-01T10:41:11Z`.

## Local post gates

The following commands passed on the exact checkpoint source tree:

```text
python tools/architecture/check_layout.py
python tools/architecture/check_compatibility.py
python tools/architecture/check_provenance.py
python tools/architecture/generate_baseline.py --skip-declarations --strict-source --output-dir benchmark-results/ci-architecture --name source
lake build NumStability NumStabilityTest
lake test
```

The combined build completed 5,540 targets and the test target completed 5,719
targets. Existing linter warnings were non-fatal.

## Fresh combined graph baseline

The checkpoint baseline was regenerated with:

```text
python tools/architecture/generate_baseline.py --no-build --output-dir docs/architecture/phases/2026-08-repository-reorganization/baselines --name C0000-combined
```

It records format-2 declaration graphs for 56,903 declarations in 978
declaration-bearing modules: 266,387 signature edges, 382,872 body/proof edges,
and 424,082 union edges. The source graph contains all 1,390 production
modules, has zero import cycles, and has zero classified reusable-to-source or
reusable-to-mixed reachable pairs.

The temporary raw format-2 stream was retained only long enough to size W01's
outgoing ownership slice: 3,697 declarations, 16,646 outgoing signature edges,
29,337 outgoing body/proof edges, and 31,539 outgoing union edges across the
four selected owners. This was planning evidence, not the durable lane
projection: P0001 later freezes both incoming and outgoing incident edges. The
raw stream is reproducible from the generation command and is not tracked.
