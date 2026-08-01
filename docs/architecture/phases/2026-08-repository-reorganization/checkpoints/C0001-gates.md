# C0001 acceptance evidence

Checkpoint commit: `d6e643adf0f20b33f7faebce7e1b9b1f87122c58`

Accepted at: `2026-08-01T11:28:54Z`

## Remote gate

[GitHub Lean CI run 30697653430](https://github.com/AlexGeorgantzas/lean-numerical-stability/actions/runs/30697653430)
completed successfully at the checkpoint commit. Its `build` job passed:

- full-history checkout;
- Python compilation plus both contract self-tests;
- the live phase, layout, compatibility, provenance, and strict source-graph
  checks; and
- `lake build NumStability NumStabilityTest` through the tracked Lean action.

The job ran from `2026-08-01T11:25:33Z` to `2026-08-01T11:28:53Z`.

## Local post gates

The following commands passed on the exact checkpoint source tree:

```text
python -m py_compile tools/architecture/check_phase.py tools/architecture/check_phase_projection.py
python -X dev tools/architecture/check_phase.py --self-test
python -X dev tools/architecture/check_phase_projection.py --self-test
python tools/architecture/check_phase.py
python tools/architecture/check_layout.py
python tools/architecture/check_compatibility.py
python tools/architecture/check_provenance.py
python tools/architecture/generate_baseline.py --skip-declarations --strict-source --output-dir benchmark-results/ci-architecture --name source
lake test
```

Existing Lean linter warnings were non-fatal.

## Fresh combined graph baseline

The checkpoint baseline was regenerated with:

```text
python tools/architecture/generate_baseline.py --no-build --output-dir docs/architecture/phases/2026-08-repository-reorganization/baselines --name C0001-combined
```

It records format-2 declaration graphs for 56,903 declarations in 978
declaration-bearing modules: 266,387 signature edges, 382,872 body/proof edges,
and 424,082 union edges. The source graph contains all 1,390 production
modules, has zero import cycles, and has zero classified reusable-to-source or
reusable-to-mixed reachable pairs.

## W01 projection evidence

The deterministic P0001 projection selects exactly the four W01 owners and
freezes their full incident graph: 3,697 declarations, 22,706 signature edges,
45,433 body/proof edges, and 48,076 union edges. The projection checker passed
against the retained full candidate stream with zero relocated declarations.
The 116 MB scratch stream was removed after verification; the hash-pinned gzip
projection remains tracked and is reproducible from the combined extractor.
