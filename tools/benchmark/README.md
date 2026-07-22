# Build benchmarks

`run.py` records reproducible Lake build timings and full logs without adding a
benchmark to ordinary pull-request CI. It supports three measurements:

- `clean`: remove only the root package's build output, then build the library
  and smoke-test targets;
- `warm`: rebuild both targets with an already warm workspace;
- `incremental`: append a temporary comment to representative source files,
  build downstream targets, restore the exact source bytes and timestamps, and
  rebuild once more to leave valid Lake traces.

Run all measurements from the repository root:

```console
python tools/benchmark/run.py
```

Run a quick warm-cache check:

```console
python tools/benchmark/run.py --mode warm
```

Override incremental scenarios when a refactor changes the representative
modules:

```console
python tools/benchmark/run.py --mode incremental \
  --scenario foundation=NumStability/FloatingPoint/Model.lean \
  --scenario endpoint=NumStability/Higham/Chapter02/Problem04.lean
```

The default scenarios deliberately compare a highly foundational module with a
source-oriented endpoint module. Do not edit those files while an incremental
benchmark is running. The runner refuses pre-existing changes in scenario files
unless `--allow-dirty-scenarios` is supplied.

Results are written to `benchmark-results/<UTC timestamp>/` and are ignored by
Git. Keep selected `summary.json` files under `docs/architecture/baselines/`
when they are intended to serve as versioned migration evidence.
