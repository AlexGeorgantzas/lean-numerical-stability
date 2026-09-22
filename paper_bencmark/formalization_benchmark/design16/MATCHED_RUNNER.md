# Design-16 matched exploratory runner

Status: `UNSCORED_ENGINEERING_EXPLORATORY`. This runner does not create an
official benchmark observation and does not perform a faithfulness audit.

Build fresh schema-v3 atlases once, outside every contestant clock. Schema v3
masks Lean line comments and nested block/doc comments before declaration and
scope recognition, preventing documentation examples from becoming packet
declarations. Do not overwrite or relabel an existing schema-v2 atlas; use new
output directories and freeze their new identities:

```bash
python3 paper_bencmark/formalization_benchmark/tools/library_atlas.py \
  --source-root /path/to/packages/mathlib/Mathlib \
  --root-module /path/to/packages/mathlib/Mathlib.lean \
  --output-root /path/to/design16-index-v3/mathlib \
  --library-commit <frozen-mathlib-commit>

python3 paper_bencmark/formalization_benchmark/tools/library_atlas.py \
  --source-root /path/to/lean-numerical-stability/NumStability \
  --root-module /path/to/lean-numerical-stability/NumStability.lean \
  --output-root /path/to/design16-index-v3/numstability \
  --library-commit <frozen-numstability-commit>
```

Generate a fresh Design-17 deployment record that layers the schema-v3
NumStability atlas over the already frozen Pilot-15 runtime, and start a fresh
campaign manifest pointing at the schema-v3 Mathlib atlas. Do not rerun or
rewrite the legacy Pilot-15 release. Existing deployment records, schema-v2
atlas directories, failed campaigns, and their hashes remain immutable
evidence.

Run one sequential matched pair with an explicitly counterbalanced order:

```bash
python3 paper_bencmark/formalization_benchmark/tools/design16_matched.py \
  --deployment /path/to/deployment-pilot-15-r1/deployment.json \
  --mathlib-atlas /path/to/design16-index/mathlib \
  --task-id H22-11 \
  --condition-order R0,R1 \
  --output-root /path/to/design16-matched/H22-11
```

`R0` retrieves from Mathlib and has no NumStability OLean mount. `R1` runs the
same query/ranking/packet code over Mathlib plus NumStability and receives the
NumStability OLean mount. Both use fresh conversations, the same prompt bytes,
limits, packet schema, compile-only template preflight, and final integrity
validator. Retrieval and formalizer wall time are logged separately; their sum
is the exploratory system-time measure. Conditions always run sequentially.

The controller rejects a contaminated Mathlib atlas, a treatment atlas without
NumStability modules, stale atlas hashes, unsafe source artifacts, malformed
condition order, failed preflight, incomplete usage, timeout, nonzero provider
exit, or failed compilation/integrity validation. A successful pair ends as
`COMPILED_UNAUDITED`; an independent condition-blind faithfulness audit is
still required before interpreting the candidates semantically.
