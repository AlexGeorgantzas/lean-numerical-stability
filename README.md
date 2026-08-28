# HighamBench execution package

This branch contains only the files needed to prepare, run, validate, and
summarize the HighamBench two-condition experiment.

The 60 fixed tasks and execution tooling are under
[`highambench`](highambench). NumStability is not stored on this branch. Lake
downloads the frozen Higham-only release at commit
`4ec1ec874353010ad93cc0bb76370ac321da4681` into
`.lake/packages/numStability`.

Material used to construct or audit the tasks is intentionally excluded. This
includes reference PDFs, private proofs, faithfulness dossiers, audit history,
review records, builder notes, and the NumStability development tree.

## Bootstrap dependencies

Install Git and Elan, then run:

```bash
lake update
lake exe cache get
```

The exact Lean, NumStability, Mathlib, and transitive package revisions are
recorded by `lean-toolchain`, `lakefile.toml`, and `lake-manifest.json`.

See [`highambench/README.md`](highambench/README.md)
for the corpus and runner entry points, and
[`highambench/EXECUTION_FREEZE.md`](highambench/EXECUTION_FREEZE.md)
for the final Linux-host freeze procedure.
