# HighamBench T1–T3 benchmark branch

This branch contains the HighamBench corpus and measurement tooling for testing
whether access to the NumStability Lean library helps an agent complete fixed
Lean proofs.

The corpus contains 60 tasks from 20 numerical-analysis papers: one task of
each type T1, T2, and T3 per paper. The task statements and their controlled
contexts are fixed before measurement.

## Repository layout

- `paper_bencmark/highambench/`: tasks, shared definitions, prompts, metadata,
  validators, runners, tests, evidence, and reports.
- `paper_bencmark/scratch_pad/`: allowlisted campaign and measurement launchers.
  Generated results and private runtime material under this directory remain
  ignored by Git.
- `NumStability/` and `NumStability.lean`: the frozen library source exposed
  read-only to Condition L. Condition N must not be able to see this library.
- `lakefile.toml`, `lake-manifest.json`, and `lean-toolchain`: the pinned Lean
  and Mathlib environment.

## Conditions

- **N**: the agent receives no NumStability source, compiled objects,
  documentation, indexes, or caches.
- **L**: the agent receives the authenticated NumStability source and compiled
  objects for local search and use.

Both conditions otherwise use the same task, context, prompt, limits, model,
Lean version, Mathlib revision, and machine class.

## Status and operation

See [`paper_bencmark/highambench/README.md`](paper_bencmark/highambench/README.md)
for the protocol, corpus status, isolation rules, validation commands, and
reporting workflow. Do not run measurements unless the controlled snapshot is
marked measurement-ready and its manifests validate.

The retained library can be checked with:

```sh
lake build NumStability
```

Benchmark outputs, provider transcripts, paper PDFs, credentials, and private
runtime environments are intentionally not part of the tracked branch.
