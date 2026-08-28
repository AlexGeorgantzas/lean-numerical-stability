# HighamBench T1–T3 benchmark branch

This branch contains the HighamBench corpus and measurement tooling for testing
whether access to a frozen NumStability Lean library helps an agent complete
fixed Lean proofs.

The corpus contains 60 tasks from 20 numerical-analysis papers: one task of
each type T1, T2, and T3 per paper. The task statements and their controlled
contexts are fixed before measurement.

## Repository layout

- `paper_bencmark/highambench/`: tasks, shared definitions, prompts, metadata,
  validators, runners, tests, evidence, and reports.
- `paper_bencmark/scratch_pad/`: allowlisted campaign and measurement launchers.
  Generated results and private runtime material under this directory remain
  ignored by Git.
- `paper_bencmark/highambench/metadata/library_source.json` and
  `library_olean.json`: authenticated descriptors for the frozen library input
  expected by Condition L. The library itself is intentionally omitted from
  this branch.
- `lakefile.toml`, `lake-manifest.json`, and `lean-toolchain`: the pinned Lean
  and Mathlib environment.

## Conditions

- **N**: the agent receives no NumStability source, compiled objects,
  documentation, indexes, or caches.
- **L**: the agent receives the authenticated NumStability source and compiled
  objects for local search and use. Those inputs are not present in this
  checkout.

Both conditions otherwise use the same task, context, prompt, limits, model,
Lean version, Mathlib revision, and machine class.

## Library availability

The tracked `NumStability/` source tree and `NumStability.lean` root module have
been removed from this branch. Condition-L admission and paired N/L measurements
therefore fail closed until the exact frozen source and compiled-object inputs
recorded by the benchmark metadata are restored. The corpus, Condition-N
materials, offline reporting code, and measurement tooling remain available.

## Status and operation

See [`paper_bencmark/highambench/README.md`](paper_bencmark/highambench/README.md)
for the protocol, corpus status, isolation rules, validation commands, and
reporting workflow. Do not run measurements unless the controlled snapshot is
marked measurement-ready and its manifests validate.

Benchmark outputs, provider transcripts, paper PDFs, credentials, and private
runtime environments are intentionally not part of the tracked branch.
