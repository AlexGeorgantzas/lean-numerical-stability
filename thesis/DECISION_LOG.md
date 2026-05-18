# Project Decision Log

This file records design decisions for the LeanFpAnalysis project.  It is
intended as thesis source material and durable project memory.

The log is project-wide, not only a benchmark log.  It should record decisions
about library design, proof organization, documentation, branches, benchmark
methodology, and thesis-facing rationale.

Important: do not include this file in solver-facing generated workspaces.  It
may contain rationale, rejected alternatives, expected difficulty, and private
project context.

## Branch Policy

### Decision: Keep Benchmark Work On A Dedicated Branch

Benchmark artifacts live on branch `benchmark`.

This includes:

- benchmark task files;
- condition-specific stubs;
- generated-workspace scripts;
- run protocols;
- task-selection rationale;
- contamination checks;
- solver-attempt logs, when added.

Reason: benchmark design is exploratory and has different risks from the core
library.  It may need several iterations, and it must avoid accidentally mixing
solver-facing material with private design rationale.  Keeping it on its own
branch lets the core library remain stable while benchmark infrastructure
evolves.

`main` is the core-library branch.  It may keep project-wide thesis notes like
this file and reusable public documentation, but benchmark harness files should
not live on `main` unless explicitly merged later.

## Core Library Decisions

### Decision: Use An Axiomatic Floating-Point Model

The library is built around `FPModel`, an axiomatic model over `Real`, rather
than a specific IEEE 754 formalization.

Reason: the goal is automatic stability analysis in a general mathematical
floating-point model.  The core theorem statements should be reusable across
formats and rounding implementations, as long as they satisfy the model
axioms.

Consequence: avoid adding IEEE-specific assumptions to core modules.  If they
are ever needed, they should belong in a separate optional module.

### Decision: Build Stability Proofs Compositionally

New results should reuse existing lower-level contracts whenever possible:
rounding lemmas support summation, summation supports dot products, dot
products support matvec/matmul, and triangular solve contracts support
higher-level solve analyses.

Reason: the thesis goal is not only to formalize isolated theorems, but to test
whether a library of reusable stability components helps future analyses.

### Decision: Mark Abstract Interfaces Honestly

Some high-level results are specification-transfer theorems: they take an
external or abstract hypothesis that is already close to the desired numerical
contract, then package the consequence.

Reason: these are useful named interfaces, but they should not be advertised as
fully derived floating-point analyses from `FPModel`.

Consequence: wrappers around external assumptions should be documented as
abstract/specification-transfer results.

### Decision: Strengthen High-Level Contracts Bottom-Up

Existing Higham-style contracts such as `HouseholderAppError`,
`HouseholderQRBackwardError`, `LUBackwardError`, and
`CholeskyBackwardError` should remain as reusable interfaces.

Reason: downstream theorems should depend on stable mathematical contracts, not
on every detail of a particular implementation.  The gap to close is not the
existence of the contract, but whether concrete rounded algorithms are proved to
satisfy it.

Consequence: implementation work should add new `def`s and bridge theorems
under the existing contracts, rather than rewriting the high-level theorem
statements or changing Higham's bounds.  For QR, the first implementation-backed
layer is concrete Householder application with `v` and `β` already supplied; the
full reflector-construction and QR-factorization stages come later.

### Decision: Keep Public Lookup Documentation

The files `docs/LIBRARY_LOOKUP.md` and `examples/LibraryLookup.lean` are public
library documentation.

Reason: the library is large.  A central lookup guide helps humans and tools
discover relevant definitions and theorem families without relying on private
agent memory.

These files are allowed on `main` because they describe the library generally.
They should avoid task-specific proof scripts.

## Benchmark Summary

The detailed benchmark design currently lives on branch `benchmark`.

Current durable decisions from that branch:

- use two benchmark conditions, not three;
- make Condition A a bare isolated workspace;
- make Condition C a fresh full-library workspace with public docs but no
  private memory or task-specific hints;
- give both conditions byte-identical task files;
- satisfy `import LeanFpAnalysis.FP` in Condition A with task-specific bare
  stubs and in Condition C with the real library;
- do not pre-solve benchmark tasks with Codex before evaluation.

Reason for keeping the detailed benchmark log on `benchmark`: the task ladder,
stubs, scripts, contamination protocol, and solver-run machinery are still
active experimental work.
