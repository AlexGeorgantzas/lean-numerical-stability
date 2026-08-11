# Repository reorganization completion (2026-08)

This active successor is rooted at predecessor C0008 code `b1b18772d80185ec08f49c818919558645c330a1` while preserving `docs/architecture/phases/2026-08-repository-reorganization/` as immutable history. C0000 is both origin and current checkpoint.

R01 (`codex-local`) and R02 (`claude-local`) are the only provisioned worker waves. Their branches start from C0000, not the later control commit. All other residual rows have a frozen semantic wave assignment and dependency-ordered milestone, but no worker ref is created by this activation.

`MatrixAlgebra.lean` is protected read-only. Shared consumers, global aggregates, manifests, controls, tools, CI, Lake files, root documentation, and `NumStabilityTest.lean` are integrator-owned. Historical owner imports are preserved through import-only wrappers or source aggregates. Repository-wide completion requires zero classification, mixed-tier, naming, documentation, and declaration-bearing-umbrella debt.
