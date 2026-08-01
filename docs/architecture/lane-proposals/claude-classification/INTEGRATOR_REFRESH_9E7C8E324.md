# Integrator refresh at `9e7c8e324`

> **Status: superseded historical refresh.** The Chapter 9 and Chapter 11
> blockers below were resolved in dependency order, both post gates passed, and
> no shared integrator action remains. See
> `docs/architecture/migrations/2026-07-31-four-lane-final-integration.md`.

The classification proposal and Chapter 9/11 contracts were re-audited after
the CI source-graph repair. No declaration route, owner, private rewrite, or
declaration-DAG edge changed.

Chapter 9 now has a current import surface: ten historical BlockLU umbrella
rows became forty exact canonical imports, and the obsolete
`MatrixInversion -> HighamChapter9` consumer edge was removed. Its pre-check
passes for all 4,420 routes, 280 exact imports, and 28 downstream consumers.

The frozen 6,385-route Chapter 11 graph also passes, but Chapter 11 remains
blocked on Chapter 9 and must regenerate its then-current imports before any
production move.

There are zero lane-owned path overlaps with QR Wave 1 or LSQ Wave 3. Shared
tiers, aggregates, root tests, and layout metadata remain integrator-owned.

The refresh also corrected a reproducibility issue in the worker handoff:
acceptance hashes had been computed from pre-commit Windows CRLF files while
`.gitattributes` commits TSV files with LF. Acceptance hashes now describe the
bytes present in a clean checkout.

Machine-readable hashes and command results are in
`INTEGRATOR_REFRESH_9E7C8E324.json`.
