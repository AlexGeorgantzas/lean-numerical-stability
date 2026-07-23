# Sylvester family aggregate

## Scope

This batch adds one documented, import-only aggregate for the 28 modules in
`NumStability.Algorithms.Sylvester`. No implementation module moves, and no
declaration name, namespace, signature, proof, or narrow consumer import
changes.

## Entry point

`NumStability.Algorithms.Sylvester` is the complete family-discovery entry
point. It intentionally contains both reusable Sylvester-equation machinery
and Higham Chapter 16 source correspondence, so it is not listed as a pure
reusable entry point. New implementation modules should continue to import the
narrowest leaf that supplies their API.

The historical `NumStability.Algorithms` aggregate replaces 28 direct family
imports with this one umbrella. Its exact complete-surface contract is
preserved while its direct-import count falls from 490 to 463 (27 fewer).

## Tests

The import smoke test checks declarations from the core specification, the
Chapter 16 problem layer, and the rounded Hessenberg solver. The layout gate
also requires the aggregate to import every current family leaf, so adding a
new leaf without updating the umbrella fails CI.

## Evidence

- Starting revision: `11a5241c7496851a8653080f30d39182c4eeb4d4`.
- Final Sylvester, public-entry-point, aggregate-contract, and full-suite
  evidence is recorded in
  [`2026-07-22-organization.md`](2026-07-22-organization.md).
