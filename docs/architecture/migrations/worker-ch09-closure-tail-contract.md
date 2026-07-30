# Chapter 9 closure-tail contract

This contract freezes the final dependency-ordered Chapter 9 source migration
before any D1, D2, or E declaration is moved.  The implementation base is
`bf8e44907610405eb5fbed51226671d39cf10dcf`, after waves A--C.  Exact
compiler-command bytes remain pinned to packet revision
`6487fc33088523b8f27ecde9ad613515b78f9977`.

## Frozen sequence

| Wave | Destination(s) | Declarations | Command groups | Private |
| --- | --- | ---: | ---: | ---: |
| D1 | `CompletePivotSharpClosure`, `ComplexClosure`, `Theorem97Classification`, `Theorem99Closure` | 189 | 141 | 0 |
| D2 | `Theorem914Actual` | 127 | 127 | 11 |
| E | `Theorem914DiagDominant`, `Theorem99ComplexClosure` | 42 | 42 | 1 |
| **Total** | **7 destinations** | **358** | **310** | **12** |

D1 is dependency-closed over the already materialized `Problems` destination.
D2 is separately reviewable and depends on the earlier
`Theorem914Primitive` destination.  E is last because its two destinations
depend on parents materialized in D1 and D2.  The exact normalized
incident-graph fingerprints are:

- D1: `18D4D860976054EC0BF654937DE0EC779AF684D1E2D4C6BF783710F4C793354D`;
- D2: `7F2E149BA7E9C07423D766F62A9DEDB5F0D97E364382B110C628D452648D3001`;
- E: `596AA5E23202542BBA17E31263FED8DF97632CECF355209B32699346AA568D4E`.

The checker independently reproduces the audited signature/body/internal
edge counts of `691/1088/943`, `533/1030/469`, and `102/236/119`,
respectively.  It rejects any cross-destination consumer of a private helper;
none exists in the frozen graph.

## Import, compatibility, and completion policy

Each canonical destination receives only its frozen direct imports and exact
earlier destination-DAG dependencies, for 135 import rows.  No canonical
destination may import a historical Chapter 9 owner.  Each of the seven
remaining historical owners becomes a one-target declaration-free wrapper.
Every destination receives a canonical-only test and an old-import-only test;
each wave also receives a worker aggregate.

After E, the checker must reconcile all 20 canonical destinations, all 4,420
declarations, all 4,108 compiler-command groups, and all 28 private
declarations.  It must also prove all 11 historical Chapter 9 owners are
declaration-free structural import facades.

## Evidence and deferred gates

The full 4,420-row Chapter 9 proposal, the A--C precursor, and this tail
contract pass against the immutable format-2 archive with SHA-256
`1C2538B428B8EC3610B3C09BBB6A4CF23ECA9F0DB17EE4AE5B63E4F371AECDED`.
The checker self-test, deterministic artifact generation, private-boundary
check, and Python compilation also pass.

No Lean build, `.ilean` command re-hash, candidate format-2 extraction, stage
comparison, axiom probe, or global build is claimed by this contract commit.
Those gates remain mandatory for the integrator under the named build mutex.
No shared root, tier, layout exception, compatibility map, QR, least-squares,
or Chapter 11 path is owned by this worker sequence.
