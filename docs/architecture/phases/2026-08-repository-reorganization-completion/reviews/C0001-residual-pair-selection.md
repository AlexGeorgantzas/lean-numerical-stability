# C0001 residual debt and successor-pair selection

Authority: `primary-human`

Base checkpoint: C0001 at code commit
`117aa2bb7e61f41e1531a78452f9f7f6cd5b0771`.

The clean C0001 inventory contains 2,631 production modules. Its exact residual
metrics are 277 unclassified modules, 9 mixed modules, 72 missing module
docstrings, 244 noncanonical modules, 21 declaration-bearing umbrellas, and
zero unsorted aggregate imports. There are 423 distinct rows carrying at least
one residual debt flag. The checkpoint inventory contains 2,183
`already_complete` rows and 448 remaining `in_scope` rows. These values were
recomputed from C0001; they are not copied from the C0000 projection.

The final repository gates therefore remain incomplete. Architecture, build
profiles, compatibility, documentation currency, entrypoint reachability,
forbidden reachability, full build, full tests, generated-artifact hygiene, and
provenance pass. Canonical layout, classification completeness, module
documentation, and outlier review remain open.

## Dependency-ready roots

After M01 and M02 were accepted, the frozen milestone DAG leaves M03/R03,
M07/R07, M11/R11, and M12/R12 dependency-ready. R08, R09, and R10 remain
blocked by their recorded predecessor milestones, so selecting them would
silently violate the reviewed DAG. R11 is the first eligible item in the
requested preference order.

Every full pair among the four ready roots was recomputed from the exact C0001
format-2 declaration graph and current module-import graph. R11/R12 is the only
pair with zero owner or ancestor overlap, zero declaration overlap, zero
signature and body edges in either direction, zero direct imports in either
direction, zero transitive owner-reachability pairs in either direction, zero
shared direct outside-module consumers, zero shared external declaration
consumers, and zero common direct project dependencies. Other ready pairs fail
at least one of these graph-independence conditions. In particular R11/R03 has
1,267 signature and 1,357 body edges from R11 to R03 and 185 transitive owner
pairs in that direction.

R11 freezes 65 owners and 1,477 declarations. R12 freezes 3 owners and 34
declarations. Their planned destinations are casefold-vacant at exact C0001,
and the two destination sets are equal-or-ancestor disjoint. The only planned
shared-request intersection is the reviewed integrator-owned union of
`NumStabilityTest.lean`, `docs/architecture/tiers.json`, and
`docs/architecture/layout-exceptions.json`; it does not weaken worker path
disjointness.

R0003 also reserves 129 exact production import consumers for the R11 cutover.
Ten are future R05 owners and one is a future R09 owner. This is an
import-token-only integrator change, not execution of those modules' residual
actions. Shared ownership is explicitly live-request scoped: C0002 must refresh
their preimages/projections and release those 11 paths after R0003 is applied,
before either later owner wave is activated.

The immutable scope assigns both R11 and R12 to `claude-lane`. Concurrent
operation therefore keeps both branch `lane_id` values unchanged and uses the
separately reviewed, temporary `codex-local` authorization for B0004 only. The
authorization expires when the pair is terminal at C0002.
