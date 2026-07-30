# Chapter 9 wave B migration

Wave B implements destination-DAG layer 8 from the frozen A/B/C contract.  It
moves exactly 1,109 public format-2 declarations, each in its own
compiler-command group, into
`NumStability.Source.Higham.Chapter09.Section11`.

The generated canonical source contains 30 frozen imports: the 27 direct
non-Chapter-9 imports inherited from the reviewed giant-owner base plus exact
dependencies on `Section02`, `Section04`, and wave-A `Section10`.  Its 1,953,693
bytes of routed command payload are copied without rewriting.

The historical `HighamChapter9` file remains a deliberate partial owner after
this slice.  All giant-owner destinations through `Section11` are imported
canonically, and only the 1,212 declarations/1,140 commands routed to
`Problems` remain declaration-bearing.  The isolated giant old-only test now
checks one public root from each of its nine materialized destinations.
`NumStabilityTest.Worker.Ch09.WaveB` imports only the new canonical test and
that isolated historical test.

## Build-independent evidence

The A/B/C checker deterministically reconstructs all prior output plus this
slice and reports 1,175 cumulative declarations in 1,164 command groups across
waves A--B.  Wave B itself has the normalized incident fingerprint
`EA7B097EA96D43230726592D672714F58224A80EAAC56DDA6BAA261ED2070B96`,
with 5,458 signature, 6,816 body/proof, and 3,602 internal typed edges.

The following build-independent gates pass:

- A/B/C contract and full Chapter 9 proposal pre-checks;
- deterministic materialized-text comparison and source-command hashes;
- worker scope allowlist and `git diff --check`;
- strict source/import graph, including cycle and reusable-to-source checks;
- compatibility and provenance contracts.

Shared root/test registration and reviewed layout-baseline updates remain
integrator-owned.  No shared root, tier, layout, compatibility map, QR, LSQ,
or Chapter 11 path was edited.

## Explicitly deferred compiler gates

No Lean command or build mutex was used.  Focused and isolated import builds,
fresh format-2 extraction, `.ilean` command re-hashing, semantic stage
comparison, axiom probes, and the full `NumStability NumStabilityTest` build
remain mandatory integrator gates.
