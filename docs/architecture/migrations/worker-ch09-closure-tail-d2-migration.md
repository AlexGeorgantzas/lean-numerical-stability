# Chapter 9 closure-tail D2 migration

D2 implements the separately reviewable layer-10
`NumStability.Source.Higham.Chapter09.Theorem914Actual` destination.  It moves
exactly 127 format-2 declarations in 127 compiler-command groups from
`NumStability.Algorithms.HighamChapter9Theorem914Actual`.

The destination has four frozen imports, including its earlier
`Theorem914Primitive` dependency.  Its 143,456 bytes and 3,253 lines of routed
command payload are copied from hash-pinned packet spans without edits.
Eleven authored helpers remain private; their compiler-generated names change
only by the frozen owner-module prefix, and the dependency graph proves none
has a cross-destination consumer.

The historical owner is now a one-target declaration-free compatibility
wrapper.  A canonical-only smoke test, historical-import-only smoke test, and
lane-local `NumStabilityTest.Worker.Ch09.WaveD2` aggregate cover the cutover.

The normalized D2 incident-graph fingerprint is
`7F2E149BA7E9C07423D766F62A9DEDB5F0D97E364382B110C628D452648D3001`,
covering 533 signature, 1,030 body/proof, and 469 internal typed edges.

## Build-independent evidence

The following gates pass:

- deterministic closure-tail pre-check and through-D2 materialized-text check;
- cumulative 316-declaration, 268-command, 12-private tail coverage through
  D2, with exact import, owner, source-span, and command-hash contracts;
- strict source/import graph generation, including cycles and
  reusable-to-source reachability;
- provenance and compatibility contracts;
- checker self-test, Python compilation, worker scope allowlist, and
  `git diff --check`.

The layout checker remains red only for integrator-owned shared registration,
naming-exception, classification, and baseline-ratchet work.  This lane does
not modify shared roots or architecture manifests.

## Explicitly deferred compiler gates

No Lean command or build mutex was used.  Focused and isolated imports, fresh
candidate format-2 extraction, `.ilean` command re-hashes, semantic stage
comparison, axiom probes, and the global `NumStability NumStabilityTest` build
remain mandatory integrator gates.
