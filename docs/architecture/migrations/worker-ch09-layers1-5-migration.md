# Chapter 9 destination-DAG layers 1--5 migration

This local worker wave implements the first five dependency layers of the
reviewed Chapter 9 contract.  It starts from remote-main commit
`32771e355612a6fca1b6153733d3f0dc124d26e2`; the separate frozen-contract
commit is `cbb47b7c`.  The worker did not push, merge, edit a shared root or
manifest, acquire the Lean build mutex, or claim a Lean build result.

## Materialized surface

Eight canonical source-correspondence modules now own exactly 1,675 format-2
declarations in 1,494 compiler-backed source-command groups:

| Layer | Destination | Declarations | Commands |
| --- | --- | ---: | ---: |
| 1 | `Chapter09.Section01` | 22 | 22 |
| 1 | `Chapter09.Theorem914Primitive` | 27 | 27 |
| 2 | `Chapter09.Section02` | 334 | 259 |
| 3 | `Chapter09.ComputedCorrection` | 6 | 6 |
| 3 | `Chapter09.Section03` | 41 | 41 |
| 3 | `Chapter09.Section04` | 498 | 414 |
| 4 | `Chapter09.Section05` | 163 | 141 |
| 5 | `Chapter09.Section06` | 584 | 584 |

Every destination is generated from the hash-pinned packet command spans;
proof and declaration text is not rewritten.  Ten authored private helpers
have explicit destination-qualified names.  The deterministic text gate
reconstructs every canonical file and the residual historical file exactly.

`HighamChapter9Theorem914Primitive` and
`HighamChapter9ComputedCorrection` are now documented import-only wrappers.
The giant `HighamChapter9` owner remains declaration-bearing for the unstarted
layers, but the 1,461 selected giant-owner commands are absent and its six new
canonical section imports are present.  This is the intended partial-wave
compatibility shape; old imports still expose every moved public declaration.

Eight canonical-only tests each import one canonical destination.  Three
old-only tests each import one historical owner, including a six-declaration
probe of the partial giant owner.  Their worker aggregate is
`NumStabilityTest.Worker.Ch09.Layers1To5`; no shared test root was edited.

## Static and semantic contract evidence

The following build-independent gates passed in the worker tree:

- checker negative self-test and Python compilation;
- full 4,420-row Chapter 9 proposal pre-check;
- layers 1--5 pre-check: 8 destinations, 3 owners, 1,675 declarations,
  1,494 command groups, and 10 private rewrites;
- deterministic materialized-text comparison of all 23 generated/changed
  production and test outputs;
- frozen evidence/base check for all eleven candidate production modules;
- strict source/import graph generation, including cycle and
  reusable-to-source reachability checks;
- compatibility check: 119 forwarding modules and 228 canonical targets;
- provenance check: 207 Apache-marked production files and five evidenced
  upstream modules;
- `git diff --check`, worker-path allowlist, and zero forbidden shared paths.

The immutable packet graph has 11,393 signature and 14,167 body/proof edges
incident to the wave, including 8,966 internal typed edges.  Its canonical
normalized fingerprint is
`1A2852BF745EBD6633E9F99B332ACA4F22401141CD3A08032497B3DA4C932E2A`.
The stage checker normalizes the ten moved private names and stable suffixes of
incident external private helpers, rejecting suffix collisions, then requires
exact equality of the complete incident graph.  After compilation it also
re-hashes all 1,494 commands through the candidate `.ilean` spans and rejects
any uncontracted destination declaration.

## Explicitly deferred Lean gates

No worker Lean build was run.  This is **deferred to the integrator, not
passed**: the new worktree had no warm `.lake` tree, and the coordinator gave
QR Q2A priority on the named build mutex.  Consequently there is not yet a
fresh candidate format-2 stream, a stage-mode semantic pass, a focused
canonical/compatibility build, an axiom probe, or a global build result for
this implementation.

After applying the shared patches below in a warm integration tree, the
integrator must run, under the named mutex:

1. a focused build of all eight canonical destinations and all three
   historical owners;
2. all eight canonical-only and three old-only tests as explicit targets;
3. `lake env lean --run tools/architecture/declaration_dependencies.lean
   <candidate.tsv>` after the production build;
4. `check_ch09_layers1_5.py --mode stage` with the immutable packet archive
   and that fresh candidate stream;
5. representative axiom probes, the architecture gates, and the full
   `NumStability NumStabilityTest` build.

## Exact shared integrator patch request

The worker intentionally did not edit the following shared files.

1. Add this test registration to `NumStabilityTest.lean`:

   `import NumStabilityTest.Worker.Ch09.Layers1To5`

2. Register the eight leaves in sorted Chapter 9 position in
   `NumStability/Source/Higham.lean`:

   - `NumStability.Source.Higham.Chapter09.ComputedCorrection`
   - `NumStability.Source.Higham.Chapter09.Section01`
   - `NumStability.Source.Higham.Chapter09.Section02`
   - `NumStability.Source.Higham.Chapter09.Section03`
   - `NumStability.Source.Higham.Chapter09.Section04`
   - `NumStability.Source.Higham.Chapter09.Section05`
   - `NumStability.Source.Higham.Chapter09.Section06`
   - `NumStability.Source.Higham.Chapter09.Theorem914Primitive`

3. Add `NumStability.Source.Higham.Chapter09.Theorem914Primitive` to the
   sorted reviewed `legacy.noncanonical_modules` list in
   `docs/architecture/layout-exceptions.json`.  The name is frozen by the
   reviewed Chapter 9 proposal; the worker did not silently rename it.

4. Add these forwarding rows to `docs/architecture/COMPATIBILITY.md`:

   - `NumStability.Algorithms.HighamChapter9ComputedCorrection` ->
     `NumStability.Source.Higham.Chapter09.ComputedCorrection`
   - `NumStability.Algorithms.HighamChapter9Theorem914Primitive` ->
     `NumStability.Source.Higham.Chapter09.Theorem914Primitive`

Before those shared patches, `check_layout.py` reports only the expected
worker-registration set: the 12 unreachable worker tests, the one reviewed
noncanonical destination, and the two source descendants not already reached
by the curated source roots.  Wrapper documentation, module documentation,
cycles, mixed modules, placeholders, aggregate sorting, and production root
reachability introduce no additional layout regression.
