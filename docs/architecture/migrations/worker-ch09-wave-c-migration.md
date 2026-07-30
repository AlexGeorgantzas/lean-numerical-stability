# Chapter 9 wave C migration

Wave C implements destination-DAG layer 9 and completes the giant Chapter 9
owner cutover.  It moves exactly 1,212 format-2 declarations in 1,140
compiler-command groups into
`NumStability.Source.Higham.Chapter09.Problems`.  Five authored helpers remain
private under their destination-qualified compiled names; the frozen graph has
no cross-destination consumer of any of them.

The canonical module has 34 frozen imports: the reviewed 27 non-Chapter-9
direct imports plus exact dependencies on `Section01`, `Section02`,
`Section03`, `Section04`, `Section05`, `Section06`, and wave-B `Section11`.
Its 1,519,842 bytes of routed command payload are byte-preserved.

`NumStability.Algorithms.HighamChapter9` is now a declaration-free
compatibility facade importing the ten canonical destinations that own its
former 3,998 declarations.  Its isolated old-only test imports only that
historical path and checks one public root from every target.  A canonical-only
`Problems` test and lane-local `NumStabilityTest.Worker.Ch09.WaveC` aggregate
complete this slice.

## Reconciliation

Waves A--C account for exactly 2,387 declarations, 2,304 command groups, and
six private declarations in five destinations.  Together with the prior
layers-1--5 migration, Chapter 9 now has 4,062 of 4,420 declarations and 3,798
of 4,108 command groups physically materialized.  The remaining closure tail
is 358 declarations in 310 command groups.

Wave C has normalized incident fingerprint
`C6C5041485BE4E94EF56F9AF1ED6F2CD4C3DE39111DF8AC8C91F918AEE06A13A`,
covering 6,180 signature, 8,510 body/proof, and 4,695 internal typed edges.

## Build-independent evidence

The following gates pass:

- full 4,420-row Chapter 9 proposal pre-check;
- deterministic A/B/C contract and through-C materialized-text comparison;
- exact declaration, command-group, private-rewrite, import, owner, source-span,
  and command-hash coverage;
- worker path allowlist and `git diff --check`;
- strict source/import graph, including cycle and reusable-to-source checks;
- compatibility and provenance contracts;
- checker self-test and Python compilation.

No Lean command or build mutex was used.  Focused builds, isolated canonical
and old import builds, fresh format-2 extraction, `.ilean` command re-hashes,
semantic stage comparison, axiom probes, and the full
`NumStability NumStabilityTest` build remain mandatory integrator gates.

## Exact shared integrator request

This worker intentionally did not edit shared files.  The integrator should:

1. register these thirteen leaves in sorted order in
   `NumStability/Source/Higham.lean`: `ComputedCorrection`,
   `DoolittleClosure`, `Problems`, `Section01`, `Section02`, `Section03`,
   `Section04`, `Section05`, `Section06`, `Section08`, `Section10`,
   `Section11`, and `Theorem914Primitive`;
2. register `NumStabilityTest.Worker.Ch09.Layers1To5`, `WaveA`, `WaveB`, and
   `WaveC` in `NumStabilityTest.lean`;
3. document the exact one-target wrappers for `HighamChapter9ComputedCorrection`,
   `HighamChapter9DoolittleClosure`, and `HighamChapter9Theorem914Primitive`,
   plus the ten-target `HighamChapter9` facade, in
   `docs/architecture/COMPATIBILITY.md`;
4. classify those four historical paths as compatibility modules and ratchet
   the corresponding unclassified/noncanonical layout debt;
5. add the already reviewed canonical naming exception for
   `NumStability.Source.Higham.Chapter09.Theorem914Primitive` and ratchet the
   resolved Doolittle wrapper module-docstring debt.

The historical `NumStability.Algorithms` root should retain its wrapper imports
for compatibility.  Narrow production-consumer import normalization remains a
separate integrator/Chapter-11-lane task.  With `Problems` canonicalized, all
61 frozen Chapter 11 dependency rows now have canonical Chapter 9 endpoints;
the remaining Chapter 9 closure tail does not block Chapter 11.
