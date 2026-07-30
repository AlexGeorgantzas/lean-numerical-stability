# Chapter 9 closure-tail E migration

Wave E implements the final two layer-11 Chapter 9 destinations after their
D1 and D2 parents:

| Destination | Layer | Declarations | Commands | Private | Frozen imports |
| --- | ---: | ---: | ---: | ---: | ---: |
| `Chapter09.Theorem914DiagDominant` | 11 | 2 | 2 | 0 | 4 |
| `Chapter09.Theorem99ComplexClosure` | 11 | 40 | 40 | 1 | 2 |

The 58,124 bytes and 1,300 lines of routed command payload are copied from
hash-pinned packet spans without edits.  The one private complex-closure
helper keeps private visibility and changes only its frozen owner-module
prefix.  The graph proves it has no cross-destination consumer.

Both historical owners are now exact one-target declaration-free wrappers.
Canonical-only and historical-import-only smoke tests cover both destinations,
and `NumStabilityTest.Worker.Ch09.WaveE` is the lane-local aggregate.  The
normalized E incident-graph fingerprint is
`596AA5E23202542BBA17E31263FED8DF97632CECF355209B32699346AA568D4E`,
covering 102 signature, 236 body/proof, and 119 internal typed edges.

## Complete Chapter 9 reconciliation

The cumulative checker now proves:

| Property | Exact result |
| --- | ---: |
| Canonical destinations | 20 |
| Declarations | 4,420 |
| Compiler-command groups | 4,108 |
| Private declarations | 28 |
| Declaration-free historical owners | 11 |

The closure tail itself accounts for 358 declarations in 310 command groups,
with 12 private declarations.  Every declaration and command group from the
immutable Chapter 9 proposal now has one canonical destination.  All eleven
historical owners contain only imports, comments, and whitespace.

## Build-independent evidence

The following gates pass:

- deterministic through-E materialized-text check and complete Chapter 9
  reconciliation;
- exact declaration, command-group, private-rewrite, import, owner,
  source-span, command-hash, and normalized dependency-graph contracts;
- strict source/import graph generation, including cycles and
  reusable-to-source reachability;
- provenance contract: 207 Apache-marked production files and five evidenced
  upstream modules;
- compatibility contract, checker self-test, Python compilation, worker scope
  allowlist, and `git diff --check`.

No Lean command or build mutex was used.  Focused and isolated imports, fresh
candidate format-2 extraction, `.ilean` command re-hashes, semantic stage
comparison, axiom probes, and the global `NumStability NumStabilityTest` build
remain mandatory integrator gates.

## Exact shared integrator request

This worker intentionally did not edit shared files.  The integrator should:

1. register all twenty canonical leaves in sorted order in
   `NumStability/Source/Higham.lean`: `CompletePivotSharpClosure`,
   `ComplexClosure`, `ComputedCorrection`, `DoolittleClosure`, `Problems`,
   `Section01`, `Section02`, `Section03`, `Section04`, `Section05`,
   `Section06`, `Section08`, `Section10`, `Section11`, `Theorem914Actual`,
   `Theorem914DiagDominant`, `Theorem914Primitive`,
   `Theorem97Classification`, `Theorem99Closure`, and
   `Theorem99ComplexClosure`;
2. register `NumStabilityTest.Worker.Ch09.Layers1To5`, `WaveA`, `WaveB`,
   `WaveC`, `WaveD1`, `WaveD2`, and `WaveE` in `NumStabilityTest.lean`;
3. document the ten-target `HighamChapter9` facade and the ten one-target
   historical wrappers in `docs/architecture/COMPATIBILITY.md`;
4. classify all eleven historical owner paths as compatibility modules and
   ratchet the resolved unclassified, canonical-reachability, worker-test,
   and module-docstring layout debt;
5. add reviewed canonical naming exceptions for `Theorem914Primitive`,
   `Theorem914Actual`, and `Theorem914DiagDominant`.

The ten one-target wrappers are `HighamChapter9ComputedCorrection`,
`HighamChapter9DoolittleClosure`, `HighamChapter9Theorem914Primitive`,
`HighamChapter9CompletePivotSharpClosure`, `HighamChapter9ComplexClosure`,
`HighamChapter9Theorem97Classification`, `HighamChapter9Theorem99Closure`,
`HighamChapter9Theorem914Actual`, `HighamChapter9Theorem914DiagDominant`, and
`HighamChapter9Theorem99ComplexClosure`.  The historical
`NumStability.Algorithms` root must retain its wrapper imports for public-import
compatibility.
