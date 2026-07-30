# Chapter 9 closure-tail D1 migration

D1 implements four dependency-closed layer-10 destinations from the frozen
closure-tail contract at `e49bd2f3`.  It moves exactly 189 format-2
declarations in 141 compiler-command groups:

| Destination | Layer | Declarations | Commands | Private | Frozen imports |
| --- | ---: | ---: | ---: | ---: | ---: |
| `Chapter09.CompletePivotSharpClosure` | 10 | 25 | 14 | 0 | 31 |
| `Chapter09.ComplexClosure` | 10 | 100 | 74 | 0 | 32 |
| `Chapter09.Theorem97Classification` | 10 | 38 | 27 | 0 | 31 |
| `Chapter09.Theorem99Closure` | 10 | 26 | 26 | 0 | 31 |

Every destination is generated from hash-pinned packet command spans; the
154,613 bytes and 3,327 lines of routed command payload are unchanged.  The
four frozen owner modules are now one-target, declaration-free compatibility
wrappers.  Canonical-only and historical-import-only smoke tests cover every
destination, and `NumStabilityTest.Worker.Ch09.WaveD1` is the lane-local
aggregate.

The normalized D1 incident-graph fingerprint is
`18D4D860976054EC0BF654937DE0EC779AF684D1E2D4C6BF783710F4C793354D`,
covering 691 signature, 1,088 body/proof, and 943 internal typed edges.

## Build-independent evidence

The following gates pass:

- deterministic closure-tail pre-check and through-D1 materialized-text check;
- exact 189-declaration, 141-command, zero-private, import, owner, source-span,
  and command-hash coverage;
- deterministic A--C precursor comparison and the full 4,420-row proposal
  hashes inherited by the tail contract;
- strict source/import graph generation, including cycles and
  reusable-to-source reachability;
- provenance contract: 207 Apache-marked production files and five evidenced
  upstream modules;
- compatibility contract, checker self-test, Python compilation, worker scope
  allowlist, and `git diff --check`.

The layout checker reports only integrator-owned registration and baseline
work: the Chapter 9 worker tests are not yet in the shared test root; these
four leaves and earlier leaves are not yet in the shared source root; the
reviewed `Theorem914Primitive` naming exception is not yet installed; and the
resolved wrapper-docstring debt needs a baseline ratchet.  This lane does not
edit those shared files.

## Explicitly deferred compiler gates

No Lean command or build mutex was used.  Focused and isolated imports, fresh
candidate format-2 extraction, `.ilean` command re-hashes, semantic stage
comparison, axiom probes, and the global `NumStability NumStabilityTest` build
remain mandatory integrator gates.
