# R0010 / W07 integration review

Status: **CURRENT**. This record reviews the W07 shared-file request against
accepted checkpoint C0007 and the joint W07/W10 integration tree.

## Immutable inputs

- target checkpoint: C0007
- target code SHA: `9eb534a06db267203c2b9b88227edd44fc64f5db`
- immutable W07 delivery: `176c72838828795b89f4aa822479010c7860c8e5`
- branch record / projection: B0011 / P0012
- request patch: `R0010.patch`
- patch size: 187,896 bytes
- patch hunks: 25
- patch SHA-256: `E05687DC8959C8B3B24DE30E996553A780839CB2C501D5A0BBBF6A39B40BF425`

The patch is independently forward- and reverse-applicable to the exact six
C0007 preimages recorded by R0010. It adds nine reusable stationary-iteration
imports to `Algorithms/LinearSystems.lean`, 25 Chapter 17 source imports to
`Source/Higham/Chapter17.lean`, the 48-test W07 aggregate and root-test import,
and the reviewed tier/layout changes. It does not contain worker-owned source
or test-leaf changes.

## Scope and preservation review

- W07 delivery scope is 103 paths: five exact owners, 34 new production
  modules, 48 new tests, and 16 evidence files.
- P0012 replays exactly 252 selected declarations, 136 relocated and 116
  retained, with 800 signature, 1,400 body/proof, and 1,474 union edges.
- The selected-induced private reverse-closure floor remains 31 = 8 private +
  23 public; no private declaration moved or changed visibility.
- Historical imports and all five historical public surfaces remain available.
- The W06 protected semiconvergence consumers remain unchanged.

## Joint overlap decision

R0010 intersects R0011 on exactly three paths:

1. `NumStabilityTest.lean`
2. `docs/architecture/layout-exceptions.json`
3. `docs/architecture/tiers.json`

The integrated tree uses a reviewed union, never sequential whole-postimage
replacement. The root test imports both W07 and W10 aggregates. The tier union
contains all W07 classifications plus all W10 classifications and aggregate
entries. The layout union performs both debt reductions and preserves both
sets of reviewed exceptions. All other R0010 and R0011 paths are disjoint.

The joint postimage has 1,417 exact tier entries and 24 prefix rules. Its layout
contract has 277 unclassified modules, 45 mixed modules, 72 missing module
docstrings, 268 noncanonical modules, 27 declaration-bearing umbrellas, and
zero unsorted aggregates. Compatibility, provenance, strict-source, and both
forbidden-reachability audits remain mandatory before the code commit.
