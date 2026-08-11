# R0011 / W10 integration review

Status: **CURRENT**. This record reviews the corrected W10 shared-file request
against accepted checkpoint C0007 and the joint W07/W10 integration tree.

## Immutable inputs

- target checkpoint: C0007
- target code SHA: `9eb534a06db267203c2b9b88227edd44fc64f5db`
- immutable corrected W10 delivery: `9e7604cbdbd2314bc4bf38bcd9e342c3accfb1d6`
- corrected delivery parent: `fe71de444ee0bc83ba85bdbabcbd95391d47342c`
- branch record / projection: B0012 / P0013
- request patch: `R0011.patch`
- formal request patch size: 33,353 bytes
- formal request patch hunks: 25 zero-context hunks across 13 paths
- formal request patch SHA-256: `71D9BD0B68C82848DAD3EBA4260A3F81FC4EF302524A68D14A449332BDA97F7A`
- immutable worker-request patch: 34,111 bytes, 14 paths, SHA-256
  `6AA9A9070BDA882DB9AA482D695F74CB15C9379BB8147B52F89BDB05CD4AA97C`

The patch is independently forward- and reverse-applicable with
`git apply --unidiff-zero` to its exact C0007 preimages. Its deterministic
constructor reproduces identical postimages. It creates the PNorm, Boyd,
TwoNorm/Dixon, Chapter 15, and W10 test aggregates; updates the existing
NormEstimation, Higham, and root-test discovery files; and applies the
reviewed tier/layout changes. It does not alter accepted consumers or the
historical root aggregate.

The immutable worker request also updates
`NumStability/Algorithms/NormEstimation/OneNorm/All.lean`. That file is an
accepted W06 destination beneath B0006's frozen OneNorm destination prefix.
Phase schema version 1 correctly forbids reclassifying it as integrator-owned
shared state, so the formal R0011 patch excludes that one section. Its exact
worker-requested postimage is preserved in the integrated tree as an explicit
W06/W10 integration overlap. This is not a waiver: the 13-path formal patch
still replays independently, the excluded postimage is byte-reviewed against
the immutable 14-path packet, and all W06 protected-surface tests remain
mandatory.

## Scope and preservation review

- Corrected W10 delivery scope is 274 paths: 27 exact owners, 96 new
  production modules, 135 new tests, and 16 evidence files.
- P0013 replays exactly 1,029 selected declarations, 895 relocated and 134
  retained, with 2,394 signature, 4,844 body/proof, and 5,075 union edges.
- The selected-induced private floor remains 132 = 80 private + 52 public;
  two additional reviewed full-graph re-entry declarations are retained at
  their exact historical owner without changing the frozen graph.
- `Algorithms.CondEstimation` is reusable in place and has no Source reachability.
- All 96 canonical modules have zero reachability to the other historical W10
  owners; the accepted W06 and W09 surfaces remain unchanged.

## Joint overlap decision

R0011 intersects R0010 on exactly three paths:

1. `NumStabilityTest.lean`
2. `docs/architecture/layout-exceptions.json`
3. `docs/architecture/tiers.json`

The integrated tree uses a reviewed union, never sequential whole-postimage
replacement. The root test imports both W07 and W10 aggregates. The tier union
contains all W10 classifications and aggregate entries plus the complete W07
classification delta. The layout union performs both debt reductions and
preserves both reviewed exception sets. All other request paths are disjoint.

The joint postimage has 1,417 exact tier entries and 24 prefix rules. Its layout
contract has 277 unclassified modules, 45 mixed modules, 72 missing module
docstrings, 268 noncanonical modules, 27 declaration-bearing umbrellas, and
zero unsorted aggregates. Compatibility, provenance, strict-source, exact
P0012/P0013 replay, and the complete Lean build/test matrix remain mandatory
before the code commit.
