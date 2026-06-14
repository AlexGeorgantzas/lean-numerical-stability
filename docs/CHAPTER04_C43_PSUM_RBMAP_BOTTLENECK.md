# Chapter 4 C4.3 Psum Native RBMap Bottleneck

This file tracks the red C4.3 bottleneck: closing Higham pp. 90--91's concrete
`O(n log n)` Psum implementation claim for duplicate active values with a
native counted `RBMap` loop.

## Target

Paper-level target: instantiate the ordered-neighbor/log-search Psum selector
with a concrete balanced search tree, including duplicate-aware deletion,
balance-backed per-step cost, recursive termination, and a full
`PsumMinOrderFrom`/log-cost trace.

Closed theorem family:

- `PsumCountRBMap.nativeOrderFromFuel` and
  `PsumCountRBMap.nativeOrderFrom` define the executable recursive counted-map
  Psum loop over a native `RBMap`.
- `PsumCountRBMap.entryStep_of_stepNative` proves each native
  selector/decrement step realizes `PsumCountRBMap.EntryStep`.
- `PsumCountRBMap.nativeOrderFrom_entryLogSearchTrace`,
  `PsumCountRBMap.nativeOrderFrom_minTrace`,
  `PsumCountRBMap.nativeOrderFrom_perm`, and
  `PsumCountRBMap.nativeOrderCostFrom_le_budget` compose the native steps into
  the existing counted-entry trace and `psumLogSearchComparisonBudget` bound.

## Dependency Checklist

| Dependency | Status | Lean surface |
|---|---|---|
| Ordered-neighbor correctness for predecessor/successor around `-acc` | closed | `PsumLowerNeighbor`, `PsumUpperNeighbor`, `psumNeighborChoice_mem_and_min` |
| Concrete red-black lower/upper-bound selector correctness | closed | `PsumRBSet.lowerBound_neighbor`, `PsumRBSet.upperBound_neighbor`, `PsumCountRBMap.lowerBound_neighbor`, `PsumCountRBMap.upperBound_neighbor`, `PsumCountRBMap.neighborSelect_mem_and_min` |
| Duplicate-aware counted-entry deletion bridge | closed | `psumCountEntriesEraseOne_perm`, `psumCountEntriesEraseOne_length` |
| Positive-count invariant for counted-entry deletion | closed | `psumCountEntriesEraseOne_preserves_positive`, `PsumCountRBMap.stepEntries_preserves_positive_entries` |
| Balance/depth step budget | closed | `PsumCountRBMap.depth_succ_le_stepBudget` |
| Certified counted-entry one-step package | closed | `PsumCountRBMap.stepEntries_certifies`, `PsumCountRBMap.entryStep_of_stepEntries` |
| Recursive counted-entry trace composition | closed | `PsumCountRBMap.EntryLogSearchTraceFrom.minTrace`, `.perm`, `.cost_le_budget` |
| Native red-black delete traversal substrate | closed | `rbNode_append_toList`, `rbNodePath_del_toList` |
| Comparator equality for native key lookup | closed | `psumRealCmp_eq_eq` |
| Native `RBMap.alter` decrement/delete branch traversal | closed | `PsumCountRBMap.eraseOneNative`, `PsumCountRBMap.eraseOneNativeBranchList`, `PsumCountRBMap.eraseOneNative_toList_of_zoom` |
| Lift active-list membership/native lookup to the exact native zoom branch | closed | `PsumCountRBMap.find?_some_of_mem_toList`, `PsumCountRBMap.exists_find?_of_mem_activeList`, `PsumCountRBMap.find?_some_zoom`, `PsumCountRBMap.eraseOneNative_toList_of_find?`, `PsumCountRBMap.eraseOneNative_toList_of_mem_activeList` |
| Native next-map active-list deletion bridge | closed | `PsumCountRBMap.eraseOneNative_activeList_perm`, `PsumCountRBMap.eraseOneNative_activeList_length`, `PsumCountRBMap.stepNative_decreases_activeList_length` |
| Native next-map positive-count invariant | closed | `PsumCountRBMap.eraseOneNative_preserves_positive`, `PsumCountRBMap.stepNative_preserves_positive` |
| Executable recursive native loop | closed | `PsumCountRBMap.stepNative`, `PsumCountRBMap.stepNative_eq_none_iff_activeList_eq_nil`, `PsumCountRBMap.nativeOrderFromFuel`, `PsumCountRBMap.nativeOrderCostFromFuel`, `PsumCountRBMap.nativeOrderFromFuel_entryLogSearchTrace`, `PsumCountRBMap.nativeOrderFrom`, `PsumCountRBMap.nativeOrderCostFrom`, `PsumCountRBMap.nativeOrderFrom_entryLogSearchTrace`, `PsumCountRBMap.nativeOrderFrom_minTrace`, `PsumCountRBMap.nativeOrderFrom_perm`, `PsumCountRBMap.nativeOrderCostFrom_le_budget` |

## Closure Evidence

The previously open native-update target is closed by the theorem family shaped
like:

```lean
PositiveCounts t ->
selected ∈ activeList t ->
selected :: activeList (eraseOneNative t selected) ~ activeList t

PositiveCounts t ->
selected ∈ activeList t ->
PositiveCounts (eraseOneNative t selected)
```

These are implemented by `PsumCountRBMap.eraseOneNative_activeList_perm` and
`PsumCountRBMap.eraseOneNative_preserves_positive`.  The recursive native loop
then uses `PsumCountRBMap.stepNative_decreases_activeList_length` as its measure
fact and `PsumCountRBMap.stepNative_preserves_positive` as its invariant step.
The final executable trace surface is
`PsumCountRBMap.nativeOrderFrom_entryLogSearchTrace`, with extensional Psum
minimality and budget corollaries supplied by
`PsumCountRBMap.nativeOrderFrom_minTrace` and
`PsumCountRBMap.nativeOrderCostFrom_le_budget`.
