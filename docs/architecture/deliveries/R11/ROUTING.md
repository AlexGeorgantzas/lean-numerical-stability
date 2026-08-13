# R11 routing

R11 executes the frozen B0003 whole-owner block route over 65 C0001 owners holding
1,477 declarations. The route was not designed here; it was read from
`branches/B0003-declaration-routes.tsv` and `branches/B0003-module-routes.tsv` at their
pinned hashes and applied exactly.

Base: C0001 `117aa2bb7e61f41e1531a78452f9f7f6cd5b0771`

Projection: P0003 · Shared request: R0003 · Active control:
`5e075b947a63e84c784afecd00e1f130e21ea659`

## Declaration routes

| historical owner | declarations | destination |
| --- | ---: | --- |
| `NumStability.Algorithms.LinearSystems.QR.HouseholderApplySupport` | 101 | `…QR.Householder.PanelApplication` |
| `NumStability.Algorithms.LinearSystems.QR.HouseholderQRSupport` | 132 | `…QR.Householder.StoredQR` |
| `NumStability.Algorithms.LinearSystems.QR.HouseholderSpecSupport` | 112 | `…QR.Householder.TrailingPanels` |
| `NumStability.Source.Higham.Chapter19.Sensitivity` | 59 | `…Chapter19.Sensitivity.Bounds.Results` |
| `NumStability.Source.Higham.Chapter19.StoredLoop` | 8 | `…Chapter19.StoredLoop.Perturbation.Bridge` |
| **relocated** | **412** | five destinations |
| `NumStability.Source.Higham.Chapter19.Core` | 1,065 | retained in place (reviewed outlier) |

1,460 declarations are public and 17 are private. By kind: 1,250 theorems, 182
definitions, 15 inductives, 15 constructors, 15 recursors.

## Why the move is a body transfer, not a re-emission

Every owner sends *all* of its declarations to *one* destination, so nothing had to be
cut per declaration. Each destination is a new header plus the owner's file body
transferred verbatim — the region from the single top-level `namespace NumStability` to
end of file, which carries every declaration, `open` line and inner namespace exactly as
authored.

`CHECK_STATIC.py` compares those body bytes against `git show C0001:<owner>` and
requires equality. That check is load-bearing: a wave that re-emitted declarations could
still compile and still satisfy a projection replay on names and edges while having
silently reformatted a proof or dropped a `noncomputable section`. Byte equality removes
the possibility rather than arguing against it.

## The retained Chapter 19 outlier

`NumStability/Source/Higham/Chapter19/Core.lean` keeps all 1,065 declarations and its
exact six imports, and the file is preserved byte-for-byte — it does not appear in the
changed-path ledger at all. B0003 records this as
`route_class = source_retained_outlier`, `normalization_decision =
approved_retained_outlier`, and the module route as "retain all frozen declarations and
exact imports in the reviewed Chapter 19 source outlier; no relocation or declaration
change".

Two consequences are worth stating plainly, because both look like violations until the
route is read:

* Core continues to import `…QR.HouseholderQRSupport` and `…QR.HouseholderSpecSupport`,
  two historical wrappers. Preserving Core byte-for-byte and retargeting its imports are
  mutually exclusive, and the route chose preservation. No cycle results: the wrappers
  import destinations, and no destination imports Core.
* Core is excluded from the 129 protected consumers precisely because it is an R11 owner.

## Compatibility contract

No historical path is deleted and none is Git-renamed, so every pre-existing import
keeps resolving.

| action | owners | what changed |
| --- | ---: | --- |
| relocated → documented import-only wrapper | 5 | body moved out; imports exactly its destination |
| declaration-free wrapper, imports retained exactly | 56 | module documentation added only |
| declaration-free wrapper, support import retargeted | 3 | documentation plus one import retarget |
| retained source outlier | 1 | nothing (byte-identical) |

The three retargeted wrappers are `NumStability.Algorithms.QR.Householder{Apply,QR,Spec}Support`,
whose single support import moves onto the corresponding destination. These are distinct
modules from the same-named `Algorithms.LinearSystems.QR.*Support` owners, and the
retarget is an explicit instruction in `B0003-module-routes.tsv`, not a widening of
scope. The task brief's summary sentence describes all 59 declaration-free wrappers as
retaining their exact imports; where that prose and the frozen route disagree, the frozen
route governs, and it is the route that is implemented and audited here.

An import-only wrapper importing just its destination preserves the whole prior surface,
because each destination inherits the owner's original imports (with an owner import
replaced by that owner's destination). Every declaration formerly reachable through the
historical path is therefore still reachable through it; only the intermediate module
identity changed. The 65 old-path-only tests are what verify this rather than assert it.

## Layering

Reusable destinations may not reach `NumStability.Source` or a historical facade; source
destinations may depend on reusable leaves.

| destination | class | transitive modules | Source | facades |
| --- | --- | ---: | ---: | ---: |
| `…Householder.TrailingPanels` | reusable | 18 | 0 | 0 |
| `…Householder.PanelApplication` | reusable | 82 | 0 | 0 |
| `…Householder.StoredQR` | reusable | 90 | 0 | 0 |
| `…Sensitivity.Bounds.Results` | source | 107 | 0 | 0 |
| `…StoredLoop.Perturbation.Bridge` | source | 91 | 0 | 0 |

The three owners form a chain — `HouseholderSpecSupport` ← `HouseholderApplySupport` ←
`HouseholderQRSupport` — and `Chapter19.StoredLoop` imports the last of them. Each
destination therefore imports the *destination* of the owner it used to import, which is
both what keeps the reusable tier free of facades and what prevents a cycle back through
a wrapper. The complete project import graph has 5,224 modules and zero cycles.
