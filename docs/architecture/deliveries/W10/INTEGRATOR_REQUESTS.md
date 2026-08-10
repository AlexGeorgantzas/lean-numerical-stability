# W10 integrator requests

Three shared changes are required that W10 is forbidden to make itself. Each is stated
with its exact C0007 path and blob, a minimal deterministic postimage, the mathematical
reason, the protected test that covers it, and whether it removes canonical-to-historical
or reusable-to-Source reachability.

W10 does not create `R0011`. These are requests, not applied changes.

| # | file | C0007 blob | class |
| --- | --- | --- | --- |
| 1 | `docs/architecture/tiers.json` | `c1afc0ad364fc908364114bfd63c5e0a2058baee` | classification |
| 2 | `docs/architecture/layout-exceptions.json` | `bbedd2a796aa7b003f89193e746599140fb03524` | naming debt |
| 3 | `NumStability/Algorithms/NormEstimation/OneNorm/GeneralIndex.lean` | accepted consumer | retarget |

---

## Request 1 — classify the reusable `NormEstimation` subtree in `tiers.json`

**Why.** `tier_assignments` resolves a module by exact entry first, then by the longest
matching prefix rule. `tiers.json` at C0007 contains exactly four `NormEstimation`
entries -- `NormEstimation`, `NormEstimation.OneNorm` and `NormEstimation.OneNorm.All`
as `aggregate`, and `NormEstimation.OneNorm.GeneralIndex` as `reusable` -- and **none of
the 23 prefix rules covers the subtree**. Every one of the 48 reusable destination
modules W10 emits therefore resolves to no tier at all and lands in the
`unclassified_modules` debt set, which `check_layout` fails on as a new addition.

The 49 Source destinations need nothing: they are covered by the existing
`{"prefix": "NumStability.Source", "tier": "source"}` rule.

**Minimal deterministic postimage.** One object appended to the `prefixes` array:

```json
{ "prefix": "NumStability.Algorithms.NormEstimation.", "tier": "reusable" }
```

The trailing dot is the spelling coordinator patch manifests already use, and
`tier_assignments` strips it (`prefix.rstrip(".")`) before boundary-safe matching. This is
consistent with the existing exact entry classifying
`NormEstimation.OneNorm.GeneralIndex` as `reusable`, and it subsumes no other subtree.

**Reachability.** Neutral. Classification does not create or remove any import edge.

**Protected test.** `Focused/TierClassification` checks that every emitted reusable
destination resolves to tier `reusable` and no W10 destination is unclassified.

---

## Request 2 — record the two `PNorm/Endpoints` modules as noncanonical naming debt

**Why.** B0012 authorizes the reusable destination
`NumStability/Algorithms/NormEstimation/PNorm/Endpoints/`. For a non-Source module,
`check_layout.noncanonical_name` rejects any part **containing** a `PROCESS_WORDS`
entry, and `Endpoint` is one of the ten. So B0012 authorizes a destination the layout
checker refuses. This was confirmed empirically by calling the checker's own predicate:
of the 97 modules W10 emits, exactly these two are rejected and 95 pass.

```
BAD  NumStability.Algorithms.NormEstimation.PNorm.Endpoints.ConvergenceStatements
BAD  NumStability.Algorithms.NormEstimation.PNorm.Endpoints.PNormRectangular
```

The material is genuinely endpoint mathematics and genuinely reusable -- the p = 1 and
p = ∞ cases of the p-norm pair (`pNormPair_inf`, `RectPNormPair.one`,
`RectPNormPair.infinity`, `holder_inf`, `infNormVec_rectMatVec_le`), 14 declarations in
all. Routing them to Source to dodge a naming rule would misstate the architecture, and
B0012 forbids inventing an unfrozen destination, so neither evasion is available.

**Precedent.** `layout-exceptions.json` already carries
`NumStability.Algorithms.Ch14ForwardErrorEndpoint` in both `noncanonical_modules` and
`unclassified_modules`, which is the same process-word situation.

**Minimal deterministic postimage.** Two strings added to `legacy.noncanonical_modules`,
in sorted position:

```
NumStability.Algorithms.NormEstimation.PNorm.Endpoints.ConvergenceStatements
NumStability.Algorithms.NormEstimation.PNorm.Endpoints.PNormRectangular
```

No other key changes; with Request 1 applied they are classified, so
`unclassified_modules` needs no addition.

**Reachability.** Neutral.

**Protected test.** `Focused/PNormEndpoints` builds both modules canonically and
`#check`s all 14 declarations at their frozen names.

---

## Request 3 — retarget `NormEstimation.OneNorm.GeneralIndex` off the historical owner

This is the only request that changes reachability, and it is the one the brief
anticipates as the integrator retarget.

**Why.** `GeneralIndex` is an accepted canonical module, tiered `reusable` by an exact
entry, and W10 must preserve it. At C0007 it opens with

```lean
import NumStability.Algorithms.CondEstimation
import NumStability.Analysis.MatrixAlgebra
```

`NumStability.Algorithms.CondEstimation` is a W10 owner and becomes a compatibility
facade, so after the split an accepted **canonical** module imports a **historical**
module. It uses exactly two declarations from it, and the split sends them apart:

| declaration | destination | tier |
| --- | --- | --- |
| `NumStability.lapackNormEstimator` | `Source.Higham.Chapter15.Algorithm04.LAPACKNormEstimator.CondEstimation` | source |
| `NumStability.lapackNormEstimator_lower_bound` | retained in `NumStability.Algorithms.CondEstimation` | historical |

`lapackNormEstimator` is Algorithm 15.4 itself -- the five-iteration cap with the
alternating-vector comparison -- so it is printed source. `lapackNormEstimator_lower_bound`
lies in the private reverse closure (it consumes
`_private.…CondEstimation.0.…oneNormStep_gamma_le`) and therefore cannot move at all.

**P0013 could not have caught this.** The frozen graph holds exactly W10's 1029
declarations, and `GeneralIndex` is outside the wave, so neither edge is a typed edge in
it. W10's own reusable-to-Source and canonical-to-historical counts are both zero over the
projection; this violation lives entirely on the accepted-consumer side. It is the W09
lesson -- a frozen projection's "zero edges" claim only covers selected declarations --
appearing on the consumer boundary rather than inside the wave.

**Minimal deterministic postimage.** Replace line 1 of
`NumStability/Algorithms/NormEstimation/OneNorm/GeneralIndex.lean`:

```lean
-import NumStability.Algorithms.CondEstimation
+import NumStability.Source.Higham.Chapter15.Algorithm04.LAPACKNormEstimator.CondEstimation
```

with no other edit. That removes the canonical-to-historical edge.

**It does not by itself remove a reusable-to-Source edge -- it exposes one.** A module
tiered `reusable` would then import a `Source` module directly. Two dispositions are
available and the choice is the integrator's, not W10's:

1. **Re-tier `GeneralIndex` to `source`** (one exact entry in `tiers.json`). Honest if the
   module is really about Algorithm 15.4's general-index form; its name and its sole
   mathematical content -- a lower bound for the LAPACK estimator at a general index --
   both point that way.
2. **Split `GeneralIndex`**, leaving the index-generic machinery reusable and moving the
   statement that mentions `lapackNormEstimator` to a Chapter 15 leaf. Cleaner
   architecturally, but it edits an accepted API, which is outside W10's authority and
   should not be done as a side effect of this wave.

W10 recommends **disposition 1**: it is one line, it is reversible, and it does not touch
an accepted proof. W10 has applied neither.

**Reachability.** Removes one canonical-to-historical edge. Exposes one reusable-to-Source
edge that is latent at C0007 and is resolved by whichever disposition is chosen.

**Protected test.** `Focused/GeneralIndexRetarget` pins the current accepted surface: it
imports `GeneralIndex` unchanged and `#check`s both `lapackNormEstimator` and
`lapackNormEstimator_lower_bound` at their frozen names, so the retarget can be validated
without editing the consumer. `Focused/AcceptedConsumers` covers the wider fanout.

---

## Accepted-consumer fanout (enumerated, not edited)

75 modules outside the wave import a W10 owner. W10 edits none of them; every one keeps
resolving because all 27 owners remain compatibility modules.

| consumer group | count | note |
| --- | ---: | --- |
| `NumStability.Algorithms` root aggregate | 1 | integrator-owned; imports 22 of the 27 owners |
| `Algorithms.LinearSystems.Underdetermined.*` | 27 | W04's accepted Chapter 21 tree; all via `CondEstimation` |
| `Source.Higham.Chapter07.*` | 33 | conditioning chapter; all via `CondEstimation` |
| `Source.Higham.Chapter06`, `CrossChapter` | 2 | via `CondEstimation` |
| `Analysis.*` | 5 | including `Analysis.ConditionEstimatorLowerBound` |
| `Algorithms.Sylvester.Higham16NormEstimator` | 1 | the accepted W06 relationship, preserved |
| `NormEstimation.OneNorm.GeneralIndex` | 1 | **Request 3** |

`CondEstimation` alone carries 73 of the 75. That concentration is why it is retained as a
declaration-bearing facade with its full original import surface restated rather than
narrowed to its destinations: a consumer that reached an identifier transitively through
this path must keep seeing the same surface.
