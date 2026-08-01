# W01 shared-file patch request

Branch `codex/reorg-2026-08-w01-fp-boundary`, phase branch `B0001`, wave `W01`.

Not applied by this wave. Both files below are outside `B0001.json`'s
`owned_paths`/`destination_prefixes`, so W01 records the request instead of editing
them.

## Request: retarget two shared modules off the compatibility paths

| File | Change |
| --- | --- |
| `NumStability/Analysis/BeneficialRounding.lean` | replace `import NumStability.Analysis.FloatingPointArithmetic` with the canonical leaves it uses |
| `NumStability/Analysis/Accumulation.lean` | same replacement |

### Why

Both modules import `NumStability.Analysis.FloatingPointArithmetic`, which W01 turns
into a compatibility module that imports the new canonical destinations. A W01
destination that needs anything from either module therefore closes a loop:

```text
Source.Higham.Chapter01.FloatingPointArithmetic.IncreasingPrecision
  -> Analysis.BeneficialRounding
  -> Analysis.FloatingPointArithmetic            (compatibility module)
  -> Analysis.FloatingPointArithmetic.NearestRoundingError
```

`lake` reports this as `build cycle detected`. It is not a defect in either shared
module: it is the ordinary consequence of a compatibility module sitting below a
consumer that used to sit above the monolith.

### What W01 did instead, and what the request unblocks

Four lemmas are involved:

| Lemma | Currently in |
| --- | --- |
| `seven_not_dvd_two_pow_nat` | `Analysis/BeneficialRounding.lean` |
| `two_thirds_not_ieeeSingleFiniteSystem` | `Analysis/BeneficialRounding.lean` |
| `two_thirds_not_ieeeDoubleFiniteSystem` | `Analysis/BeneficialRounding.lean` |
| `real_abs_exp_sub_one_le_of_abs_le` | `Analysis/Accumulation.lean` |

Exactly three declarations use them, so those three stay in their original modules
rather than moving to a Chapter 1 destination:

| Declaration | Retained in |
| --- | --- |
| `expm1Algorithm2_exp_sub_one_abs_le_of_abs_x_le` | `Analysis.CancellationOfRoundingErrors` |
| `increasingPrecisionExampleElse_two_precision_failure_of_ieee_fin…` | `Analysis.IncreasingPrecision` |
| `increasingPrecision_one_seventh_binary_grid_abs_error_ge` | `Analysis.IncreasingPrecision` |

Retention is inside the projection contract, not a workaround of it: `P0001` lists
all four historical modules under `--allow-module`, so each declaration keeps its
name, kind, visibility and every incident edge. The projection comparison passes with
these three in place.

Once the two imports are retargeted, a follow-up may move all three into
`NumStability.Source.Higham.Chapter01.FloatingPointArithmetic.{CancellationOfRoundingErrors,IncreasingPrecision}`
with no other change, at which point the four old paths become purely import-only.

### Not requested

No change to `docs/architecture/tiers.json`, `layout-exceptions.json`,
`COMPATIBILITY.md`, any root aggregate (`NumStability/Analysis.lean`,
`NumStability/Source.lean`, `NumStability.lean`), `NumStabilityTest.lean`, or CI. The
four compatibility modules keep their original import surface, so every existing
consumer of the old paths resolves unchanged and no aggregate needs a new member.
