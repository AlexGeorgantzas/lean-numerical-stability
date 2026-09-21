# Design-16 development smoke results

Status: `UNSCORED_ENGINEERING_EXPLORATORY`  
Faithfulness: `PENDING_INDEPENDENT_SCREEN`

These are consumed development tasks, not official successor-pilot observations.
Both Design-16 candidates passed compilation/integrity validation, but a compile
pass is not evidence of semantic faithfulness. No scientific outcome should be
reported until an independent condition-blind faithfulness screen passes.

## Raw observations

| Task | Run | Time (s) | Net-new tokens | Candidate lines | Compile/integrity |
|---|---|---:|---:|---:|---|
| H5-5 | Design-16 L development | 488.456 | 81,111 | 85 | pass |
| H5-5 | sealed Pilot-15 L | 476.945 | 110,588 | 131 | sealed baseline |
| H5-5 | sealed Pilot-15 N | 638.640 | 77,709 | 211 | sealed baseline |
| H10-7 | Design-16 L development | 854.250 | 86,725 | 158 | pass |
| H10-7 | sealed Pilot-15 L, cumulative | 1,517.499 | 237,128 | 127 | sealed baseline |
| H10-7 | sealed Pilot-15 N | 536.626 | 68,203 | 139 | sealed baseline |

The H10-7 Pilot-15 L baseline is cumulative across its initial submission and
repair. That makes the adaptation comparison useful for diagnosing the new
delivery architecture, but it is not a fresh matched-condition comparison.

## Primary development comparison: Design-16 L versus sealed Pilot-15 L

Negative percentages mean Design-16 used less of the metric.

| Task | Time change | Token change | Line change | Development reading |
|---|---:|---:|---:|---|
| H5-5 | +2.4% (1.024×) | -26.7% (0.733×) | -35.1% (0.649×) | Token and line adaptation improved; wall time was essentially flat and 2.4% higher. |
| H10-7 | -43.7% (0.563×) | -63.4% (0.366×) | +24.4% (1.244×) | Large time/token adaptation improvement against the cumulative repaired L baseline; output was longer. |

This is the relevant engineering comparison for whether bounded composition
packets reduce the previous L-side adaptation burden. It is not an R0/R1 result.

## Secondary context only: Design-16 L versus sealed Pilot-15 N

| Task | Time change | Token change | Line change | Contextual reading |
|---|---:|---:|---:|---|
| H5-5 | -23.5% (0.765×) | +4.4% (1.044×) | -59.7% (0.403×) | Faster and much shorter than old N, with slightly more tokens. |
| H10-7 | +59.2% (1.592×) | +27.2% (1.272×) | +13.7% (1.137×) | Worse than old N on all three reported metrics. |

These N comparisons are descriptive context only. They cross protocols and do
not substitute for the frozen matched R0/R1 experiment. In particular, they do
not justify calling either task a positive benchmark result.

The exact values, deltas, ratios, and interpretation policy are in
`development_results.json` beside this report.
