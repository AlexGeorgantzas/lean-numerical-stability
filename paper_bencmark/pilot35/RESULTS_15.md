# Fifteen-task proof-required composite: Pilots 34 and 35

The predeclared, hash-checked [machine-readable report](RESULTS_15.json)
completed successfully. Under the recorded binary faithfulness audits, **all 15
N/L pairs produced faithful statements and complete, kernel-checked proofs**.
The report includes every scheduled task and every unfavorable outcome. These
are paired task-time sums, not the parallel campaign's elapsed wall clock.

| Measure (15 pairs) | N | L | L relative to N |
|---|---:|---:|---:|
| Statement code lines | 514 | 552 | 7.4% more |
| Proof code lines | 4,913 | 4,413 | 10.2% fewer |
| Statement + proof lines | 5,427 | 4,965 | 8.5% fewer |
| Time to faithful statement | 2,045 s | 2,398 s | 17.3% slower |
| Proof-stage time | 8,470 s | 6,579 s | 22.3% faster |
| Total contestant-active time | 10,515 s | 8,978 s | 14.6% faster |
| Formalization net-new tokens | 542,141 | 1,180,836 | 2.18× |
| Proof net-new tokens | 1,260,741 | 1,062,126 | 15.8% fewer |
| Total net-new tokens | 1,802,882 | 2,242,962 | 24.4% more |

L had shorter proof code on **8/15** tasks and was faster end-to-end on **9/15**.
Its elaborated target statements directly reached a substantive NumStability
declaration on **12/15**, and its accepted proof terms directly used at least
one NumStability declaration on **14/15**. The proof-term count comes from the
compiled Lean proof expression, not text or import matching. The exception,
`P14-SHIFTED-SUM`, was faster and shorter under L despite no direct declaration
use; that outcome cannot be attributed to library reuse.

## Task-level outcomes

All numbers below are N → L. “Retained” means the task was deliberately chosen
after favorable earlier evidence; the other ten are newly screened, not
independent random samples. Seconds include formalization and proof attempts,
but exclude auditing and validation.

| Task | Stratum | Proof lines | Total seconds |
|---|---|---:|---:|
| CAST08-FIXED3 | Retained | 325 → 221 | 603 → 387 |
| P14-T1 | New | 201 → 227 | 604 → 453 |
| HI21-LEM2.2 | New, predeclared hard | 39 → 49 | 135 → 199 |
| CAST08-PROP3.1 | Retained, hard | 373 → 200 | 816 → 527 |
| P14-T2 | New | 364 → 345 | 725 → 619 |
| RUMP12-THM3.4 | Retained | 599 → 333 | 1,243 → 982 |
| P14-LOGSUMEXP | New | 204 → 257 | 558 → 499 |
| H20-8 | Retained | 243 → 167 | 703 → 313 |
| P14-ALT-SOFTMAX | New | 383 → 443 | 826 → 837 |
| CAST08-PROP3.2 | Retained, hard | 329 → 245 | 619 → 423 |
| P14-SHIFTED-SUM | New | 349 → 313 | 851 → 516 |
| P14-SHIFTED-LOG | New | 451 → 425 | 777 → 882 |
| P14-SHIFTED-SOFTMAX | New, hard | 481 → 493 | 972 → 1,009 |
| P14-SHIFTED-WEIGHTED | New | 290 → 379 | 587 → 777 |
| HI21-EQ2.7 | New | 282 → 316 | 496 → 555 |

The five outcome-aware retained tasks account for **all of the aggregate proof
code reduction**: 1,869 → 1,166 lines (37.6% fewer), with all five shorter
and faster. Across the ten newly screened tasks, L instead wrote **3,247 vs
3,044** proof lines (6.7% more); only 3/10 were shorter. Their aggregate total
time was nearly tied, 6,530 → 6,347 seconds (2.8% faster for L). The selected
four “hard” tasks split 2/4 on shorter proof code and 2/4 on faster total time.
`HI21-LEM2.2` proved easy in practice (N: 39 proof lines, 29 proof seconds),
despite its predeclared difficulty label.

The source clusters also differ: CAST08 (three tasks) and the singleton H20 and
RUMP12 tasks all favor L on proof size and total time; HI21 (two tasks) favors
N; P14 (eight closely related tasks) has 2,882 L versus 2,723 N proof lines,
although L is modestly faster in aggregate. Eight related P14 tasks are not
eight independent demonstrations. On `P14-ALT-SOFTMAX`, L's proof term directly
uses NumStability's floating-point model, recursive-sum operation, γ lemmas,
and a recursive-sum error bound, yet L's proof is 60 lines longer. Thus
**declaration use and topical overlap alone do not guarantee a code-size win**.
By contrast, the retained CAST08, H20, and RUMP12 tasks use reusable error,
least-squares, or floating-point-format results in their accepted proofs and
show substantial savings. HI21's L proofs use the tree representation, but its
two tasks have no proof-code advantage. These are observations, not a causal
decomposition of every extra line.

## Resource accounting and provenance

The auditor work is separately logged and excluded from contestant metrics.
Summing per-condition audit records gives 5,051 seconds / 5.11 million tokens
for N and 5,960 seconds / 5.59 million tokens for L; roles and lanes overlap,
so these sums are **not** elapsed campaign time. Including cached input,
contestant usage was 39.29 million tokens N versus 82.49 million L, of which
37.48 million and 80.25 million respectively were cached input. The table's
“net-new” metric avoids counting that cached prefix as new work but does not
turn L into a token winner.

The three lanes each had an 8-logical-CPU/24-GiB envelope. Sampled maxima in
the report were 5.85 CPU cores and 2.35 GiB RAM; samples can miss short peaks.
Titan's root filesystem had about 2.7 GiB free at recovery completion. The
conversation, command, submission, compilation, audit, proof, usage, and
hardware artifacts remain under the two campaign roots on Titan.

Pilot 33 is preserved as a pre-contestant deployment/index mismatch, not a
task result. Pilot 34 stopped after a `CAST08-PROP3.1` audit-schema incident:
the N statement was contradictory and judges called it unfaithful, but the
validator rejected a vacuity-aware judgment. Its partial N and complete L
halves remain incident evidence, not a paired observation. A fresh diagnostic
audit under the corrected controller returned unfaithful without incident.
Pilot 35 then ran a **fresh N/L pair** for that task plus ten never-started
tasks. The other four valid Pilot 34 pairs were not rerun. Pilot 35 sealed
`COMPLETE_RECOVERY` with eleven hash-valid pairs. The final report SHA-256 is
`3faeb35af66f5c3c9d16e0800a4c88bd5cef09e1a35f0bc10e6c387f40d9c050`.

The protocol accepts a genuinely stronger theorem as faithful. Both conditions
received a stronger classification on several tasks; N alone received it on
`P14-SHIFTED-LOG` and `P14-SHIFTED-WEIGHTED`. Accordingly these are comparisons
of successful paper-faithful work, not always identical Lean propositions.

**Defensible thesis claim:** the library demonstrably supports large proof-size
and proof-time reductions for some mature, directly reusable areas. This
exploratory, outcome-aware corpus does **not** show that library use generally
reduces code: all net code-size gains came from previously favorable retained
tasks, and new P14/HI21 tasks often needed equal or more code. Broader and
better-matched reusable APIs, followed by a source-diverse held-out evaluation,
would be needed for a general claim.
