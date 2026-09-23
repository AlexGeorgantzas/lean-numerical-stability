# Pilot 26 complete twelve-task review

Pilot 26 completed all twelve scheduled tasks on Titan. Eleven pairs ended with
audited faithful statements in both conditions; one pair is ineligible because
the N formalizer crossed the frozen exploration-interface rule before its
candidate could be audited. These are **exploratory development** results on
an outcome-aware corpus, not a held-out estimate of NumStability's general
effect. Pilot 25 remains separate and is not pooled into the figures below.

The immutable campaign is
`/hdd/alexgeorgantzas/highambench/pilot26-development-12-20260923-a`.
Its final `campaign.json` is `COMPLETE` with SHA-256
`8f605dd182a5b2c513941cefc3a39d81594e25c61cbf58b19835083035a25655`.
It ran from 2026-09-23 15:19:47 to 17:28:46 UTC, including the planned
first-pair review pause. The measured controller remained frozen at
`00d8ba371957e69633c55fec59b09b02526db53d`; later documentation commits
did not alter its code or inputs. The corpus, admission, and preflight hashes
are respectively `098b5968cbfa8b6e38311bad3a2bb3a830173cc859a4d0750303ee327ed25476`,
`1e905517311cb80dc513234f47a4e139c7f26f75cb9a0e7b75db7096942c93cc`,
and `a76ca3965cda309d3557f3b2a849ae83f1add2907ead3893f01abc746fd048ac`.
All twelve IDs match the frozen corpus, and all twelve pair-report hashes match
their journal entries.

## Paired results

The primary time is cumulative **contestant-system wall time**, including
task-time retrieval and every formalization/repair attempt, but excluding Lean
validation and faithfulness auditing. `L/N` below is the L time divided by the
N time; below 1 favors L. `N/L lines` counts the final Lean candidate, not a
proved development. The target theorem is intentionally left `sorry`; success
means a compiling, integrity-checked, faithfully formalized statement.

| Task | N/L submissions | N/L time (s) | L/N time | N/L net-new tokens | N/L lines | Final pair |
| --- | ---: | ---: | ---: | ---: | ---: | --- |
| RUMP12-THM3.5 | 1/1 | 235/249 | 1.061 | 52,155/64,590 | 102/80 | Faithful |
| FAB19-EQ3.5 | 1/1 | 223/174 | 0.779 | 52,229/54,702 | 97/62 | Faithful |
| FAB19-EQ3.7 | 1/1 | 184/282 | 1.533 | 61,077/70,725 | 66/88 | Faithful |
| H20-8 | 1/1 | 99/123 | 1.242 | 23,234/52,799 | 42/28 | Faithful |
| RUMP12-THM3.4 | 1/1 | 165/150 | 0.910 | 34,632/55,608 | 68/44 | Faithful |
| FAB19-EQ3.6 | 1/1 | 144/165 | 1.143 | 31,130/70,911 | 44/27 | Faithful |
| CAST08-PROP3.2 | 1/1 | 142/133 | 0.936 | 23,935/22,204 | 54/46 | Faithful |
| CAST08-FIXED3 | 1/1 | 204/174 | 0.855 | 26,843/62,313 | 57/48 | Faithful |
| LL07-THM4 | 2/2 | 379/399 | 1.050 | 56,846/80,833 | 186/137 | Faithful after repairs |
| LL07-THM7 | 1/2 | 245/381 | 1.556 | 40,732/81,862 | 187/170 | Faithful after L repair |
| FAB19-THM4.1 | 1/1 | 221/271 | 1.226 | 33,984/65,898 | 87/82 | Faithful |
| FAB19-THM4.2 | 1/1 | 194/173 | — | 39,553/25,876 | 75/79 | **Ineligible:** N interface violation; L faithful |

On the **eleven eligible pairs only**, L was faster on 4 and slower on 7.
The geometric-mean L/N time ratio was **1.092** (about 9% slower); the ratio
of summed contestant-system times was **1.116** (2,501 versus 2,242 seconds).
The geometric-mean contestant-active ratio, excluding task-time retrieval,
was **1.015**. Retrieval itself took 305 versus 157 seconds in total, an
additional 148 seconds for L; this accounts for about 57% of the 259-second
summed system-time gap. Task-specific retrieval is part of the primary time
and is **not** retroactively amortized away.

L used 682,445 versus N's 436,797 net-new tokens (1.56 times by summed
counts). Its final candidates used 812 versus 990 lines (18% fewer), and were
shorter on 10 of the 11 eligible tasks. Thus the observed code-size benefit
is real in this pilot, but it did not translate into lower measured time or
token use overall. These descriptive statistics are not a causal population
estimate: this is one run per task on a development-selected corpus, and some
tasks/pilot inputs were adapted after earlier outcomes.

## What the L candidates actually reused

The admission gate identified source-relevant NumStability declarations for
all twelve tasks. That is a *potential-support* check, not evidence the final
formalizer used those declarations. The campaign's elaborated-declaration
uptake record reports **direct NumStability reaches on 9/11 eligible L
candidates** (also 9/12 of all L candidates). FAB19-EQ3.7 and FAB19-THM4.1
only imported a NumStability module; neither reached a declaration in the
final statement. The ineligible FAB19-THM4.2 L candidate also reached none.

Substantive task-specific algorithm or error interfaces were reached in four
eligible candidates: H20-8's least-squares backward-error interface,
FAB19-EQ3.5's recursive and higher-precision summation definitions,
FAB19-EQ3.6's recursive/Kahan definitions, and CAST08-FIXED3's dot-product
and recursive-summation definitions. The other direct-reach candidates used
more foundational FP-format, `FPModel`, `gamma`, or polynomial definitions.
Direct reach does not prove that a declaration saved time. In particular,
FAB19-EQ3.7's source requires independently varying per-operation errors,
while the retrieved algorithms expose an `FPModel` operation; its L candidate
instead redefined the relevant summation algorithms and was the largest
non-repair time loss. FAB19-THM4.1 similarly used a separate relational
arithmetic model. These are observable representation/interface mismatches,
not evidence that the library is absent or that the formalizer was denied
access to it.

## Ineligible pair and audit integrity

FAB19-THM4.2 N ran a command using `$(printenv LEAN_PATH | cut -d: -f1)` to
search a Mathlib directory. The frozen interface allows the standalone
literal `printenv LEAN_PATH` but rejects compiler-path expansion inside a
compound command; the policy record flags compiler search-path inspection and
environment enumeration. This command is not evidence of NumStability
leakage, but it violates the exact predeclared checker. N was stopped before
faithfulness auditing; L's first statement was faithful. The pair is neither
an L speed win nor an N faithfulness failure, and no retrospective waiver or
measured rerun was applied. This is a useful prospective interface-design
issue for any later pilot, not a license to reclassify Pilot 26.

The faithfulness audits retained independent blind translation, direct and
round-trip judgments, conditional adjudication, per-dependency records, and
the mandatory 16-item semantic checklist. The binary final decision permits
faithful strengthening but not partial-domain coverage. Auditors were fresh
and condition-blind; candidate-specific files were frozen and hashed before
audit. The same formalizer conversation received neutral mismatch feedback
for repairs. Across all twelve tasks and both conditions there were 27
formalization submissions. Excluded audit work totaled 12,334.5 cumulative
judge-seconds and 10,448,843 audit tokens; because judges and lanes ran in
parallel, the summed judge-seconds are **not** campaign wall time.

Every formalization attempt was admitted in its fixed 8-logical-CPU,
24-GiB, no-swap lane. The largest sampled one-second-mean CPU use was 1.91
cores; the largest sampled current RAM use was 0.993 GiB. No OOM events were
recorded. These are sampled peaks, not instantaneous maxima; cgroup lifetime
memory peaks can include preceding conditions in a reused lane. The frozen
NumStability build and one-time orientation/indexing were reused rather than
rebuilt per task, and their costs are not folded into the primary per-task
contestant clock.

## Thesis-safe reading

Pilot 26 demonstrates that the full automatic, paper-faithfulness-gated
workflow can complete twelve tasks with three isolated concurrent lanes.
For this development corpus, NumStability usually made the final statement
shorter, but it did **not** make the formalizer faster or less token-hungry on
average. The main measurable bottlenecks are the extra task-specific retrieval
cost and representation mismatch on some supposedly supported tasks. These
are findings to report, not numbers to repair post hoc. Any change to the
retriever, library interface, corpus, model, or exploration rule after these
outcomes needs a new pilot identity and separately reported artifacts.
