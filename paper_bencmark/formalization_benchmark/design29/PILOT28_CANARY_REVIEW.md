# Pilot 28 proof-required canary review

Pilot 28 completed its three predeclared tasks on Titan, with frozen
controller `ff3261d90f3f71181169e9c67e0c8013906c31d0` and campaign
`/hdd/alexgeorgantzas/highambench/pilot28-proof-canary-20260924-b`.
The terminal campaign journal SHA-256 is
`463e2db23fbc434928b038dd5ecbb1583677d67bd8776402776c3783518b7dd0`.
All three pairs have audited faithful statements in both conditions. Two
pairs have complete, unchanged, kernel-checked proofs on both sides; one has
no accepted proof on either side. These are exploratory development results
and must not be pooled with the Pilot 26 statement-only or Pilot 27 incident
measurements.

| Task | N/L statement lines | N/L final proof lines | N/L inclusive contestant time (s) | N/L net-new tokens | Direct L reach | Proof outcome |
| --- | ---: | ---: | ---: | ---: | --- | --- |
| FAB19-EQ3.5 | 63 / 69 | 333 / 320 | 670 / 625 | 120,808 / 163,341 | FPModel/gamma, not summation algorithm | Both proved |
| CAST08-FIXED3 | 56 / 48 | 368 / 212 | 639 / 361 | 107,784 / 138,874 | `fl_dotProduct`, `fl_recursiveSum`, FPModel/gamma | Both proved |
| FAB19-EQ3.6 | 47 / 73 | — / — | 515 / 620 | 72,540 / 170,106 | None | Both reached four-attempt proof limit |

The CAST08-FIXED3 result is the relevant-library proof-code canary: L's
final Lean source is 156 raw lines (42.4%) shorter, and its total contestant
time is 278 seconds (43.5%) lower; L uses 28.8% more net-new tokens. Its
proof explicitly applies the frozen library's `dotProduct_backward_error`,
`recursiveSum_backward_error`, and `gamma_mul` lemmas while composing the
three-level bound. Thus the direct-use result is not merely an unused import
or a task-name match. N proves its version without NumStability. Its pair
report SHA-256 is
`df9fcd70fffb7c8e7fa853aeb99a67005c10d6de4a264b255aeaab1dee48bc91`.
FAB19-EQ3.5 is a smaller proof-code/time win but lacks task-specific
algorithm uptake. Its pair report SHA-256 is
`8b19937e4c3d8e8872990cbe480bb456c95e4f72607aa1858066ed87e3853584`.

FAB19-EQ3.6 is preserved as an unfavorable/model-gap result. Both formalizers
left their audited targets unproved, and each wrote an off-target Lean file
demonstrating a contradiction from the frozen proposition at `k=2`, `b=1`,
input `[1,0]` with allowed rounding errors. The output has a first-order
`3u` term, while the requested per-input bound has `2u`. Their event logs
record successful Lean checks of the counterexamples; neither changed the
frozen target or supplied an accepted proof. The modeled error in an exact
zero/subtraction operation is a likely source of the discrepancy. This is
not a benchmark-controller failure and must not be reclassified as proof
success or omitted. Its pair report SHA-256 is
`d1fb9922ca662c4e0ccf0ccb3ce369b919cfcb8eb0ba660203f0d5fb12320554`.

The first two tasks show that the proof checker and semantic-freeze bridge
now work under the fixed Pilot 28 controller. The third shows that a
statement faithfulness judgment does not establish that the theorem follows
from its chosen rounding model. The prospective ten-task Pilot 29 corpus was
frozen before CAST08-FIXED3 sealed and explicitly retained FAB19-EQ3.6 after
the N counterexample became known, as a disclosed proof-risk case. Pilot 29
must report actual direct uptake, all statement outcomes, both-proved proof
LOC separately, and the full task ledger. No task may be removed because it
is unfavorable after launch.

Across all three Pilot 28 tasks the largest sampled one-second CPU peak was
2.54 cores of the fixed 8-core lane, and the largest sampled current RAM was
1.48 GiB of its 24-GiB cap. These are sampled peaks, not instantaneous
maxima; the per-turn cgroup lifetime memory peaks remain in each immutable
resource record. Concurrent lanes are physically disjoint in CPU affinity,
with no swap allowed. The campaign included task-time searching in the
contestant clock; excluded audits and Lean validation are separately logged.
