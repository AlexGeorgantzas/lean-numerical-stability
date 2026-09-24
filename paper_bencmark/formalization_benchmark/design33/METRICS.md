# Pilot 33 prospective phase and uptake metrics

This contract is written before any Pilot 33 contestant attempt. It is not a
result and does not make the screening worklist an admitted corpus.

For each condition/task, the frozen pair record already has the required
observables; the Pilot 33 reporter must hash-check the pair, candidate,
submission, and admission records before deriving comparisons.

| Metric | Source fields and rule |
| --- | --- |
| Formalization time | `condition.contestant_system_wall_seconds`, from the first timed statement turn through the frozen faithful statement (or the terminal unsuccessful statement turn); this includes task-time library search and candidate freezing, but excludes compilation and auditing. |
| Formalization tokens | `condition.net_new_tokens`, cumulative over all statement submissions; keep full input/output/cached-token counters separately. |
| Proof time | `condition.proof_stage.contestant_active_seconds`, accumulated only after the faithful statement is frozen; null if no proof stage starts. Rejected `sorry` submissions count toward it. |
| Proof tokens | `condition.proof_stage.net_new_tokens`, cumulative over up to four proof submissions; null if no proof stage starts. |
| Total time/tokens | Formalization plus proof for a condition; use the controller's `end_to_end_contestant_system_wall_seconds` and `end_to_end_net_new_tokens` as consistency checks. This is contestant-active system time, **not** real campaign makespan or excluded auditor time. |
| Audit/validation overhead | Sum independently logged excluded audit, compilation, semantic-dossier, and proof-validation times/tokens. Report separately and never subtract from the above fields a second time. |
| Code size | Raw and nonblank/noncomment lines of the final faithful statement for every paired faithful task; raw and code lines of the final proof only when both conditions have kernel-accepted zero-hole proofs. Show proof attrition for every scheduled task. |
| Treatment uptake | Direct elaborated NumStability declaration reach in the final L statement **and** constants reached from the kernel-accepted L proof term, traversing only proof-local helper bodies with `design33_proof_dependencies.lean`. The latter is recompiled and read after the run; it never enters the contestant clock. Imports, generic FPModel/gamma alone, or a private admission candidate do not count as substantive statement uptake. Record declaration names in both channels separately. |
| Hardware | Per-turn cgroup-sampled peak CPU cores, memory-current GiB and OOM events, plus pre/post CPU affinity, memory cap, host RAM and system disk. Distinguish sampled peaks from true instantaneous maxima. |

The final report must give paired N/L phase ratios only for comparable
eligibility strata, with denominators explicit. For example, formalization
time can compare any pair with two faithful statements, while proof-code lines
require two complete proofs; failed or incident tasks remain in the scheduled
task table. L search time may be shown separately as an explanatory
diagnostic, but search-excluded time or tokens may not replace the inclusive
comparison. A larger or outcome-aware selected corpus is descriptive
development evidence, not a held-out causal estimate.

The controller already disables `multi_agent`/`multi_agent_v2` and
`agents.enabled` by session flags, attests those flags, and fails on any
observable collaboration/subagent call. A prompt reminder alone is not the
isolation mechanism. The visible event and tool traces are retained; hidden
chain-of-thought is not available and must never be described as logged.
