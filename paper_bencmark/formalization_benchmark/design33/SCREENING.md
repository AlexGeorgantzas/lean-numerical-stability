# Pilot 33 high-overlap screening ledger (development; not admitted)

This is an outcome-aware worklist, **not** a frozen measured corpus or a claim
of eligibility. Pilot 29/31/32 artifacts remain immutable. The new pilot will
not launch until its task set, source PDFs, non-collision evidence, private
compiling statement skeletons, and independent source-faithfulness reviews are
sealed. A task is excluded rather than padded into the corpus when a gate
fails. All screening decisions, including rejected candidates, stay in this
ledger.

## Predeclared selection objective

Aim for 15–20 paper results with direct, useful NumStability overlap, including
3–4 tasks classified as hard before their new-pilot outcomes. The final
criterion is *not* previous L success: a source-complete statement must reach
a relevant library algorithm/error interface on the frozen snapshot, and the
library must not already prove the selected result. The five prior direct-use,
both-proved favorable results below are deliberately retained and are labeled
outcome-aware. The prospective additions are leads, not admitted tasks.

| Candidate | Source/overlap lead | Current gate or caution |
| --- | --- | --- |
| CAST08-FIXED3 | Direct `fl_dotProduct` and `fl_recursiveSum`; prior both-proved pair | Retain; previous positive outcome known. |
| CAST08-PROP3.1 | Direct `fl_recursiveSum`; t-level summation and optimality | Retain; previous positive outcome known; hard. |
| CAST08-PROP3.2 | Direct `fl_dotProduct`; t-level superblock dot | Retain; previous positive outcome known; hard. |
| RUMP12-THM3.4 | Direct finite-format summation interface | Retain; previous positive outcome known; foundational rather than algorithm/error overlap. |
| H20-8 | Direct least-squares backward-error interface | Retain; previous positive outcome known; no FPModel. |
| P04-T1 | Product-path error lemma and mixed block-FMA trace | Latest Manchester author PDF obtained; original audit PDF hash differs. Old faithful statement uses per-operation trace, whereas a deterministic `FPModel` wrapper may narrow the trace domain. Do **not** admit until a full-domain bridge is compiled and audited. |
| P04-T2 | Product-path and componentwise perturbation error lemmas | Same PDF/version and operational-model gap as T1. Do **not** admit by merely inserting `FPModel` or generic gamma into a trace statement; hard lead only. |
| P10-T1 | Matrix-product perturbation error interface | Verify paper PDF, no target collision, and direct statement reach. |
| P10-T2 | Matrix-product perturbation plus three-source error rule | Verify paper PDF, no target collision, and direct statement reach; hard lead. |
| P12-T2 | Finite-format nearest-rounding interface; FastTwoSum | Verify paper PDF, arbitrary-radix domain, non-collision and direct interface. |
| P14-T1 | Recursive-summation error interface in positive exponential sum | Exact prior PDF hash verified; source pp. 2317–2318 visually inspected. A private `FPModel`/`fl_recursiveSum` statement compiled on Titan (one admission-only target `sorry`) and its extracted semantic dossier directly reaches both declarations. Fresh blind/direct/round-trip candidate audit accepted it as faithful-stronger (result SHA-256 `f47c8367c84e08bd9777e99cede23e45a0f735580a6830094ff9c07f7e9e51eb`); source packet SHA-256 `9fd32199f87e51def28269df3d24b9fda5fa7e7892e2fcff719d3a70f305c10b`, candidate SHA-256 `59b5fa6ce3299424f6ba9c1977f33cb434e09fc253c02616a7e404372085a06d`. Target-result lexical/source scan found no positive exponential-sum error result in NumStability. **Eligible for final freeze, subject to independent source-packet review/collision sign-off.** |
| P14-T2 | Recursive-summation error interface in softmax | Exact source PDF pp. 2317–2319 visually inspected. A private full-domain `FPModel`/`fl_recursiveSum`/`infNormVec` statement compiled on Titan. Fresh blind/direct/round-trip candidate audit accepted it as faithful-equivalent (result SHA-256 `2f1dcfb581a35d6153cbe1ba8107da4817418ceedd6723f4b172139d24e74b69`, candidate SHA-256 `a4e754a8b81e50dc2da2049ee45a2cdde5d7746d384b8eba90e08575a3d77806`). **Eligible for final freeze, subject to collision sign-off.** |
| P14-LOGSUMEXP | Absolute unshifted log-sum-exp error estimate preceding Theorem 3.2 | Exact P14 source pp. 2317–2318 visually inspected. A private `FPModel`/`fl_recursiveSum` statement compiled on Titan. Fresh blind/direct/round-trip candidate audit accepted it as faithful-equivalent; candidate SHA-256 `4cf8f573d4aa57c67c82ef1a210aafde3c2d2bb739247a0a751586f18b6a1a75`, audit-result SHA-256 `9ac38ba7dfa7090885c1b1be2d4043a606b373308d2954fe6163628b6856cc71`. **Eligible for final freeze, subject to collision and independent source-packet sign-off.** |
| HI21-THM2.4 | General-tree summation bound and `SumTree` interface | **Rejected as printed:** the paper's last inequality has an apparent missing first-order factor: for a single rounded addition it would bound an O(u) error by O(u²). Its proof also claims `(1+u)^h ≤ hu/(1-hu)`, false for small `u`. Do not quietly correct the source and call the result faithful. The preceding exact-error Lemma 2.2 remains a separate possible lead. |
| P17-T2 | Finite-expectation and recursive-sum expansion interfaces | Verify paper PDF and source-correct stochastic-rounding execution; hard lead. |
| P20-T2 | Matrix-product input-conversion error interface | Verify paper PDF, mixed narrow-range operation and complete underflow domain. |
| H20-9 | Least-squares backward-error formula components (20.21) | Local Higham chapter available; check entire formula not present, source-complete skeleton and proof feasibility; hard lead. |

The nine Pxx source targets above were among the accepted eligible tasks in
faithfulness audit 004 (`benchmark_faithfulness_audit`, finalized
2026-08-23), but that validates *those earlier Lean statements*, not any
future generated statement or library representation. In particular, the old
paper-scoped shared definitions must never be supplied to N as a common
scaffold in this source-first pilot. New private skeletons are admission
evidence only and never enter contestant workspaces.

## Exclusions already established

- H5-5 and H23-6: likely target-result leakage.
- H10-7: the frozen library already develops the equation-(10.13)
  complete-pivoting invariant; not a clean construction task.
- CAST08 equation (2.2): `blockDotProduct_error_bound` already supplies the
  relevant bound, so it cannot be counted as a fresh result.
- P02-T2: NumStability does not expose the paper's `VecSum`/`Sum2` algorithm;
  generic summation helpers alone do not satisfy the high-overlap gate.
- FAB19-EQ3.5/3.6, RUMP12-THM3.5, LL07-THM4/7: prior proof or
  representation/incidence problems; preserve their historical outcomes but
  do not automatically recycle them to fill this corpus.

## Measurement and integrity requirements for a new identity

- GPT-6 Sol/high single-agent N/L; disable and attest subagent tools. Same
  paper PDF and common prompt; L receives only the frozen library and its
  one-time task-neutral orientation, with no automatic task router.
- Four statement submissions and a separate maximum of four proof attempts.
  A proof with `sorry`/`admit` is rejected and never called proved. The
  prospective no-hole prompt replaces the ambiguous Pilot 29 prompt only
  under the new pilot identity.
- Record formalization-to-faithful, proof-after-faithful, and inclusive total
  contestant time/tokens separately. Preserve audits outside those clocks,
  plus raw observable tool/chat traces, candidate hashes, code size, direct
  declaration reach, proof attrition, and hardware peaks. Do not claim access
  to hidden chain-of-thought.
- Freeze schedule, hashes, difficulty labels, resource envelope, selection
  decisions and report script before measurement. Review the first pair(s)
  for protocol defects, then either continue the frozen schedule or preserve
  that pilot and start a distinctly identified revision. Never silently rerun
  a measured task or remove an unfavorable result.
