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
| P14-ALT-SOFTMAX | Division-free unshifted softmax, Theorem 3.4 | Exact source pp. 2318–2319 visually checked. A private `FPModel`/`fl_recursiveSum` full-execution statement compiled on Titan and a fresh blind/direct/round-trip audit accepted it as faithful-equivalent (candidate SHA-256 `9a00ecffe328586fd2eac0ee840e58592f2ae5ccbab12db63f21dd5d6d5b6491`, audit-result SHA-256 `929163e182d4b9e310fb6b574c6aee9ce5ef55a59ee674acc370157f2dc6d3e2`). **Eligible for final freeze, subject to collision and independent source-packet sign-off.** |
| P14-SHIFTED-SUM | Shifted positive exponential sum, equation (4.6) | Exact source pp. 2321–2322 visually checked. Private statement compiles on Titan after retaining the paper's omission of the selected maximum; one target `sorry` is admission-only. Fresh blind/direct/round-trip audit accepted it as faithful-equivalent (candidate SHA-256 `7324539266f7d7b7ba3e08232e3c7ab4850f2a536bb5a3fe8f2ae2923264cfe2`, audit-result SHA-256 `504bcfc6509de4c986f5c641e6f58cb0abe5b975cb4dbd43ac9bf7d4080e0911`). **Eligible for final freeze, subject to collision and independent source-packet sign-off.** |
| P14-SHIFTED-LOG | Shifted log-sum-exp intermediate, equation (4.8) | Exact source pp. 2321–2323 visually checked. Candidate models the paper's intermediate before the explicitly ignored final rounded addition and compiles on Titan. Fresh blind/direct/round-trip audit accepted faithful-equivalent (candidate SHA-256 `2f74e4831d041a296c4125ecc007384e5fe9036a9a13a9f6e934abe289f89663`, result SHA-256 `df171f6e2637d689985fd20107962faabdb6a38303f70b71c4c4d9bb15c2ef46`); statement directly reaches `NumStability.fl_recursiveSum` and `infNormVec`. **Eligible for final freeze, subject to collision sign-off.** |
| P14-SHIFTED-SOFTMAX | Shifted softmax, Theorem 4.3 | Exact source pp. 2321–2324 visually checked. Candidate models all output entries, local shifted-exponential errors, omission of only the selected maximum from the denominator sum, and rounded final divisions; compiles on Titan. Fresh blind/direct/round-trip audit accepted faithful-equivalent (candidate SHA-256 `371a0238b77c7df09c19e6e56297361687f2d41bf7f27e39d04995063ba80851`, result SHA-256 `fe4da567bfa5c30415108597a8ee2ee06069c950a27d92227017ed12d2bcb148`); statement directly reaches `NumStability.fl_recursiveSum` and `infNormVec`. **Eligible for final freeze, subject to collision sign-off.** |
| P14-SHIFTED-WEIGHTED | Term-specific shifted exponential-sum error, equation (4.5) | Exact source pp. 2321–2322 visually checked. Candidate keeps each term's gap and recursive-sum position; compiles on Titan. Fresh blind/direct/round-trip audit accepted faithful-equivalent (candidate SHA-256 `ff790d417f8e16ebb25f5b08f91c4680c65d97c4761716f71d0d438b0fa104df`, result SHA-256 `ca7143bf101438725d788c4ff458ea8da73836213b97d2f613befdff9ffbd15a`). This is a correlated finer bound for the same algorithm as P14-SHIFTED-SUM, not an independent paper replication. **Eligible for final freeze, subject to collision sign-off.** |
| HI21-LEM2.2 | General binary-tree summation, exact error expansion | An initial candidate compiled and was accepted as faithful-equivalent (SHA-256 `75c3e3af9885c7e7a11d39080b1b6988e68bc67877084da2dee5367dbc1edec4`), but a later independent audit of the related Eq. (2.7) exposed a shared source-domain flaw: `FPModel` requires zero-operand exactness absent from the paper's abstract relative-error assumptions. **The initial acceptance is not used for admission.** A full-domain relational trace using `NumStability.signedRelErrorWitness`, `SumTree`, and `SumTree.exactSum` compiles; fresh audit-b accepted faithful-stronger, candidate SHA-256 `e716f25dca02d883b343e27dfaaee0bb71015535a6edd156446c3ad84981f7d0`, result SHA-256 `83585e3ab9d2006a45d8a0469db23a521e94f0f39a1e9ba4ca334d588d3f2185`. Eligible for freeze subject to final direct-use and collision gates. |
| HI21-LEM2.3 | General binary-tree local-error expansion | Private full-domain statement compiled and independent audit accepted faithful-equivalent (candidate SHA-256 `8adec1b181d209608e1da40167229146583de70803df0a6acefb967a3c7eb549`, result SHA-256 `383800954aaafd8b49321791e02cfa86968dca6a6a682609c08c8e258bd7f834`). **Excluded for content-near-collision:** `NumStability.SumTree.runningErrorContribution_eq_error` already establishes the arbitrary-tree exact local-error decomposition in a dual inverse-relative-error parameterization. Different witness radii prevent calling it literally identical, but treating a simple reparameterization as new construction would overstate the benefit. |
| HI21-EQ2.7 | First-order general-tree error expansion | First candidate rejected `unfaithful-weaker` for allowing the O(u²) coefficient to depend on tree height (result SHA-256 `1313b98a3a4d706f8dd8dedd9e1d53494fd867338a67f691ed33f51522ef19d9`). Audit-b stopped at a basename preflight. Corrected uniform-coefficient audit-c was rejected `unfaithful-weaker` because `FPModel` imposes zero-operand exactness, narrowing the paper's execution domain (result SHA-256 `4df07e16fb74daf904ee63965e743dd189d5ea5b5922d0f92dcea2002fe9c127`). A full-domain relational trace using `NumStability.signedRelErrorWitness`, `SumTree`, and `SumTree.exactSum` compiles; fresh audit-d accepted faithful-equivalent, candidate SHA-256 `9431f05a978f224a38f10927c662830f644ad27ce1a65d04e530d19050e319af`, result SHA-256 `18352a7e3979c0b583f05c32d10ef0efba3222babeb55e50e7cc92f72c3a094a`. All prior candidates and diagnostics remain preserved. Eligible for freeze subject to final direct-use and collision gates. |
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
