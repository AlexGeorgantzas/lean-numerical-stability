# Prospective Pilot 20: corpus and resource gates

Status: **design only, not an admitted or launched measured pilot**. Pilot 19's
`HM19-3-2` pair and its unfavorable/incident outcomes remain frozen. No Pilot
19 input, audit, or result is rewritten by this proposal.

## Corpus gate (highest priority)

A source task enters the new measured corpus only after an independent,
source-first admission record contains all of the following:

1. The exact source theorem/equation and full domain, algorithm, assumptions,
   conclusion, and all referenced definitions; unresolved source wording fails.
2. At least one **specific declaration in the pinned NumStability snapshot**
   that can occur in a faithful full-domain Lean statement or its essential
   algorithm implementation. Record its exact name, signature, module, hash,
   and the role it plays. A mere topical resemblance, shared `gamma`, or a
   deterministic analogue of a stochastic trace is not enough.
3. A separately checked absence of the target result under any name in that
   snapshot. The L condition must gain reusable components, not the answer.
4. A private `by sorry` compatibility skeleton that compiles against the
   frozen NumStability snapshot and uses the named declaration without
   weakening/narrowing the source task. This skeleton is admission evidence,
   **not** a solver packet, prompt, gold Lean theorem, or proof hint.
5. A source/packet and declaration-collision review completed before measured
   attempts. Known older benchmark outcomes must be marked as development
   evidence; selecting only their favorable cases cannot be a confirmatory
   result.

Preliminary re-screen of old suggestions (not final admissions):

| Task | Finding | Current disposition |
|---|---|---|
| Pilot 19 `HM19-3-2` | Its accepted L statement reached no NumStability declaration. Its first L candidate did attempt lower-level `BasicOp` use, but the bounded interface rejected those members; this is a separate prospective interface defect. The deterministic `fl_dotProduct`/`FPModel` interface also does not automatically represent the paper's independent stochastic operation trace. | Preserve the pair; do not claim confirmed direct-use overlap or attribute the outcome to a single cause. |
| `H5-5` | The pinned snapshot's `fl_rootProductEval_forward_error_bound` has exactly the packet's proposed `γ_(2n)` bound for `fl_rootProductEval`; this was checked in the Lean source, not inferred from the name. The book itself only says “give an error analysis”; the packet chose that coefficient. | Exclude: target-result leakage, not a clean primary task. |
| `H7-12` | The formerly cited `higham12_componentwiseBackwardOmega_*` declarations concern a Chapter 12 discontinuity construction, not the Chapter 7 symmetric perturbation existence result. | Exclude under the direct-use criterion unless genuinely relevant declarations are found. |
| `H10-7` | `higham10_7_fl_cholesky_success` is an unrelated **Theorem** 10.7, but deeper source inspection found `psd_pivoted_cholesky_exists_tail`, explicitly documented as the exact (10.13) complete-pivoting column-tail invariant requested by **Problem** 10.7. | Exclude: target-result leakage. |
| `H20-8` | The source asks to evaluate **`η_F(0)`** at `θ=∞`/`Δb=0`. The old packet incorrectly required `y ≠ 0` and instead targeted a generic limiting case. The pinned library defines `lsNormwiseBackwardErrorMatrixOnlyEtaF` and proves a generic limit, but the checked least-squares module has no closed-form zero-vector evaluation. A private full-domain statement using the library definition and the `b=0`/`b≠0` branches compiled on Titan against the frozen `.olean` snapshot. | Promising **development canary** after a new source-correct packet and independent collision review; previous exposure prevents treating it as held-out confirmation. |
| `H20-9` | The pinned least-squares module already contains the (20.21) formula RHS and many exact `lsNormwiseBackwardErrorEtaF_eq_formulaRHS_*` branches, including the source-facing rank/attainment cases. This is substantive target coverage, not merely a similarly named quantity. | Exclude: target-result leakage. |
| `H23-6` | The frozen snapshot has `higham23_threeMStrassen_sourceCoefficient`, whose source comment and full Lean conclusion explicitly give the combined 3M–Strassen (23.14) coefficient with multiplier six and four added. The packet also flags wording ambiguity. | Exclude: source-result leakage, independently of the wording issue. |

The prior `higham_exercise_screening.md` labels some of these “building blocks
only.” That label is not authoritative after these concrete checks. The
remaining Pilot 19 probabilistic tasks likewise need per-task compatibility
proofs; the old thematic component table is insufficient. Do not fill a
twelve-task quota with non-overlapping tasks. A smaller honest corpus is better.

## Prospective retrieval and warm-start policy

Pilot 19's statement runner made the automatically retrieved packet an
**exhaustive access whitelist**: only selected NumStability `.olean` modules
were mounted, library source/index searches were rejected, and direct use of
an unlisted declaration failed validation. This can suppress useful library
support even when it exists. Its results remain unchanged.

For Pilot 20, the packet is a **ranked starting guide, not an access boundary**.
The L formalizer receives the entire pinned NumStability source, compiled
snapshot, and declaration index read-only. It may query/search them and use
any compatible declaration, including one the router missed. N analogously
may search its full Mathlib source/index, but cannot see NumStability. The
source packet, candidate-integrity rules, condition blindness of auditors,
and target-result collision gate remain unchanged. Task-time search, Lean
probes, and compilation are logged and charged to the formalizer clock; no
task-specific declaration packet is supplied off-clock. Semantic dossiers
record the actual direct NumStability declarations used, not name mentions.

The one-time Pilot 20 L orientation prompt requests verified exact imports
and types for task-neutral basics such as `FPModel`, `BasicOp`, `gamma`,
`gammaValid`, and rounding tools. Its frozen conversation will be forked for
each L task; scouting time/tokens are recorded once outside per-task metrics.
The orientation is not a substitute for full library access. A new warm root
and pilot identity must be frozen before measured work; Pilot 19's root is not
retrofitted. The open-snapshot runner path and prompt are coded but no Pilot
20 warm root or measured task has yet been launched under this policy.

Promising *new* source to inspect, **not yet admitted**: Blanchard–Higham–Mary,
*A Class of Fast and Accurate Summation Algorithms* (2019), §§3–4,
<https://eprints.maths.manchester.ac.uk/2729/3/paper.pdf>. Its FABsum family
builds block sums using recursive summation, and the library exposes
`fl_recursiveSum` (and `FPModel`). Equations (3.5)–(3.7) specialize to concrete
choices; Theorems 4.1–4.6 cover inner products, matrix products, triangular
solves, and LU. Exact algorithm/model matching, first-order `O(u²)` semantics,
result leakage, and full-domain skeletons remain to be checked. Several
results from one paper are correlated, not independent evidence.

### FABsum source-specific screening, 2026-09-23

Two distinct Algorithm 3.1 specializations now have prospective packets,
`design20/packets/FAB19-EQ3.5.json` and `FAB19-EQ3.7.json`, tied to the
author-hosted PDF SHA-256
`6a450af462ecb0479f8d96a7833e6c09ae915b678fbef4e86d5b373cde509ff1`.
They are **candidates pending independent source review**, not admitted tasks
or benchmark results.

- Equation (3.5): recursive size-`b` blocks at roundoff `u`, recursive
  accumulation of all `k=n/b` block totals at roundoff `u²`, then one working-
  precision rounding. Direct library components are `fl_recursiveSum` and
  `fl_higherPrecisionRecursiveSum`. A private `by sorry` statement compiled
  against frozen `.olean`s for arbitrary positive `k,b` and all real inputs;
  its finite-`u` coefficient is
  `γ_(b-1)(u) + γ_(k-1)(u²) + γ_(b-1)(u)γ_(k-1)(u²)
   + u(1+γ_(b-1)(u))(1+γ_(k-1)(u²))`, whose first-order term is `b*u`.
  **Source-domain detail requiring independent review:** at `k=1` the paper
  says FABsum is entirely FastSum. The private statement now includes an
  explicit structural working-format representability predicate and the law
  that rounding an already representable block result is exact, so it does not
  silently drop `k=1` or permit a spurious extra rounding. Review whether this
  abstract law sufficiently captures the paper's nested precisions.
- Equation (3.7): recursive size-`b` blocks and arbitrary-length pairwise
  accumulation of `k` totals. Direct components are `fl_recursiveSum` and
  `fl_clog2PairwiseSum`; the latter supports any positive `k` using exact zero
  padding, with a public `clog2PairwiseSum_backward_error` lemma. A private
  `by sorry` statement compiled for arbitrary positive `k,b` and all real
  inputs. Its finite-`u` coefficient is
  `γ_(b-1)(u)+γ_(ceil(log₂ k))(u)+γ_(b-1)(u)γ_(ceil(log₂ k))(u)`, agreeing to
  first order with the paper's `(b-1+ceil(log₂ k))*u`.

Both private statements are in
`/hdd/alexgeorgantzas/highambench/pilot20-admission-private/FAB19-EQ3.5-3.7-skeleton.lean`
(SHA-256 `5fab82937c8671347e283086ef01e2efacde698d0ae965505512d299fe8b3e47`),
outside the contestant checkout. Compile exit status was zero with only the
expected `sorry` warnings. The frozen source modules containing the direct
components hash to `3dc26514...` (Recursive/Core) and `607acea5...`
(Pairwise/Core). A name/content scan found no `FABsum`/block-composition target
in the frozen library; independent semantic collision review is still required.
This pair is from a single paper and shares its recursive-block kernel, so
its outcomes must not be counted as two independent source families.

Another author-hosted source screened but **not admitted**: Xiaobo Liu,
*Mixed-Precision Paterson–Stockmeyer Method for Evaluating Polynomials of
Matrices*, Lemma 2.2 and Theorem 2.3,
<https://eprints.maths.manchester.ac.uk/2888/1/paper.pdf>. The pinned library
has a directly usable `fl_matMul` and an exact Paterson–Stockmeyer algorithm,
but the printed Lemma 2.2 initializes `X̂₀ = X`, then says
`X̂ₖ = fl(X̂ₖ₋₁ X)` for `k=1:t` while treating `X̂ₜ` as `X^t`; literally this
recurrence gives `X^(t+1)` in exact arithmetic. The adjoining proof starts at
`t=2`, suggesting a one-based intended recurrence. Do not silently repair
this in a measured packet. Source-resolution review is needed before either
that lemma or the dependent Theorem 2.3 is admitted. The inspected PDF is
`design20/sources/LIU24-PS.pdf`, SHA-256
`56e71da96e04d1a8c216a70207b856f993405d24334e3152b4d0d0c39d6ecdc7`.

A separate **potential source family**, not yet admitted, is Langlois–Louvet,
*Faithful Polynomial Evaluation with Compensated Horner Algorithm*,
<https://arxiv.org/pdf/cs/0610122>, Algorithm 6 and Theorem 4. The target
forward-error bound is `u|p(x)| + γ_(2n)^2 p̃(x)`. The frozen library has
`fl_hornerDesc`, which Algorithm 6 can use for its correction-polynomial
evaluation, but no `CompHorner`/`EFTHorner` implementation or result was found
in the checked Horner module. Source faithfulness hinges on representing the
actual error-free `TwoProd`/`TwoSum` transformations and their no-underflow
conditions, rather than smuggling the final bound into an abstract EFT
contract. The inspected PDF is `design20/sources/LL07-CompHorner.pdf`, SHA-256
`acba19c03f7997d6fa0b5537d1b7a79491ae952f3425a4604e04c2be18fb929e`.
No packet or compatibility skeleton is claimed yet.

## Three-lane resource gate

Titan currently exposes 32 logical CPUs and about 94 GiB physical RAM. Its
CPU topology is asymmetric: CPUs 0–15 form eight SMT pairs; CPUs 16–31 are
sixteen single-thread cores. Three proposed non-overlapping, *topologically
balanced* lanes are:

| Lane | Logical CPUs | Distinct physical cores | RAM cap |
|---|---|---:|---:|
| A | `0-3,16-19` | 6 | 24 GiB |
| B | `4-7,20-23` | 6 | 24 GiB |
| C | `8-11,24-27` | 6 | 24 GiB |

CPUs `12-15,28-31` remain outside benchmark lanes. Before admission, validate
current topology, actual affinity/cpuset, `MemoryMax=24GiB`, swap prohibition,
and cgroup containment for each lane. Three times 24 GiB is 72 GiB; spare RAM
does **not** by itself rule out shared cache/memory-bandwidth, CPU-frequency,
storage, or model-provider contention. Run a predeclared, non-contestant
single-lane versus three-lane calibration first. If the three-lane setup
materially degrades a fixed workload or produces unbalanced lanes, stay
sequential or report concurrent timing as a separate setting. Do not switch
because a benchmark outcome is unfavorable.

The prospective `tools/design20_envelope.py` now launches separate systemd
services with the exact A/B/C CPU sets, `MemoryMax=24GiB`, swap disabled, and
an 18-GiB generated-command child cap. A non-contestant **simultaneous
three-service canary** on Titan on 2026-09-23 returned `admitted=true` for all
three, with distinct cgroup paths, exact CPU affinity, exact 24-GiB effective
memory ceilings, and `memory.swap.max=0`. This establishes resource
containment, **not** performance noninterference or readiness to run three
measured tasks. The predeclared contention calibration is still pending.

Calibration is fixed *before any Pilot 20 contestant run*: eight independent
SHA-256 workers per lane, each hashing a private 64-MiB buffer 64 times. Run
three solo repetitions for each lane, then three simultaneous A/B/C
repetitions using the same script and workload. Compare the median elapsed
time of each lane's triple runs with its solo median. Three-way measured
dispatch is admitted only if every ratio is at most **1.25** and the
three triple medians differ by at most **15%** (`max/min ≤ 1.15`), with no OOM
or cgroup violation. All calibration traces and ratios remain in the record
even if this gate fails. This calibration tests local CPU/memory interference,
not remote model-provider concurrency; co-load must still be logged per
condition and interpreted cautiously.

The fixed calibration was run on Titan on 2026-09-23, before any Pilot 20
contestant. Nine solo and nine triple service reports and their per-run
resource traces are retained, without overwrite, at
`/hdd/alexgeorgantzas/highambench/pilot20-calibration-20260923/` (directory
mode 0700; report/trace files mode 0400). The calibration script SHA-256 in
every report is
`fa62f173f80cbb9ea8c3149525d54d6b45b9d4632babe541cb02fe7b2ab44aa4`.
The simultaneous intervals overlap for all three triple repetitions.

| Lane | Solo median, s | Triple median, s | Triple / solo | Peak sampled RAM across runs |
|---|---:|---:|---:|---:|
| A | 2.186 | 2.219 | 1.015 | 0.546 GiB |
| B | 2.174 | 2.199 | 1.011 | 0.546 GiB |
| C | 2.110 | 2.338 | 1.108 | 0.546 GiB |

Triple-median imbalance was `1.063`; no run reported an OOM event. The
predeclared local-hardware gate therefore **passes**. The approximately 8.05
sampled peak CPU cores sometimes exceeds the eight-CPU physical cap by less
than 1% due to short-interval accounting/timestamp noise; preserve raw values
and label them sampled interval estimates, not instantaneous hardware peaks.
This short synthetic workload does not establish that Lean compilation or
remote GPT-6 calls will have the same interference profile. Neither the
measured corpus nor the full three-task controller is admitted yet.

Run an initial pair or two behind the existing early-review gate before
dispatching three different tasks in parallel. Keep R0 and R1 of each task
sequential in the same lane; alternate order as frozen. Each lane needs a
separate lock and cgroup. Log companion workload/condition IDs so paired
timings can be interpreted when another lane changes state. Never launch an
overlapping campaign or silently rerun a measured task.

For each condition, sample `memory.current`, `memory.peak`, `cpu.stat`, and
`memory.events` from its exact lane cgroup. Report sampled condition-local peak
RAM, peak one-second average CPU cores (and percent of eight), cumulative CPU
seconds, cgroup-lifetime RAM peak (labelled as such), OOM events, sample cadence,
and the complete trace hash. Resource collection is outside the contestant
token/time accounting; it must not be used to discard slow or unfavorable
outcomes. `tools/design20_telemetry.py` has unit tests and is integrated
behind a **prospective-only** `--sample-hardware` flag in the shared statement
runner. It resolves the bounded lane **parent** service cgroup containing both
the trusted controller and generated-command child, then samples from the
formalizer turn through
candidate freeze, sealing a read-only trace and summary under each attempt.
No Pilot 20 wrapper enables this flag yet, and the three-lane envelope has
not passed calibration; this is not evidence that a measured concurrent run
is ready. A non-contestant read of Titan's cgroup-v2 `cpu.stat`,
`memory.current`, and `memory.peak` succeeded on 2026-09-23; that checks the
sampling mechanism, not the 8-CPU/24-GiB isolation or peak attribution in a
full contestant run.

## Prospective integrity repairs already coded on the new branch

The validator now distinguishes an inductive constructor/projection named
`constant` from a forbidden top-level `constant` declaration. The treatment
interface, when `FPModel` is exposed, now admits only the closed foundational
`BasicOp` constructor/exact-interpreter family used by that public model;
unlisted results in the same module remain barred. Regression tests cover both
cases. These fixes are **prospective**: Pilot 19's earlier rejections remain
recorded as they occurred and are not retrospectively converted to successes.

The candidate-development packet `design20/packets/H20-8.json` now reflects
the book's actual zero-vector exercise and includes both `b` branches. The
task-neutral least-squares router family exposes the public matrix-only error
quantity and generic normal-equations characterization, not the closed-form
answer. This router change was made using a **development canary**, so H20-8
must not be counted as held-out evidence for the new router.

The refined private H20-8 admission skeleton (a statement ending in
`by sorry`, not a proof) includes **attainment**, because the source uses a
minimum rather than an arbitrary infimum. Its SHA-256 is
`d6a8b1004f9e2c9df8d3ea4cc4c4975ddb20a89779a6e738769b0dd3f993606b`.
It compiled against Titan's frozen NumStability `.olean` snapshot on
2026-09-23. It is stored outside the benchmark checkout at
`/hdd/alexgeorgantzas/highambench/pilot20-admission-private/H20-8-attainment-skeleton.lean`
with mode 0600 and must not be mounted in either contestant workspace or sent
to any formalizer/auditor. The initial infimum-only draft was retained at
`H20-8-skeleton.lean` for provenance but is not the admission statement.
