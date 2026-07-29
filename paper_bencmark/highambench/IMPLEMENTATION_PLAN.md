# Implementation plan for the P01--P02 pilot

## 1. Read and classify before writing code

The benchmark specification, all 17 pages of P01, and all 34 pages of P02 were
read before selecting the new tasks. P01 has no numbered theorem blocks. P02
has numbered theorem, lemma, proposition, corollary, algorithm, and equation
blocks.

The selection rule was:

1. Use a claim that is made or derived in this paper.
2. Avoid claims whose proof is mainly delegated to another paper.
3. Avoid experimental tables because they are observations, not proof targets.
4. Avoid first-order `O(u^2)` statements unless they can be replaced by a clear,
   exact bound with all assumptions shown.
5. Do not choose a theorem whose exact fixed Lean statement already exists in
   mathlib or NumStability.

For P01 this produced one target for every tier:

- T1 specializes the existing pairwise bound to nonnegative inputs.
- T2 combines the pairwise bound, recursive bound, and the comparison between
  their bound factors.
- T3 asks for the no-guard recursive-summation running-error bound in equation
  (5.3). Its right side uses the actual computed prefix sums. NumStability has
  no accumulated no-guard running-budget theorem. Condition L has a one-step
  no-guard identity and a generic local-error recurrence scaffold, but still
  needs new no-guard state, witness, indexing, and budget bridges or a fresh
  full induction.

P02 also supports every tier:

- T1 is the exact-sum invariant for `VecSum` in equation (4.7)(i), a direct
  iteration of the error-free `TwoSum` identity and close to the library's
  compensated-prefix exactness results.
- T2 is Proposition 4.5, equation (4.8). It combines the `VecSum` invariant,
  Lemma 4.2, ordinary recursive summation, final rounding, and a gamma
  inequality specific to the paper's proof.
- T3 is the no-multiplication-underflow absolute bound in Proposition 5.11.
  It requires an iterated `VecSum`/`SumK` analysis, an error-free product
  transform, its absolute-mass estimate, and new gamma comparisons. The exact
  `DotK` result is absent from NumStability.

Theorem 3.4 was not selected because its central exactness proof is delegated
to earlier work. Relative-error corollaries, experiments, operation counts,
and the larger underflow/error-estimator branches were also not selected.

## 2. Freeze the meaning of each statement

The shared definitions must be usable without importing NumStability. They must
provide only the small setting required by the targets:

- a standard rounded-addition model;
- a no-guard-digit rounded-addition model, where the left and right inputs may
  receive separate small errors;
- exact finite sums and sums of absolute values;
- recursive summation;
- power-of-two pairwise summation;
- the computed-prefix running budget from equation (5.3);
- `gamma u k = (k * u) / (1 - k * u)` in a suitable real-number form;
- the validity assumption `k * u < 1`.
- an abstract error-free `TwoSum` contract;
- `VecSum`, iterated `VecSum`, `SumK`, and `Sum2`;
- the no-multiplication-underflow error-free `TwoProduct` contract; and
- the transformed vector and `DotK` definitions used by Algorithm 5.10.

The word *model* means a small list of rules that an operation must follow. It
does not claim to describe every detail of a physical IEEE-754 machine.

The fixed target declarations are:

- `p01_t1_pairwise_nonnegative`;
- `p01_t2_pairwise_vs_recursive_bounds`;
- `p01_t3_noGuard_recursive_running_error_bound`.
- `p02_t1_vecSum_preserves_sum`;
- `p02_t2_sum2_error_bound`;
- `p02_t3_dotK_error_bound`.

Their fixed files are under `tasks/P01/` and `tasks/P02/`, with one `Target.lean`
per tier. Shared definitions are in `shared/HighamBench/Definitions.lean`.
Every target must compile in clean N and L before the expanded package is
refrozen; target and controlled-file hashes are then recorded in the manifest.

## 3. Keep the statement neutral between conditions

The target statement and every name in it must come from mathlib or the shared
task files. No target statement may mention a NumStability declaration.

Condition L may use a separate adapter in the submitted proof. An adapter is a
small piece of code that connects the shared model to the library's model. The
fixed target file itself stays unchanged. Condition N must not contain that
adapter if it exposes a library name or artifact.

Before release, build every fixed statement in both clean environments. Hash the
controlled files and have the validator reject any changed hash.

## 4. Build the validator

The validator must run in a fresh hidden copy of the frozen project and check:

1. The exact target declaration is present and Lean accepts it.
2. Controlled statement and task files have their recorded SHA-256 values.
3. The proof has no `sorry`, `admit`, new axiom, unsafe checking bypass, hidden
   answer, or forbidden import.
4. Only allowed local tools were used and no network request was attempted.
5. Condition N exposes no NumStability source, compiled file, documentation,
   name list, search index, or cache.
6. A condition-L pass records the NumStability declarations in the checked
   proof's full dependency chain. A dependency chain is the list of definitions
   and theorems on which a proof ultimately relies.

A text search for a library name is not enough for step 6. The check must inspect
Lean declarations reached by the proof and by any local helper declaration.

## 5. Freeze evaluation inputs

The current fixed items are recorded in `metadata/config.json`:

- Lean toolchain;
- mathlib commit;
- NumStability baseline commit;
- 900-second wall-clock limit;
- 120,000-total-token limit;
- three repetition IDs;
- deterministic pair order;
- model-tool network isolation requirement.

The exact agent version, model version, prompt hash, allowed-tool list, and
machine class are frozen in `metadata/config.json` and `metadata/environment.json`.
The selected backend has no demonstrated random-seed control, and the runner
uses fresh bubblewrap namespaces rather than a frozen OCI container image. An
OCI image is a packaged operating-system environment. These two differences are
recorded explicitly and make the result observational, not an official
reference-protocol score.

## 6. Run the two conditions fairly

For each task and repetition:

1. Start the first condition shown in `metadata/run_order.json` in a new
   bubblewrap namespace and new conversation.
2. Stop at the first valid proof, the time limit, the token limit, or when the
   agent ends.
3. Save the raw log without showing it to the paired run.
4. Destroy the namespace, temporary agent state, and generated caches.
5. Start the second condition in another new namespace and conversation.

Do not pass messages, files, build output, searches, caches, or knowledge from
one condition to the other.

## 7. Record measurements

For every run record:

- pass or fail;
- real wall-clock stop time;
- scored time, using 900 seconds for a failure;
- input, output, cached-input, and total model-token counts;
- whether a passed L proof truly depends on NumStability;
- the library declaration names used;
- one failure code and a short explanation when the run fails.

Use the failure-code order from HighamBench 0.2. A timeout remains
`TIME_LIMIT` even when the last Lean file also has an error.
A denied socket call is recorded outside the evaluated process and prevents a
pass, including when the proof passes Lean validation. It becomes
`RULE_VIOLATION` unless `TIME_LIMIT`, `TOKEN_LIMIT`, or `NO_SUBMISSION` has the
higher-priority label. A clean agent exit with no proof remains
`NO_SUBMISSION`; failure to start the agent is a measurement-system error
rather than an agent omission.

## 8. Analyze without hiding runs

Report all 36 assignments. Do not choose the best repetition.

For N and L, report overall and by T1, T2, and T3:

- scored runs, passes, and pass rate;
- median scored time;
- median token count;
- each failure-code count;
- for L, passed runs that actually use NumStability.

For each matching task and repetition, calculate L minus N. Report the pass-rate
change and the median of paired time and token changes. Do not combine these
different measures into one score.

The full specification asks for a 95 percent range by resampling whole papers.
With only P01 and P02, this range has extremely limited resolution. Keep all
three tiers from a paper together and label the two-paper limitation plainly.

## 9. Complete two reviews

Two separate review records cover every task:

- Reviewer 1 checks the paper citation, meaning, proof context, and tier choice.
- Reviewer 2 checks the neutral Lean interface, existing-library overlap,
  condition isolation, hashes, and validator readiness.

The first records were preliminary reviews. After the build, isolation, search,
and construction evidence is frozen, two separate final review passes must
replace them. A status changes to `pass` only when saved evidence supports it.

## 10. Completion checklist

- [x] Exactly P01 and P02, and no other papers, are in the manifest.
- [x] T1, T2, and T3 are selected for both papers before evaluation.
- [x] Source and specification PDFs are hashed.
- [x] Lean, mathlib, and NumStability source versions are frozen.
- [x] Limits and three repetition IDs are fixed.
- [x] Pair order is fixed by a repeatable rule.
- [ ] Two review records cover all six tasks against current evidence.
- [x] All six final fixed Lean statements compile in both clean conditions.
- [x] Exact controlled task hashes and the expanded construction-package hash are frozen.
- [x] N is rechecked to contain no NumStability artifact for every task.
- [ ] L dependency checking finds real declarations in all six private L construction proofs.
- [x] Agent, model, prompt, tools, and machine class are frozen.
- [x] The lack of a backend seed and OCI image is recorded as an observational limitation.
- [ ] Two final independent review records pass against the frozen evidence.
- [ ] All 36 isolated runs are complete.
- [ ] Raw logs, result tables, and the final plain-language PDF report are built.
