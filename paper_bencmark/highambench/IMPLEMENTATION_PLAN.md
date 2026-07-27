# Implementation plan for the P01 pilot

## 1. Read and classify before writing code

The benchmark specification and all 17 pages of the source paper were read
before selecting a task. The paper has no numbered theorem blocks. Its main
formal results are numbered equations and nearby prose statements.

The selection rule was:

1. Use a claim that is made or derived in this paper.
2. Avoid claims whose proof is mainly delegated to another paper.
3. Avoid experimental tables because they are observations, not proof targets.
4. Avoid first-order `O(u^2)` statements unless they can be replaced by a clear,
   exact bound with all assumptions shown.
5. Do not choose a theorem whose exact fixed Lean statement already exists in
   mathlib or NumStability.

This produced one target for every available tier:

- T1 specializes the existing pairwise bound to nonnegative inputs.
- T2 combines the pairwise bound, recursive bound, and the comparison between
  their bound factors.
- T3 asks for the no-guard recursive-summation running-error bound in equation
  (5.3). Its right side uses the actual computed prefix sums. NumStability has
  no accumulated no-guard running-budget theorem. Condition L has a one-step
  no-guard identity and a generic local-error recurrence scaffold, but still
  needs new no-guard state, witness, indexing, and budget bridges or a fresh
  full induction.

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

The word *model* means a small list of rules that an operation must follow. It
does not claim to describe every detail of a physical IEEE-754 machine.

The fixed target declarations are:

- `p01_t1_pairwise_nonnegative`;
- `p01_t2_pairwise_vs_recursive_bounds`;
- `p01_t3_noGuard_recursive_running_error_bound`.

Their fixed files are `tasks/P01/T1/Target.lean`,
`tasks/P01/T2/Target.lean`, and `tasks/P01/T3/Target.lean`. Shared definitions
are in `shared/HighamBench/Definitions.lean`. All three targets now compile in
N and L, and the final hashes are recorded in the manifest.

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

Report all 18 assignments. Do not choose the best repetition.

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
With only P01, this resampling always selects the same paper, so the range has no
useful information. Generate it only for format compatibility and label it as a
single-paper limitation.

## 9. Complete two reviews

Two separate review records cover every task:

- Reviewer 1 checks the paper citation, meaning, proof context, and tier choice.
- Reviewer 2 checks the neutral Lean interface, existing-library overlap,
  condition isolation, hashes, and validator readiness.

The first records were preliminary reviews. After the build, isolation, search,
and construction evidence is frozen, two separate final review passes must
replace them. A status changes to `pass` only when saved evidence supports it.

## 10. Completion checklist

- [x] Only P01 is in the manifest.
- [x] T1, T2, and T3 are selected before evaluation.
- [x] Source and specification PDFs are hashed.
- [x] Lean, mathlib, and NumStability source versions are frozen.
- [x] Limits and three repetition IDs are fixed.
- [x] Pair order is fixed by a repeatable rule.
- [x] Two preliminary review records cover all tasks.
- [x] Final fixed Lean statements compile in both clean conditions.
- [x] Exact task hashes are added; the final release hash remains pending until all tools are stable.
- [x] N is shown to contain no NumStability artifact.
- [x] L dependency checking finds real declarations in all three private L construction proofs.
- [x] Agent, model, prompt, tools, and machine class are frozen.
- [x] The lack of a backend seed and OCI image is recorded as an observational limitation.
- [ ] Two final independent review records pass against the frozen evidence.
- [ ] All 18 isolated runs are complete.
- [ ] Raw logs, result tables, and the final plain-language PDF report are built.
