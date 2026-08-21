---
name: highambench-task-builder
description: Repair and rebuild existing HighamBench Lean tasks that failed or remained unresolved in a faithfulness audit. Use when the Builder is asked to fix, correct, reconstruct, or revise a task such as P11-T1, or to improve the audited-task repair workflow under paper_bencmark. Require the latest hash-verified audit decision as diagnostic input, reconstruct the selected paper result faithfully, update construction artifacts, validate both benchmark conditions, and prepare the task for an independent re-audit.
---

# HighamBench Task Builder

Repair exactly one existing task per invocation unless the user explicitly asks
for a paper batch. Preserve the selected paper result; do not replace it with an
easier supporting lemma merely to retain a tier or obtain a proof.

## Keep roles separate

- The Builder may edit the task statement, paper-specific definitions,
  construction metadata, context, and private construction proofs.
- The Builder must not edit prior task-local `faithfulness/` artifacts or
  `faithfulness_audit/history/audit_NNN/`.
- The Builder may perform a semantic pre-check but must not declare its own
  repair faithful. An independent Auditor decides that.
- The Executor may run measurements only after the repaired task is independently
  accepted and the corpus is frozen.
- Do not commit, push, run measurements, or create a new audit entry unless the
  user explicitly requests it.

## Load the audited failure

1. Read `paper_bencmark/AGENTS.md`,
   `paper_bencmark/TASK_SOURCE_TAGS.md`, and
   `paper_bencmark/highambench/README.md`.
2. Validate the requested ID. Do not guess which task the user means.
3. Run:

   ```bash
   python3 <skill-directory>/scripts/audit_context.py P11-T1 \
     --repo-root /path/to/lean-fp-analysis
   ```

   The script selects the newest completed corpus audit containing the task,
   verifies the history result hash, verifies or recovers the pinned decision
   and report, and compares the current target and PDF with their audited hashes.
4. Stop before editing when the PDF hash differs. If the target hash differs,
   inspect the intervening changes and determine whether the audit still applies;
   never apply findings blindly to a different target.
5. If the latest decision has `accepted: true`, do not repair the task unless
   the user explicitly asks for another change.
6. Read the complete final decision and report. Also read the source contract,
   direct judgment, round-trip judgment, and adjudication output when present.
   The audit is a mandatory diagnosis, not a substitute for checking the paper.

## Establish the repair contract

Before editing, state a concrete checklist that includes:

- the exact selected paper result and surrounding theorem or derivation;
- every binder, quantifier dependency, hypothesis, conclusion, case, and
  constant;
- dimensions, index sets, norms, and equality or inequality direction;
- exact, computed, rounded, and perturbed quantities;
- algorithm, execution model, floating-point assumptions, exceptional-value
  scope, error notion, and higher-order terms;
- every audit finding, including minor findings and unresolved uncertainties;
- every failed or unclear semantic check;
- why each previously failed implication direction will hold after the repair;
- nonvacuity and satisfiability of the proposed assumptions;
- whether a faithful rebuild still has the task's recorded tier.

Classify each audit item as `must change`, `must preserve`, or
`needs source resolution`. Resolve every item before handoff.

## Reconstruct from primary evidence

1. Verify the paper path and SHA-256 from the audit and `task.json`.
2. Read the selected PDF result, its definitions, hypotheses, surrounding
   theorem, and proof context. Inspect rendered pages for notation that text
   extraction may lose.
3. Read `Target.lean`, `context.md`, `task.json`, the paper's
   `paper.json`, the complete imported local definitions, and the elaborated
   types of every nontrivial declaration in the target.
4. Search the frozen mathlib and NumStability baselines for exact and nearby
   results. Verify declaration names in source and Lean.
5. Rebuild the mathematical proposition, not the wording of the old target.
   Preserve algorithm linkage, witness dependence, computed status, norm
   semantics, dimensions, and source assumptions.

The repaired declaration may be equivalent to the paper result or genuinely
stronger. A statement with added assumptions, reduced dimensions, deleted
conclusions, changed norms, detached algorithms, or vacuous premises is not a
faithful strengthening.

If the selected source is ambiguous, unsuitable as a standalone benchmark
claim, or mainly delegated to another paper, stop and present the evidence.
Do not silently select a different result. Source reselection requires explicit
user approval and then follows the full paper-task selection workflow.

## Preserve benchmark construction rules

- Put definitions used by only this paper in
  `shared/HighamBench/P0XDefinitions.lean`. Move a definition to
  `Core.lean` only when at least two papers genuinely use it.
- Make the target import only `HighamBench.P0XDefinitions`.
- Keep the target statement and controlled shared files condition-neutral. No
  NumStability name may occur there.
- Keep `classification_frozen_before_runs` false during repair.
- Update `Target.lean`, `context.md`, `task.json`, `paper.json`, and source tags
  where the repaired mathematics requires it.
- Keep source tags and result-form tags tied to the selected paper claim, not a
  supporting lemma.
- Re-evaluate the tier against the frozen library. Do not weaken the theorem to
  preserve its old T1/T2/T3 label. If the correct tier would collide with
  another task or require paper-level reassignment, stop and propose the
  coordinated change before renaming or replacing tasks.
- Keep complete private N and L proofs outside the controlled task. Do not put a
  gold proof into `Target.lean`.

## Defer corpus-wide snapshot hashes

During an active multi-task rebuild cycle, do not run the full snapshot refresh
or hand-edit global metadata merely to propagate hashes. In particular, leave
`metadata/controlled/*.json`, `metadata/manifest.json`, `metadata/config.json`,
`metadata/environment.json`, `metadata/release_files.json`, and
`metadata/run_order.json` for the end-of-cycle snapshot checkpoint. Their stale
construction values must not be used to authorize benchmark measurements.

The current task may still be committed and independently audited: the audit
uses the task-local files, imports, and PDF and computes its own hashes. Read
`paper_bencmark/task_builder/WORKFLOW.md` when the user asks to finalize or
refresh the complete snapshot. At that point, wait for all task and audit
writers to finish, reconcile semantic metadata, refresh once, verify the whole
snapshot, and commit the generated files together.

## Validate the repair

Before handoff:

1. Check the reconstructed statement against the paper line by line and against
   every repair-contract item.
2. Compile the target and affected paper definitions.
3. Complete and validate private proofs in both N and L with the paper-scoped
   bundle.
4. Run the negative import probe proving that other paper modules are absent.
5. Run:

   ```bash
   python3 paper_bencmark/highambench/tools/task_tags.py \
     --benchmark-root paper_bencmark/highambench
   ```

6. Run relevant task-local construction and unit checks. Defer global
   manifest-hash and release-snapshot checks to the checkpoint described above.
   Never use `--phase measurement-ready` during an individual repair.
7. Confirm that no prior audit artifact or history entry changed.

## Handoff to the Auditor

Report:

- task ID and source audit ID;
- old classification, target hash, and failed implication directions;
- exact selected paper result;
- files and declarations changed;
- disposition of every audit finding and failed or unclear semantic check;
- old and new target hashes;
- tier decision and library-search evidence;
- compilation and N/L construction checks;
- whether the corpus-wide snapshot refresh is deferred;
- any residual uncertainty.

End with `awaiting independent re-audit`. Do not state that the task is now
faithful merely because it compiles or because the Builder's own checklist
passes.
