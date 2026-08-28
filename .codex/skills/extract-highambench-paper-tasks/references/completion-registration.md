# Completion and registration gates

Read this reference completely before accepting or registering work in either
mode. Satisfy the common invariants in `../SKILL.md` and the selected mode's
workflow first.

Keep mathematical validation separate from release registration. Direct Lean
compilation of the exact current private N/L artifacts establishes
construction-stage solvability. The isolated construction checker records the
stronger measurement-ready release state; it is not required merely to finish
private proofs or begin T4 faithfulness review.

## T1--T3 gates

Build complete private proofs in both conditions before acceptance: N has no
NumStability artifact and L has the frozen library. Keep private proofs outside
the controlled task. Then compile every target in N and L; run negative import
probes for `HighamBench.Core` and `HighamBench.SemanticCore`; authenticate the
exact one-file paper bundle, which makes every foreign paper module unavailable
without reading sibling-paper state; and verify tier evidence, tags, scopes,
and skipped-tier notes.

## T4 content and faithfulness gates

Before reporting T4 extraction and faithfulness complete:

1. Reconcile the Lean declarations against the full coverage ledger and run a
   fresh completeness review of the PDF, ledger, and declaration mapping. No
   unresolved precise claim may disappear silently.
2. Audit the minimal semantic dependency closure and confirm there are no
   proof helpers or conclusions hidden in the paper-owned setting.
3. Revalidate the proof-complete private N and L solutions required by
   [T4 private solvability](t4-private-solvability.md)
   against the exact final statement, import, and semantic-dependency hashes.
   Verify that every inventoried benchmark hole is replaced exactly once, no
   hole or bypass remains, and each solution compiles using only its condition's
   allowed environment.
4. Confirm every included atomic source item occurs in exactly one accepted
   review unit, every primary declaration is covered, and every review unit has
   passed the fresh-context Direct and Round-Trip protocol, including any
   required adjudication. A declaration reused across units is accepted only
   when every containing unit passes. If review causes any statement, import,
   or semantic-dependency revision, redo the minimality and private-solvability
   gates before submitting fresh packets to new reviewers.
5. Compile the byte-identical placeholder-bearing target and paper bundle in N
   and L. Permit exactly the inventoried T4 benchmark `sorry` positions during
   construction while still rejecting every other `sorry`, `admit`, new axiom,
   `unsafe`, forbidden import, or hidden proof artifact. Do not use a
   proof-submission validator mode that rejects the controlled skeleton's
   designated holes.
6. Run negative probes showing `HighamBench.Core` and
   `HighamBench.SemanticCore` are unavailable, authenticate the exact one-file
   paper bundle (which excludes every other paper module without consulting
   sibling state), and validate the declaration-level metadata, source
   locations, review records, private-solvability evidence, placeholder count,
   paper-owned file scope, and identical N/L inputs.

## Register measurement-ready construction state

Only when preparing measurement-ready release, or when the user explicitly
requests final hardened registration, run `tools/check_construction.py` with
exactly one `--paper-id P0X` and `--paper-local-evidence`, plus the pinned
private-gold, Lean, package, library, and isolated-runtime paths required by
that command.
This is the generic construction-registration command. It:

1. invokes the generic paper finalizer in construction phase to compile only
   `P0XDefinitions.lean`, publish the exact one-file `P0X` trusted bundle and
   bundle receipt, and refresh only `metadata/papers/P0X/controlled/*.json` and
   the paper registration;
2. discovers the complete task list and theorem/declaration obligations from
   `tasks/P0X/paper.json` and its listed `task.json` files, never from
   `metadata/manifest.json`;
3. runs the private N/L, controlled-skeleton, and negative-import checks in
   fresh isolated workspaces; and
4. after a complete pass, atomically writes
   `metadata/papers/P0X/construction.json`, binds it to the current definition,
   paper record, task records, controlled manifests, bundle, and checker
   certificate, then refreshes the same paper's registration commit marker.

The construction-phase registration written during step 1 is deliberately a
draft: its readiness artifacts may say `pending`, and its existence is not a
measurement-ready claim. Only the step-4 refresh with authenticated
construction evidence satisfies the current measurement-ready construction
registry gate. It does not replace or invalidate the earlier direct
private-solvability result. For T4, measurement-ready publication additionally
requires authenticated faithfulness-review evidence.

The bundle finalizer alone does **not** attest private solvability. A passing
paper-local construction receipt is required for every measurement-ready
paper. Faithfulness review evidence is additionally required exactly when the
paper contains T4; for papers containing only T1--T3, registration records the
review gate as `not-applicable`. Publish the T4 review receipt before switching
that paper and its tasks to measurement-ready, then run the generic finalizer
with `--phase measurement-ready` to verify and publish the final paper-local
commit marker.

If the hardened checker cannot run because the current host lacks its required
namespace or isolation permission, do not treat that as mathematical failure
and do not create a custom Bubblewrap/seccomp/network wrapper or alter shared
registry tools to force a receipt. Keep the direct proof result and completed
review. Report the state precisely as “T4 extraction and faithfulness complete;
measurement-ready registration pending,” then run the unchanged final check on
a compatible executor if and when measurement-ready release is requested.

For finalizer inspection, `--dry-run` and `--write-set` may create only unique
system temporary compilation/shadow files, which are removed before return.
They create or change no benchmark or scratch-pad output; reported write sets
are prospective only.

Do not update a corpus-wide manifest, environment record, run order, release
manifest, snapshot, or legacy `metadata/controlled/**` view, and do not defer
any merge or refresh to a later serialized session. Corpus consumers discover
valid paper registrations deterministically at read time.

Do not run measurements, mark the corpus measurement-ready, commit, or push
unless the user explicitly asks. Distinct user-started paper invocations may
run concurrently.
