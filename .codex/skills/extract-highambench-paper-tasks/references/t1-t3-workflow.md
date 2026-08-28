# T1--T3 selected-result workflow

Read this reference only for a T1--T3 request. It governs target selection,
tiering, and tier evidence; the common preparation and invariants in
`../SKILL.md` still apply.

## Select honest targets

1. Survey the paper's formal claims before choosing targets. Search the frozen
   mathlib and NumStability baselines for exact and nearby results. Prefer exact
   finite claims with proofs in this paper; reject experiments, cost claims,
   vague asymptotics, and results whose proof is mainly delegated elsewhere.
2. Select at most one honest target for each available tier. Do not invent a
   target or inflate its difficulty to fill a missing tier. After a reasonable
   paper survey and library search, skip any tier with no suitable result, set
   its `result_survey` entry in `tasks/P0X/paper.json` to
   `"available": false`, and record what was examined and why it failed the
   tier. Continue with every remaining available tier and record rejected
   candidates.
3. Act as the annotator: record the source selection, tier, tags, minimal
   assumptions, line-by-line faithfulness check, and concise proof synthesis.
4. Write `tasks/P0X/T*/Target.lean`, `context.md`, and `task.json`; update only
   that paper's `paper.json` and paper-local metadata. Never update a
   corpus-wide manifest from a paper extraction invocation.

## Establish solvability directly

Before accepting a selected target, construct separate proof-complete private N
and L files for its exact current statement and compile both directly with the
pinned Lean environments. Check that N has no NumStability artifact, that L
alone receives the frozen library, and that neither proof changes the target or
uses a bypass. This direct check establishes construction-stage solvability.
Do not require the locked measurement workspace, final registry, Bubblewrap,
or a special recorder until measurement-ready release is explicitly requested.
After any statement or dependency edit, rerun both direct compiles.

## Assign the tier

- `T1` -- **Direct use**: close to one basic library theorem; the main challenge
  is finding and applying it.
- `T2` -- **Combine**: needs several library facts plus paper-specific steps.
- `T3` -- **Extend**: goes beyond the library and needs new lemmas or a longer
  argument.

Judge tiers against the frozen library baseline, not against expected agent
ability. Tier, source presentation, and result form are independent.

## Record the tier rationale

For every T1--T3 target, add a nonempty `tier_rationale` to `task.json`. Base it
on a verified frozen-library search and include exact module paths and fully
qualified declaration names; verify names in source and with Lean.

- For T1, name the close theorem and the remaining specialization or
  application.
- For T2, name the reusable facts and the paper-specific connecting steps.
- For T3, name the closest facts, identify the missing models, algorithms,
  lemmas, or connections, and record searched locations as absence evidence.

If no relevant result exists, say so and record the search scope. Summarize the
same evidence in the tier decision in `paper.json`.

## Assign the result form

For a T1--T3 target, `result_form_tag` contains exactly one primary conclusion:

- `BND`: bound or inequality.
- `EQ`: equality or identity.
- `CMP`: comparison.
- `EX`: existence or construction.

Use `CMP` only when comparison is the main claim; otherwise tag an estimating
inequality as `BND`.
