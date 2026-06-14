# Formalization Automation Prompts

This file is a reusable prompt playbook for Lean formalization work in this
repository. Its purpose is to prevent the kind of manual supervision where a
human has to inspect the generated PDF, discover irrelevant results, ask whether
hidden hypotheses were used, and redirect the proof effort after the fact.

The prompts below are meant to be applied in a loop. A run is not complete until
the final gate passes.

Important distinction: for a broad formalization request, a failed final gate is
not a stopping condition. It is the next work queue. If the gate fails because a
requested paper-level theorem, background foundation, or PDF "What Is Not
Proved" item remains open, immediately continue with the highest-priority open
ledger row unless the user explicitly asked only for a status report or pause.
However, continuing must be structured. If the same row survives repeated
passes, switch from general progress to the bottleneck protocol: name the exact
blocking theorem, list its dependencies, and count only dependency-closing work
as progress. Once a bottleneck is red, broad continuation stops: the loop may
only close a listed dependency, rule out a listed route, or ask for a genuine
mathematical route choice.

For papers/books with incomplete proofs, the process must not start by guessing
the missing mathematics.  After local library search and before hard proof work,
run a front-loaded proof-source acquisition phase: search primary external
literature, build a source-chain ledger, choose a proof route, and only then
formalize the dependency chain.

Before hard proof work, also run a foundation feasibility gate.  Do not attempt
downstream paper-level theorems, floating-point transfer corollaries, or PDF
polish while the final theorem still depends on an unproved foundation such as
matrix concentration, Lieb concavity, spectral perturbation, SVD/rank theory,
convex optimization, graph Laplacian theory, or a floating-point primitive.

## Master Loop Prompt

Use this prompt when starting a new theorem, algorithm, or stability analysis.

```text
You are working in the lean-fp-analysis repository.

Goal:
<state the mathematical goal, source paper/algorithm/equation, and desired Lean
artifact here>

Work autonomously until the goal is genuinely satisfied. Do not stop after a
partial proof, a conditional theorem with unexplained assumptions, or a PDF that
only lists Lean theorem names.

Loop until every final-gate item passes:

1. Extract the mathematical requirements.
2. Create or update the theorem ledger before proving anything.
3. Map each requirement to existing repository definitions and theorems.
4. Reuse existing library results whenever possible; reimplement only after an
   explicit failed search.
5. Classify each source proof as complete, proof sketch, citation-only, or
   missing.
6. If the local repository and bundled dependencies do not contain the needed
   mathematics, or if the source paper/book proof skips intermediate steps,
   run the proof-source acquisition phase before designing a replacement proof.
7. Run the foundation feasibility gate. If a required foundation is missing,
   make that foundation the active theorem target before downstream algorithm
   claims.
8. Design the Lean theorem statements before proving them.
9. Prove the results in Lean.
10. Audit every hypothesis.
11. Audit the natural-language theorem/corollary story against the Lean theorem
   statements.
12. Run repeated weak-component checks until fragile parts have consecutive
   clean passes.
13. Run the bottleneck detector. If the same paper-level row, concentration
    theorem, FP budget, perturbation bridge, or PDF claim fails twice for the
    same reason, create a named bottleneck theorem and dependency ledger before
    adding more supporting lemmas.
14. Remove or quarantine irrelevant material.
15. If anything remains unproved, store it in a named ledger with the exact
   source claim, current Lean status, missing foundations, and next action.
16. Keep paper-level results, deterministic subtheorems, proof adapters, and
   open foundations in separate ledger sections.
17. For full-paper work, keep the live theorem ledger separate from the
   not-proved ledger when practical: the theorem ledger records every extracted
   source claim, classification, random variable, event, Lean theorem name,
   hypothesis class, status, and next step; the not-proved ledger is the
   authoritative FAIL/PASS gate for open paper-level items.
18. Maintain a proof-source ledger for every incomplete paper proof: source
   chain, exact theorem/equation/page references, Lean target, route status,
   and whether the source was formalized, advisory only, rejected, or open.
19. Maintain a bottleneck ledger whenever a row turns red. A red bottleneck
    freezes adjacent work: only listed dependency closures, route eliminations,
    or statement corrections count as progress.
20. Update README, docs/LIBRARY_LOOKUP.md, examples/LibraryLookup.lean, and any
   proof-summary PDF/TeX.
21. Run the verification commands and report exact results.
22. If the final gate fails because open requested paper-level items remain,
    select the highest-priority open ledger row and restart the loop on that
    row. Treat the failed gate as a continuation checkpoint, not a final answer.

Completion means:
- `lake build` succeeds.
- `lake env lean examples/LibraryLookup.lean` succeeds.
- No `sorry`, `admit`, new `axiom`, new `unsafe`, or placeholder theorem is
  present in the touched files.
- The final theorem's `#print axioms` output contains only standard Lean/mathlib
  axioms unless an explicit, documented mathematical axiom was requested.
- Every theorem/corollary claimed in prose has a matching Lean theorem name.
- Every nontrivial Lean hypothesis is listed and classified.
- Every external paper, book, note, or documentation source used to fill a proof
  gap is cited in the theorem ledger/PDF/README as appropriate, with the exact
  theorem/lemma/page/section used and a note explaining whether it was
  formalized or only advisory.
- Every incomplete source proof has a proof-source ledger entry before hard
  proof work starts.
- Every paper-level theorem has passed the foundation feasibility gate before
  downstream theorem work starts.
- Weak components have been checked more than once from different angles.
- Active bottlenecks have either been closed, reduced by closing a listed
  dependency, or explicitly reported as genuine mathematical choices.
- The PDF states exactly what was proved, not what would be nice to have proved.
- Unused, irrelevant, or misleading results have been removed or clearly
  quarantined.
- Every explicit "What Is Not Proved" item is mirrored in a maintained ledger,
  and closed subtheorems are separated from still-open paper-level results.
- No paper-level theorem is marked closed merely because a conditional transfer,
  deterministic consequence, or exact-arithmetic sublemma was proved.
- Any remaining open item is either outside the user's requested scope by
  explicit agreement or keeps the final gate marked FAIL.
- If the final gate is FAIL for an item still inside the requested scope, the
  next action is continued proof work, not a final "cannot complete" report,
  unless the user explicitly requested a status-only update.
- If the same item remains open after two focused passes, the next action is
  not another adjacent lemma; it is the bottleneck protocol below.
- If a red bottleneck exists, adjacent infrastructure, documentation polish, and
  transfer corollaries do not count as progress unless they close or document a
  listed dependency in that bottleneck ledger.
```

## Prompt 1: Requirement Extraction

```text
Before writing code, extract the formal requirements from the user's request and
the cited source.

Produce:
1. The exact algorithm/equation/theorem from the source being formalized.
2. The mathematical objects involved.
3. The desired output theorem in plain English.
4. Whether the result is deterministic, probabilistic, floating-point, or a
   combination.
5. The expected probability statement, including the event, bound, parameters,
   and failure probability.
6. Any quantities that are random variables.
7. Any quantities that are deterministic inputs.
8. A list of theorem obligations that must exist in Lean before the task can be
   called complete.
9. Every source-section item named "not proved", "future work", "open",
   "assume", "with high probability", or "it follows from" that might hide a
   missing theorem.
10. Whether each obligation is a paper-level theorem, a deterministic
   subtheorem, a floating-point transfer theorem, a probability foundation, or
   documentation-only scope note.
11. Whether the source gives a complete proof, a proof sketch, a citation-only
   proof, or no proof for each paper-level theorem.
12. If the source proof is incomplete, the initial list of cited and likely
   external proof sources to inspect before proving.

If any part of the mathematical target is ambiguous, ask a focused question
before formalizing. Otherwise continue.
```

## Prompt 1A: Not-Proved Ledger and Closure Protocol

```text
Maintain a live not-proved ledger whenever the paper, PDF, README, or user names
missing results.

For a full-paper formalization, also maintain a live theorem ledger. The theorem
ledger and not-proved ledger may cross-reference each other, but they have
different jobs:
- theorem ledger: every extracted claim, assumption, random variable, event,
  classification, intended/current Lean theorem names, status, hidden
  hypotheses, and next proof step;
- not-proved ledger: only the still-open paper-level or generated-document
  claims that block a PASS result.

For each item record:
- Source location: paper section/equation/algorithm/page or generated PDF
  section.
- Exact mathematical claim, copied or paraphrased precisely.
- Current Lean status: unstarted, partial foundation, deterministic subtheorem,
  conditional transfer, fully proved, or deliberately out of scope.
- Final theorem names that close it, if any.
- Missing foundations, if not closed.
- Why the current theorem is or is not enough to close the paper-level claim.
- Next concrete proof step.

Closure rules:
- A conditional theorem does not close an item whose missing part is exactly the
  condition.
- A deterministic transfer theorem does not close a randomized concentration
  theorem unless the concentration event and probability bound are also proved.
- An expectation theorem does not close a high-probability theorem.
- A statement about a different algorithmic object, even if true, does not close
  the source claim.
- Closed subtheorems must be recorded separately from still-open paper-level
  results.
- If the user asks to prove every item in a "What Is Not Proved" section, the
  final gate cannot pass while any item remains open.

Loop:
1. Pick the highest-priority open ledger item.
2. Search the library for all required foundations.
3. Prove missing foundations or mark the exact missing foundation.
4. Update the ledger immediately.
5. Run a weak-component check on the ledger classification itself.
6. Continue until the ledger is empty or the user explicitly narrows scope.
```

## Prompt 1B: Open-Foundation Continuation Protocol

```text
When a final gate or not-proved ledger still has open items inside the user's
requested scope, do not stop at the diagnosis.

Convert the failure into the next formalization task:
1. Rank open rows by:
   - user priority or most recent correction,
   - number of other rows unblocked,
   - proximity to existing repository foundations,
   - risk that docs/PDF currently overstate the result.
2. Pick the top row and write a frontier theorem target with:
   - exact source claim it advances,
   - smallest useful Lean theorem to prove next,
   - expected file/module location,
   - existing local theorems to reuse,
   - validation command for that module.
3. Attempt the proof or prove the next reusable prerequisite. Do not merely say
   the area is large.
4. If the full row is too large, close a meaningful prerequisite theorem, add it
   as a scoped subtheorem, keep the paper-level row open, and continue to the
   next prerequisite.
5. Update the theorem ledger, not-proved ledger, README/lookup/PDF if their
   claims changed, and the weak-component log.
6. Run the relevant validation gate.
7. Repeat until:
   - the paper-level row closes,
   - all requested rows close,
   - the user asks to pause/status-only,
   - a mathematical choice is genuinely needed,
   - or an external blocker prevents further local proof work.

Forbidden stopping pattern:
"This is a major formalization project, so it remains open" is not a final
answer for an autonomous full-paper request. It may appear only as a scoped
status note inside a report that also states the next concrete Lean theorem and
continues unless the user asked to stop.
```

## Prompt 1C: Bottleneck Detection and Escape Protocol

```text
Use this prompt after each failed final gate, after every weak-component pass,
and whenever proof work starts producing adjacent lemmas without closing the
paper-level row.

Detect a bottleneck if any condition holds:
1. The same paper-level ledger row survives two consecutive proof/audit passes.
2. Two or more new subtheorems were added, but the missing foundation field for
   the row did not change.
3. Lean failures keep occurring around the same theorem family, typeclass/API
   mismatch, probability construction, measurability/support fact, norm bridge,
   spectral theorem, or floating-point budget.
4. The PDF, ledger, or status report repeats the same next step in different
   words.
5. A new theorem does not appear in the target theorem's dependency list or in
   the proof sketch of a listed dependency.

A bottleneck is **red** if the same paper-level row survives two focused passes
with the same missing foundation. Red status freezes downstream work.

When a bottleneck is detected, immediately create a bottleneck ledger entry:
- Source claim and source location.
- Blocking Lean theorem name.
- Exact theorem statement, before proving.
- Required dependency list.
- Existing local theorem candidates and why each is reused, adapted, or
  insufficient.
- External source candidates, if any, with exact theorem/equation/page/section.
- Failed routes and the concrete obstruction for each route.
- Chosen route, with assumptions and constants.
- Next dependency theorem to prove.
- Validation command for the file/module containing that dependency.

If the bottleneck is red, store this entry in a dedicated bottleneck ledger file
or a clearly named bottleneck-ledger section. Do not leave it only as scattered
prose in the theorem or not-proved ledger.

Bottleneck progress test:
- Does the new theorem close a listed dependency?
- Is it syntactically used by the bottleneck theorem or by a listed dependency?
- Does it remove or reclassify a hidden/suspicious hypothesis?
- Does it rule out a failed route with evidence?
- Does it correct the target statement to match the source claim?

If the answer to all five questions is no, the work is adjacent. Quarantine or
remove it, and return to the bottleneck dependency list.

Escape rules:
1. Prove only the next listed dependency.
2. After each focused pass, update the dependency status as closed, narrowed,
   blocked, or wrong route.
3. If no dependency changes status in one focused pass, do not keep orbiting the
   same proof. Either switch to a different listed route, or ask the user only
   if the choice changes the mathematical theorem.
4. Do not add broad foundations just because they are nearby. Add them only when
   the bottleneck ledger shows where they are used.
5. A final report for a failed full-paper gate must include the active
   bottleneck theorem, failed routes, exact obstruction, and next dependency.
6. For a red bottleneck, do not update the PDF, README, lookup, or examples as
   the main deliverable unless the update records the bottleneck or a listed
   dependency closure. Documentation cannot substitute for proof progress.
```

## Prompt 1D: Foundation Feasibility Gate

```text
Run this gate before hard Lean proof work on any paper-level theorem and again
whenever a high-priority row changes proof route.

Create a feasibility table:
- Paper-level theorem and source location.
- Intended final Lean theorem name.
- Required foundations: probability model, concentration inequality, spectral
  theorem, perturbation theorem, norm bridge, SVD/rank theory, convex
  optimization, graph/Laplacian theory, floating-point primitive, or other.
- For each foundation, status:
  available-local, small-adapter, missing-foundation, route-choice, or
  out-of-scope-by-user.
- Existing local theorem names or exact external source locations.
- Smallest next Lean theorem if missing.
- Whether downstream algorithm/FP/PDF work is allowed.

Rules:
1. If a required foundation is `available-local`, reuse it.
2. If it is `small-adapter`, prove the adapter before the downstream theorem.
3. If it is `missing-foundation`, the active proof target becomes that
   foundation. Do not prove a downstream theorem that assumes it.
4. If it is `route-choice`, compare routes by source fidelity, assumptions,
   constants, and local-library fit. Ask the user only when the choice changes
   the theorem being formalized.
5. If a missing foundation is too large, split it into a dependency DAG and
   create or update the bottleneck ledger. Progress means closing a node in that
   DAG, not adding unrelated infrastructure.
6. Do not polish the PDF or advertise new corollaries while the final theorem's
   feasibility table still has an in-scope `missing-foundation`, except to state
   the blocker honestly.

For matrix concentration targets, this gate must explicitly name whether the
proof route uses Lieb/Tropp trace-MGF, Golden-Thompson/Ahlswede-Winter,
covering nets, scalar symmetrization, or another route. A theorem depending on
matrix Bernstein/Khintchine cannot be attempted as final until the selected
matrix concentration foundation is locally proved.
```

## Prompt 2: Library Reuse Search

```text
Search the repository before implementing anything from scratch.

Required searches:
- Read docs/LIBRARY_LOOKUP.md.
- Read examples/LibraryLookup.lean.
- Use `rg` for relevant names, concepts, and nearby algorithms.
- Use `#check` or `#print` for candidate definitions/theorems.
- Inspect imports of nearby files to identify the intended dependency chain.

Produce a reuse table with columns:
- Needed concept.
- Existing candidate result or definition.
- File.
- Whether it is reused directly, wrapped by a small adapter, or insufficient.
- If insufficient, why.

Rule:
Do not reimplement a theorem, bound, probability construction, floating-point
lemma, norm lemma, or algebraic identity if an existing local result can be
used with a small adapter.
```

## Prompt 2A: Front-Loaded External Proof-Source Acquisition

```text
Use this prompt after the repository and bundled dependency search, and before
hard proof work, whenever the source paper/book gives an incomplete proof,
cites a result without proof, hides steps behind phrases like "standard",
"well known", "by matrix concentration", or requires a theorem whose
hypotheses are unclear.

External search is mandatory in this situation. Do not start inventing local
adapters for the hard theorem until the proof-source ledger and route plan are
written.

Search policy:
1. Prefer primary sources: original papers, journal versions, arXiv preprints,
   official books/monographs, author lecture notes, and official documentation.
2. Search as deeply as needed. Start with the cited paper/book. If a proof step
   depends on another result, follow the citation chain one paper at a time:
   Paper 1, Paper 2, Paper 3, and so on, until the missing intermediate step is
   explicit enough to formalize or until a genuine mathematical choice remains.
3. For technical questions, rely on primary sources rather than blogs or
   secondary summaries. Secondary sources may help locate names or references,
   but must not be the sole basis for a Lean theorem.
4. Record the exact source location for every imported idea: theorem number,
   lemma number, equation, page, section, and URL or bibliographic citation.
5. Translate each external result into a local Lean target with explicit
   hypotheses. Do not cite an external paper as a hypothesis replacement.
   Either prove the result locally, reuse an already formalized theorem, or keep
   the ledger item open.
6. If multiple sources state variants with different constants or assumptions,
   choose the version closest to the repository's existing definitions and
   easiest to formalize. Record alternatives and why they were not chosen.
7. If a source uses hidden assumptions, such as independence, measurability,
   boundedness, finite dimension, positivity, invertibility, symmetry,
   self-adjointness, or floating-point validity, expose those assumptions in
   the theorem design and hypothesis audit.
8. If the proof route requires a major mathematical framework, such as spectral
   theorem, trace exponential, SVD, convex optimization, or graph Laplacians,
   create a foundation sub-ledger and continue by proving the smallest reusable
   prerequisite theorem.

Deliverables after searching:
- A proof-source ledger:
  paper claim, missing proof step, source chain, exact source location, Lean
  theorem target, dependencies, route status, and next proof action.
- A source chain table:
  source, claim used, exact location, role in proof, Lean target, status.
- A dependency DAG:
  paper-level theorem -> external theorem(s) -> local foundation theorem(s) ->
  final Lean theorem.
- A decision table:
  candidate proof route, assumptions, constants, formalization difficulty,
  chosen/not chosen, reason.
- Ledger updates:
  mark each source-derived step as unstarted, partial foundation, fully proved,
  advisory only, or rejected.
- Documentation updates:
  cite sources in the theorem PDF and README when their results guide a proved
  theorem or define the scope of an open item.

Forbidden shortcuts:
- Do not close a Lean theorem by saying "this follows from the literature".
- Do not assume concentration, perturbation, spectral, SVD, optimization, or
  floating-point results just because a paper cites them.
- Do not use an external theorem with stronger or different hypotheses unless
  the local theorem explicitly includes those hypotheses or proves the bridge.
- Do not silently swap the paper's target theorem for a weaker theorem found
  online. If a weaker theorem is useful, classify it as a support theorem and
  keep the paper-level row open.
- Do not keep adding adjacent local lemmas when the proof-source ledger still
  says the same external theorem is missing.
```

## Prompt 3: Theorem Design

```text
Design the theorem statements before proving.

For each theorem/corollary, write:
- Lean name.
- Informal theorem statement.
- Exact hypotheses.
- Which hypotheses are mathematical assumptions from the source.
- Which hypotheses are floating-point model validity assumptions.
- Which hypotheses are proof artifacts that should be removed if possible.
- Dependencies on previous local theorems.
- Whether this theorem is a final user-facing result or an internal adapter.

Reject theorem designs that assume the desired concentration, stability, or
error bound instead of proving it from existing local results or newly proved
lemmas.
```

## Prompt 4: Implementation Loop

```text
Implement in small layers.

For each layer:
1. Add definitions in the file where they logically belong.
2. Add lemmas next to the material they support.
3. Prefer adapters around existing theorems over fresh long proofs.
4. Build the touched module.
5. If a proof becomes large, stop and search again for an existing theorem.
6. If the same proof fails twice at the same dependency, invoke Prompt 1C before
   adding more bridge lemmas.
7. If a theorem is only a bridge, name it as a bridge and avoid advertising it
   as a main result.

After each layer, update the theorem design table with actual theorem names and
any changed hypotheses.
```

## Prompt 5: Probabilistic Audit

```text
Audit every high-probability claim.

For each probabilistic theorem:
- Identify the probability space or finite distribution.
- Identify the event.
- Identify the random variables.
- Identify the deterministic parameters.
- State the exact lower bound on event probability.
- Check whether concentration is proved or assumed.
- If a concentration inequality is used, name the Lean theorem proving it.
- If the result is derived by Markov, Chebyshev, Chernoff, or another inequality,
  name the Lean theorem and list its hypotheses.
- Confirm that no hidden event such as `goodEvent`, `boundedEvent`, or
  `concentrationEvent` is assumed without a probability theorem for it.
- Confirm that high-probability corollaries do not merely assume a bound on a
  random counter, embedding error, leverage score event, or norm event.
- If a threshold such as `Q`, `τ`, or `ε` is selected, prove its probability
  guarantee from the random model, or keep the result deterministic/conditional
  and mark the high-probability item open.

If concentration is assumed instead of proved, mark the final gate as FAIL.
```

## Prompt 6: Floating-Point Audit

```text
Audit every floating-point claim.

For each floating-point theorem:
- Identify the exact real algorithm.
- Identify the floating-point algorithm.
- Identify each rounded operation.
- Search for existing local floating-point results for those operations.
- Reuse local results such as dot-product, summation, division, matrix-vector,
  or matrix-matrix bounds whenever possible.
- State the final perturbation budget.
- Classify each validity hypothesis, such as `gammaValid`, nonzero denominator,
  positive sample count, or positive probability denominator.
- Make dimension dependence explicit in names or notation when a budget depends
  on dimensions, dot-product lengths, sample counts, or row/column counts.
- Audit indexed definitions: if a definition is written as a family
  `(...)_{i,j}` or `(...)_{j,k}`, check that the expression actually depends on
  the displayed indices; otherwise rewrite the notation or theorem statement.

If the proof treats an operation as exact that the algorithm computes in
floating point, either justify this as the intended model or add a fully
floating-point corollary.
```

## Prompt 7: Hidden-Hypothesis Audit

```text
List every hypothesis of every final theorem.

For each hypothesis, classify it as one of:
- Source assumption: required by the mathematical statement.
- Domain assumption: positivity, dimension, nonzero denominator, or support.
- Floating-point validity: required by the FP model or gamma bound.
- Reused theorem assumption: inherited from a local theorem.
- Suspicious/proof artifact: should be eliminated or explicitly justified.

Then answer:
1. Did we assume the target result?
2. Did we assume the concentration result?
3. Did we assume unbiasedness or variance when it should have been proved?
4. Did we assume exact arithmetic where the requested theorem is floating-point?
5. Did we introduce any theorem that is true but irrelevant to the requested
   algorithm?
6. Did we close a paper-level ledger item using only a subtheorem?
7. Did the PDF, README, or lookup file say "proved" where Lean only proves a
   conditional, expectation, deterministic, or transfer result?

If any answer reveals a gap, mark the final gate as FAIL and continue.
If the gap is inside the requested scope, immediately invoke Prompt 1B and work
on the next frontier theorem instead of ending with the audit result.
```

## Prompt 8: Natural-Language PDF Audit

```text
Generate or update the theorem-style PDF only after the Lean results build.

The PDF is a mathematical note, not a dump of Lean theorem names. Write it for
a mathematically trained reader who wants to understand what was proved before
looking at the code.

The PDF must be organized as:
1. Title and short abstract.
2. Notation and algorithm setup, including the source algorithm/equation.
3. Definitions in mathematical notation.
4. Lemmas/theorems/corollaries in standard mathematical prose.
5. Short proof ideas that match the actual Lean dependency chain.
6. Compact "Lean formalization" blocks after statements, containing theorem
   names as references, not as the main exposition.
7. A section called "Hypotheses and Scope".
8. A section called "What Is Not Proved" if there are meaningful limitations,
   or an explicit scope bullet if the limitation is short.
9. A file map only if it helps the reader navigate the formalization.

Style requirements:
- Lead with mathematics: notation, assumptions, events, probability spaces,
  bounds, perturbation budgets, and conclusions.
- Use conventional theorem/lemma/corollary environments.
- State equations with standard notation before mentioning Lean names.
- Keep Lean identifiers visually subordinate, preferably one per line in small
  reference blocks.
- Do not present a long list of Lean theorem names as the theorem statement.
- Do not use vague labels such as "the theorem above" if several statements
  intervene; name the relevant equation, theorem, or corollary.
- Do not claim equivalence to a mathematical object that the repository has not
  defined. For example, if the repository uses a vector-action predicate instead
  of a supremum-valued spectral norm, say exactly that.
- Do not hide proof limitations in technical prose; put them in "Hypotheses and
  Scope" or "What Is Not Proved".

Mathematical audit:
- Every claimed theorem has a matching Lean theorem.
- Every Lean final theorem has a readable theorem/corollary entry.
- Every displayed probability statement identifies the event, the bound, and the
  failure probability.
- Every floating-point statement identifies which operations are rounded and
  the final perturbation budget.
- No irrelevant definitions, trace constructions, or bridge lemmas are promoted
  as main mathematical results.
- The PDF does not claim a high-probability result when Lean only proves an
  expectation result.
- The PDF does not hide assumptions inside prose.
- The PDF separates paper-level open claims from newly closed deterministic
  subtheorems or transfer lemmas.
- A "What Is Not Proved" section is generated directly from the live ledger; do
  not rewrite it from memory.
- The theorem/corollary numbering and cross-references still make sense after
  edits; no scalar expression should be displayed with misleading vector or
  matrix indices.

Visual and readability audit:
- Run LaTeX with `-halt-on-error`.
- Run `git diff --check`.
- Extract text with `pdftotext` and inspect the theorem/corollary sections for
  readability.
- Render representative pages with `pdftoppm` or another PDF renderer and
  visually inspect them.
- Fix overfull/underfull output that affects readability, especially long Lean
  identifiers spilling into margins or dominating the page.
- The final PDF should be readable as a standalone mathematical note.
```

## Prompt 9: Cleanup and Modularity Audit

```text
Before finalizing, inspect organization.

Check:
- Does each definition live in the file matching its mathematical role?
- Are probability definitions separated from Gram/error analysis when sensible?
- Are floating-point adapters near the FP material they support?
- Are previous results reused instead of duplicated?
- Are there unused theorems introduced only because an earlier approach was
  wrong?
- Are conditional transfer theorems stored near the stability material they
  transfer, while the missing probabilistic foundations remain in probability
  or concentration files?
- Are README, docs/LIBRARY_LOOKUP.md, examples/LibraryLookup.lean, and project
  memory updated?
- Does the dependency graph build from basic definitions to final corollaries?
- Does every open ledger item have a next file/module where the missing
  foundation should live?

Remove unused or misleading material. If removal is risky, quarantine it in a
clearly named experimental file and do not cite it as a result.
```

## Prompt 10: Final Gate

```text
Run the final gate.

Commands:
- `git status -sb`
- `git diff --stat`
- `git diff --check`
- `lake build`
- `lake env lean examples/LibraryLookup.lean`
- `rg -n "\b(sorry|admit|axiom|unsafe|opaque)\b" <touched Lean files>`
- `#print axioms <final theorem name>` for each final theorem.
- If a PDF/TeX file was changed:
  - `pdflatex -interaction=nonstopmode -halt-on-error -output-directory docs <pdf-source.tex>`
  - `pdftotext <pdf-output.pdf> - | <targeted inspection command>`
  - Render representative pages, for example with `pdftoppm`, and visually
    inspect the output.

Final report must include:
- The main theorem/corollary names.
- The files changed.
- The validation commands and outcomes.
- Any remaining warnings and whether they are pre-existing.
- The hidden-hypothesis table.
- The bottleneck ledger status, including active bottleneck theorem names,
  closed dependencies, failed routes, and next dependency if any.
- The not-proved ledger status: closed items, open items, and whether the final
  gate passed or failed because of them.
- The exact PDF path if a PDF was generated.
- A short note that the PDF was checked for mathematical readability, not only
  for successful compilation.

If any required command fails, or if any suspicious hypothesis remains, do not
claim completion. Continue the loop or ask the user for the missing mathematical
choice.

If the required commands pass but the not-proved ledger still contains requested
paper-level items, treat the final gate as a checkpoint. Update the report
fields, then continue via Prompt 1B unless the user asked for a status-only
response.
```

## Prompt 11: Adversarial Review

```text
Pretend the user is going to inspect the PDF and try to find a mismatch.

Actively look for:
- A theorem whose prose is stronger than its Lean statement.
- A theorem whose name suggests an algorithm but formalizes a different object.
- An expectation result described as high probability.
- A deterministic result described as random.
- A probabilistic result whose concentration is assumed.
- A floating-point theorem that omits a rounded operation.
- A result that is true but irrelevant to the cited algorithm.
- A proof that duplicates an existing library theorem.
- A "not proved" item that disappeared from the PDF/ledger without a closing
  Lean theorem.
- A paper-level theorem marked complete because a related deterministic
  subtheorem was completed.
- A theorem whose notation suggests dependence on an index or dimension that is
  not present in the Lean definition.

If any issue is found, fix it before finalizing.
```

## Prompt 12: Repeated Weak-Component Checks

```text
Run a repeated weak-component audit. Do not trust the first clean pass.

Create a weak-components ledger with columns:
- Component.
- Why it is weak or failure-prone.
- First-pass finding.
- Fix or justification.
- Second-pass finding.
- Third-pass finding, required if either previous pass found an issue.
- Evidence: theorem names, file links, command output, or PDF section.
- Status: PASS, FIXED, or FAIL.

Automatically mark these as weak components:
- Any final theorem with more than three hypotheses.
- Any theorem whose name contains high-probability, concentration, Chernoff,
  Markov, Chebyshev, expectation, floating-point, FP, stability, or perturbation.
- Any theorem that transfers a deterministic bound into a probabilistic bound.
- Any theorem that adapts an existing local theorem.
- Any generated PDF section describing theorem statements.
- Any generated PDF whose Lean-reference blocks contain long identifiers or
  whose mathematical claims were rewritten after the Lean proof.
- Any "What Is Not Proved" or theorem-ledger section.
- Any bottleneck ledger entry or theorem that remained open after a prior pass.
- Any result whose proof required a new probability distribution, event, support
  lemma, norm inequality, or floating-point budget.
- Any place where exact arithmetic and floating-point arithmetic coexist.
- Any place where a theorem statement changed during the implementation.
- Any theorem closing a source-paper equation, especially if the source theorem
  is asymptotic, high-probability, or uses a norm not exactly represented in
  the repository.

Check each weak component from at least two independent angles:
1. Lean angle: inspect the theorem type, hypotheses, dependencies, and
   `#print axioms`.
2. Mathematical angle: compare the statement against the source algorithm,
   equation, and intended theorem.
3. Documentation angle: compare README/PDF/lookup prose against the exact Lean
   theorem.
4. Reuse angle: search the repository again for existing results that should
   replace local proof work.

Rules:
- A weak component passes only after two consecutive clean checks.
- If a check finds an issue, fix it and restart the two-clean-check count for
  that component.
- If a component remains suspicious but useful, downgrade the prose claim and
  document its exact scope.
- If a component is irrelevant to the requested theorem, remove it or quarantine
  it outside the advertised library path.
- The final report must include the weak-components ledger or a concise summary
  of it.
- If the same component fails two passes for the same reason, invoke Prompt 1C
  and stop treating the weak-component audit as the main loop.
```

## Minimal Autonomous Invocation

For future work, this short prompt can be pasted into Codex:

```text
Use docs/FORMALIZATION_AUTOMATION_PROMPTS.md as the operating loop for this
formalization task. Do not stop until the final gate passes. If the final gate
fails because an in-scope paper-level theorem or "What Is Not Proved" row remains
open, immediately convert the highest-priority open row into the next Lean proof
target and continue instead of returning only a failure report. Reuse existing
repository theorems wherever possible, prove missing background only when the
library search shows it is absent, and run a foundation feasibility gate before
hard proof work. If a final theorem depends on a missing foundation, make that
foundation the active Lean target before downstream algorithm/FP/PDF work.
Audit hidden hypotheses, update the theorem PDF, README, LIBRARY_LOOKUP.md, and
examples/LibraryLookup.lean. Run repeated weak-component checks until every
fragile theorem, proof adapter, probabilistic claim, floating-point claim,
ledger item, and PDF claim has two consecutive clean passes. Maintain a
not-proved ledger; do not mark paper-level claims closed using only conditional
transfers or deterministic subtheorems. Run the bottleneck detector after
failed passes; if the same row fails twice with the same missing foundation,
create a named red bottleneck theorem and dependency ledger, freeze adjacent
work, and count only listed dependency closures, route eliminations, or theorem
statement corrections as progress. Report intermediate checkpoints only when
asked, blocked, or facing a genuine mathematical route choice; otherwise keep
proving from the next ledger dependency. Final reporting must include theorem
names, weak-component summary, bottleneck summary, not-proved ledger status,
and validation commands.

Task:
<insert theorem or algorithm request>
```
