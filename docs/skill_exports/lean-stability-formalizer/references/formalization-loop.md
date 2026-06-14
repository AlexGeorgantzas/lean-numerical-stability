# Formalization Loop Reference

Use this reference when formalizing paper algorithms and analyses in Lean.

## Continuation Rule

For broad requests, a failed final gate is not a stopping point. If a requested
paper-level theorem, missing foundation, or "What Is Not Proved" row remains
open, immediately select the highest-priority open ledger item and continue
proof work. Do not end with only "this is a major formalization project" unless
the user asked for a status-only report or a genuine mathematical choice blocks
the next proof step.

Choose the next row by user priority, how many other results it unlocks,
proximity to existing local infrastructure, and risk of documentation
overclaiming. If the row is too large, prove the next reusable foundation
theorem, record it as a scoped subtheorem, keep the paper-level row open, run
validation, and continue.

Continuation must be dependency-directed. If the same row survives repeated
passes with the same missing foundation, switch to a red-bottleneck protocol:
freeze downstream work and prove only listed dependencies of the blocker.

## Paper Extraction

For each algorithm in the paper, extract:

- algorithm name/number and source equation numbers;
- inputs, outputs, deterministic parameters, and random choices;
- exact arithmetic mathematical object;
- floating-point or computed object;
- target deterministic, expectation, high-probability, or asymptotic theorem;
- every assumption needed by the source theorem;
- the natural final Lean theorem statement.

Create a ledger with one row per theorem/corollary.

Also create a not-proved ledger when the source paper, generated PDF, README,
or user names missing work. Each row must record source location, exact claim,
current Lean status, missing foundations, next action, and whether any completed
result is merely a deterministic subtheorem, conditional transfer, or adapter.

## Library Reuse Search

Before implementing:

- read `docs/LIBRARY_LOOKUP.md`;
- read `examples/LibraryLookup.lean`;
- search with `rg` for relevant concepts and nearby algorithm files;
- use `#check`, `#print`, and imports from neighboring modules;
- classify each needed concept as reused directly, wrapped by adapter, or
  missing.

Only prove missing background after this search is documented.

## Proof-Source Acquisition

Before proving a hard paper-level theorem, classify the uploaded source proof:

- complete proof;
- proof sketch with missing algebra/probability/FP steps;
- citation-only proof;
- no proof.

If the proof is not complete and the missing theorem is not already in the
local repository, search external primary literature before adding proof
infrastructure.  Start from the source's citations, then follow citation chains
as far as needed until the missing step is explicit enough to formalize or a
genuine mathematical route choice remains.

Create a proof-source ledger before implementation:

- paper claim and source location;
- missing proof step;
- external source chain with theorem/lemma/equation/page/section/URL;
- assumptions and constants in each source;
- intended local Lean theorem names;
- dependency DAG from external theorem to local foundations;
- chosen route, rejected alternatives, and reason;
- status: unstarted, partial foundation, formalized, advisory only, rejected,
  or open.

External sources are guidance, not hypotheses.  Close a paper-level theorem
only after the source-derived result is proved locally or reused from an
already formalized local theorem.

## Foundation Feasibility Gate

Before hard proof work on a paper-level theorem, create a feasibility table:

- paper-level theorem and source location;
- intended final Lean theorem name;
- required foundations, such as probability model, concentration inequality,
  spectral theorem, perturbation theorem, norm bridge, SVD/rank theory, convex
  optimization, graph/Laplacian theory, or floating-point primitive;
- status of each foundation: available local theorem, small adapter, missing
  foundation, route choice, or explicitly out of scope;
- smallest next Lean theorem when a foundation is missing;
- whether downstream algorithm/FP/PDF work is allowed.

If a required foundation is missing, the active proof target becomes that
foundation. Do not prove downstream algorithm theorems, FP transfer corollaries,
or PDF-polish results that assume it. For matrix concentration, explicitly name
the route: Lieb/Tropp trace-MGF, Golden-Thompson/Ahlswede-Winter, covering net,
scalar symmetrization, or another route.

## Theorem Design

For each theorem, record:

- Lean name;
- informal theorem;
- exact hypotheses;
- source assumptions;
- domain assumptions;
- FP model assumptions such as `gammaValid`;
- reused theorem assumptions;
- suspicious artifacts to eliminate;
- final-user-facing vs internal adapter status.

Never assume the concentration, stability, or perturbation bound that the user
asked to prove.

Do not close a paper-level theorem with a theorem that only proves a condition,
transfer step, expectation version, deterministic subcase, or different
algorithmic object.

## Bottleneck Protocol

Trigger a bottleneck if:

- the same row remains open after two proof/audit passes;
- new lemmas do not change the missing-foundation field;
- Lean failures recur around the same API, typeclass, measurability,
  independence, norm, spectral, or constants issue;
- the PDF/ledger/final report repeats the same next step.

The bottleneck is red if the same paper-level row survives two focused passes
with the same missing foundation.

Create a bottleneck ledger row with:

- blocking theorem statement;
- source claim;
- dependency list;
- local theorem candidates;
- external source candidates;
- failed routes and errors;
- chosen route;
- next dependency theorem;
- validation command.

For a red bottleneck, use a dedicated bottleneck ledger file or clearly named
section. Do not keep adding adjacent lemmas unless they are listed dependencies.
Count progress only when a listed dependency closes, a failed route is ruled out
with evidence, or the theorem statement is corrected to match the source claim.

## Probabilistic Audit

For each probabilistic theorem:

- identify probability space/distribution;
- identify event;
- identify random variables and deterministic parameters;
- state exact probability lower bound;
- name the inequality used: Markov, Chebyshev, Chernoff, Bernstein, union bound,
  or another formal theorem;
- verify no hidden `goodEvent`, `boundedEvent`, or `concentrationEvent` is
  assumed without a probability theorem.

If concentration is assumed instead of proved, the gate fails.

If a high-probability result is obtained by selecting a threshold such as `Q`,
`τ`, or `ε`, prove the probability of that threshold from the stated random
model. Otherwise keep the theorem deterministic/conditional and leave the
high-probability paper-level item open.

## Floating-Point Audit

For each FP theorem:

- identify exact algorithm;
- identify computed algorithm;
- list rounded operations;
- reuse local FP lemmas for arithmetic, dot products, sums, divisions, and
  matrix operations;
- state final perturbation budget;
- expose dimension factors hidden in dependent types;
- classify all validity assumptions.

If an operation is treated as exact, justify that as the intended model or add a
fully floating-point corollary.

Make dimension and sample-count dependence explicit. Audit notation so indexed
families such as `(...)_{i,j}` or `(...)_{j,k}` really depend on the displayed
indices.

## Natural-Language PDF Rules

The PDF must be a mathematical note:

- title and abstract;
- notation and algorithm setup;
- definitions in mathematical notation;
- theorem/lemma/corollary statements in standard prose;
- proof ideas matching Lean dependencies;
- compact Lean reference blocks after statements;
- `Hypotheses and Scope`;
- `What Is Not Proved` when limitations matter;
- optional file map.

Do not make Lean theorem names the main exposition.  Do not overstate Lean
results.  Do not hide hypotheses.

Generate `What Is Not Proved` from the live ledger. Separate still-open
paper-level claims from newly closed subtheorems.

PDF validation:

- run `pdflatex -interaction=nonstopmode -halt-on-error`;
- run `pdftotext` and inspect theorem/corollary sections;
- render representative pages with `pdftoppm` or equivalent;
- fix readability issues, especially long identifiers in margins.

## Weak-Component Ledger

Automatically mark these weak:

- final theorem with more than three hypotheses;
- any theorem involving probability, concentration, expectation, floating
  point, stability, perturbation, or proof transfer;
- adapters around previous local theorems;
- generated PDF theorem sections;
- newly introduced distributions/events/norm inequalities/FP budgets;
- places where exact and FP arithmetic coexist;
- theorem statements changed during implementation.
- any not-proved ledger item or PDF claim about missing work;
- any theorem that claims to close a source-paper equation or high-probability
  result.

Each weak component needs two consecutive clean passes from different angles:

- Lean theorem type, dependencies, `#print axioms`;
- mathematical comparison to the paper;
- README/PDF/lookup comparison to Lean;
- repository reuse search.

## Final Gate

Run:

```bash
git status -sb
git diff --stat
git diff --check
lake build
lake env lean examples/LibraryLookup.lean
rg -n "\b(sorry|admit|axiom|unsafe|opaque)\b" <touched Lean files>
```

Also run `#print axioms` for final theorem names.

For PDFs, run LaTeX, text extraction, and representative page rendering.

The final response must report theorem names, changed files, validation
outcomes, hidden hypotheses, weak-component summary, not-proved ledger status,
active bottleneck status, and PDF path. If a requested paper-level item is still
open, say that the final gate failed for that scope rather than claiming
completion. For autonomous full-paper requests, make that a checkpoint and
continue with the next open row unless the user explicitly asked to pause or
receive only a status report. If a red bottleneck exists, continue only by
closing a listed dependency, ruling out a listed route, or presenting a genuine
mathematical route choice.
