# Chapter Formalization Loop

Use this reference as the operating loop for one Vershynin high-dimensional
probability chapter PDF.

## Requirement Extraction

Before proving, extract:

1. Chapter title, section numbers, theorem/lemma/proposition/corollary labels.
2. Definitions and notation introduced in the chapter.
3. Random variables, distributions, independence assumptions, probability
   spaces, events, and parameters.
4. Norms and spaces: Euclidean, operator, Frobenius, Orlicz, psi-alpha,
   covering numbers, metric entropy, empirical process classes, or matrix norms.
5. Deterministic assumptions: dimension, sample size, constants, convexity,
   boundedness, isotropy, centering, covariance, rank, sparsity, or net size.
6. Exact statements and proof dependencies.
7. Claims with hidden phrases: "with high probability", "standard", "it is
   easy to see", "by a union bound", "by symmetrization", "by contraction",
   "up to constants", "there exists an absolute constant", "by concentration",
   "by a net argument", or "by truncation".
8. For each theorem-level claim, whether the chapter proof is complete, a proof
   sketch, citation-only, or missing.

## Classification

Classify each target as one of:

- definition/interface;
- deterministic analytic lemma;
- scalar probability lemma;
- moment/tail equivalence;
- concentration inequality;
- covering/net/metric entropy theorem;
- random-vector theorem;
- random-matrix theorem;
- empirical-process theorem;
- application corollary;
- conditional transfer theorem;
- open foundation.

## Ledger Rules

Maintain two ledgers for every chapter.

The theorem ledger records every extracted claim:

- source location;
- exact mathematical statement;
- intended Lean theorem name;
- current status;
- hypothesis classes;
- reused local theorem candidates;
- missing foundations;
- next proof step.

The not-proved ledger records only blockers to a PASS chapter gate:

- open chapter-level claims;
- generated-PDF claims without Lean backing;
- conditional results that do not close the source theorem;
- weak versions advertised separately from the chapter theorem.

Never delete an open row because it is large.  Close it only when a matching
Lean theorem exists and validation passes.

## Library Search

Search in this order:

1. Local project lookup docs and executable lookup files.
2. Local source with `rg`.
3. Mathlib with `rg`, `#check`, `#print`, and small scratch files.

## Proof-Source Acquisition

After local and mathlib search, and before hard proof work, run this phase for
every chapter theorem whose proof is a sketch, citation-only, or missing.

Search external primary literature:

1. Start with the chapter's cited source.
2. Follow citation chains one paper/book/note at a time until each missing
   proof step is explicit enough to formalize or a genuine route choice remains.
3. Prefer original papers, journal/arXiv versions, monographs, and author
   lecture notes over secondary summaries.
4. Record exact theorem/lemma/equation/page/section references and URLs.

Create a proof-source ledger:

- chapter claim and source location;
- missing proof step;
- external source chain;
- assumptions and constants in each source;
- intended local Lean theorem names;
- dependency DAG;
- chosen route and rejected alternatives;
- status: unstarted, partial foundation, formalized, advisory only, rejected,
  or open.

External sources guide theorem design; they do not close a theorem until the
needed result is formalized locally.

## Foundation Feasibility Gate

Before hard Lean work on a chapter-level theorem, create a feasibility table:

- chapter theorem and source location;
- intended final Lean theorem name;
- required foundations: probability model, concentration inequality,
  tail/moment equivalence, Orlicz norm fact, covering number, net argument,
  independence/measurability/integrability fact, spectral theorem, random
  matrix theorem, or asymptotic-constant translation;
- status of each foundation: available-local, small-adapter,
  missing-foundation, route-choice, or out-of-scope-by-user;
- existing local theorem or exact external source location;
- smallest next Lean theorem when missing;
- whether downstream chapter corollaries/PDF work are allowed.

If a required foundation is missing, make that foundation the active target.
Do not prove downstream chapter theorems or polish PDF claims that assume it.
For concentration targets, explicitly name the route: Chernoff/Bernstein,
symmetrization, contraction, chaining, covering-net, matrix concentration, or
another source-backed route.

## Proof Order

Use dependency order, not chapter order, when proving:

1. Local notation and definitions.
2. Deterministic inequalities and norm facts.
3. Basic probability and expectation lemmas.
4. Moment-generating-function or tail kernels.
5. Tail/moment/Orlicz norm equivalences.
6. Net and covering-number lemmas.
7. Concentration inequalities.
8. Random-vector/random-matrix theorems.
9. Chapter corollaries and applications.

## Bottleneck Protocol

Trigger a bottleneck if:

- the same row remains open after two proof/audit passes;
- new lemmas do not change the missing-foundation field;
- Lean failures recur around the same API, typeclass, measurability,
  independence, norm, or constants issue;
- the PDF/ledger/final report repeats the same next step.

The bottleneck is red if the same chapter-level row survives two focused passes
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

Do not keep adding adjacent lemmas unless they are listed dependencies.
For a red bottleneck, use a dedicated bottleneck ledger entry/file and count
progress only when a listed dependency closes, a failed route is ruled out with
evidence, or the theorem statement is corrected to match the chapter source.

## Weak-Component Checks

Run repeated checks until two consecutive passes are clean for:

- hidden hypotheses;
- probability events and failure probabilities;
- independence assumptions;
- measurability/integrability assumptions;
- constants and asymptotic translations;
- theorem/PDF mismatch;
- conditional transfer misuse;
- proof adapters about the wrong object;
- unused or irrelevant theorems.

## Final Chapter Gate

A chapter gate is PASS only when:

- every in-scope chapter-level theorem has a matching Lean theorem;
- weaker or conditional results are not advertised as source theorem closures;
- all hypotheses are exposed and classified;
- ledgers, lookup docs, examples, and PDF agree with Lean names;
- `lake build` succeeds;
- touched Lean files contain no `sorry`, `admit`, new `axiom`, new `unsafe`, or
  placeholder theorem;
- `#print axioms` is acceptable for final theorem names;
- the proof PDF compiles and rendered pages are readable.

If the gate fails for an in-scope theorem, continue from the highest-leverage
open ledger row unless the user requested status-only or a genuine mathematical
choice blocks progress. If a red bottleneck exists, continue only by closing a
listed dependency, ruling out a listed route, or presenting the route choice.
