---
name: lean-stability-formalizer
description: Use when Codex must read a numerical linear algebra or numerical analysis paper, identify every algorithm and error/stability theorem, formalize exact stability/error bounds in Lean, then re-prove the analysis with floating-point/inexact arithmetic using the local repository library. Triggers include RandNLA, stability analysis, backward/forward error, perturbation bounds, exact probability laws, computed bases/singular vectors/projectors/preconditioners, high-probability claims, concentration, theorem PDFs, not-proved ledgers, hidden-hypothesis audits, weak-component loops, library reuse, and external literature searches for missing proof steps.
---

# Lean Stability Formalizer

## Operating Principle

Treat the user as asking for a complete formalization program, not a single
lemma. Read the paper carefully, extract every algorithm and analysis target,
reuse the repository aggressively, and continue until the Lean proof, prose
theorem PDF, lookup docs, and validation gates agree.

Treat user corrections as regression tests for the workflow. If the user points
out that a theorem is irrelevant, conditional, too weak, or misdescribed in the
PDF, update the ledger and docs immediately and prevent the same failure mode in
later work.

## Open-Foundation Continuation Rule

For broad requests such as "prove the full paper", "prove everything in What Is
Not Proved", or "do not stop until the final gate passes", a failed final gate is
not a stopping point. It is a work queue.  But continuation is not permission to
orbit the blocker with adjacent infrastructure.

When an open paper-level item remains in the theorem or not-proved ledger:

- Do not end the turn with only "this is a major formalization project" or "the
  foundation is missing".
- Immediately pick the highest-leverage open ledger row and convert it into the
  next concrete Lean proof target.
- Prefer the row that unlocks the most other rows, is closest to existing local
  infrastructure, or is explicitly requested by the user.
- If the target is too large to finish in one proof step, prove the next reusable
  foundation theorem, update the ledger/PDF/docs, run validation, then continue
  to the next frontier item.
- Only return a final "still open" report when the user asks for status, asks to
  pause, a mathematical choice is genuinely required, or a hard external blocker
  prevents further proof work. In that report, name the exact next theorem to
  attempt, not just the missing field of mathematics.

In other words: honest failure reporting is required, but passivity is a bug.

## Foundation Feasibility Gate

Before proving downstream algorithm theorems, run this gate for every
paper-level target:

1. Name the final paper-level theorem and its exact source location.
2. List the required foundations: probability, concentration, spectral,
   perturbation, convexity, SVD/rank, graph, optimization, and floating-point
   facts.
3. For each foundation, mark one of:
   - `available-local`: already proved in this repository;
   - `small-adapter`: follows from a local theorem with a small wrapper;
   - `missing-foundation`: not locally proved;
   - `route-choice`: several mathematically different routes are viable.
4. If any required foundation is `missing-foundation`, the next formalization
   target is that foundation, not a downstream theorem that assumes it.
5. If any foundation is `route-choice`, compare sources, assumptions,
   constants, and local-library fit before proving.

Do not start PDF polish, floating-point transfer corollaries, or algorithm-level
"final" theorems while the feasibility gate contains an unresolved
`missing-foundation` that the final theorem depends on.

## Empirical Machine-Output Rule

Many numerical analysis books include experiments run on an actual computer and
print only the final output, not a fully specified machine-level computation.
For any book or paper, classify these claims before trying to formalize them.

- `fully-specified-computation`: The source fixes enough details to define one
  mathematical computation: input values, algorithm, operation order,
  floating-point format, rounding mode, exceptional behavior, library routines,
  random seed/law if relevant, and output formatting. Formalize this as an
  executable/model theorem or a compact certificate when it matters.
- `empirical-source-output`: The source reports what happened on a machine but
  omits details such as hardware, compiler, flags, extended registers, fused
  operations, libm version, calculator firmware, decimal I/O, print formatting,
  random seed, or the exact program. Do not treat the reported output as a
  paper-level Lean theorem.
- `mathematical-phenomenon`: The experiment illustrates a stable mathematical
  or floating-point mechanism that can be stated independently of the
  historical machine. Formalize this theorem instead.

For `empirical-source-output` rows:

- This is not permission to skip a hard formalization silently. Every row must
  remain visible in the theorem/not-proved ledger with source location, the
  exact printed claim, missing machine details, any closed replacement theorem,
  and the user-facing status.
- Before assigning this classification, split the source text into subclaims.
  If it contains a formalizable theorem, algorithm specification, smaller
  deterministic computation, or machine-independent phenomenon, formalize that
  part and ledger only the historical machine output as empirical.
- Do not delete, merge away, mark complete, or treat a source claim as out of
  scope solely because it was labeled `empirical-source-output`.
- Do not try to reconstruct an unspecified vendor machine, compiler, libm,
  calculator, or runtime environment just to match a printed number.
- Do not count a local rerun, C/Python trace, emulator output, or sampled plot as
  a proof. It may be recorded only as advisory or as a reproducibility artifact.
- Formalize the algorithmic/mathematical phenomenon that the experiment is
  meant to demonstrate, or prove a conditional theorem under an explicit machine
  model if that is useful.
- Record the printed result in the not-proved/theorem ledger as an empirical
  source-output claim, with the missing machine details and the exact condition
  under which it could later be formalized.
- Downgrade user-facing theorem PDFs honestly: say the historical computer
  output is not formalized unless the machine model is supplied, while naming
  the closed theorem(s) for the underlying phenomenon.

This rule applies to all books, not just Higham. A full chapter formalization
does not require proving under-specified historical computer outputs, but it
does require proving every formalizable subclaim around them, preserving their
source text faithfully, and documenting the empirical carve-out so it cannot be
mistaken for a closed Lean result.

## Computed-Quantity Floating-Point Rule

For every algorithm, distinguish **computed quantities** from quantities used
only in the analysis. Floating-point or inexact-arithmetic theorems must account
for every quantity the implemented algorithm computes, stores, normalizes, or
uses after sampling. The only standing exception in the current RandNLA project
is probability construction itself: sampling probabilities/laws are exact by
user convention. Do not charge FP error for objects that appear only in the
proof or analysis and are never computed by the algorithm.

Before closing any algorithm FP theorem, make an explicit computed-quantity
audit:

- Probability tables or sampling laws: by current user convention for this
  RandNLA project, sampling probabilities are treated as exact mathematical
  inputs/laws. Do not add floating-point error terms, probability-construction
  certificates, sampling-law perturbation losses, cumulative/alias construction
  errors, or normalization/repair obligations for the probabilities unless the user
  explicitly reopens probability-computation error. If the sampling law is
  mathematically fixed, such as uniform `1/m`, say so explicitly and charge
  only the non-probability quantities computed before/after sampling.
- Non-probability computations: the probability exception is narrow. Still
  model FP/inexact-arithmetic error for every computed non-probability quantity:
  singular vectors, bases, projectors, preconditioners, random transforms,
  signs, scale denominators, square roots, row/column scaling, matrix products,
  dot products, sketches, Gram/RHS products, solver inputs, and returned
  outputs.
- Bases and spectral objects: if the algorithm computes singular vectors,
  orthonormal bases, leverage bases, projections, pseudoinverses, QR/SVD data,
  or rank-revealing objects, model the computed versions and their generation or
  storage errors. Do not silently use exact singular vectors or exact projectors
  in an implementation-facing theorem.
- Random transforms and preconditioners: if the algorithm forms or applies
  objects such as `H D U`, SRHT/FHT transforms, Gaussian/FJLT matrices,
  projection matrices `Π`, diagonal signs, scale factors, or preconditioned
  bases `Vhat`, expose the computed object and a perturbation/certificate that
  charges generation, storage, transform arithmetic, normalization, row/column
  scaling, matrix products, dot products, and downstream Gram/RHS computations.
- Algorithm outputs: include rounded arithmetic for every produced sketch,
  sampled matrix, preconditioned matrix, least-squares system, solver input,
  and returned vector/residual.
- Analysis-only objects: if a Gram matrix, covariance, ideal projector, exact
  basis, expectation, or auxiliary event is used only to prove a theorem and is
  not computed by the algorithm, do not invent FP assumptions for it. Instead,
  use it as the exact reference object in the error statement.

Implementation-facing theorem sheets must not replace the floating-point
analysis of computed non-probability quantities by a generic assumption such as
"suppose a certificate exists", "suppose the perturbation is bounded by
\(\tau\)", or "let the implemented object satisfy an error certificate" and
then present the result as final.  If a computed object is used by the
algorithm, the displayed theorem must either:

- instantiate an actual locally proved bound for that object and propagate it
  through all downstream computations; or
- explicitly remove that implementation path from the final closed theorem and
  place it in the not-proved ledger.

Certificate/transfer theorems are allowed only as intermediate infrastructure,
not as the final answer to a user request for floating-point reassessment of an
algorithm.  A PDF or standalone theorem sheet may include them only in a clearly
separate "intermediate infrastructure" or "not yet closed" section, and it must
not count them as final theorem surfaces.  The final implementation-facing
section must contain actual proved bounds for every modeled computed
non-probability operation on the selected algorithm path.

If a concrete implementation routine is not yet formalized, do not close the
algorithm FP theorem for that routine. Record the missing routine instantiation
in the not-proved ledger and state the closed theorem only for the concrete
modeled routine(s) whose error bounds have actually been proved. The PDF must
say whether the displayed theorem is exact-law, exact-object-plus-rounded-use,
fully computed-object implementation-facing, or intermediate infrastructure;
only the fully computed-object theorem may be presented as final for a
computed implementation path.

### Bound Interpretability Rule

Exact error formulas are required, but they are not enough when the displayed
bound is algebraically complicated. For every implementation-facing
floating-point/stability theorem whose final radius has nested definitions,
many sums, or several interacting roundoff terms:

- first state the exact proved bound, with no hidden computed quantities;
- then simplify it into a readable closed form depending on minimal meaningful
  terms such as dimensions, sample size, condition/radius parameters, unit
  roundoff, \(\gamma\)-factors, and relative denominator or solver errors;
- substitute intermediate definitions when doing so improves interpretability;
- for every named composite term that appears in a final theorem surface, give
  a recursive irreducible expansion nearby: replace all locally introduced
  shorthand such as \(T\), \(\tau\), \(\rho\), \(\zeta\), \(K\), \(S(t)\),
  condition/radius aliases, and relative-error aliases by their definitions
  until only primitive theorem inputs, source parameters, norms, dimensions,
  and primitive floating-point quantities remain.  Compact notation may still
  be introduced for readability, but it must not be the only displayed form of
  the final bound or order statement.
- give a big-\(\Theta\) or, when only one-sided control is justified, big-\(O\)
  order statement for the simplified bound, and write that order both in a
  compact form and, for complicated expressions, in the same irreducibly
  expanded variables used by the exact bound;
- state the asymptotic regime for the order statement, including which
  dimensions/parameters are fixed or varying and which roundoff quantities are
  small;
- include a non-vacuity check, such as the bound tending to zero as roundoff
  terms tend to zero for fixed dimensions and source parameters;
- avoid presenting a bound only through opaque symbols like \(T\), \(\tau\), or
  \(\rho\) unless their exact formula, simplified formula, and order are given
  nearby.

The \(\Theta\) statement is explanatory, not a replacement for the exact
proved inequality. If the exact formula is too large for the final theorem
surface, place it in a preceding displayed definition and keep the theorem's
main line in the simplified closed form plus order form.

### Mathematical-Result Correction Rule

When a user identifies a missing computed-quantity, floating-point, stability,
or probability-law assumption in an existing theorem/corollary, do not fix the
PDF with prose-only commentary.  The correction must be written as a
mathematical result whenever it changes the theorem surface:

- state a named theorem/corollary/lemma/proposition or clearly labeled
  corrected-result block;
- list the hypotheses explicitly, including computed objects, certificates,
  probability-law transfer losses, perturbation radii, and positivity or
  nonzero conditions;
- display the corrected inequality/probability/error bound with all new loss
  terms;
- identify which terms correspond to computed algorithm quantities and which
  objects remain exact analysis-only references;
- name the Lean theorem(s) or certificate constructors that prove the displayed
  statement, and record any uninstantiated computation routine in the
  not-proved ledger.

Short remarks may still explain why the old statement was exact-law or
exact-object-only, but they must not be the only correction when the
implementation-facing theorem needs a stronger mathematical surface.

## Red Bottleneck Rule

A bottleneck becomes **red** when the same paper-level theorem survives two
focused proof/audit passes with the same missing foundation.

When a red bottleneck exists:

- freeze downstream work on the blocked paper-level theorem;
- create or update a dedicated bottleneck ledger file, not only prose inside
  another ledger;
- write the exact blocking theorem family and a dependency checklist;
- count progress only when a listed dependency closes, a failed route is ruled
  out with evidence, or the theorem statement is corrected to match the source;
- do not add adjacent adapters, transfer theorems, PDF sections, or lookup prose
  unless they directly document or close a listed dependency;
- after one focused pass with no dependency status change, switch to a different
  listed route or ask the user only if the choice changes the theorem being
  formalized.

For a red bottleneck, "do not stop until the final gate passes" means: do not
stop until the red bottleneck is closed, reduced to a strictly smaller proved
dependency, or a genuine mathematical route choice is presented. It does not
mean keep producing surrounding infrastructure.

## Front-Loaded Proof-Source Rule

Do not wait until a proof is stuck to discover that the source paper omitted
the intermediate mathematics.  For full-paper work, or for any target involving
concentration, spectral perturbation, SVD/rank, convex optimization, graph
Laplacians, or nontrivial floating-point composition, run a proof-source
acquisition phase before attempting the hard Lean proof.

Before proving a paper-level theorem:

- decide whether the proof in the uploaded paper is complete enough to
  formalize directly;
- if not, search external primary literature immediately, after the local
  repository search and before adding new proof infrastructure;
- identify the original/cited papers, journal/arXiv versions, monographs,
  lecture notes, and citation-chain dependencies needed for every missing
  proof step;
- create a proof-source ledger mapping
  `paper claim -> missing step -> external source location -> Lean target`;
- record exact theorem, lemma, equation, page, section, URL, and whether the
  source is formalized locally, advisory only, rejected, or still open;
- choose a proof route only after comparing assumptions, constants, source
  fidelity, formalization difficulty, and fit with existing local definitions.

External sources guide theorem design and proof order, but they never close a
Lean theorem by citation.  A paper-level row closes only when the needed result
is proved locally or reused from an already formalized local dependency.

## Bottleneck Detection Rule

Do not confuse activity with progress. A proof effort has hit a bottleneck when
any of the following occurs:

- the same paper-level ledger row remains open after two consecutive proof or
  audit passes;
- two or more new lemmas were added, but the row still has the same missing
  foundation;
- Lean failures keep returning to the same theorem family, API mismatch,
  probability construction, norm bridge, or floating-point budget;
- the PDF, ledger, or final report repeats essentially the same "next step";
- a new theorem is not syntactically used by the target theorem or by a listed
  dependency of that theorem.

When a bottleneck is detected:

- freeze the work into one named bottleneck theorem with an exact Lean statement;
- add a bottleneck entry to the theorem/not-proved ledger with the source claim,
  target theorem, required dependencies, failed routes, chosen route, and next
  validation command;
- stop proving adjacent adapters unless they are explicitly listed as
  dependencies of the bottleneck theorem;
- count progress only when a listed dependency closes, a failed route is ruled
  out with evidence, or the bottleneck theorem statement is corrected to match
  the source claim;
- if several proof routes remain possible, compare assumptions, constants,
  source fidelity, and local-library fit before choosing one;
- ask the user only when a genuine mathematical choice changes the theorem
  being formalized.

After one focused bottleneck pass, run a weak-component check on the bottleneck
entry. If no listed dependency changed status, do not keep orbiting; report the
exact theorem, obstruction, failed route, and next mathematical choice, then
continue only if there is a different dependency route inside the ledger.

When working inside `lean-fp-analysis`, first read:

- `docs/FORMALIZATION_AUTOMATION_PROMPTS.md`
- `docs/LIBRARY_LOOKUP.md`
- `examples/LibraryLookup.lean`

Use `references/formalization-loop.md` for the full loop and gate checklist.
Use `references/formalization-automation-prompts.md` when you need the complete
project prompt playbook, including repeated weak-component checks and
math-readable PDF requirements.

## Workflow

1. Parse the paper.
   - Extract all algorithms, equations, assumptions, random variables, error
     events, deterministic parameters, and theorem/corollary claims.
   - Separate exact arithmetic, randomized, floating-point, and mixed claims.
   - Classify every reported computer experiment as
     `fully-specified-computation`, `empirical-source-output`, or
     `mathematical-phenomenon` under the Empirical Machine-Output Rule.
   - For each algorithm step, mark every quantity that is computed in practice:
     probabilities, normalizers, bases, singular vectors, projectors,
     preconditioners, transforms, scale denominators, sketches, Gram/RHS data,
     solver inputs, and outputs.
   - Mark analysis-only quantities separately so FP error is not added to proof
     artifacts that the implementation never computes.
   - Identify which claims are stability bounds, approximation bounds,
     concentration bounds, or algorithmic definitions.
   - Mark whether the uploaded paper gives a complete proof, a proof sketch, a
     citation-only proof, or no proof for each paper-level target.

2. Build a theorem ledger.
   - For each algorithm, write the target Lean theorem names before proving.
   - Classify every hypothesis as source assumption, domain assumption,
     floating-point validity, reused theorem assumption, or suspicious artifact.
   - Reject theorem designs that assume the target concentration, stability, or
     perturbation result.
   - Maintain a not-proved ledger for every source claim or generated-PDF claim
     still missing. Record exact source location, current Lean status, missing
     foundations, next action, and whether any closed result is only a
     subtheorem.
   - For `empirical-source-output` rows, record missing machine details and do
     not promote the printed output to a theorem target unless the user supplies
     or requests an explicit machine model.
   - An empirical classification never lets a row disappear. Cite the exact
     source location, keep the printed output in the ledger, and state which
     surrounding subclaims remain ordinary formalization obligations.
   - Never close a paper-level result using only a conditional transfer,
     deterministic consequence, expectation bound, or proof adapter.
   - Maintain a proof-source ledger for every target whose proof is incomplete
     in the uploaded paper.  Cross-reference it from the theorem and
     not-proved ledgers.

3. Search before proving.
   - Read the lookup docs and use `rg` for definitions, theorem names, and
     nearby algorithms.
   - Prefer existing local results and small adapters.
   - Re-prove background only after a library search shows it is absent.
   - Keep reusable algebra/probability/FP infrastructure in the logically
     appropriate shared file, not inside an algorithm-specific file.

4. Acquire proof sources before hard proof work.
   - If the repository and bundled dependencies do not contain the needed
     theorem, or if the paper/book proof skips intermediate steps, search the
     internet and external primary literature deliberately before inventing a
     replacement proof.
   - Prefer primary sources: original papers, journal versions, arXiv
     preprints, official books/monographs, author lecture notes, and official
     documentation.
   - Follow citation chains as deeply as needed: start with the cited source,
     then inspect one, two, three, or more supporting papers until the missing
     proof step is explicit enough to formalize or a real mathematical choice
     remains.
   - Record every external source in the theorem/not-proved ledger with exact
     theorem, lemma, equation, page, section, URL or bibliographic citation,
     and whether it was formalized, rejected, or advisory only.
   - Produce a proof-route plan before implementing: source chain, theorem
     dependency DAG, local Lean targets, route alternatives, chosen route,
     risks, and validation commands.
   - External literature may guide theorem design, constants, and proof order,
     but it must not become a hidden hypothesis.  Close a paper-level row only
     after the needed result is proved locally or reused from a formalized
     local dependency.
   - If competing sources give different assumptions or constants, choose the
     version closest to the repository definitions, record the alternatives,
     and expose all assumptions in Lean.

5. Formalize exact analysis first.
   - Define the exact algorithm and mathematical objects.
   - Prove deterministic or probabilistic exact-arithmetic bounds.
   - For high-probability results, prove the event probability from the local
     probability library or newly formalized concentration results.

6. Formalize floating-point analysis.
   - Identify every computed quantity and every rounded operation in the
  algorithm, excluding probability construction under the current exact-law
  convention, but including basis/SVD/projector construction,
  transform/preconditioner generation, non-probability normalization, sketch
  formation, Gram/RHS products, solver inputs, and returned outputs.
   - Treat the probability exception as the only exception. If a quantity is
     computed by the algorithm and is not the probability law/table itself, add
     an FP bound, a perturbation certificate, or a visible not-proved ledger
     obligation.
   - For this project, assume the probability distribution used by Algorithms
     1--3 is exact unless the user explicitly asks to model probability
     computation again.
   - For computed singular vectors, bases, projectors, or preconditioners, prove
     or require explicit generation/storage certificates and propagate those
     errors through the algorithm-level bound.
   - For exact uniform or otherwise fixed sampling laws, state that the
     probabilities themselves are not computed from data and charge only the
     computed preprocessing/sketching quantities.
   - Reuse local FP results for addition, summation, division, dot product,
     matrix-vector, matrix-matrix, and perturbation bounds.
   - State a deterministic FP perturbation budget when appropriate.
   - Combine exact analysis and FP stability into the final inexact-arithmetic
     theorem.
   - Make hidden dimension factors explicit with closed-form lemmas when a
     budget hides dimensions in dependent types.

7. Audit weak components repeatedly.
   - Repeat checks for fragile theorems, proof adapters, high-probability
     claims, floating-point claims, and PDF claims until there are two
     consecutive clean passes.
   - Run the bottleneck detector after each failed audit pass. If a component
     fails for the same reason twice, create a named bottleneck theorem and
     dependency ledger before adding more foundations.
   - If a claim is weaker than the paper's theorem, downgrade the prose and
     state exactly what was proved.
   - Re-audit ledger classifications themselves. A "not proved" item must not
     disappear unless a matching Lean theorem closes the paper-level claim or
     the user explicitly narrows scope.
   - If the full-paper gate still fails after the audit, select the next open
     row and continue proving. Do not treat the audit result itself as the
     deliverable.
   - Do not fail a full-chapter gate merely because an under-specified
     `empirical-source-output` row is not proved. The gate fails only if the row
     is misclassified, unledgered, overstated in the PDF, or a fully specified
     theorem/phenomenon remains open.
   - If an empirical row hides a formalizable theorem, algorithmic invariant,
     deterministic computation, or machine-independent phenomenon that is still
     missing from Lean or the not-proved ledger, the full-chapter gate fails.
   - Check notation and dimensions: any displayed indexed quantity must really
     depend on its indices, and all dimension/sample-count dependence in FP
     budgets must be explicit.

8. Write the theorem PDF as mathematics.
   - Present notation, definitions, theorem/corollary statements, source
     references, scope, exact-vs-floating-point computability, and Lean
     provenance. Do not include sketched proofs or "proof idea" sections in
     user-facing theorem PDFs unless the user explicitly asks for them.
   - Put Lean names in compact reference blocks after mathematical statements.
   - Include `Hypotheses and Scope` and, when needed, `What Is Not Proved`.
   - Generate `What Is Not Proved` from the live ledger; separate open
     paper-level claims from closed deterministic subtheorems.
   - Render and visually inspect representative pages; do not rely only on
     successful LaTeX compilation.

9. Update library navigation.
   - Update `README.md`, `docs/LIBRARY_LOOKUP.md`,
     `examples/LibraryLookup.lean`, project memory, and any theorem ledger.
   - Add `#check`s for new user-facing definitions and theorems.

10. Run the final gate.
   - `git diff --check`
   - `lake build`
   - `lake env lean examples/LibraryLookup.lean`
   - placeholder scan for touched Lean files:
     `rg -n "\b(sorry|admit|axiom|unsafe|opaque)\b" <touched Lean files>`
   - `#print axioms <final theorem>` for final theorem names
   - PDF compile/text/render checks if docs changed

## Output Standard

Final reports must include:

- final theorem/corollary names;
- external sources used, with exact source locations and whether each source was
  formalized, rejected, or advisory only;
- proof-source ledger status for any paper-level theorem whose uploaded proof
  was incomplete;
- changed files;
- validation commands and outcomes;
- hidden-hypothesis summary;
- weak-component summary;
- bottleneck summary, if any row required bottleneck handling;
- not-proved ledger status, including open paper-level items;
- empirical-source-output summary, if any such rows exist: source locations,
  exact printed outputs, why they are under-specified, what theorem(s) were
  proved instead, and what would be needed to formalize the historical output;
- exact PDF path if generated;
- any warnings, with pre-existing warnings clearly separated.

Do not claim completion if the Lean theorem is conditional on an unexplained
bound, if a PDF theorem is stronger than the Lean statement, or if a
high-probability claim merely assumes concentration.

If completion is not yet possible because paper-level rows remain open, keep
working from the highest-priority open row unless the user explicitly requested
only a report or pause.
