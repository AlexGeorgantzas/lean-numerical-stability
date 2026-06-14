---
name: vershynin-hdp-formalizer
description: Use when Codex must formalize one PDF chapter from Vershynin's High-Dimensional Probability or a similar probability text in Lean. Triggers include chapter-by-chapter formalization, concentration inequalities, subgaussian/subexponential variables, random matrices, covering nets, empirical processes, theorem ledgers, not-proved ledgers, bottleneck detection, hidden-hypothesis audits, and math-readable proof PDFs.
---

# Vershynin HDP Formalizer

## Scope

Work on one uploaded chapter PDF at a time.  Do not treat a chapter request as
the whole book unless the user explicitly asks for a cross-chapter project.

Use `references/chapter-formalization-loop.md` as the operating loop.  Use
`references/example-prompt.md` when the user asks how to invoke the skill.

## Operating Principle

Treat each chapter as a formalization program:

- extract every definition, theorem, lemma, proposition, corollary, assumption,
  random variable, probability event, concentration statement, asymptotic
  claim, and proof dependency from the chapter;
- create a theorem ledger and a not-proved ledger before proving;
- search the local Lean repository and mathlib first;
- classify every chapter proof as complete, proof sketch, citation-only, or
  missing before hard proof work;
- run a front-loaded proof-source acquisition phase for incomplete proofs:
  search primary literature, follow citation chains, and build a source-chain
  ledger before adding local proof infrastructure;
- prove missing foundations only after search shows they are absent;
- run a foundation feasibility gate before downstream chapter theorem work:
  if a theorem depends on an unproved concentration, covering, tail/moment,
  spectral, measurability, independence, or asymptotic foundation, make that
  foundation the active target before proving corollaries that assume it;
- use external primary literature when the chapter skips intermediate steps,
  but formalize the needed result locally before closing a chapter theorem;
- never close a chapter theorem by assuming its concentration inequality,
  event probability, independence property, tail bound, moment bound, norm
  estimate, or covering-number estimate;
- continue from open ledger rows rather than stopping at a failed gate;
- switch to the red-bottleneck protocol when the same row survives repeated
  passes with the same missing foundation. Red status freezes adjacent work:
  count only listed dependency closures, route eliminations, or statement
  corrections as progress.

## Chapter Workflow

1. Read the chapter PDF and extract source claims.
   - Record exact page/theorem/equation labels.
   - Normalize notation for norms, constants, probability space, independence,
     random variables, Orlicz norms, subgaussian parameters, nets, dimensions,
     and asymptotic notation.
   - Separate textbook definitions/examples from final theorem obligations.

2. Create chapter ledgers.
   - Use names such as `docs/vershynin_chXX_THEOREM_LEDGER.md`,
     `docs/vershynin_chXX_NOT_PROVED_LEDGER.md`, and, if needed,
     `docs/vershynin_chXX_BOTTLENECK_LEDGER.md`.
   - For every claim record: source location, precise mathematical statement,
     Lean target names, status, hypothesis classes, missing foundations, failed
     proof routes, and the next proof step.

3. Search before proving.
   - Read local lookup files if present.
   - Use `rg`, `#check`, and `#print` for existing definitions/theorems.
   - Reuse local probability, norm, algebra, topology, finite-dimensional,
     measure-theory, and real-analysis facts whenever possible.

4. Acquire proof sources before hard proof work.
   - For every incomplete chapter proof, identify the cited/original papers,
     monographs, lecture notes, and citation-chain dependencies needed to fill
     the gaps.
   - Record exact theorem/lemma/equation/page/section/URL references.
   - Build a proof-source ledger mapping chapter claim, missing proof step,
     external source, Lean target, dependencies, route status, and next action.
   - Do not use an external theorem as a hidden hypothesis; formalize it
     locally or keep the chapter row open.

5. Run the foundation feasibility gate.
   - For each chapter-level theorem, list required foundations and classify
     them as available-local, small-adapter, missing-foundation, route-choice,
     or out-of-scope-by-user.
   - If a required foundation is missing, make that foundation the next Lean
     theorem target.
   - Do not prove downstream corollaries, PDF claims, or transfer theorems that
     assume a missing in-scope foundation.

6. Formalize in dependency order.
   - Definitions and notation.
   - Deterministic analytic inequalities.
   - Scalar probability foundations.
   - Tail and moment equivalences.
   - Covering/metric entropy facts.
   - Random-vector and random-matrix concentration theorems.
   - Chapter corollaries and applications.

7. Handle constants honestly.
   - Prefer explicit constants over `O`, `o`, or hidden universal constants.
   - If the chapter uses universal constants, introduce a transparent Lean
     parameter or prove a concrete constant version.
   - Do not mark the chapter claim closed if Lean proves only a weaker
     expectation, deterministic, or conditional statement.

8. Audit hidden hypotheses.
   - Classify each as source assumption, domain assumption, measurability/
     integrability assumption, independence assumption, distributional
     assumption, reused theorem assumption, or suspicious proof artifact.
   - Remove suspicious artifacts or downgrade the theorem and keep the ledger
     item open.

9. Use the red-bottleneck protocol.
   - If a row survives two passes, freeze one exact blocking theorem statement.
   - List required dependencies and failed routes.
   - Count progress only when a listed dependency closes, a failed route is
     ruled out, or the theorem statement is corrected to match the chapter.
   - Do not keep adding adjacent lemmas, PDF polish, or lookup prose as the
     main deliverable while the same missing foundation remains open.

10. Write a math-readable chapter proof note.
   - Use theorem/lemma/corollary style, not a dump of Lean names.
   - Include notation, hypotheses, proof ideas, Lean reference blocks, a
     Hypotheses and Scope section, and a What Is Not Proved section generated
     from the not-proved ledger.

11. Run the final chapter gate.
   - `git diff --check`
   - `lake build`
   - any local lookup/example Lean file
   - placeholder scan for touched Lean files
   - `#print axioms` for final theorem names
   - PDF compile/text/render checks if a proof PDF was generated

## Final Report

Report final theorem names, changed files, validation commands, hidden
hypotheses, weak components, bottlenecks, not-proved ledger status, external
sources used, and the exact PDF path.  If any in-scope chapter theorem remains
open, mark the chapter gate as FAIL and continue from the highest-leverage open
row unless the user asks for status-only or a genuine mathematical choice is
needed. If a red bottleneck exists, continue only by closing a listed dependency,
ruling out a listed route, or presenting the route choice.
