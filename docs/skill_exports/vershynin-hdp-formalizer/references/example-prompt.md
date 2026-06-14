# Example Prompt

```text
$vershynin-hdp-formalizer

I uploaded one chapter PDF from Vershynin's High-Dimensional Probability.

Use the chapter formalization loop. Treat this as a one-chapter Lean
formalization program, not a single-lemma request.

Read the chapter carefully and:

1. Extract every definition, theorem, lemma, proposition, corollary, assumption,
   random variable, probability event, concentration claim, norm estimate,
   covering/net claim, and proof dependency.
2. Create or update:
   - docs/vershynin_chXX_THEOREM_LEDGER.md
   - docs/vershynin_chXX_NOT_PROVED_LEDGER.md
   - docs/vershynin_chXX_BOTTLENECK_LEDGER.md if needed
3. Search the repository and mathlib first using lookup docs, rg, #check, and
   #print. Reuse existing Lean theorems wherever possible.
4. Before hard proof work, classify each chapter proof as complete, proof
   sketch, citation-only, or missing. For incomplete proofs, search external
   primary literature, follow citation chains as deeply as needed, and create a
   proof-source ledger mapping each missing step to exact theorem/page/equation
   references and intended Lean targets.
5. Run a foundation feasibility gate before downstream theorem work. For every
   chapter-level theorem, list required foundations and mark them
   available-local, small-adapter, missing-foundation, route-choice, or
   out-of-scope-by-user. If a required foundation is missing, make that
   foundation the active Lean target.
6. Formalize the chapter in dependency order:
   definitions, deterministic inequalities, probability kernels, tail/moment
   equivalences, covering arguments, concentration theorems, and chapter
   corollaries.
7. Do not assume concentration, independence, measurability, integrability,
   tail bounds, Orlicz norm equivalences, covering numbers, or universal
   constants unless already proved locally or proved in this run.
8. External literature may guide the route, but it must not close a theorem by
   citation. Formalize the needed result locally before closing a chapter
   theorem.
9. Audit hidden hypotheses and weak components repeatedly until there are two
   consecutive clean passes.
10. If the same theorem remains open after repeated attempts, invoke the
   red-bottleneck protocol: name the blocking theorem, write its Lean statement,
   list dependencies, record failed routes, freeze adjacent work, and only count
   progress when a listed dependency closes, a route is ruled out, or the
   statement is corrected.
11. Update the chapter proof PDF in readable theorem/lemma/corollary style, plus
   README/lookup/example files if this repository uses them.
12. Run the final validation gate and report theorem names, changed files,
    hidden hypotheses, bottlenecks, not-proved status, external sources, and
    the PDF path.

Do not stop until the chapter gate passes unless I ask for a status-only report
or a genuine mathematical choice blocks progress. If a red bottleneck exists,
continue only by closing a listed dependency, ruling out a listed route, or
presenting the route choice.
```

Replace `chXX` with the chapter number or title slug used in the local
repository.
