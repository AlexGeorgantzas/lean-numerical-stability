---
name: higham-chapter-formalization
description: Use when Codex is asked to read and formalize a chapter of Higham's numerical analysis book in Lean/Mathlib. This skill applies a needs-based selection policy, follows the project's four-way split and contract documents, reuses existing library results, produces end-to-end proofs, audits difficult probability and floating-point claims, handles missing foundations and bottlenecks, skips empirical or underspecified material, and records every formalize/reuse/skip/defer decision.
---

# Higham Chapter Formalization

Use this skill to turn one supplied chapter of the Higham book into a reviewable Lean/Mathlib contribution. The default objective is **not** to encode every sentence. The default objective is to formalize the chapter's important, precise mathematical content and every dependency needed for that content, while avoiding work on empirical demonstrations, machine anecdotes, vague prose, and glossary-only terminology.

The required result is:

1. compiling Lean code for the selected mathematical content;
2. end-to-end proofs with no gaps disguised as assumptions;
3. a complete source inventory showing what was formalized, reused, skipped, deferred, or marked as a benchmark candidate;
4. dependency, source, and audit records proportionate to the difficulty of the selected targets; and
5. a concise completion report.

For routine algebraic chapters, the inventory and report may be enough. For hard imported results, high-probability theorems, implementation-facing floating-point results, or repeated blockers, also maintain the specialized ledgers and audits required below.

## Governing policy

Apply these rules in this order:

1. Follow the user's explicit instructions for the current task.
2. Follow repository-local instructions such as `AGENTS.md`, contribution guides, naming conventions, and the existing file architecture.
3. Follow this skill.
4. Follow the book's mathematical intent, translating it into idiomatic Lean rather than imitating printed notation literally.

When the source meeting contains both tentative early comments and a later consensus, use the later needs-based consensus. In particular, do **not** interpret an early suggestion to formalize every notation item as a mandate to build a glossary or reproduce the book's typesetting conventions.

### Scope of the advanced procedures

The needs-based Higham policy and the selected mode govern all imported workflow guidance:

- A broad continuation rule applies only to targets inside the selected `core`, `comprehensive`, or `benchmark` scope. It does not enlarge core scope to every sentence, experiment, or historical output.
- Requirements written for a different repository, paper, or RandNLA project apply only when the current repository or user explicitly adopts them. In particular, do not inherit project-specific probability, documentation, or file-layout conventions automatically.
- A theorem PDF, README update, lookup example, or dedicated ledger file is mandatory only when requested, required by repository practice, or triggered by the complexity rules in this skill.
- When two auxiliary procedures conflict, choose the one that preserves source fidelity, end-to-end proof, the repository's conventions, and the main needs-based selection policy.

## Parallel formalization coordination documents

**Assigned partition:** Split 3 of 4.

This project is carried out in four parallel splits. Before building a chapter inventory, designing contracts, or writing Lean code, each Codex agent must locate and consult these shared planning documents. Their contents must remain in those documents rather than being copied into this skill.

Read and use them in this order:

1. Read `HIGHAM_PARALLEL_FORMALIZATION_BLUEPRINT.md` in full first. Use it for the shared split mechanism, split boundaries, dependency and placeholder protocol, contract rules, cross-split imports, merge plan, and chapter-by-chapter skeleton.
2. Identify the assigned split, then read that split's complete section in `split_primary_contracts.md`. Use it for the exact split-owned primary labels, local equation ledger, problem ledger, and Appendix A ownership.
3. Use `chapter_index.md` as the project-wide lookup table for chapter sections, source locations, labels, numbered equations, and problem or solution numbers.

The planning documents govern parallel ownership and coordination; this skill governs content selection, proof quality, audits, and reporting. The rendered book PDFs remain the source of truth for exact mathematical statements. If the files are stored under a repository subdirectory such as `planning/`, locate them by these exact filenames and follow the repository's paths. Do not start work until the assigned split and owned source items are known.

## Default mode and optional modes

### Core mode - default

Formalize named results, important numbered equations, precise symbolic claims, theoretical exercises, and only the definitions and infrastructure required by them. This is the release-quality first pass.

### Comprehensive mode - only when explicitly requested

After the core pass compiles, revisit additional precise symbolic claims that were not needed by a core theorem. The exclusions for empirical, machine-specific, qualitative, editorial, and literature-review material still apply.

### Benchmark mode - only when explicitly requested

Formalize algorithms and imported results needed to compare methods or measure formalization effort, even when the book introduced them only through a numerical example. Keep benchmark work separate from the core chapter-completeness accounting.

If the prompt merely says "formalize Chapter X", use **core mode**.

## Required inputs

At minimum, locate or obtain:

- the chapter source, preferably the original PDF pages plus extractable text;
- the exact book edition;
- the chapter number and title;
- the Lean repository and its current toolchain; and
- any existing formalization of earlier chapters or shared numerical-analysis infrastructure.

Useful optional inputs include a chapter page range, previous inventories, issue trackers, and benchmark requirements.

### Edition verification is mandatory

Do not assume the edition from a filename. Verify it from the title page, copyright page, chapter numbering, equation numbering, or repository metadata. Record the edition in the inventory and report. Do not mix page numbers, theorem labels, or equations from different editions.

If the edition remains ambiguous and the ambiguity changes the mathematical content or numbering, ask one targeted clarification before coding. Continue with unambiguous repository inspection while waiting.

## Key terms used by this skill

- **Core target**: a declaration that the chapter itself presents as mathematically important, such as a named result, a significant equation, a precise definition, or a theoretical exercise.
- **Dependency**: a definition, lemma, structure, notation bridge, or imported result required to state or prove a core target.
- **Precise claim**: a statement whose domain, assumptions, quantifiers, and conclusion can be translated without inventing a threshold, constant, probability model, or meaning for qualitative language.
- **Symbolic example**: a parameterized or general mathematical example, such as a matrix depending on `ε`, whose conclusion is an exact identity, inequality, or theorem.
- **Fixed numerical example**: a particular vector, matrix, decimal input, calculator output, or machine run used to illustrate behavior.
- **Empirical claim**: a claim supported by computed outputs, tables, plots, timings, named hardware, or observations such as "we find" or "typically" rather than by a stated proof.
- **Educational foreshadowing**: an early informal use of a theorem whose full definition or proof is given in a later chapter.
- **End-to-end proof**: a proof using only explicit source assumptions, established earlier declarations, or trusted library theorems. It does not assume the target or an equivalent imported claim merely to make the file compile.
- **Source proof status**: whether the book supplies a complete proof, a proof sketch, a citation-only justification, or no proof for a selected claim.
- **Implementation-facing theorem**: a theorem presented as describing an algorithm actually computed in inexact arithmetic, rather than only an exact reference object or an abstract transfer principle.
- **Computed quantity**: an object the modeled algorithm forms, stores, normalizes, transforms, or uses after input acquisition.
- **Analysis-only object**: an exact reference object used only in the proof and not computed by the modeled algorithm.
- **Fully specified computation**: a concrete computation whose inputs, operation order, arithmetic format, rounding behavior, exceptional cases, relevant library routines, randomness, and output interpretation are specified well enough to define one mathematical execution.
- **Empirical source output**: a reported machine result lacking enough implementation detail to define a unique computation.
- **Mathematical phenomenon**: a precise, machine-independent theorem or mechanism illustrated by an experiment.
- **Open selected-scope row**: an inventory or not-proved item that remains required by the current mode but is not yet closed by a matching Lean theorem.
- **Bottleneck**: a selected-scope target that repeatedly fails for the same missing foundation or proof route.
- **Red bottleneck**: a bottleneck that survives two focused passes with the same missing foundation; downstream and adjacent work must then freeze.
- **Weak component**: a theorem, proof bridge, ledger classification, or documentation claim that is especially prone to hidden assumptions or overstatement and therefore requires repeated independent audit.

## The non-negotiable operating principles

1. **Inventory before implementation.** Read the whole chapter and classify its contents before committing to a formalization plan.
2. **Needs-based first pass.** Start from core theorem-level content and backtrack to dependencies.
3. **Repository-first and Mathlib-first.** Search before defining or reproving.
4. **Precise and symbolic beats empirical and numerical.** Formalize exact general mathematics; skip observed machine behavior by default.
5. **A precise prose claim can be a theorem.** Do not restrict attention to labels or display equations.
6. **A numbered equation is a strong signal, not an unconditional command.** Inventory every numbered equation and formalize it by default unless a documented exclusion applies.
7. **Definitions are demand-driven.** Formalize semantic definitions that are required or mathematically central; skip terms that only name an informal idea.
8. **Prefer end-to-end proofs.** Do not hide an unproved mathematical result in a hypothesis.
9. **Defer foreshadowing to its real treatment.** Formalize the lightweight foundational definition now if useful, but place the full theorem where the book proves it.
10. **Every omission must be visible.** A skipped or deferred item needs a reason in the inventory.
11. **Run a feasibility gate before hard downstream work.** A missing foundational theorem becomes the active target; it is not converted into a convenient hypothesis.
12. **Continue dependency-first within the selected scope.** A failed final gate is a work queue for open selected-scope rows, not a reason to polish adjacent material or stop at a vague diagnosis.
13. **Account for every modeled computation.** An implementation-facing floating-point theorem must model or explicitly leave open every computed quantity and rounded operation on its chosen algorithm path.
14. **External literature guides proofs but does not replace them.** A citation can determine a Lean target and proof route, but only a local theorem or trusted imported library result closes the row.
15. **Corrections are regression tests.** When a user or audit finds an irrelevant result, hidden hypothesis, weak statement, or documentation mismatch, update the theorem surface, inventory, and report together and prevent recurrence.
16. **Audit fragile results more than once.** Probability, stability, perturbation, floating-point, transfer, and documentation claims require independent clean checks before completion.

# Workflow

## Phase 0: Inspect the repository and establish a clean baseline

Before reading the chapter in detail:

1. Complete the mandatory planning-document read described in **Parallel formalization coordination documents**, and record the assigned split and owned chapter range.
2. Read all applicable `AGENTS.md` files and project documentation.
3. Inspect `lean-toolchain`, `lakefile.lean`, `lake-manifest.json`, import conventions, namespaces, and nearby chapter files.
4. Identify the project's standard build and test commands.
5. Run the smallest relevant baseline check before editing.
6. Search for existing definitions and results from previous chapters.
7. Note whether the repository uses one file per chapter, multiple topic files, or shared foundational modules.
8. Locate repository navigation and theorem-discovery documents such as `README.md`, library lookup notes, examples, or generated theorem summaries when they exist.
9. Record the baseline status of files and warnings that may later need to be distinguished from new issues.
10. Do not reorganize unrelated code.

Typical checks, adjusted to the repository, include:

```bash
rg -n "relevantName|relevant phrase" .
lake env lean path/to/File.lean
lake build
```

Do not assume these exact commands if the repository defines another workflow.

## Phase 1: Read the entire chapter and build the source inventory

Read the full chapter before writing substantial Lean code. Do not stop after the first theorem.

For PDFs:

- use extracted text for search and navigation;
- inspect rendered pages whenever equations, subscripts, superscripts, matrix layout, diagrams, or footnotes may have been corrupted by extraction;
- use printed page numbers and source labels, not only raw PDF page indices;
- inspect footnotes when they change assumptions, such as a guard-digit requirement; and
- do not guess an unreadable formula.

Inventory all of the following, even when the final decision is to skip:

- every theorem, lemma, proposition, corollary, and explicitly named result;
- every numbered equation;
- every precise unnumbered identity, inequality, recurrence, limit, expansion, or invariance claim;
- mathematical definitions embedded in prose;
- algorithms and pseudocode;
- symbolic and numerical examples;
- figures and tables;
- cross-references to earlier or later chapters;
- exercises and all of their subparts;
- imported claims attributed to other sources;
- explicit phrases such as "not proved", "it follows from", "with high probability", "standard", "future work", or "see Chapter Y" that may conceal dependencies; and
- for each algorithm, every quantity that is an input, a random choice, computed in exact arithmetic, computed in inexact arithmetic, or used only in the analysis.

Use this inventory schema:

```markdown
| ID | Source location | Kind | Statement summary | Precision | Generality | Source proof | Dependencies | Decision | Reason code | Lean artifact/status |
|---|---|---|---|---|---|---|---|---|---|---|
```

Recommended values:

- `Precision`: `precise`, `partly precise`, `underspecified`.
- `Generality`: `general`, `symbolic family`, `fixed exact instance`, `fully specified computation`, `empirical run`, `editorial`.
- `Source proof`: `complete`, `sketch`, `citation-only`, `none`, `not applicable`.
- `Decision`: `FORMALIZE_CORE`, `FORMALIZE_DEPENDENCY`, `REUSE_EXISTING`, `DEFER`, `BENCHMARK_CANDIDATE`, `SKIP`.

For an algorithmic or probabilistic chapter, supplement the inventory with an extraction table:

```markdown
| Algorithm/source | Inputs | Outputs | Deterministic parameters | Random choices/law | Exact object | Computed object | Computed quantities | Analysis-only objects | Target claims |
|---|---|---|---|---|---|---|---|---|---|
```

For every reported experiment, split the surrounding passage into separately classifiable subclaims and assign one of:

- `fully-specified-computation`;
- `empirical-source-output`; or
- `mathematical-phenomenon`.

A single paragraph may contain all three. Keep the historical output visible in the inventory, formalize any selected precise phenomenon, and do not let an empirical label hide an algorithm specification, invariant, exact computation, or theorem.

Treat user corrections to an inventory row, theorem statement, or scope classification as regression tests: update the affected row and audit analogous rows before continuing.

Do not begin the main implementation until all named results and numbered equations have inventory rows.

## Phase 2: Classify each item with the decision procedure

Apply the following decision procedure in order.

```text
1. Is the item merely editorial, historical, bibliographic, typographic, or expository?
   -> SKIP.

2. Is it a programming-language convention, named-machine observation,
   calculator exercise, empirical table, plot, or hardware-specific output?
   -> SKIP in core mode.

3. Is its mathematical conclusion underspecified by words such as
   "much worse", "almost", "typically", "small", "large", "can be",
   "virtually constant", or "of order" without a precise meaning?
   -> SKIP or DEFER. Do not invent a theorem.

4. Is it educational foreshadowing whose required theorem is proved later?
   -> DEFER the full result; formalize only a central lightweight definition
      if it is independently useful now.

5. Is it a named theorem, lemma, proposition, corollary, or proof problem?
   -> FORMALIZE_CORE, unless the statement itself is empirical or underspecified.

6. Is it a numbered mathematical equation?
   -> FORMALIZE_CORE by default, unless it is only fixed test data,
      machine output, an empirical-only formula, a duplicate already reused,
      or a result explicitly deferred to a later chapter.

7. Is it a precise unnumbered mathematical claim with a true/false content?
   -> FORMALIZE_CORE if central; otherwise FORMALIZE_DEPENDENCY or include
      it in the optional comprehensive pass.

8. Is it a definition needed to state or prove a selected target?
   -> FORMALIZE_DEPENDENCY or REUSE_EXISTING.

9. Is it a precise symbolic example that proves or exposes a mathematical
   phenomenon independently of one machine run?
   -> Usually FORMALIZE_CORE or FORMALIZE_DEPENDENCY.

10. Is it a fixed numerical example?
    -> SKIP by default. Promote only if it is a necessary exact witness for a
       selected theorem or an explicitly requested benchmark.

11. Does it set up a useful algorithmic comparison for benchmarking?
    -> Mark BENCHMARK_CANDIDATE. Do not silently add it to core scope.
```

### Subclaim splitting and empirical classification

Do not classify an entire example as empirical merely because it contains printed output. Separate:

1. the algorithm or formula being used;
2. any exact deterministic or symbolic claim;
3. the machine-independent phenomenon the example illustrates; and
4. the historical output itself.

In core mode, a fully specified fixed computation is still skipped by default unless it is a necessary witness for a selected theorem or the user requests executable/machine semantics. In benchmark mode it may become a target. An under-specified historical output remains `SKIP-EMPIRICAL` or `SKIP-MACHINE-SPECIFIC`, but the row must state what details are missing and what precise replacement theorem, if any, was formalized.

### Reason codes

Use one of these stable reason codes in the inventory:

- `CORE-NAMED-RESULT`
- `CORE-NUMBERED-EQUATION`
- `CORE-PRECISE-PROSE`
- `CORE-SYMBOLIC-EXAMPLE`
- `CORE-THEORETICAL-EXERCISE`
- `DEP-REQUIRED`
- `REUSE-REPOSITORY`
- `REUSE-MATHLIB`
- `DEFER-LATER-CHAPTER`
- `DEFER-MISSING-PRECISE-STATEMENT`
- `BENCHMARK-COMPARISON`
- `SKIP-EMPIRICAL`
- `SKIP-FIXED-NUMERICAL`
- `SKIP-MACHINE-SPECIFIC`
- `SKIP-PROGRAMMING-LANGUAGE`
- `SKIP-QUALITATIVE`
- `SKIP-TERMINOLOGY`
- `SKIP-FIGURE-TABLE`
- `SKIP-EDITORIAL`
- `SKIP-LITERATURE-REVIEW`
- `SKIP-DUPLICATE`

## Phase 3: Search the repository and Mathlib before defining anything

For every proposed definition or theorem:

1. Search the current repository by mathematical term, likely Lean name, notation, and neighboring concepts.
2. Search the installed Mathlib source and use Lean queries such as `#check` or `#find` where useful.
3. Inspect the actual theorem statement and required imports. Do not rely only on a search-result title.
4. Reuse the existing declaration directly when it matches.
5. If source traceability is useful, add a thin, proved wrapper theorem rather than duplicating the underlying development.
6. If a book definition differs only by notation, translate it to the existing representation instead of creating a parallel type.
7. Record the reused declaration in the inventory.

Examples of concepts that are likely to exist in some form include matrices, finite vectors, norms, floor and ceiling, real and complex analysis, probability distributions, determinants, QR-related infrastructure, limits, asymptotics, and standard series identities. Their existence must still be checked in the actual project version.

### Do not build a duplicate lexicon

Printed conventions such as "capital letters denote matrices" or MATLAB-style colon notation are not mathematical objects that need independent Lean declarations. Use the repository's existing matrix and indexing representation. Add source-facing notation only when it materially improves later statements and does not create a competing API.

## Phase 3A: Acquire proof sources before hard missing-foundation work

Run this phase when a selected target has a proof sketch, citation-only proof, omitted intermediate mathematics, or a missing foundation not found in the repository or installed Mathlib.

1. Classify the source proof as `complete`, `sketch`, `citation-only`, or `none`.
2. Search the source's own citations first, then primary literature such as original papers, journal or arXiv versions, official monographs, and author notes.
3. Follow citation chains until the missing step is explicit enough to state in Lean or a genuine mathematical route choice remains.
4. Compare candidate routes by source fidelity, assumptions, constants, formalization difficulty, and fit with local definitions.
5. Translate each external result into an explicit local Lean target. Do not cite the external result as a hypothesis substitute.
6. Record hidden assumptions exposed by the source, including independence, measurability, boundedness, finite dimension, positivity, invertibility, self-adjointness, rank, or floating-point validity.
7. Stop source acquisition once the dependency route is sufficiently explicit; do not turn it into an unrelated literature survey.

Maintain a proof-source ledger when this phase is triggered:

```markdown
| Selected claim | Missing proof step | External source and exact location | Assumptions/constants | Intended Lean target | Route/status | Local closure theorem |
|---|---|---|---|---|---|---|
```

Allowed route/status values include `formalized`, `partial foundation`, `advisory only`, `rejected`, `route choice`, and `open`. Record theorem, lemma, equation, page, section, bibliographic identifier, and stable URL when available. Represent multi-source citation chains in the dependency graph. External sources may guide statement design and proof order, but a selected row closes only through a local proof or an already formalized trusted dependency.

## Phase 4: Build the dependency graph and choose the chapter boundary

For each selected target, list:

- source definitions it uses;
- existing repository or Mathlib declarations it uses;
- new local definitions required;
- lemmas needed for the proof;
- results referenced from earlier chapters;
- results referenced from later chapters; and
- any ambiguity or missing side condition.

Then topologically order the implementation.

### Cross-chapter rules

1. Reuse already formalized earlier chapters.
2. Reuse Mathlib when possible.
3. If the current chapter's selected theorem genuinely requires a local missing lemma, prove it now.
4. If the passage is merely an early illustration of a theorem developed later, defer the illustration or full stability analysis to the later chapter.
5. If a later result is essential to a current named theorem rather than mere exposition, either formalize the dependency in a reusable earlier module or report a genuine blocker. Do not assume it.
6. Every deferred row must name the likely destination chapter or section when the source identifies one.

### End-to-end does not mean assumption-free

Mathematical hypotheses and model specifications are allowed. For example, a theorem may assume a standard roundoff model, differentiability, nonzero denominators, or matrix invertibility when those are source assumptions.

What is forbidden is adding a hypothesis equivalent to an unproved intermediate theorem merely to complete the current proof. For example, if the text informally invokes "the QR algorithm is backward stable" before proving it later, do not add that sentence as a free hypothesis and call the resulting example end-to-end.

### Foundation feasibility gate

Before hard proof work on each selected chapter-level theorem, create a feasibility table:

```markdown
| Selected theorem/source | Intended Lean theorem | Required foundation | Status | Existing theorem/source | Smallest next Lean target | Downstream work allowed? |
|---|---|---|---|---|---|---|
```

Use these statuses:

- `available-local`: directly reusable;
- `small-adapter`: a small proved wrapper is needed;
- `missing-foundation`: absent locally and required;
- `route-choice`: several mathematically different proof routes are plausible;
- `out-of-scope-by-policy`: excluded by the selected mode.

If a required foundation is `missing-foundation`, make that foundation the active target before proving downstream algorithm, stability, floating-point transfer, or documentation-facing theorems that depend on it. If it is a `route-choice`, compare assumptions, constants, source fidelity, and library fit before choosing. Ask the user only when the choice changes the mathematical theorem or requested scope in a material way.

Examples of foundations that often need an explicit gate include probability constructions, concentration inequalities, spectral and perturbation theory, SVD/rank results, convexity or optimization, graph/Laplacian facts, asymptotic bridges, and floating-point primitives. When matrix concentration is required, name the intended route explicitly—for example trace-MGF/Lieb-Tropp, Golden-Thompson/Ahlswede-Winter, a covering-net argument, scalar symmetrization, or another precise route—before downstream work.

### Selected-scope continuation rule

For an autonomous request to complete the selected mode, a failed final gate is a work queue:

1. rank open selected-scope rows by user priority, number of dependents unlocked, proximity to local infrastructure, and risk of documentation overclaiming;
2. choose the highest-leverage row;
3. make its smallest meaningful missing dependency the next Lean target;
4. update the inventory and any not-proved or proof-source ledger immediately after progress; and
5. rerun the relevant validation before moving on.

This rule never promotes skipped empirical, qualitative, machine-specific, or comprehensive-only material into core scope. If a target is too large, close a genuine reusable dependency, keep the chapter-level row open, and continue dependency-first.

### Bottleneck detection and red-bottleneck protocol

A target is bottlenecked when any of the following holds:

- the same selected-scope row survives two proof or audit passes;
- two or more new lemmas were added but the missing foundation did not change;
- Lean failures repeatedly return to the same API, typeclass, measurability, norm, spectral, probability, or floating-point issue;
- the report repeats the same next step; or
- a new theorem is not used by the target or any listed dependency.

Create a bottleneck ledger entry containing the source claim, exact blocking Lean theorem, dependency list, local and external candidates, failed routes with concrete errors, chosen route, next dependency theorem, and validation command.

A bottleneck becomes **red** after two focused passes with the same missing foundation. Then:

- freeze downstream, transfer, PDF-polish, and adjacent infrastructure work;
- keep a dedicated bottleneck ledger file or clearly named report section;
- count progress only when a listed dependency closes, a route is ruled out with evidence, a hidden hypothesis is removed, or the theorem statement is corrected to match the source; and
- after one focused pass with no dependency-status change, switch to another listed route or present the genuine route choice if it changes the theorem.

Do not orbit a blocker with unrelated adapters.

## Phase 5: Write an implementation and theorem-design plan before the main proof work

The plan should state:

- files to create or modify;
- selected declarations in source order;
- reused repository and Mathlib declarations;
- new dependencies and their feasibility status;
- external proof sources and route choices, when needed;
- deferred items and benchmark candidates;
- expected proof risks and weak components;
- any computed-quantity, probability, or floating-point audit required; and
- the incremental and final verification commands.

Design the theorem statements before proving them. Use a table such as:

```markdown
| Source target | Lean name | Plain mathematical statement | Exact hypotheses | Hypothesis classes | Dependencies | Source proof | Final or internal | Status |
|---|---|---|---|---|---|---|---|---|
```

Classify hypotheses as:

- `source assumption`;
- `domain assumption`;
- `floating-point/model validity`;
- `reused theorem assumption`; or
- `suspicious proof artifact`.

Reject a design that assumes the requested concentration, stability, perturbation, correctness, or error bound. Also reject a design that closes a source theorem only with an expectation result, deterministic consequence, conditional transfer, different algorithmic object, or exact-arithmetic subcase unless that is exactly the selected source claim.

When selected-scope claims remain open, maintain a not-proved ledger:

```markdown
| Source location | Exact selected claim | Current Lean status | Why current results do not close it | Missing foundation | Next concrete theorem | Blocking final gate? |
|---|---|---|---|---|---|---|
```

Recommended Lean-status values are `unstarted`, `partial foundation`, `deterministic subtheorem`, `conditional transfer`, `exact-arithmetic subcase`, `fully proved`, and `out of scope by policy`.

The source inventory remains the authoritative record for all chapter content; the not-proved ledger is a focused gate for still-open selected-scope claims. Do not let a row disappear merely because a related subtheorem was proved. A conditional theorem does not close a row whose missing content is exactly the condition; an expectation theorem does not close a high-probability row; and a theorem about a different object or algorithm does not close the source claim.

Prefer a small number of coherent declarations over many speculative helpers. Do not over-generalize beyond the source merely because a more abstract theorem is conceivable.

## Phase 6: Implement in Lean

### Source fidelity

- Preserve the source's mathematical domain unless a library theorem supplies a harmless generalization.
- Make necessary side conditions explicit: nonzero denominators, positivity, dimensions, differentiability, invertibility, and index bounds.
- Do not replace `≈`, `O(·)`, `≪`, or qualitative prose by equality or an arbitrary inequality.
- Do not silently repair a suspected typo. State the issue in the report and, if safe, implement a clearly documented corrected version.
- Distinguish a minimum from an infimum. If existence of a minimizer is not established, do not assert `min` merely because the prose uses that word informally.
- When an audit or user correction changes a theorem's assumptions, computed objects, probability loss, perturbation radius, or conclusion, make the correction as a named Lean result or corrected theorem statement. Do not patch only the prose while leaving the mathematical surface unchanged. The corrected surface must list the new hypotheses and loss terms, identify computed versus analysis-only objects, name the Lean declarations that prove it, and leave any uninstantiated routine visible in the not-proved ledger.

### Declaration choice

- Use `def` for semantic definitions.
- Use `abbrev` only for transparent source-facing aliases that add no new mathematics.
- Use `lemma` or `theorem` for true/false claims.
- Use a `structure` or predicate for an abstract numerical model when appropriate.
- Comments and docstrings document a declaration but never count as formalization by themselves.

### Partial mathematical notions

If the book says a notion is undefined on part of its domain, model that honestly. Prefer an explicit domain hypothesis, subtype, or existing partial representation over an arbitrary totalization.

Example: for relative error, do not silently define the zero-denominator case to be zero unless the project has already adopted that convention. State `x ≠ 0` where needed.

### Abstract numerical models versus machine emulation

Formalize the mathematical specification, not a named calculator or historical workstation.

For a standard floating-point model, prefer a predicate or structure expressing the existence of an error term `δ` satisfying the stated bound. Do not attempt to emulate MATLAB, Fortran, an HP calculator, or a particular processor unless the user explicitly requests a machine-semantics project.

Incidental values such as the unit roundoff of a historical machine are skipped in core mode. A precise abstract theorem about a floating-point system may still be core in a chapter devoted to that mathematical model.

### Computed quantities and implementation-facing theorems

For every selected algorithm, distinguish exact reference objects, computed objects, and analysis-only objects before stating a floating-point or inexact-arithmetic theorem.

Audit every quantity the modeled implementation forms, stores, normalizes, transforms, or uses, including when relevant:

- bases, singular vectors, projectors, factorizations, pseudoinverses, and preconditioners;
- random transforms, signs, scale factors, denominators, square roots, and normalization constants;
- matrix products, dot products, sketches, Gram matrices, right-hand sides, solver inputs, and returned outputs;
- input conversion, storage, and intermediate rounding when they are part of the chosen model; and
- probability tables or sampling-law construction when the source or repository models them as computed.

Do not add error terms to objects used only in the proof and never computed. Use them as exact reference objects. Conversely, do not silently use an exact basis, projector, factorization, or transform in an implementation-facing theorem when the algorithm is claimed to compute it.

No project-specific exception—such as treating probability construction as exact—applies unless the user, source model, or repository explicitly adopts it. State any exact-operation convention on the theorem surface and in the report.

Generic certificates and transfer theorems are useful intermediate infrastructure, but they do not by themselves close an implementation-facing path. The final theorem for that path must either instantiate locally proved bounds for all modeled computed quantities and propagate them to the output, or leave the path visibly open in the not-proved ledger. Label theorem surfaces honestly as one of:

- exact arithmetic;
- exact object plus rounded use;
- fully computed-object implementation-facing; or
- intermediate certificate/transfer infrastructure.

### Algorithms

Do not formalize pseudocode merely because it appears.

Formalize an algorithm when at least one of these holds:

- the algorithm is itself a central mathematical definition;
- a selected theorem proves its correctness or stability;
- later core results require its semantics; or
- benchmark mode explicitly requests it.

Translate the mathematical semantics, not MATLAB syntax or comment markers. A function that compiles is not, by itself, a proof of the book's claim about the algorithm.

If an algorithm appears only to generate a table or demonstrate one machine's behavior, skip it in core mode.

### Probabilistic and high-probability claims

When a selected claim is probabilistic:

- identify the probability space or distribution, random variables, deterministic parameters, and event;
- state the exact probability bound and failure probability;
- prove the event probability using a local theorem or a newly formalized result;
- name the concentration or probability inequality used and expose all of its hypotheses; and
- verify that thresholds such as `Q`, `τ`, or `ε` receive their guarantee from the stated random model.

A deterministic theorem conditioned on `goodEvent`, a bound on a random counter, or a concentration event does not close a high-probability source theorem unless the probability of that event is also proved. An expectation theorem does not close a high-probability theorem. Keep the source row open and describe the proved result at its actual strength.

### Symbolic versus numerical examples

Formalize a parameterized example when it yields an exact proof, such as an `ε`-dependent matrix factorization or a symbolic error bound. Skip a fixed decimal matrix and its observed output by default.

A fixed exact instance may be promoted only when it is logically necessary as a witness or counterexample to a selected theorem. If promoted, encode the exact mathematical values, not rounded display strings.

### Indexing

The book commonly uses one-based mathematical indices while Lean structures often use zero-based finite types. Make the translation explicit and test boundary cases.

- Prefer existing finite-index conventions in the repository.
- State how source index `i = 1, ..., n` maps to Lean indices.
- Avoid ad hoc natural-number indexing with repeated bound proofs when a finite type is standard.
- Check row/column orientation carefully for submatrices and replaced columns.

### Norms and unspecified choices

Do not choose an "appropriate norm" on the author's behalf. Formalize a generic normed statement when the source supports it, or wait until the book specifies a concrete norm such as the 2-norm.

### Exact and approximate arithmetic

- Exact algebraic identities and inequalities are suitable targets.
- Approximate decimal outputs from floating-point runs are empirical and skipped by default.
- A theorem about an error bound is suitable when the bound and assumptions are explicit.
- A rule of thumb such as "forward error is approximately condition number times backward error" is not a theorem until the source gives a precise formulation.

### Bound interpretability

For a selected implementation-facing error or stability theorem with a complicated final radius:

1. state the exact proved inequality with no hidden computed quantities;
2. give a readable closed form in primitive source parameters, dimensions, norms, unit-roundoff or `γ` terms, and solver/denominator errors;
3. recursively expand locally introduced shorthand near the theorem until a reviewer can see the primitive dependence;
4. give a big-`O` or big-`Θ` interpretation only when justified, state the asymptotic regime, and show both compact and fully expanded parameter dependence when the compact form hides meaningful terms;
5. prove or check non-vacuity, such as convergence of the bound to zero as roundoff terms tend to zero with dimensions and source parameters fixed; and
6. keep the exact theorem primary—the asymptotic explanation never replaces it.

Do not present only opaque aliases such as `T`, `τ`, `ρ`, or `K` on the final theorem surface.

### Proof construction

- Reuse library lemmas before writing low-level algebra.
- Keep helper lemmas local to the mathematical dependency they serve.
- Prefer transparent, maintainable proofs over brittle tactic scripts.
- Compile incrementally after each coherent declaration.
- Do not use `sorry`, `admit`, `by_contra!`-style guesswork without understanding the goal, or a new global `axiom`.
- Do not assume the target conclusion or an imported stability theorem as a hypothesis.
- Do not weaken the statement merely to obtain an easy proof without reporting the change.
- Implement in layers: add a coherent definition or lemma group, compile the touched module, update the theorem-design and ledger status, then continue.
- If a proof becomes unexpectedly large, search the repository and proof-source ledger again before writing more low-level infrastructure.
- If the same dependency fails twice, invoke the bottleneck protocol rather than adding adjacent bridge lemmas.
- Name internal adapters and transfer lemmas as such; do not advertise them as the chapter-level result.

### Source traceability

Every source-facing declaration should have a concise docstring containing, when available:

- book edition;
- chapter and section;
- printed page;
- equation, theorem, lemma, or problem label; and
- a short paraphrase of the source statement.

Do not paste long book passages into comments. Keep docstrings concise and mathematical.

Example pattern:

```lean
/-- Higham, 2nd ed., Chapter X, Section X.Y, equation (X.Z):
    concise paraphrase of the mathematical statement. -/
theorem ... := by
  ...
```

Follow the repository's naming conventions. Do not force this exact name or layout when the project uses another standard.

When an external source supplied a missing proof route, record its exact theorem, lemma, equation, page, or section in the proof-source ledger and, when appropriate, in a concise code comment or report entry. Do not paste long copyrighted passages.

## Phase 7: Verify and audit the formalization

At minimum:

1. Compile every changed Lean file.
2. Run the repository's relevant build or test target.
3. Search touched files for unfinished proofs, new axioms, unsafe placeholders, and accidental experimental declarations.
4. Run `#print axioms` for each final selected theorem when practical.
5. Confirm imports are no broader than necessary.
6. Confirm all source labels, theorem statements, and inventory decisions against the rendered source.
7. Confirm the code reuses current repository definitions rather than duplicates.
8. Check one-based/zero-based index translations, dimensions, row/column orientation, denominators, and domain restrictions.
9. Confirm every open selected-scope row remains visible in the not-proved ledger and every skipped empirical row remains visible in the source inventory.
10. Distinguish new warnings from pre-existing baseline warnings.

Typical final checks, adapted to the repository, include:

```bash
git status -sb
git diff --stat
git diff --check
rg -n "\b(sorry|admit|axiom|unsafe|opaque)\b" path/to/touched/files
lake env lean path/to/Changed.lean
lake build
lake env lean examples/LibraryLookup.lean  # when this repository uses it
```

Use repository-specific commands when they differ. A text scan is an audit prompt, not proof that every matched token is invalid; inspect each new match. Do not claim completion if a selected declaration does not compile or an open selected-scope row remains.

### Hidden-hypothesis audit

List every hypothesis of every final selected theorem and classify it as `source assumption`, `domain assumption`, `floating-point/model validity`, `reused theorem assumption`, or `suspicious proof artifact`.

Answer explicitly:

1. Is the target conclusion or an equivalent missing theorem assumed?
2. Is a concentration, stability, unbiasedness, variance, perturbation, or correctness result assumed when it should be proved?
3. Is exact arithmetic assumed for a quantity that the theorem presents as computed?
4. Does a conditional, expectation, deterministic, transfer, or different-object result falsely close a stronger source row?
5. Does the report or optional PDF say more than the Lean theorem proves?

Any affirmative answer keeps the final gate open until corrected or the source row is honestly reclassified.

### Probabilistic audit

For each selected probabilistic theorem, verify:

- the probability space or distribution;
- the event and all random variables;
- deterministic parameters and support/measurability assumptions;
- the exact lower probability bound;
- the local theorem proving each concentration or tail step; and
- the absence of an unproved `goodEvent`, `boundedEvent`, or equivalent hidden event.

A high-probability source row fails the gate if concentration is only assumed.

### Floating-point and computed-quantity audit

For each selected floating-point theorem, verify:

- the exact algorithm and computed algorithm are both identifiable;
- every rounded operation and computed quantity on the advertised path is listed;
- exact-operation conventions are explicit and justified;
- local error lemmas are instantiated rather than replaced by a generic unexplained certificate;
- dimension and sample-count dependence is visible;
- indexed notation genuinely depends on its displayed indices; and
- the final exact bound, simplified interpretation, and non-vacuity claim agree.

If a concrete computation routine is not formalized, do not describe that path as fully implementation-facing.

### Repeated weak-component audit

Automatically mark as weak:

- final theorems with more than three nontrivial hypotheses;
- any probability, concentration, expectation, floating-point, stability, perturbation, or transfer theorem;
- adapters around existing results;
- theorem statements changed during implementation;
- new distributions, events, norm bridges, or error budgets;
- places where exact and inexact arithmetic coexist;
- source rows claimed to close a numbered equation or major theorem; and
- inventory, not-proved, bottleneck, report, or optional PDF claims about completion.

Use a ledger such as:

```markdown
| Component | Why weak | First check | Fix/justification | Second independent check | Third check if needed | Evidence | Status |
|---|---|---|---|---|---|---|---|
```

Check each weak component from at least two independent angles: Lean theorem type and axioms, mathematical comparison with the book, documentation comparison, and repository-reuse search. A component passes only after two consecutive clean checks. If it fails twice for the same reason, invoke the bottleneck protocol.

### Adversarial and cleanup audit

Act as a skeptical reviewer and look for:

- prose stronger than Lean;
- a theorem name suggesting a different algorithmic object;
- expectation described as high probability;
- deterministic described as randomized;
- a floating-point path omitting a computed operation;
- irrelevant but true results promoted as core;
- a duplicated library theorem;
- an open row that disappeared without a matching Lean theorem;
- misleading indexed or dimensional notation; and
- unused helpers left from a failed route.

Remove unused or misleading material. If risky to delete, quarantine it in a clearly experimental location and do not count it as a chapter result. Update repository navigation documents only when new public declarations or repository practice require it.

### Optional theorem-note or PDF audit

Generate a theorem-style PDF or standalone mathematical note only when the user requests it or the repository requires it. Build it only after the corresponding Lean results compile.

The note should contain, as appropriate:

1. a title and short abstract;
2. notation and algorithm or equation setup;
3. mathematical definitions;
4. readable theorem, lemma, and corollary statements;
5. compact Lean-provenance blocks after the mathematics;
6. a `Hypotheses and Scope` section;
7. a `What Is Not Proved` section generated from the live ledger when limitations remain; and
8. an optional file map.

Keep Lean names subordinate to the mathematics. Every probability statement must identify its event and failure probability; every floating-point statement must identify the rounded path and perturbation budget. Do not overstate conditional or partial results. Include a concise proof-dependency outline only when requested or customary; do not invent proof sketches unsupported by Lean.

When a PDF is produced, compile it with a halting-on-error mode, extract text, render representative pages, and visually inspect theorem readability, long identifiers, cross-references, and margins.

## Phase 8: Produce the decision report

Create or update a chapter report. Include the conditional sections only when relevant, but never omit information needed to understand an open or excluded source item.

```markdown
# Higham Chapter X Formalization Report

## Source and scope
- Edition:
- Chapter:
- Printed pages:
- Source file:
- Mode: core | comprehensive | benchmark
- Parallel split: 1 | 2 | 3 | 4
- Planning documents consulted: blueprint | assigned split contract | chapter index
- Selected-scope gate: PASS | FAIL

## Completed selected targets
| Source label | Lean declaration | File | Theorem surface | Notes |

## Reused from repository or Mathlib
| Source concept/result | Existing declaration | File/module |

## New dependencies
| Declaration | Why needed | Used by | Feasibility status |

## External proof sources
| Selected claim | Source and exact location | Role | Local Lean closure | Status |

## Skipped items
| Source location | Summary | Reason code |

## Empirical source outputs
| Source location | Printed claim/output | Missing machine details | Precise subclaim/replacement theorem | Status |

## Deferred items
| Source location | Summary | Destination/dependency | Reason |

## Benchmark candidates
| Source location | Methods compared | Required dependencies |

## Open selected-scope items
| Source location | Exact claim | Current Lean status | Missing foundation | Next theorem |

## Hidden-hypothesis summary
- Final theorem assumptions and classifications:
- Suspicious assumptions found and resolved:

## Weak-component and bottleneck summary
- Weak components checked:
- Active/closed bottlenecks:
- Failed routes and next listed dependency, if any:

## Verification
- Commands run:
- Result:
- New versus pre-existing warnings:

## Documentation
- Inventory path:
- Not-proved/proof-source/bottleneck ledger paths, if any:
- Theorem note or PDF path, if generated:

## Open issues
- Ambiguities, suspected source typos, route choices, or genuine blockers.
```

The report and source inventory together must account for every named result, numbered equation, exercise subpart, and empirical output claim. A reviewer should be able to see why any item is absent from Lean and whether the absence is an intentional policy decision or an unresolved selected-scope gap.

A skipped or correctly classified under-specified empirical output does not make the selected-scope gate fail. The gate fails when such an item is unrecorded or overstated, when a formalizable subclaim around it is missed, or when a selected mathematical target remains open.

# Detailed content-selection rules

## Named theorems, lemmas, propositions, and corollaries

Formalize them unless:

- the printed statement is itself empirical;
- the conclusion is underspecified;
- it is only a citation to a theorem developed later and not needed now; or
- the user excludes it.

Include the proof. If the book omits proof but the result is core, search the repository and Mathlib, then prove or explicitly defer it. Do not create an axiom.

## Numbered equations

Every numbered equation must be inventoried. Formalize it by default when it is:

- a definition;
- an identity;
- an inequality or error bound;
- a recurrence with mathematical significance;
- an abstract model assumption;
- a formula used by a core result; or
- a precise statement that can stand independently of an experiment.

A numbered equation may be skipped or deferred when it is only:

- fixed test data for a numerical run;
- a machine-specific output;
- a formula whose only role is an excluded empirical experiment;
- a duplicate of a reused standard theorem; or
- an early preview of a theorem intentionally handled later.

Document the exception. Do not silently omit numbered material.

## Precise prose claims

A sentence embedded in prose should become a lemma when it has a determinate mathematical content.

Examples of the right shape include:

- invariance under a stated scaling;
- equality of two formulas;
- a bound under explicit assumptions;
- existence or uniqueness under clear hypotheses; and
- a symbolic implication.

Do not skip such a claim merely because it lacks a number or theorem heading.

## Qualitative or pseudo-theorem prose

Skip claims whose conclusion cannot be stated without making up mathematics. Red-flag words include:

- much better or much worse;
- nearly, almost, virtually, usually, generally, typically;
- small or large without a quantified context;
- severe, harmless, satisfactory, accurate, robust;
- can be or may be when no existential statement is intended;
- of order `u` when no asymptotic or explicit bound is provided; and
- phrases justified only by a figure or table.

Do not repair such prose by selecting an arbitrary epsilon, norm, probability distribution, constant, or asymptotic filter.

If a later chapter replaces the prose by a precise theorem, defer to that theorem.

## Definitions and terminology

Formalize a definition when:

- it is mathematically precise;
- it is used by a selected theorem;
- it is a central reusable concept of numerical analysis; or
- later chapters will clearly depend on it.

Skip or defer terminology when:

- it merely names an informal concept;
- the book does not reason with it formally;
- implementing it would require an arbitrary representation unrelated to later theorems; or
- its defining words are themselves qualitative.

Do not create a digit-list API merely to encode the phrase "significant digits" when no theorem requires it. Conversely, a precise concept such as relative residual or QR factorization is a legitimate definition when used by results.

## Notation and background conventions

Use Lean's and Mathlib's native representations. Do not formalize:

- letter-shape conventions;
- typography;
- comment syntax of another language;
- colon notation merely as printed syntax; or
- statements that a symbol will be used for a computed quantity.

Do formalize semantic operations, such as a submatrix or column replacement, when a selected theorem actually needs them and they are not already available.

## Figures and tables

Skip the visual artifact itself in core mode.

- Do not recreate plots.
- Do not encode table entries from experiments.
- Do not formalize a diagram as a graphical object.

If the surrounding text states an independent precise mathematical relation, formalize that relation separately.

## Numerical experiments and machine-specific material

Classify each experimental passage before deciding what to formalize.

### Fully specified computation

A computation is fully specified only when the source fixes enough detail to define a unique mathematical execution: inputs, algorithm, operation order, floating-point format, rounding mode, exceptional behavior, relevant library routines, randomness or seed/law, and output interpretation.

Even then, skip a fixed computation in core mode unless it is a necessary exact witness for a selected theorem. It may be formalized in benchmark mode, comprehensive mode when explicitly selected, or a user-requested machine-semantics task.

### Empirical source output

Skip the historical output itself when details such as hardware, compiler, fused operations, extended registers, library version, decimal I/O, calculator firmware, random seed, or exact program are missing. Do not reconstruct an unspecified machine merely to match a printed number, and do not count a local rerun or emulator trace as proof.

Keep the row visible with:

- the source location and printed claim;
- the missing implementation details;
- any precise algorithmic or mathematical subclaim extracted from the passage;
- the theorem formalized instead; and
- what additional model would be required to formalize the historical output.

### Mathematical phenomenon

Formalize a precise machine-independent phenomenon illustrated by the experiment when it is a selected theorem or dependency. Examples include exact cancellation identities, symbolic instability families, abstract roundoff bounds, or deterministic error propagation.

This rule does not prohibit formalizing an abstract floating-point model or a precise theorem about representable numbers when that is central mathematical content.

## Complexity and flop counts

Formalize a complexity result only when the cost model, input size, and conclusion are precise enough to state as a theorem and the result is core or needed later.

Skip informal highest-order flop commentary, implementation-dependent counts, and empirical timing comparisons unless benchmark mode requests them.

## Exercises

Classify each exercise and each subpart separately.

Formalize exercises that ask to:

- prove an inequality, identity, limit, or error bound;
- derive a condition number;
- show equivalence of formulas;
- prove correctness or stability under explicit assumptions; or
- construct a symbolic counterexample or formula.

Skip exercises that ask to:

- type values into a calculator;
- run MATLAB or another program;
- plot results;
- compare observed outputs;
- inspect a machine-specific phenomenon; or
- perform a purely empirical experiment.

For mixed exercises, formalize the theoretical subclaim and skip the experimental instruction. If an exercise explicitly requires later chapters, mark it `DEFER-LATER-CHAPTER` unless its dependencies already exist.

## Imported claims and standard results

When the book states a known result without proof:

1. Search the repository and Mathlib.
2. Reuse a matching theorem if available.
3. Classify the source proof as complete, sketch, citation-only, or absent.
4. If a selected dependency is absent locally, acquire primary proof sources and choose a route before building substantial infrastructure.
5. Prove the needed result in an appropriate reusable module or keep the selected row open with its exact missing foundation.
6. If it only supports an empirical illustration, skip it in core mode.
7. If it enables a useful method comparison, mark it as a benchmark candidate.

An external citation is not permission to add an unproved axiom or a free hypothesis. Record the exact source location and local theorem that ultimately closes the dependency.

## Educational foreshadowing

Introductory chapters often use a later theorem to explain intuition. Detect this pattern through phrases such as "see Chapter Y", "as will be shown", or a direct later theorem reference.

In core mode:

- formalize a central basic definition if lightweight;
- do not duplicate the later chapter's full analysis;
- do not assume the later theorem to make the current example compile; and
- record the deferral and destination.

This preserves end-to-end proofs and avoids doing a major topic in the wrong chapter.

## Benchmark candidates

A numerical example may reveal a useful benchmark when it compares two methods or algorithms and the project wants to measure formalization of their correctness or stability.

Mark it `BENCHMARK_CANDIDATE` when:

- two or more methods are explicitly contrasted;
- the comparison suggests a meaningful theorem-level task;
- dependencies can be isolated from the empirical data; and
- the benchmark would measure the intended capability rather than machine output transcription.

In benchmark mode, formalize the mathematical methods and precise claims, not the original sample table or hardware run.

# Precision audit

Before accepting any statement as a target, answer all of these:

1. What are the quantified variables?
2. What are their types and dimensions?
3. What assumptions are explicit or mathematically necessary?
4. Are all denominators nonzero?
5. Is the norm specified?
6. Is the indexing convention clear?
7. Does `min` actually exist, or is an infimum intended?
8. Does approximate notation have a defined semantics?
9. Is the conclusion exact enough to be true or false?
10. Can the statement be formalized without inventing a constant or threshold?
11. Is it a theorem, a model assumption, a definition, or merely an observation?
12. Is a later theorem being used prematurely?
13. If probabilistic, what are the distribution, event, random variables, and exact probability guarantee?
14. If implementation-facing, which quantities are computed and which are analysis-only?
15. Does the source prove the claim, sketch it, cite it, or omit it?
16. Does a proposed theorem close the exact source claim rather than only a transfer, expectation, deterministic subcase, or different object?
17. Are all asymptotic regimes and dimension dependencies explicit?

If the answer to 9 or 10 is no, skip or defer rather than guessing. If 13 through 17 reveal a missing foundation, keep the claim selected but make the missing foundation the active target.

# Lean modeling guidance for recurring Higham concepts

These are modeling principles, not mandatory APIs. Follow the repository and installed Mathlib version.

## Vectors and matrices

Prefer the project's existing `Matrix` and finite-index representation. Match dimensions explicitly. Use standard matrix operations and finite sums instead of custom nested lists unless the repository already chose a list-based model.

## Error measures

Represent absolute, relative, normwise, and componentwise errors with explicit domains. If the source distinguishes signed error from absolute error, preserve that distinction.

Prove simple structural facts, such as scaling invariance, as lemmas when the assumptions are precise and the facts are used or mathematically central.

## Backward and forward error

Prefer problem-specific definitions over a premature universal stability framework. The book often adapts the notion to each problem. Avoid a generic predicate containing an undefined word such as "small".

When backward error is an optimization over perturbations, model the feasible set carefully and prove existence before using a minimum. Use an infimum if that is the mathematically correct available notion.

## Conditioning and asymptotics

A condition number formula, derivative expression, or Taylor theorem is suitable when differentiability and nonzero conditions are explicit. Intuitive rules of thumb are not substitutes for quantitative bounds.

Use Mathlib's asymptotic framework only when the source really states an asymptotic claim and it contributes to a selected target.

## Floating-point arithmetic

Separate:

- an abstract roundoff model;
- a mathematical floating-point system; and
- one concrete machine implementation.

The first two may be formal targets in appropriate chapters. The third is skipped by default. Model assumptions should be explicit predicates or structures, not global axioms about all real arithmetic.

For an implementation-facing theorem, inventory every computed object and rounded operation, reuse local error lemmas for arithmetic and matrix operations, make dimension dependence explicit, and propagate concrete bounds to the returned result. Treat abstract certificates as intermediate unless instantiated for the advertised path.

## Probability and randomized numerical analysis

Use the repository's existing probability model and distributions. State random and deterministic quantities separately, define the event, and prove its probability. Do not introduce hidden `goodEvent` assumptions. If the selected theorem needs concentration absent from the repository, run proof-source acquisition and the foundation feasibility gate before downstream work.

## Factorizations and numerical algorithms

Reuse existing determinant, LU, QR, orthogonality, triangularity, and norm infrastructure. Formalize the exact algebraic definition before a stability theorem. If a stability theorem belongs to a later chapter, defer it rather than using it as an assumption in an introductory example.

# Chapter 1 calibration examples

Use these examples to calibrate future decisions. They are examples of the policy, not an exhaustive Chapter 1 task list.

## Formalize or reuse in core mode

- The abstract standard roundoff equation and its error bound, modeled as a specification rather than hardware emulation.
- Absolute, relative, and componentwise error definitions when used by later statements.
- The precise prose claim that relative error is invariant under nonzero common scaling.
- Precise mixed forward-backward error equations.
- Concrete Taylor expansions and condition-number formulas with explicit assumptions.
- The symbolic cancellation error inequality for perturbed `a` and `b`.
- The general quadratic formula, subject to the proper side conditions.
- General sample mean and variance formulas and their exact algebraic equivalence.
- Relative residual and the stated lemma identifying it with a normwise backward error.
- The `ε`-parameterized LU/pivoting example, because it is symbolic rather than one machine run.
- A standard exact series identity when it is useful and already available or reasonably reusable.
- A precise numbered error relation such as the displayed roundoff equation in the `expm1` discussion.
- The basic definition of QR factorization.
- Exact symbolic equations in the upper-Hessenberg analysis.
- Theoretical exercises that ask for proofs or explicit bounds.

## Skip in core mode

- Letter-shape and MATLAB notation conventions.
- Historical single- and double-precision values tied to particular machines.
- A glossary implementation of significant digits when no theorem needs it.
- Fixed decimal examples comparing significant digits.
- Figures illustrating forward/backward error.
- MATLAB, Fortran, and calculator experiments.
- Fixed numerical vectors and matrices together with observed outputs.
- Claims such as "accuracy can be much worse", "the error typically increases", "virtually constant", or "almost entirely" without a quantified conclusion.
- Design advice, misconception lists, anecdotes, historical notes, and literature review.
- Tables and plots of computed values.
- Calculator-oriented exercises.

## Defer

- Full QR stability analysis used as educational foreshadowing before the later chapter that proves it. Formalize the QR definition now if needed; formalize the stability theorem at its proper treatment.
- Earlier prose that points directly to a later precise theorem.

## Mark as benchmark candidates

- GEPP versus Cramer's rule or similar explicit method comparisons. In core chapter mode, skip the empirical table; in benchmark mode, reuse or formalize the algorithms and theorem-level correctness/stability claims.

# Anti-patterns

Never do the following:

- Formalize every noun or terminology sentence "just in case".
- Recreate the book's notation as a parallel API when Mathlib already has the concept.
- Build a simulator for a historical calculator to explain one table.
- Treat every displayed formula as a theorem without checking its role.
- Skip a precise prose theorem because it is not numbered.
- Convert "almost" or "much worse" into an arbitrary epsilon statement.
- Use a future theorem as an unproved hypothesis and call the result end-to-end.
- Add `sorry`, `admit`, or a new `axiom` to satisfy the compiler.
- Reprove a standard result before searching the repository and Mathlib.
- Mix editions or copy equation labels from the wrong edition.
- Ignore the difference between one-based book indices and Lean indices.
- Choose a norm, tie-breaking rule, rounding mode, or zero-denominator convention without source or project support.
- Spend the core pass on benchmark infrastructure unless benchmark mode was requested.
- Claim the chapter is complete without an inventory accounting for skipped and deferred items.
- Close a high-probability theorem by assuming its concentration event.
- Close a chapter-level result with only a conditional transfer, expectation theorem, deterministic subcase, or different algorithmic object.
- Present a generic perturbation certificate as the final implementation-facing floating-point theorem without instantiating the computed path.
- Hide an exact-operation convention for a quantity the algorithm computes.
- Add adjacent lemmas after the same bottleneck has repeated without showing that they close a listed dependency.
- Let a source or not-proved row disappear because a related but weaker theorem was proved.
- Polish a PDF or README while a required foundation remains open and the documentation work does not record or close that blocker.
- Describe a theorem in prose more strongly than its Lean type.

# Handling ambiguity and blockers

Do not ask broad questions that the chapter or repository can answer. Continue all unambiguous work.

Ask a targeted clarification when:

- the edition changes the statement;
- the source formula is unreadable after inspecting the rendered page;
- two non-equivalent formalizations are both plausible;
- the repository has conflicting conventions; or
- a requested scope mode is genuinely unclear and would multiply the work substantially.

When blocked by a missing deep dependency:

1. record the exact selected target and dependency;
2. search the repository and Mathlib again with alternate terminology;
3. inspect the book's proof, citation, and later cross-reference;
4. run proof-source acquisition when the source is incomplete;
5. update the feasibility table and choose a local, shared-module, later-chapter, or route-choice disposition;
6. make the smallest meaningful missing dependency the next Lean target;
7. complete independent selected targets without hiding the blocker; and
8. report the blocker precisely.

If the same blocker survives repeated passes, create the bottleneck ledger and obey the red-bottleneck protocol. Ask the user only for a genuine mathematical choice that changes the theorem, not for questions answerable from the source or repository.

# Completion checklist

Before finishing, verify every box:

## Source and scope

- [ ] Exact edition verified and recorded.
- [ ] Entire chapter read, including exercises and footnotes affecting assumptions.
- [ ] Every named result inventoried.
- [ ] Every numbered equation inventoried.
- [ ] Every exercise and subpart classified.
- [ ] Core/comprehensive/benchmark mode recorded.
- [ ] `HIGHAM_PARALLEL_FORMALIZATION_BLUEPRINT.md` was read first, the assigned split's section of `split_primary_contracts.md` was read, and `chapter_index.md` was used as the lookup table.
- [ ] The implementation and any cross-split placeholders respect the assigned split's ownership and the shared merge protocol.
- [ ] Source proof status recorded for selected imported or nontrivial claims.
- [ ] Algorithms and experiments split into formalizable subclaims, computed quantities, analysis-only objects, and empirical outputs when relevant.

## Selection quality

- [ ] Precise prose claims were considered, not ignored.
- [ ] Empirical and machine-specific material was excluded from core scope.
- [ ] Qualitative claims were not turned into invented theorems.
- [ ] Terminology-only material was skipped unless needed.
- [ ] Symbolic examples and fixed numerical examples were distinguished.
- [ ] Cross-chapter foreshadowing was identified.
- [ ] Benchmark candidates were separated from core work.

## Library and architecture

- [ ] Repository and Mathlib searched before new definitions or proofs.
- [ ] Existing declarations reused where appropriate.
- [ ] No duplicate parallel API was introduced without justification.
- [ ] Dependency graph is acyclic and matches the chapter boundary.
- [ ] Source labels and index translations are correct.
- [ ] Foundation feasibility gate completed for hard selected targets.
- [ ] External proof sources and route choices recorded when local foundations were missing.
- [ ] Public repository navigation updated only where required.

## Proof quality

- [ ] All selected declarations compile.
- [ ] No `sorry`, `admit`, or new global `axiom` remains.
- [ ] No target or equivalent missing theorem is smuggled in as a hypothesis.
- [ ] Necessary domain and nonzero assumptions are explicit.
- [ ] Statements preserve the source's meaning.
- [ ] Proofs are maintainable and use existing library results.
- [ ] `#print axioms` checked for final selected theorems when practical.
- [ ] High-probability claims prove the event probability rather than assume it.
- [ ] Implementation-facing floating-point claims account for all modeled computed quantities and rounded operations.
- [ ] Exact, simplified, and asymptotic bound descriptions agree and are non-vacuous when such descriptions are present.
- [ ] No weaker subtheorem or conditional transfer is mislabeled as closing a stronger source claim.

## Reporting

- [ ] Completed targets listed with Lean names and files.
- [ ] Reused results listed.
- [ ] Skipped items have reason codes.
- [ ] Deferred items name their dependency or destination.
- [ ] Benchmark candidates listed separately.
- [ ] Verification commands and results recorded.
- [ ] Genuine ambiguities or blockers reported honestly.
- [ ] Open selected-scope items remain in the not-proved ledger.
- [ ] Proof-source and bottleneck ledgers are present when triggered.
- [ ] Hidden hypotheses were classified and suspicious artifacts resolved or reported.
- [ ] Weak components received two consecutive clean checks.
- [ ] Empirical source outputs record missing machine details and any replacement theorem.
- [ ] Optional theorem PDF or note, if generated, matches Lean and was textually and visually inspected.

# Expected final response to the user

After modifying the repository, respond with:

1. a short statement of what was formalized in the selected mode;
2. the main Lean theorem or corollary names;
3. the files changed;
4. the build, test, placeholder-scan, and relevant axiom-check results;
5. the most important skipped, empirical, deferred, and benchmark categories;
6. the status of open selected-scope rows and any active bottleneck;
7. a concise hidden-hypothesis and weak-component summary when relevant;
8. the external proof sources used and whether each was formalized, advisory, rejected, or still open when proof-source acquisition was triggered; and
9. a link or path to the chapter decision report and any generated theorem note or PDF.

Keep the response concise when the report contains the detail. Do not claim full chapter coverage if a selected target remains unproved, and do not treat correctly classified empirical output as an unproved mathematical theorem.
