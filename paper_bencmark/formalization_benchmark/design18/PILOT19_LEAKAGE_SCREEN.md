# Pilot 19 pre-candidate treatment-content screen

This review was completed before any Pilot-18/19 formalizer submission. It
asks whether the frozen NumStability snapshot already supplies a selected
source result (which would turn R1 into answer retrieval), as distinct from
lower-level components. The exact source/compiled-library closure and
corrected declaration-catalog hashes are pinned in `ATLAS_RELEASE.json`; the
NumStability declaration file is SHA-256
`3731abb791ba4598176a4527c19927ed3dcce5f837333746c8ac6dc7b950f9ea`.

## Review performed

1. All twelve source packets were compared against the component inventory
   in `LIBRARY_SCREEN.md`. The selected target conclusions are probabilistic
   operation/algorithm error bounds, not deterministic `FPModel` or `gamma`
   facts. The earlier corrected-atlas name/signature co-occurrence probe
   found no declaration simultaneously naming a selected algorithm family
   and a probabilistic/concentration conclusion. This is a filter, not proof.
2. Relevant frozen NumStability algorithm source modules were inspected for
   declarations using `eventProb`, measure/independence, probability, or
   high-probability language. Summation/Tree/Core contains general tree
   evaluation, exact/computed internal sums, deterministic error bounds, and
   a statistical RMS contribution lemma, but no tree-specific tail theorem.
   The probability-bearing algorithm modules found by the source scan concern
   other topics (notably RandNLA and test matrices); a `Doolittle.lean`
   lexical hit is only a comment saying “non-probability.”
3. `Analysis/StatisticalRounding.lean` gives finite-sample-space expectation,
   second-moment, and RMS lemmas for weighted errors. It has no selected
   algorithm conclusion. `Analysis/FiniteProbability.lean` gives generic
   event, moment, MGF, and concentration inequalities, not any of the twelve
   paper-specific error events or coefficients. A contestant may use these
   as components; an auditor must reject a resulting statement that silently
   restricts the paper's probability-space domain to finite `Ω`.
4. The `HI21-2-6` source PDF was visually checked at Model 1.1, Algorithm
   2.1/Definition 2.1, and Theorem 2.6. Its general-tree domain, two failure
   parameters, exponential factor, and exact-internal-sum norm are required
   in the common packet. No matching NumStability theorem was found in the
   summation-tree modules. The original ambiguous `CASTRO24-4-1` packet was
   removed prospectively, not after a result.

## Decision and limitation

**No selected result or semantically equivalent source-specific theorem was
found in the reviewed frozen library surface.** This passes the bounded
pre-candidate content-leakage screen for Pilot 19. It is a documented expert
negative search, not a formal proof that no disguised equivalence exists in
every declaration. Every actual R1 candidate still receives a fresh semantic
dependency dossier and a blind/direct/round-trip faithfulness audit. A later
discovered target collision is a disclosed benchmark incident, not a reason
to erase or relabel an unfavorable outcome.

This screen does not assert that R1 will be faster. In particular, the library
mostly offers deterministic algorithms and a finite-probability layer,
whereas the selected sources use stochastic execution models; bridging that
gap may dominate a contestant's work. That is a legitimate possible negative
result, not a license to provide the bridge or target conclusion for free.
