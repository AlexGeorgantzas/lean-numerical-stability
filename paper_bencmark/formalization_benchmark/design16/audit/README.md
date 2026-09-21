# Design-16 development faithfulness screen

This directory defines a **cheap development gate**, not a scientific
faithfulness audit. It uses one fresh, stateless, condition-blind judge over the
authoritative PDF, a condition-neutral source packet, and the pseudonymized
semantic closure of one compiled candidate.

The screen intentionally retains the depth checks most likely to prevent false
passes:

- exactly one record for every reached dependency;
- all sixteen numerical semantic checks;
- both implication directions;
- explicit full-domain, extra-assumption, and nonvacuity accounting;
- binary fail-closed output;
- stronger-than-source acceptance only for genuine, full-domain strength;
- no partial-domain pass.

It is cheaper because it omits the independent source-contract extractor,
blind translator, independent round-trip judge, and conditional adjudicator.
It therefore cannot establish scientific inclusion. A candidate that passes
this screen must still undergo the complete multi-role audit before it can be
reported as a benchmark success. A screen failure is a development rejection,
not a replacement for a final audit classification.
