# Formalization benchmark recovery dispositions

This directory records study-level dispositions outside the hash-frozen pilot
release and run tree. It never changes a pair controller's terminal state. The
benchmark owner adopted the P01-T2 disposition on 2026-09-16, **after** the
infrastructure incident and recovery-audit verdict were known. It is therefore
a disclosed post-hoc amendment, not an original-protocol `COMPLETE` result.

## Audited infrastructure recovery rule

Eligibility is determined without regard to the later audit verdict and applies
symmetrically to conditions N and L:

1. A candidate and its active-time, token, and candidate-freeze records were
   frozen and authenticated before the failure; those measurements are complete.
2. Compilation and proof-integrity validation passed. The sole failure was in
   off-clock audit preparation or audit infrastructure, before a faithfulness
   verdict or repair feedback reached the formalizer.
3. The corrective change is narrowly identified and hashed. The exact frozen
   candidate, paper, task packet, formalizer environment, and original
   measurements are reused. No formalizer turn or repair is rerun.
4. Fresh condition-blind auditors evaluate the exact candidate under the
   unchanged audit prompts, schemas, model, and reasoning effort. The corrected
   dossier must pass provenance-blinding checks. Audit work stays off-clock.
5. A faithful verdict, together with an accepted verdict for the other
   condition, yields `RECOVERED_COMPLETE` for study reporting. A rejection,
   unclear verdict, or audit-system incident does not. The original pair's
   terminal status and hashes remain visible in every case.

`RECOVERED_COMPLETE` is an explicit study-level classification, not a rewrite
of the pilot controller's `PAIR_INCIDENT` or a claim that the frozen protocol
anticipated this recovery. Analyses that strictly follow the original pilot-5
protocol should exclude recovered pairs; amended or sensitivity analyses may
include them with this flag. This case-specific decision does not silently
authorize the same procedure for future incidents; a prospective rule should
be frozen before their recovery verdicts are observed.

The machine-readable P01-T2 decision is in `P01-T2-pilot-5.json`. Its referenced
Titan addendum and audit decision contain the full code, prompt/schema,
hardware, and auditor evidence manifests.
