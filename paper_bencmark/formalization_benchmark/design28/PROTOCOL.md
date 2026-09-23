# Pilot 28 proof-controller repair canary

Pilot 28 is a **new exploratory pilot**, not a continuation or repair of
Pilot 27's measured data. It uses the same three source tasks, source PDFs,
NumStability snapshot, condition prompts, task-neutral warm L root, models,
hardware lanes, audit rubric, time/token limits, and no-automatic-retrieval
policy as the frozen Pilot 27 protocol. The corpus identity and measured
controller commit are new and are pinned in the Pilot 28 campaign journal.

The only intended implementation changes are:

1. Create private validation and semantic-dossier scratch directories before
   off-clock checking of each frozen proof submission. Pilot 27 omitted these
   directories and therefore misclassified its first N proof candidate as a
   validation infrastructure incident without ever compiling it.
2. Surface a proof infrastructure fault as `PAIR_PROOF_INCIDENT` and pause the
   campaign instead of allowing later measured tasks to launch on the strength
   of statement faithfulness alone. Statement-only comparisons remain visible
   but cannot be interpreted as proof-required pair effects.

The first pair must again run alone and pause for review. No Pilot 27
formalizer conversation, candidate, proof, or audit feedback enters either
Pilot 28 contestant. The same immutable Pilot 27 artifacts remain reportable
as an infrastructure-incident pilot; they must not be silently erased or
pooled with Pilot 28. A full campaign of 10–15 tasks requires a separately
frozen corpus and the strict source/overlap gate; this three-task canary is
not a substitute for one.
