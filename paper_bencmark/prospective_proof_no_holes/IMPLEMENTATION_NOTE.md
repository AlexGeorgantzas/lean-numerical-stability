# Prospective proof-stage clarification

The active Pilot 29/31 prompt is hash-frozen and must not be changed. It
already says that the checker rejects `sorry` and `admit`, but its closing
instruction to leave a "best honest attempt" can reasonably lead a model to
finish a turn with the existing target `sorry`. The controller then freezes
`Candidate.lean` after **every** timed turn, whether or not the model claims
it is submitting a proof. The current validator correctly rejects such a
file before compilation, yet records it as a failed proof attempt.

For a future pilot, use `PROOF_PROMPT.md` only with a new frozen prompt hash
and pilot identity. To make the "no proof holes in submitted proofs" rule
operational rather than merely exhortative, the controller should distinguish
three events after a timed turn: (1) a zero-hole candidate eligible for Lean
validation, (2) an explicit `NO_COMPLETE_PROOF` abstention, and (3) an invalid
attempt containing a hole or forbidden construct. Freeze and meter all three;
accept only (1) after compilation and semantic-hash preservation. Neither
(2) nor (3) is a proved result. The handling of an abstention and the attempt
budget must be fixed prospectively, before any measured task in that pilot.

This clarification cannot convert an unproved or false statement into a
proof. Review counterexample claims separately; do not retroactively revise
active pilot results or reuse their partial candidates in a fresh condition.
