# P01-T4 task context

Complete every controlled proof hole in `Target.lean` at its uniquely identified
`-- PROOF_START P01-D…` placeholder. The file is a whole-paper statement
corpus for Nicholas J. Higham's *The Accuracy of Floating Point Summation*;
it is one benchmark task with multiple required declarations, not a choice of
independent subtasks.

Keep every declaration name, type, definition, assumption, and source-status
record unchanged, including the declaration order and every controlled marker.
A submission must replace all and only the controlled `sorry` terms. It may
add imports available in the assigned condition and fully proved local helper
declarations in `Candidate.lean`, but only outside the fixed controlled
declaration surface. It may not leave or add any `sorry` or `admit`, introduce
a new axiom or constant, use an `unsafe` or `opaque` bypass, or change, omit, or
reorder a controlled declaration or statement.

Condition N supplies the fixed target and its paper-scoped neutral definitions.
Condition L supplies the byte-identical files and additionally makes the frozen
condition-specific support library available. No declaration from that library
occurs in the controlled statement surface.
