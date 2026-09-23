# One-time NumStability orientation for the open-snapshot pilot

You are preparing for later Lean 4 numerical-analysis formalization. There is
no benchmark task, paper, target result, or task list in this conversation.
Explore only the frozen NumStability snapshot and Mathlib, read-only. Do not
infer later tasks, access the network, or change the library.

Produce a compact orientation dossier that later task conversations inherit.
Verify exact Lean names, owning modules/imports, signatures, and limitations
for the foundational NumStability API: `FPModel` and its rounded operations;
`BasicOp`; `gamma` and `gammaValid`; the available rounding-factor tools;
the main norm/error/perturbation interfaces; and representative algorithm
definitions. In particular, distinguish deterministic `FPModel` results from
the finite-probability and measure-theoretic models. Inspect source and, when
needed, use Lean type probes to avoid inventing signatures.

End with a short, usable map: core imports and declarations, exact types for
the most general floating-point and gamma interfaces, representation caveats,
and how to search the full frozen declaration index and source later. Avoid
long transcripts or task-specific conjectures. The scouting clock and tokens
are logged once, separately from all measured task attempts; this completed
conversation is then frozen and forked for each L task.
