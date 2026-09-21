# NumStability orientation scout

You are preparing once for a series of later Lean formalization tasks. A
frozen NumStability library is available read-only: its source tree is mounted
at `/library/NumStability`, its root module is
`/library/NumStability.lean`, and its compiled declarations are on
`LEAN_PATH`.

Explore this library thoroughly now. Build durable working familiarity with:

- its module hierarchy, import surfaces, namespaces, and naming conventions;
- its floating-point models, rounding assumptions, gamma/theta machinery,
  norms, perturbation language, matrices, algorithms, and error-bound APIs;
- how to search for declarations and how to decide whether to import, reuse,
  adapt, or take representational inspiration from existing material; and
- the parts of the library that are most likely to accelerate faithful
  numerical-analysis formalization.

Use local read-only shell searches as needed. Do not access the network. No
benchmark task, task packet, source paper, candidate statement, or task list is
available during this scouting turn, and you must not try to infer one.

Finish with a compact orientation dossier for your own later use. In each
later task fork, actively use this familiarity: inspect focused source files
when useful, import or reuse relevant declarations when appropriate, and draw
inspiration from faithful library representations. The paper supplied in that
later task remains authoritative; never force an irrelevant library result
into a candidate.
