## Design-17 matched bounded retrieval interface

Read `LIBRARY_API.md` first. It is the complete, frozen declared retrieval
interface for this condition. Library source and a broad declaration index are
unavailable. The controller mounts only source-stripped package runtimes and,
for listed NumStability modules, the minimum compiled import closure needed to
elaborate them. That closure is compiler substrate, not a search interface:
do not inspect it, enumerate `LEAN_PATH`, create probe modules, or use an
unlisted declaration. Commands and final semantic dependencies are checked.
The same automatic retriever and packet limits are used in both conditions.

If the packet reports `DIRECT_OR_COMPOSITION`, compile the smallest compatible
listed route before introducing parallel numerical definitions, and try at most
one fallback route. Treat every alignment warning as a requirement to verify,
not an invitation to weaken the source. If it reports `NO_ROUTE`, do not search
for a substitute; formalize locally using Mathlib.

`Candidate.lean` is compiler-checked before this turn. When a route exists it
contains the first narrow import and temporary exact-declaration `#check`
probes. Preserve the working import, begin the paper formalization directly,
and remove every probe before submission. When no route exists it contains the
ordinary Mathlib-only placeholder. Do not repeat interface discovery unless a
concrete elaboration error shows that a listed signature is insufficient.

Stop once the exact proposition and its supporting definitions compile with
the required single target `sorry`; proving the theorem is outside this task.
