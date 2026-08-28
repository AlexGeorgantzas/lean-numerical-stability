# T4 private solvability

Read this reference completely before constructing or revalidating private T4
solutions on the exact current controlled surface. The common preparation and
invariants in `../SKILL.md` still apply. Read
[T4 corpus construction](t4-construction.md) too only if statements, mappings,
imports, or controlled semantic definitions may change.

Private solvability is a mandatory pre-review gate, not a substitute for the
controlled placeholder corpus. The controlled target retains its enumerated
proof holes for measured agents. Separately construct proof-complete private N
and L solutions for the exact same current statements, imports, and controlled
semantic-dependency bytes. Validate both conditions before any faithfulness
review or measurement campaign begins.

## Use the smallest valid pre-review gate

For trusted paper-local proof files produced during extraction, the complete
pre-review gate is:

1. hash the exact current target, paper definitions, imports, and private N/L
   files;
2. check that every designated public hole is replaced exactly once in each
   private file, while controlled statements, imports, and semantic
   dependencies remain identical;
3. compile N and L separately with the pinned Lean toolchain and package paths,
   with no NumStability artifact available to N and the frozen evaluated
   library available only to L; and
4. record the hashes, toolchain and condition identity, obligation counts,
   dependency results, commands or command identity, exit status, and time in a
   short paper-local non-revealing record.

A normal direct Lean invocation is sufficient. The record may be a small
paper-local JSON result or an existing simple gate file; no dedicated recorder,
registry finalizer, locked workspace, Bubblewrap namespace, seccomp launcher,
network filter, or authenticated construction receipt is required to establish
solvability or to begin faithfulness review. Never claim that isolation was
used when it was not, and never put private proof text or compiler output that
reveals a proof into public metadata or reviewer packets.

This direct path is for the trusted extraction artifacts being checked. Code
from an unknown measured benchmark agent is a different stage and may require
the authorized isolated measurement runner. Do not import that measurement
security machinery into ordinary private-proof construction.

Replace every designated benchmark `sorry`; permit no remaining `sorry`,
`admit`, new axiom, `unsafe` bypass, extra premise, changed statement, or
condition-specific change to the controlled surface. Proof-local helper lemmas
are allowed only inside the private solution and must themselves be proved from
that condition's available environment. N has no NumStability artifact; L alone
has the frozen evaluated library.

The hashes bind one check to one exact snapshot; they do not permanently freeze
the task. If the target, imports, or controlled definitions change, edit them
normally and rerun this direct gate. If a later measurement-ready registration
tool cannot start because the host lacks an isolation permission, preserve the
passing direct result and continue faithfulness review. Report only the final
measurement-ready registration as pending. Do not create a host-specific
Bubblewrap or seccomp fallback, weaken arguments, move stale receipts, or edit
shared registry/checker code merely to turn that infrastructure failure into a
construction pass.

Keep private proof source and compiled proof artifacts outside every controlled
task, trusted paper bundle, review packet, agent prompt, and public metadata
field that could reveal a solution. A statement, import, or controlled semantic
definition change invalidates both private-solvability records; rebuild N and L
for the revised bytes before review resumes.

If proof construction exposes a false, underspecified, or mistranslated claim,
return to the source and construction workflow. Never weaken the source claim
or enrich the controlled environment merely to make a private proof easier.
