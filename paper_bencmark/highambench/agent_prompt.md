# HighamBench proof task

You are given an informal statement, a short paper-proof explanation, a fixed
Lean theorem, and shared Lean definitions.  Your only job is to construct a
Lean proof of the fixed theorem.

The complete context and fixed target are appended below.  Read-only copies of
them and `HighamBench/Definitions.lean` are also below the `task/` directory;
use `find task -type f` if you want their paths.  Create a new file named
`Submission.lean` in the workspace root.  Copy the import, namespace, theorem
name, arguments, assumptions, and conclusion from the fixed target exactly.
Replace only the proof that starts after `-- PROOF_START`.  You may put proved
local helper lemmas in `Submission.lean` before the target theorem.

The fixed wall-clock limit is 900 seconds.  The fixed model limit is 120,000
input-plus-output tokens, with cached input counted as input.  Stop as soon as
`lean Submission.lean` succeeds.

Rules:

- Do not change `Target.lean`, `context.md`, or `HighamBench/Definitions.lean`.
- Do not use `sorry`, `admit`, `sorryAx`, a new `axiom` or `constant`, `unsafe`,
  `opaque`, or any device that avoids Lean's proof checker.
- Do not import a hidden answer or any file outside the mounted workspace and
  locally mounted libraries.
- Do not use the internet or attempt any network request.
- You may inspect and search local files with normal shell tools.
- You may import and use a locally mounted formal library if one is present.
- The final response should be brief; the checked `Submission.lean` file is the
  submission.

The validator will rebuild the file in a fresh hidden copy, confirm that the
fixed statement is unchanged, reject forbidden shortcuts, and inspect the
proof's actual declaration dependencies.
