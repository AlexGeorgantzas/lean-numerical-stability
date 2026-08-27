# HighamBench proof task

You are given an informal statement, a short paper-proof explanation, one or
more fixed Lean declarations, and shared Lean definitions.  Your only job is
to construct Lean proofs for every controlled proof hole in the required
declarations.  A selected-result T1--T3 task normally has one required
declaration and one controlled hole; a whole-paper T4 task may have many.

The complete context and fixed target are appended below. Read-only copies of
them and the task's paper-owned Lean definition file is also below the `task/` directory;
use `find task -type f` if you want their paths.  Develop the proofs in the
scratch file `Candidate.lean`.  Retain the fixed target's imports and namespaces
and every controlled declaration's order, name, arguments, assumptions, and
conclusion exactly.  Replace all and only the proofs that start after controlled
`-- PROOF_START` markers.  You may add imports available in the assigned
condition and proved local helper declarations, but these additions must remain
outside the controlled declaration surface.

The fixed wall-clock limit is 1,800 seconds.  The fixed model limit is 5,000,000
input-plus-output tokens, with cached input counted as input.

Never create, modify, rename, or copy a file to `Submission.lean`; that path is
owned by the trusted benchmark runner.  Test the complete scratch candidate
with Lean first.  If you delegated work, the root coordinator must then wait
until every subagent is terminal, collect all useful results, and make sure no
child work or message remains pending.  Only the root coordinator may submit.
In a separate final model response, make exactly one model tool call: `exec`.
Its raw input must be exactly these two lines, including the final newline:

```javascript
// @exec: {"yield_time_ms": 2400000}
text(await tools.submit_proof({candidate_path:"Candidate.lean"}));
```

Do not add any other code, text, tool call, or action to that response.  The
yield setting is transport-only and does not extend the 1,800-second proof
deadline.  The `text` wrapper makes a rejection visible so you can repair and
make another tested submission; an accepted call ends the attempt automatically
and must remain unanswered.

Rules:

- Do not change `Target.lean`, `context.md`, or any file below
  `task/shared/HighamBench/`.
- Do not change, omit, or reorder a controlled declaration or its statement,
  and do not add or move a controlled `PROOF_START` marker.
- Do not leave or add any `sorry`, `admit`, `sorryAx`, a new `axiom` or
  `constant`, `unsafe`, `opaque`, or any device that avoids Lean's proof
  checker. Candidate-local helpers must be fully proved.
- Do not import a hidden answer or any file outside the mounted workspace and
  locally mounted libraries.
- Do not use the internet or attempt any network request.
- You may inspect and search local files with normal shell tools.
- You may import and use a locally mounted formal library if one is present.
- Submit only through `submit_proof`; a normal final message is not a submission.

The validator will rebuild the file in a fresh hidden copy, confirm that the
fixed statement is unchanged, reject forbidden shortcuts, and inspect the
proof's actual declaration dependencies.
