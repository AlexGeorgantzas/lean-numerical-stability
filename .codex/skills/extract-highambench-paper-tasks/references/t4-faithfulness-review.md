# T4 claim-scoped source-faithfulness review

Read this reference completely only when a T4 corpus is ready for independent
review. Do not start this protocol until the placeholder corpus and the private
N and L solutions required by
[T4 private solvability](t4-private-solvability.md) pass for exactly the same
statement, import, and semantic-dependency hashes. Load that proof procedure
only when constructing or revalidating the solutions; otherwise check its
recorded non-revealing gate evidence. The direct exact-byte N/L record defined
there is sufficient to start review; a locked construction-runner receipt or
measurement-ready registration is not a precondition. Never disclose private
solutions or proof-derived hints to a reviewer.

## Enter final review only after construction stabilizes

Do not use a durable campaign as an iterative construction scratchpad. While
the inventory, definitions, statements, mappings, or private proofs are still
changing, keep editing the paper-owned files and use direct local audits or
disposable packet previews. Do not create an immutable campaign directory,
campaign plan, or accepted review record for those drafts.

Start a durable review attempt only after one complete candidate has passed
the exact-byte N/L gate. The packets for that launched attempt remain immutable
so its verdicts can be traced to the bytes the reviewers actually saw. This is
not a lock on the paper: if review exposes a problem, return to mutable
construction, batch and validate the repairs, and then create a new attempt.
Never rewrite or "unfreeze" the previous attempt.

## Build immutable review units and packets

Create one review unit for each atomic included source claim, coalescing
multiple source items only for a true duplicate or restatement with identical
semantics. A unit contains exactly its recorded primary carrier or smallest
necessary declaration group, including central algorithm definitions;
semantic-context declarations appear only in the Lean packet's transitive
closure. Controlled overlap between units is permitted only for explicitly
recorded carrier reuse. Judge statement and definition semantics, never the
placeholder or a possible proof.

For each unit in a launched final-review attempt, make immutable source and
Lean packets with per-declaration records. The source packet contains the exact
claim, enough surrounding text and formula images to recover scoped notation
and assumptions, exact PDF/printed page, section and anchor, and the paper
hash. The Lean packet contains the declaration group with its proofs erased
plus the transitive closure of every custom definition, structure invariant,
notation, coercion, and constant needed to interpret it. Hash the packets. Keep
long copyrighted text private; public records may retain the PDF locator,
anchors, and packet hashes.

Here immutable means “never rewrite this attempt's packet.” It does not freeze
construction: a semantic correction creates a newly hashed attempt after fresh
direct N/L checks.

Use the prompt, authorization, and durable-artifact contracts hash-bound by the
paper's generic workspace descriptor. Render paper-specific role prompts and
packets into a new immutable campaign directory; do not rewrite the role
protocol from memory or copy a prior paper's rendered campaign.

The isolation rules below apply to external semantic-review roles, not to the
trusted private N/L compile. Use the already supported sealed packet interface
and the minimum controls needed to enforce role blindness. Do not create a
paper-specific host sandbox or Bubblewrap/seccomp fallback merely to launch a
review role. If the authorized review runtime itself is unavailable, retain
the finished construction and direct proof result and report review as pending.

## Seal freshness, blindness, tools, and delegation separately

Do not use "fresh context" as shorthand for disabling all capabilities. Seal
and hash four independent runtime requirements so that each can be audited
without weakening the others:

1. **Conversation freshness.** Use a newly spawned clean-context agent for
   every role, review unit, and attempt. A production role starts as a new root
   with no parent, resume, fork, inherited conversation, or prior turns. Prefer
   an ephemeral root when the selected runtime supports the sealed delegation
   and packet-tool contract from such a root. If the pinned runtime requires a
   stored parent rollout for a full-history child to inherit packet-local tools,
   use a non-ephemeral root only inside a new, empty, per-role temporary Codex
   home; authenticate that the home contained no prior thread, export no raw
   rollout into campaign artifacts, and delete the temporary home after the
   role tree. This storage choice does not permit conversation reuse. Do not
   substitute an empty-history fork for the top-level role. Never reuse the
   extractor, reviser, a prior judge, or an adjudicator.
2. **Role blindness.** Supply exactly the role-visible immutable packet
   components listed below. No role may access the host repository, full PDF,
   private proofs or proof-derived hints, web, undeclared files, or artifacts
   from a prior attempt. Current-attempt verdicts are visible only to the
   Adjudicator. A clean conversation does not by itself establish this data
   boundary.
3. **Packet-local tools.** Useful tools may operate only on packet bytes already
   visible to that role. The dynamic utility set is exactly in-memory literal
   `review.search_packet` and bounded non-executing exact-arithmetic
   `review.calculate`. Across the root/child tree allow at most 12 utility calls.
   Bound search queries to 512 UTF-8 bytes, results to 12, surrounding context
   to 512 UTF-8 bytes per match (with matched text separately bounded to 512),
   and canonical search results to 16384 bytes. Bound calculator expressions to
   512 UTF-8 bytes and canonical results to 4096 bytes. Do not expose a
   shell, filesystem, repository search, arbitrary code execution, network,
   browser, environment, process, or unrestricted tool broker. If the selected
   model requires the isolated code-mode wrapper, disclose it explicitly and
   authenticate its exact nested registry. It must be a fresh V8 isolate with
   no Node, host filesystem, network, process, or console access; native
   collaboration remains governed separately by the bounded-delegation
   contract. Seal the wrapper's companion executable, require its local stdio
   transport, and forbid websocket or gRPC listeners. Configure the pinned
   runtime so the nested wrapper contains only the two review utilities:
   exclude both the default `functions` namespace and the `skills` namespace;
   disable request-user-input, update-plan, orchestrator-skill, and
   orchestrator-MCP surfaces; give collaboration a separately named direct-only
   namespace; disable host fallback; and make tool-name collisions fail closed.
   Explicitly suppress automatic skill instructions and bundled skills, project
   document discovery, generic primary/subagent usage hints, and the generic
   multi-agent-mode hint. Do not assume that disabling app, environment, or
   collaboration-mode instruction blocks also suppresses those independent
   prompt channels. Authenticate the normalized provider request shape: its
   only model-visible natural-language channels are the sealed tool
   descriptions, the frozen role instructions, and the role packet. Reject any
   other developer/user context or any host path.
   If the wrapper still advertises its same-cell `wait` control, deny it before
   dispatch and reject it in the event audit; explicitly forbid `yield_control`
   in every role prompt. Set the wrapper's automatic-yield threshold strictly
   above the sealed maximum root-session deadline, and authenticate both values.
   Start from an
   isolated state directory with no ambient MCP, plugin, app, or user config.
   Before any model thread, read the initialized runtime's effective config with
   layer information and require the sealed feature, model, reasoning, sandbox,
   history, agent-bound, instruction, and empty external-capability projection.
   Reject unexpected managed, project, or other nonempty configuration layers
   and require every security-critical leaf to originate in sealed session
   flags. Persist only hashes and normalized nonsecret attestations, never the
   raw effective configuration or origin data. Before starting any model
   thread, query the initialized runtime's paginated
   effective MCP-server status and require the first and only response page to
   contain exactly no servers and no continuation cursor. Bind the request
   contract and empty response hash into runtime provenance so managed or system
   configuration cannot silently add another tool namespace.
   Seal the provider wire surface and app-server canonical collaboration-event
   surface independently; do not claim a one-to-one mapping unless the pinned
   runtime has demonstrated it. Permit only provider `spawn_agent` and
   `wait_agent`, and only app-server `spawnAgent` and `wait`; deny every other
   advertised or fail-safe collaboration action before dispatch where possible
   and reject any such observable event. Authenticate the exact provider tool
   schemas, a finite call budget shared across the root/child
   tree, output limits, role scope, and a compact audit containing call
   identifiers and input/output hashes rather than hidden reasoning.
   Seal the exact tool implementation hash before and after every root-tree
   session. Hash each role's exact ordered searchable-section list and the
   canonical dynamic-tool specifications derived from it; the canary receives
   only its synthetic canary section.
   For source-crop images, never use a local-path attachment form: some runtimes
   expose that absolute path in a model-visible image wrapper. Read and hash the
   authorized PNG in the runner, construct an in-memory
   `data:image/png;base64,...` image input, request original detail, and require
   that the provider-bound data URL decodes to the authenticated source bytes
   without a path field or path-bearing text. Blind and canary roles remain
   text-only.
4. **Bounded Ultra delegation.** When the authorized campaign specifies Ultra,
   pass literal Ultra reasoning to every semantic role session. If the pinned
   Codex runtime translates its Ultra product setting to another provider-wire
   effort spelling, authenticate and disclose that exact translation rather
   than claiming that the provider receives the literal string. A top-level
   role root may make at most one native Codex `spawn_agent` attempt in its
   entire root tree. Enforce that counter before child creation with an audited,
   fail-closed `PreToolUse` hook; a prompt instruction or concurrency cap alone
   is insufficient. Fix maximum tree depth at one and maximum root-plus-child
   concurrency at two. Omit `fork_turns` (the default `all`) or set it exactly to
   `all`; deny `none` and positive turn counts so the child inherits the current
   sealed role attempt. Use a fixed, source-independent child task name and cap
   the child message at 16384 UTF-8 bytes. The spawn supplies no model or
   reasoning-effort override, so the new child thread inherits literal Ultra. It is not an independent
   judge: it has the same semantic role, no more than the root's packet and
   capabilities, no grandchildren, and no follow-up or resumed work turn. The
   clean-context requirement applies to the top-level role session. The child's
   one initial response is advisory; the root alone returns the required role
   JSON. The same `PreToolUse` guard must deny native `sendInput`, `resumeAgent`,
   `sendMessage`, `followupTask`, `interruptAgent`, and `listAgents` work or
   control actions before dispatch. Only passive `wait_agent`/`wait` may follow
   the spawn; cap it at four complete action lifecycles per root tree, constrain
   every explicit timeout to an integer in the authenticated runtime range, bind
   the maximum root-session deadline, and reject any blocked or excess action in
   the event audit. Do not permit `closeAgent`; session teardown belongs to the
   runtime orchestrator after the root turn has been validated.
   Record hook decisions and the spawn counter, authenticated model/reasoning
   settings, parent/child role and attempt identifiers, packet/capability-scope
   hashes, and advisory-output hash.

Honor the authorized speed mode independently of reasoning effort. For a
Standard profile, use the runtime's Standard/default service tier and reject a
Fast, Priority, or other accelerated tier. Apply literal Ultra to every role,
including both canaries and any Adjudicator, subject only to an authenticated
and disclosed provider-wire translation.

Authenticate a standalone preflight canary before campaign execution and an
internal canary before any semantic transmission. Each is a fresh root using
the same provider, model, literal Ultra, and packet tools; it sees no semantic
packet, calls the calculator at the root, and must produce exactly one child
that calls packet search. Run the two distinct canary roots in the same
authorized campaign checkpoint and overall ledger, with the standalone
preflight first and the internal canary immediately before semantic roots. This
lets the ledger enforce identity uniqueness without importing a reusable
cross-run receipt. Semantic roots may produce zero or one child. Before every
root process launch, durably reserve its one possible child and resolve that
reservation as observed, unused, or unknown after a crash. Count every root
launch and reservation, including canaries and retries, against the disclosed
worst-case bound. Persist validated root JSON, hashes, counts, and sanitized
status codes only—never hidden reasoning, raw app-server streams, tool payloads,
child advice, spawn prompts, hook feedback, account state, or prior conversation.

Fail closed on any undeclared access, tool, server request, undeclared inherited context,
recursive delegation, child work action, scope expansion, or audit mismatch. Before launch,
disclose the sealed policies, model/reasoning settings, tool capabilities,
the exact packet-tool implementation hash, packet contents, and worst-case
top-level and delegated session counts; obtain
authorization for those exact hashes. A packet-policy reseal requires renewed
authorization even when the controlled semantic bytes and private N/L gate are
unchanged.

A valid standing authorization may replace a repeated authorization question
only when its recorded paper/campaign scope, replacement flag, provider,
account, model, Ultra/Standard profile, transmitted artifact classes,
role-isolation and packet-tool policy, and all session ceilings cover the new
plan. Still disclose and bind each new manifest and campaign-plan hash before
launch. If the standing scope covers the launch, proceed without stopping for
another confirmation; otherwise obtain authorization for the changed scope.

For `U` included units, authorized per-role attempt cap `A`, and infrastructure
retry cap `R` in `0..3`, disclose at most `2 + 4*U*A` logical roots overall
(standalone canary, internal canary, and four possible semantic roles),
`(2 + 4*U*A)*(R + 1)` root launches and child reservations, and twice that
last quantity for the combined root-plus-child session ceiling. Also bind the
planned concurrent-root cap; for this campaign it is at most eight.
Put the exact paper-local candidate manifest, all-unit selection,
attempt/retry/concurrency bounds, model, provider, Ultra settings, service tier,
Codex binary, runner, packet tool, policy hashes, maximum root-session deadline,
and computed session ceilings in one canonical campaign-plan
object. Obtain authorization for its SHA-256 and make the runner require that
expected hash before any root launch.

## Run the semantic roles

1. **Direct Judge.** Give only the source and Lean packets, without extractor
   rationale, intended paraphrase, proof sketch, or prior verdict. Compare the
   definitions and intended objects, domains and quantifiers, assumptions and
   side conditions, constants and indices, algorithm/problem semantics, and
   conclusion. Return a structured score, tag, concise evidence, and every
   material discrepancy.
2. **Blind Translator.** Give a fresh agent only a sanitized Lean packet: no
   source text, paper metadata, source-oriented comments or identifiers,
   `context.md`, intended paraphrase, or verdict. It produces and locks a
   literal natural-language reconstruction containing all quantifiers,
   hypotheses, definitions, edge conditions, and the conclusion. It never sees
   the source and does not score.
3. **Round-Trip Judge.** Give a third fresh agent only the source packet and the
   locked reconstruction, not the Lean code or Direct verdict. It compares
   their mathematical content, not prose style, and returns the same structured
   score, tag, evidence, and discrepancies.

## Apply the score and adjudication contract

- `3 / faithful-equivalent`: all material content is preserved with the same
  mathematical meaning. Definitional, notational, syntactic, and other benign
  semantics-preserving representation changes belong here too.
- `4 / faithful-stronger`: over the same intended objects and semantics, the
  Lean statement entails the source claim and genuinely states more. Extra
  assumptions, a narrowed domain, altered constants, or a weaker conclusion
  are not strengthening.
- Scores `0`--`2` fail. Any tag other than `faithful-equivalent` or
  `faithful-stronger` is nonpassing and must identify the mismatch or an
  unreviewable packet.

A verdict passes exactly when it is `3 / faithful-equivalent` or
`4 / faithful-stronger`. These are the only passing score/tag pairs. Without
disagreement, accept only when both judges pass and give the same tag; different
numeric scores alone do not trigger adjudication.
Any tag disagreement or pass/fail disagreement invokes a new clean-context
Adjudicator, even when both raw scores fail. Give it both packets, the locked
reconstruction, and both verdicts. It resolves the semantic issue rather than
averaging scores and returns the controlling final score, tag, and evidence;
accept only if that verdict passes. Same-tag dual failure proceeds directly to
revision.

If both judges agree on failure or the adjudicated verdict fails, revise the
Lean declaration or its semantic definitions, recompile the placeholder target
and proof-complete private solutions in N and L, regenerate the packets, and
rerun the entire protocol with new agents. Any changed statement, import, or
transitive controlled semantic-dependency byte invalidates every dependent
declaration's review and private-solvability evidence in this paper. The
paper-owned closure must prevent that change from invalidating another paper.
Preserve the immutable history, but never reveal prior attempts to new judges.
If only a packet or procedural constraint was defective, repair it and rerun
fresh rather than pretending the Lean statement changed.

## Record non-leaking evidence

Record outside controlled run prompts: source-item, review-unit, and declaration
IDs; mapping roles and smallest-group/reuse rationale; packet and output hashes,
source anchors, exact Lean semantic closure, N/L placeholder compile results,
private N/L solvability-validation hashes and results without proof content,
revision number, role prompt version, agent/model identifier, fresh-context and
blindness attestations, both verdicts, locked reconstruction, any adjudication,
discrepancy/revision notes, and final status. Record concise verdict evidence,
not hidden chain-of-thought.

Keep every candidate, campaign plan, checkpoint, immutable attempt history, and
final review record below the selected paper's owned review root. Never use a
mutable corpus-wide campaign ledger or output directory.

Follow the workspace-bound
`templates/T4/review/durable-artifact-policy.v1.md`: persist and hash the exact
versioned prompts, packets, manifests, plans, resumable checkpoints, validated
final role JSON, provenance, and semantic repair ledger. These—not hidden
chain-of-thought, raw conversational transcripts, raw event streams, or child
advice—are the reusable state from which a fresh session or later paper should
resume.
