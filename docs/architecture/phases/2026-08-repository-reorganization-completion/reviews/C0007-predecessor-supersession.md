# C0007 predecessor-phase supersession review

Decision time: `2026-08-25T15:18:24Z`

Authority and reviewer: `primary-human`, recorded under the repository owner's
explicit authorization to complete the reorganization closeout work.

The retained phase
`repository-reorganization-2026-08` is effectively superseded by
`repository-reorganization-completion-2026-08`. The explicit active-phase
pointer already selects the successor at
`docs/architecture/phases/2026-08-repository-reorganization-completion`.

The predecessor's `phase.json` remains immutable historical evidence. Its
preserved SHA-256 is
`7E19F798C3B14E44F8765CF72E31CE8C47BC6D4862A528305FA7D61E9FB2ECA2`;
the original `active` field is not rewritten. The adjacent
`supersession.json` supplies the effective terminal status and hash-pins this
review. Accepted checkpoints, gate reports, requests, projections, branch
records, and baselines remain unchanged.

The phase checker must accept the override only while all of these facts hold:

- the preserved predecessor hash matches;
- this review exists with the recorded digest;
- the successor id and path resolve to a retained phase;
- the reviewer is a principal in the successor authority;
- the successor chain is acyclic and terminates at the sole effective active
  phase; and
- the active-phase pointer selects that sole active phase.

This decision reconciles operating status only. It does not assert bounded or
repository-wide completion, accept a new checkpoint, or alter compatibility
and public-import obligations.
