# R0015 / CODE-03 planned-control review

Status: **authorized packet; implementation not applied; independent review pending**.

R0015 is the indivisible CODE-03 rollback unit authorized by
`reviews/C0007-bounded-epoch-operator-authorization.json`. The packet was
materialized in a detached worktree at the exact C0007 code checkpoint; neither
implementation path was edited in the shared worktree while this packet was
prepared.

## Base and authority

- C0007 code checkpoint: `4e26820d1f4989ec4ec77b7113085f593570e11b`.
- Authorized control head: `8960f2a980be22166f321c4ba452eb547529b1fd`.
- The two requested blobs are identical at both commits.
- Operator: `codex-local`, acting under the task-bounded authorization recorded
  by `primary-human`.
- Request issuer and later resolver: `primary-human`.
- Target checkpoint / validity boundary: C0007. Any base, patch, path, or
  postimage drift expires this request and requires a superseding packet.

## Exact two-path rollback boundary

| Path | C0007 blob | C0007 SHA-256 | Candidate SHA-256 |
|---|---|---|---|
| `NumStability/Source/Higham/Chapter19/Core.lean` | `9d753fc27d6ce54cce21283b45158022e667e3bc` | `8599A1F13F1A241EFE90BB1059D98C09A4419BE4C2202B97F45DEC69189B3FE3` | `F7CA8E4C2D8F50702DA3A0B0E217153990A4BF8DAD8031B5CC970BCF7A2F56A6` |
| `tools/architecture/check_compatibility.py` | `2786591fe5ca54ecc8a024279b28e664414dab6d` | `F44794AC5411847FF7FC12856850162A5EBC61DDEC646D8D40C23903298F7057` | `C2B3E460A3E2706548E52BD7E04447641539A90479CB154F8001BB60B19FF8D5` |

`R0015.patch` has SHA-256
`A6EAA922363136C5B15351849260632094C1A707D7134E7084CBA6556415E820`.
Its changed-path set is exactly the two rows above. Reverse replay against the
detached candidate succeeds, and clean forward replay must reproduce both
postimage hashes in `R0015-postimages.tsv` before activation. The two files are
applied or rolled back together; partial application is forbidden.

## Prescribed transformation

`Chapter19/Core.lean` changes only import lines 5 and 6:

- `HouseholderQRSupport` becomes `Householder.StoredQR`;
- `HouseholderSpecSupport` becomes `Householder.TrailingPanels`.

The retained wrapper files already import those exact canonical destinations.
No declaration text, namespace, visibility, type, tier, compatibility mapping,
wrapper, aggregate, or entrypoint is changed.

`check_compatibility.py` removes the exhausted two-edge exception set, its
Chapter19.Core SHA-256 pin, and the now-unused `hashlib` import. Its replacement
helper rejects every production import edge whose target is a documented
historical path. Embedded positive and adversarial tests prove that an empty
edge set passes, one historical edge fails with the exact diagnostic, and two
historical edges produce two failures. The success report now states the strict
production-import count directly.

## Direct-consumer freeze

`reviews/CODE03-consumers.tsv` was independently derived from the C0007
production import graph with the repository's comment-aware import parser. It
contains exactly 61 module-sorted data rows. Every row binds the direct
consumer's module, path, C0007 blob OID, byte SHA-256, and one existing test
that directly imports that consumer. The deterministic test selection prefers
the existing R03 protected-consumer test; where none exists, it uses the first
module-sorted direct test. All 61 consumers have at least one direct test.

The bounded completion checker must re-derive this set and reject a missing,
extra, reordered, rehashed, or untested consumer unless a superseding reviewed
request explains the change. That checker binding is an activation condition,
not evidence that this packet may self-approve.

## Existing compatibility and API tests

The activation and verification sets include:

- `NumStabilityTest/Reorganization/R11/Canonical/NumStability_Algorithms_LinearSystems_QR_Householder_StoredQR.lean`;
- `NumStabilityTest/Reorganization/R11/Canonical/NumStability_Algorithms_LinearSystems_QR_Householder_TrailingPanels.lean`;
- `NumStabilityTest/Reorganization/R11/OldOnly/NumStability_Algorithms_LinearSystems_QR_HouseholderQRSupport.lean`;
- `NumStabilityTest/Reorganization/R11/OldOnly/NumStability_Algorithms_LinearSystems_QR_HouseholderSpecSupport.lean`;
- `NumStabilityTest/Worker/QrCh19/Canonical/Core.lean`;
- the 61 direct downstream tests named in `CODE03-consumers.tsv`.

Because only two imports change and the old wrappers forward to the same two
canonical modules, the candidate preserves Chapter19.Core declaration text and
availability. Final activation still requires the supported-API checker to
confirm normalized public signatures and entrypoint reachability against the
C0007 freeze.

## Candidate validation performed

- `git diff --check`: PASS in the detached candidate.
- Python bytecode compilation of `check_compatibility.py`: PASS.
- `python tools/architecture/check_compatibility.py`: PASS, reporting 712
  forwarding modules, 2,364 canonical targets, and 0 production imports of
  historical paths.
- `lake build` for canonical `Householder.StoredQR` and
  `Householder.TrailingPanels`: PASS (3,007 jobs). One pre-existing unused-simp
  warning appeared in an unrelated matrix-inequality dependency.
- A direct absolute-path Core elaboration was attempted but did not reach the
  candidate: the local cache lacked the pre-existing `GivensQR.olean` import.
  The full Core module and named Worker test therefore remain mandatory on the
  exact implementation head in CI / VERIFY-01; this cache miss is not recorded
  as a candidate pass or failure.

## Review and activation state

The packet and its postimages were generated by `codex-local`; that principal
must not independently review the exact evidence it generated or the exact
application action it performs. Independent semantic inspection is **pending**
and may be recorded by `primary-human` or another registered non-service
principal who did not author/generate this packet and did not perform the
reviewed action. GitHub Actions is replay evidence, not the semantic reviewer.

Activation additionally requires green exact-head planned-control CI, clean
forward replay from C0007, exact postimage verification, the consumer-set gate,
supported-API preservation, and the named canonical/old-only/Core tests. R0015
does not authorize a Chapter19 Core split, declaration rename, wrapper removal,
R11 ownership reassignment, C0008 acceptance, or repository-wide completion.
