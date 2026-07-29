# Integrator request

Lane: classification-ch09-ch11

Base SHA: `6ecc4d5513226e67594bb22985913f6a4a383e5c` (coordinator-published evidence base; packet inventory base is `6487fc33088523b8f27ecde9ad613515b78f9977`)

Worker branch and commit: `codex/org-classification-prep` at the final implementation/evidence commit recorded in `DELIVERY.md`

Shared file that appears necessary: `NumStabilityTest.lean`

Why lane-owned work cannot avoid it: The packet requires three standalone
worker smoke modules but explicitly forbids this lane from editing any root
test aggregate. The repository layout checker requires every test module to be
reachable from `NumStabilityTest`. It therefore reports exactly these three
intentional worker modules and no other lane-owned failure.

Exact proposed patch:

```lean
import NumStabilityTest.Worker.ClassificationAudit.Chapter09Historical
import NumStabilityTest.Worker.ClassificationAudit.Chapter11CanonicalExisting
import NumStabilityTest.Worker.ClassificationAudit.Chapter11Historical
```

Validation already performed: The three paths are isolated under the allowed
worker prefix; static trust-marker scan passes; Chapter 9 and Chapter 11
format-2 pre-checks pass. `check_layout.py` exits 1 solely because the three
imports above are absent.

Dependency/order constraint: Apply only when integrating this lane, then run
the three `lake env lean` smoke commands, `python tools/architecture/check_layout.py`,
the focused Chapter 9/11 builds, full build, and `lake test` under the shared
Lean mutex. Do not begin Chapter 11 implementation before Chapter 9 is merged.

Do not apply this patch in the worker branch. Send this request to the
integrator.
