# Design-16 canonical audit batch

`tools/design16_audit_batch.py` is the provider-free control plane that runs
the canonical multi-role faithfulness audit after a timed Design-16 campaign.
It does not call a model directly.

The controller fails closed unless:

- the campaign manifest identity, state hash chain, and summary hash chain all
  validate;
- the campaign and every timed task are terminal;
- all 13 planned tasks have exactly one terminal record;
- each selected task has campaign outcome
  `FORMALIZATION_COMPLETE_AUDIT_PENDING` and pair status
  `FORMALIZATION_FROZEN_PENDING_AUDIT`;
- the campaign nonce, per-pair nonce, runner logs, and complete pair artifact
  closure match `campaign-pair-attestation.json`;
- both condition reports, frozen submissions, paper copies, and source packets
  match their recorded hashes and matched-pair contracts.

Campaign incidents are excluded. Each eligible condition gets a new output
root under `audits/<task>/<R0-or-R1>`. `R0` maps to the `N` compilation
environment and `R1` maps to `L`; this mapping is used only to extract the
candidate semantics. The underlying full-audit controller remains blind to
condition, attempt, retrieval, proof text, and performance telemetry.

This external controller audits proof-mode pairs only. Statement-only runs
perform their audit/repair loop inside the matched runner and produce
`AUDITED_FAITHFUL_PAIR` or `AUDITED_PAIR_INELIGIBLE`; the batch skips those
already-audited pairs. Unknown or mismatched contracts stop the batch before
an auditor call.

Audits run with bounded parallelism (two by default). A hash-chained journal
records every start and terminal outcome. A resumed started audit is recovered
from its validated canonical `result.json`, or recorded as an incident; it is
never rerun. One incident does not stop the remaining audits.

Audit outcomes are distinct from formalization completion:

- `SCIENTIFICALLY_ELIGIBLE`: canonical audit finished faithful;
- `SCIENTIFICALLY_INELIGIBLE`: canonical audit finished unfaithful;
- `AUDIT_INCIDENT`: the audit did not produce a valid canonical decision.

Example:

```bash
python3 paper_bencmark/formalization_benchmark/tools/design16_audit_batch.py \
  --campaign-root /path/to/design16-campaign \
  --deployment /path/to/deployment.json \
  --output-root /path/to/design16-audits \
  --max-parallel 2
```

Auditor time and tokens remain outside contestant measurements.
