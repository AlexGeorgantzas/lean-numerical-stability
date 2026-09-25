# Pilot 35: bounded recovery after Pilot 34 audit-schema incident

Pilot 34's corpus, source packets, warm state, model, conditions, task order,
proof requirement, and hardware lanes remain frozen. Its valid sealed pairs
must not be rerun. The `CAST08-PROP3.1` pair is not comparable: the N candidate
was correctly judged unfaithful for a contradictory equality, but the audit
validator rejected the round-trip judge's nonvacuity-aware classification on
all three infrastructure retries. N never received the normal repair feedback.
The L half of that pair is preserved only as incident evidence; it must not be
paired with a fresh N run.

Pilot 35 has a distinct campaign and controller identity. It will run one fresh
N/L pair for `CAST08-PROP3.1`, then only tasks that Pilot 34 never launched,
in their original order and with their original condition-order parity.
Every Pilot 34 report and the paused campaign journal are hash-pinned in a
recovery manifest created after Pilot 34 seals its already-running sibling.
The controller verifies the manifest and refuses any partition discrepancy.
It pauses after any new incident, allowing only already-running siblings to
finish. No participant sees Pilot 34 outputs or audit feedback.

The narrow audit correction clarifies that a vacuous material implication is
not faithful strengthening. It also accepts a judge's literal `yes/no`
implication record paired with an explicit failed S16 nonvacuity check and
`unfaithful-different` classification. This preserves the judge's reasoning
while preventing a correctly detected contradiction from becoming an audit
system incident. The regression test requires this exception and ensures it
cannot apply when S16 passes.

The predeclared composite report verifies both campaign journals, all selected
pair-report hashes, all candidate/audit/proof artifacts, source admission, and
the original interrupted pair. It uses Pilot 34's valid sealed pairs and
Pilot 35's new pairs. All failures remain visible. Paired proof-code comparisons
use only pairs with faithful statements and complete kernel-checked proofs in
both conditions. Formalization, proof, and total time/tokens are separate;
auditor overhead and sampled CPU/RAM peaks are reported. This is an
outcome-aware, source-clustered exploratory composite, not a held-out estimate.
