# Branch registry

One JSON record is tracked per phase branch. A planned branch must start from
the current accepted checkpoint and use an active lane baseline projection.
Delivery, integration, ancestry, and retirement fields are updated rather than
replaced by prose-only status messages.

[`B0001`](B0001.json) is planned for W01 from green checkpoint C0001 at
`d6e643adf0f20b33f7faebce7e1b9b1f87122c58`. The remote branch need not exist
until its active writer starts. Later records are published only when their
prerequisite checkpoint exists.

B0001 may add focused old-import and canonical-import files only under
`NumStabilityTest/Reorganization/W01/`; existing `Import/`, `Worker/`, and root
test files remain forbidden. The worker builds those files directly with
`lake env lean`. It records its delivery report, scope evidence, and any
proposed shared patch under `docs/architecture/deliveries/W01/`. After the
delivery commit is pushed, the integrator hashes those artifacts into B0001,
creates any required shared-file request, wires shared test/aggregate roots,
and runs the acceptance checkpoint. Workers never edit the registry to mark
their own delivery accepted.
