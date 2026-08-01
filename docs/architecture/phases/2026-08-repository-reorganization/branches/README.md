# Branch registry

One JSON record is tracked per phase branch. A planned branch must start from
the current accepted checkpoint and use an active lane baseline projection.
Delivery, integration, ancestry, and retirement fields are updated rather than
replaced by prose-only status messages.

W01 is the first eligible wave, but no branch is planned or active at C0000.
Its record is published only after the control-plane commit becomes a green
checkpoint with a durable lane projection. Later records are published when
their prerequisite checkpoint exists.
