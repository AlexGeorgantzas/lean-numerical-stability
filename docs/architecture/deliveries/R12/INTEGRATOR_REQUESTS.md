# R12 integrator-only request

R0004 is owned by primary-human and is deliberately absent from the worker
delivery. It changes exactly NumStabilityTest.lean,
docs/architecture/layout-exceptions.json, and docs/architecture/tiers.json.

CHECK_REQUEST_REPLAY.py hash-verifies the active request, its three preimages,
three postimages, reviewed union artifacts, and exact path-list hash. It replays
R0004 forward and reverse from clean C0001, then overlays this worker delivery
onto exact active control in a disposable clone and runs the complete
architecture/source/build gate battery there.

At integration, primary-human must merge the immutable R11 and R12 deliveries
separately, then apply the reviewed R0003-R0004 union patch exactly once. The
two whole-file requests must not be applied sequentially.
