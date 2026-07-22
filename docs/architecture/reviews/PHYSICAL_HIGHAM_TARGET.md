# Physical Higham target decision

Decision: **keep the logical `NumStability.Higham` layer in the existing Lake
library for this migration**.

A separate physical library is premature because:

- source declarations remain embedded in high-fan-in reusable-looking modules,
  especially `Norms`, `BlockLU`, `LSQRSolve`, and `LSE`;
- several generic modules still depend on mixed source modules;
- the executable tier inventory is incomplete, so a global zero
  reusable-to-source edge count has not yet been established;
- the new Higham hierarchy and compatibility imports have not completed a
  release cycle;
- no clean and incremental benchmark yet shows that a second library offsets
  its packaging, CI, and versioning cost.

Reconsider the decision only when the tier inventory reaches 100% coverage
with no `mixed` modules, the generated import audit reports zero
direct or transitive reusable-to-source dependencies, curated entry points and
old-path tests are stable, and repeated clean/incremental measurements show a
material benefit. A logical tier does not require a separate Lake target.
