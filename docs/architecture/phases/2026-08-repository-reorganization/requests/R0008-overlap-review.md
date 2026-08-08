# R0008 integration-overlap evidence

Base checkpoint: C0006 / `a32095e6e50189f7dcc39312bb4c6a36f421fab5`.

R0008 was applied and validated independently in a disposable C0006 Git index.
Its six sorted patch paths exactly match the request record. The null-preimage
W09 test root is import-and-docstring-only; the two existing production
aggregates and root test change imports only.

| Path | C0006 preimage | Integrated postimage | Class |
| --- | --- | --- | --- |
| `NumStabilityTest/Reorganization/W09.lean` | `null` | `d9b171617fd59c1ab09efbf60c87d266bee08a21` | import-only test aggregate |

The immutable W09 packet stated that no integrator-owned file needed to change,
but the read-only combined layout audit proved the omitted obligations exactly:
191 unreachable tests, 34 missing reusable classifications, ten stale
docstring debts, and 34/51 missing descendants from the Analysis and Chapter 28
aggregates. R0008 records that necessary integration correction without
altering the immutable delivery packet.

R0008 intersects each of R0007 and R0009 only at `NumStabilityTest.lean`,
`docs/architecture/layout-exceptions.json`, and `docs/architecture/tiers.json`.
The final tree contains the deliberate three-way union, while every request
patch remains independently applicable to C0006.
