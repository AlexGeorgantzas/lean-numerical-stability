# C0008 residual accounting

Frozen inventory: **2,593** production modules at `b1b18772d80185ec08f49c818919558645c330a1`; every base blob OID is preserved.

Residual basis before clean consumers: **467** unique debt-flagged rows plus **15** explicitly reviewed debt-free W90 outliers = **482**. `NumStability/Analysis/MatrixAlgebra.lean` is the one protected read-only outlier and is therefore `already_complete`; the other 481 residual owners are assigned exactly once.

Clean hash-pinned consumer additions: **11** under integrator wave I01. Final dispositions: **492 in_scope**, **2,101 already_complete** (`2101` exact rows).

Wave counts: R01=16, R02=28, R03=47, R04=19, R05=48, R06=75, R07=45, R08=45, R09=72, R10=18, R11=65, R12=3.

The prior W90 action-category partition is not reused: the fresh graph contains exactly 90 direct W90 edges crossing document/rename/aggregate/outlier categories, including cyclic category pairs. The successor groups semantic dependency families and records the complete acyclic quotient in `milestone-dag.tsv`.
