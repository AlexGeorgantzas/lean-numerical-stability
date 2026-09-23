# Prospective ten-task proof campaign — screening, not admitted

This is a worklist, **not** a frozen campaign or positive-result selection.
Pilot 26 outcomes and the Pilot 27 first pair are known; any later run on
these tasks is outcome-aware exploratory development, not held-out evidence.
The candidate ordering is not yet fixed. No benchmark task has been launched
from this document.

The proposed mix keeps source variety and has ten IDs only if the new
`CAST08-PROP3.1` candidate passes its remaining admission checks. Nine older
tasks had faithful N/L statements and *observed* direct NumStability reach in
Pilot 26. This is a broader direct-declaration stratum, **not** ten tasks
with verified task-specific algorithm/error reuse.

| Candidate | Source area | Prior L direct reach / intended component | Strict algorithm/error gate |
|---|---|---|---|
| FAB19-EQ3.5 | Mixed-precision blocked sum | `fl_recursiveSum`, `fl_higherPrecisionRecursiveSum` in Pilot 26; only FPModel/gamma in Pilot 27 | Potential overlap, actual Pilot 27 uptake failed |
| FAB19-EQ3.6 | Compensated blocked sum | `fl_recursiveSum`, `fl_kahanSum` in Pilot 26 | Potential overlap; Pilot 28 canary pending |
| CAST08-FIXED3 | Three-level superblock dot | `fl_dotProduct`, `fl_recursiveSum` in Pilot 26 | Potential overlap; Pilot 28 canary pending |
| CAST08-PROP3.2 | General t-level superblock dot | FPModel/gamma in Pilot 26; private replacement directly reaches `fl_dotProduct` | Private direct-reach and independent audit pending |
| CAST08-PROP3.1 | General t-level superblock sum | New private statement directly uses `fl_recursiveSum` | Local compile passed; exact-snapshot check and audit pending |
| RUMP12-THM3.4 | Finite-format rounding | `FloatingPointFormat` representation in Pilot 26 | Foundational model only; no task-specific algorithm/error theorem |
| RUMP12-THM3.5 | Finite-format rounding | `FloatingPointFormat` representation in Pilot 26 | Foundational model only; no task-specific algorithm/error theorem |
| LL07-THM4 | Polynomial/finite-format | `FloatingPointFormat`, `polyDesc`, `polyDescAbs` in Pilot 26 | Foundational/polynomial definitions only |
| LL07-THM7 | Polynomial/finite-format | `FloatingPointFormat`, `polyDesc`, `polyDescAbs` in Pilot 26 | Foundational/polynomial definitions only |
| H20-8 | Matrix-only least-squares backward error | `lsNormwiseBackwardErrorMatrixOnlyEtaF` and norm/feasibility interface in Pilot 26 | Relevant error interface, but no FPModel |

Before freezing a full run: finish the Pilot 28 early review; independently
audit the new CAST08-PROP3.1 statement and the repaired CAST08-PROP3.2
private statement; verify exact snapshot compilation and semantic direct
reach; screen every target-result collision; and decide **prospectively**
whether the four foundational/finite-format cases are a transparent secondary
stratum or violate the user's strict FPModel preference. If they are excluded,
there is not yet a ten-task corpus. Do not silently relabel them as strict
algorithm tasks or pad a corpus to reach ten.

The later proof-required protocol must still present statement-level results
and attrition for every task, and count final proof-code lines only when both
conditions have independently faithful, unchanged, kernel-checked proofs.
Search-inclusive time/tokens remain primary timing/accounting observations;
search-time-excluded values are descriptive diagnostics only.
