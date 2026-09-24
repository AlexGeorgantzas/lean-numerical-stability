# Pilot 32: one-pair recovery, not a fresh ten-task pilot

Pilot 29 sealed five pairs before a Titan outage. Pilot 31 sealed four more
pairs, including the unfavorable LL07-THM4 proof-stage telemetry incident.
Its controller then stopped with LL07-THM7 unsealed. All partial artifacts
remain in their original directories. The measured ten-task description is
therefore a composite of three separately frozen campaigns, never one
uninterrupted run or held-out evaluation.

Pilot 32 runs **only LL07-THM7**, original scheduled index 8 and original
condition order N then L, in lane C (8 logical CPUs, 24 GiB RAM). Both
conditions use fresh task conversations. It uses the same frozen Pilot 29/31
corpus, source packet, admission, model qualification, warm root, prompts,
NumStability snapshot, four proof submissions, proof time limit, and no
automatic retrieval. It does not carry forward the interrupted candidate,
proof, audit feedback, or task-specific search.

The controller verifies Pilot 29 and Pilot 31 journal and pair hashes,
the Pilot 31 interrupted pair hash, the original ten-task schedule, and at
least 2 GiB free on the system filesystem before any launch. It holds the
timed-contestant host lock and creates a new output directory. An incident
is recorded as an incident, never turned into a success or silently retried.

The predeclared report hash-checks all ten sealed pair reports across the
three campaigns and retains proof attrition and unfavorable outcomes. Only
pairs in which **both** conditions have independently faithful statements
and complete proofs count toward paired proof-code-size results. Search-
inclusive contestant time and net-new tokens are preserved, as are sampled
CPU and RAM peaks. Direct NumStability reach from the elaborated statement
is reported separately from proof-body dependencies, which are not audited
by this report.

## Disk incident and recoverability

Before recovery, the Titan system filesystem had 1.7 GiB available, while
the benchmark filesystem had 2.4 TiB available. By user authorization,
81 closed system journal files (1,536,013,928 bytes) were moved without
overwriting to the root-only archive
`/hdd/alexgeorgantzas/system-journal-archive-20260924-a`. No active journal,
other user's file, Docker data, or Snap installation was removed. The
files can be moved back to the original machine-ID journal directory.
The system filesystem had 3.2 GiB available afterward. This operation
does not establish what caused the Pilot 31 controller to stop.
