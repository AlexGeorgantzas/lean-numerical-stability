# Pilot 31: disclosed five-pair recovery extension

This implements the user's 2026-09-24 request to keep the positive Pilot 29
results and finish the ten tasks, rather than rerun all ten. Pilot 29's
complete and partial evidence remains untouched. The earlier Pilot 30
full-retry proposal was never measured. Its fresh static preflight was stopped
at the first R0 template after the user changed course; it is off-benchmark
and produced no result.

The exact five remaining tasks and prior artifact hashes are frozen in
`RECOVERY_5.json`. Five completed Pilot 29 pairs are carried forward *as
Pilot 29 pairs*. Three interrupted pairs are run afresh in both conditions
under a new Pilot 31 identity, with all old partial attempts retained but
excluded from the new pair metrics. Two unstarted tasks get their first
measured N/L pairs. The original ten-task order determines N/L condition
order, so no parity flips. No task is silently dropped, no unfavorable result
is overwritten, and no source candidate or feedback crosses conversations.

Pilot 31 uses the identical frozen source packets, target admission, common
and L prompts, warm orientation root, model/effort, audit procedure, proof
limits, library and Mathlib snapshots, and three disjoint 8-logical-CPU /
24-GiB/no-swap lanes of Pilot 29. The recovery controller only changes which
tasks launch and where their immutable results are written. It hash-checks
Pilot 29's journal and completed/partial report identities before launching.
No Pilot 30 measured task may be launched. If Pilot 31 itself is interrupted,
do not silently restart one of its tasks.

The ten-task report is explicitly a **recovery composite**, not a single
uninterrupted campaign or a held-out effect estimate. It comprises all five
sealed Pilot 29 pairs plus all five Pilot 31 pairs. Report source campaign and
restart flags per row. Use the same predeclared Pilot 29 metrics: paired
faithful statement code size; paired fully proved proof code size; proof
attrition; direct NumStability declaration reach; inclusive contestant wall
time and net-new tokens; and sampled CPU/RAM peaks. All ten tasks must appear,
including any L loss, non-uptake, unfaithful statement, or proof failure.
