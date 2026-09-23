# Pilot 22 first-pair controller incident (2026-09-23)

Pilot 22 is frozen and stopped at the mandatory first-pair gate. Its Titan output
root is `/hdd/alexgeorgantzas/highambench/pilot22-dev3-20260923-a`.
Controller commit: `20a0a77f5775e788b4dae4241b74e7adfa70b714`.
The final `campaign.json` SHA-256 is
`3fd61c1180031831a6d3dfb6374634c6c5f0732d2f3d2b0b9447e04f089d7d16`;
the `FAB19-EQ3.5/pair-report.json` SHA-256 is
`fc62e9773ffc35801b81f76b56dbbe7971898e713ba9c3b0c8d6f3001f705dba`.
Status is `PAUSED_FIRST_PAIR_INCIDENT`, not a scored pair. Neither remaining
scheduled task was started.

R0 (Mathlib only) submitted once, compiled, and passed a fresh full faithfulness
audit (`faithful-stronger`). Its candidate SHA-256 is
`3830adb1900b0b857e03b7bd13c0c735642d8ed8e0e09b3ad6d28889733c49e4`;
contestant-active time was 180.394 seconds, net-new provider tokens 46,112,
candidate length 76 lines. Audit time was 391.962 seconds and excluded. The
resource trace sampled peak memory 955,326,464 bytes and peak one-second CPU
mean 0.998 cores on the 8-CPU/24-GiB lane, with no OOM event.

R1 (NumStability) began its measured turn and worked on a candidate. The
controller failed **before freezing a submission or obtaining an audit**, with
`BenchmarkError: forbidden workspace control surface: .codex`. Thus no L/N
comparison can be drawn from Pilot 22. The `.codex` directory in R1's workspace
was empty; `.agents` and `.git` were likewise empty, all created together at
10:02:22 UTC when the warm-fork Codex tool sandbox initialized. The first
read-only workspace listing inside R1 already displayed these directories;
the contestant's recorded tool calls did not create them. R0's cold workspace
did not have them. The safety check treated an empty top-level mount point as
an instruction-bearing control surface.

Prospective fix for a *new* Pilot 23: allow only an **empty top-level** `.codex`
directory during workspace-safety scanning. Any populated or nested `.codex`
directory, symlink, or protected control file remains prohibited. Add regression
tests for all three cases. Pilot 22's frozen checkout and output root must not
be modified or resumed; disclose the incident and rerun the pair only under
the new frozen pilot identity.
