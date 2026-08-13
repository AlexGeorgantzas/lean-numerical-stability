# R12 delivery

R12 splits the three C0001 Chapter 13 declaration-bearing owners into six
canonical leaves while retaining the historical paths as documented complete
compatibility aggregates. It preserves 34 public declarations, with no private
declarations or private-name normalization.

The delivery changes 51 exact paths: three modified owners, six new production
leaves, 27 R12 tests, and 15 evidence artifacts. It contains no shared-file,
phase-control, tool, CI, Lake, root-documentation, or MatrixAlgebra change.

All Lean and baseline operations are run while holding the Windows named mutex
Local\lean-reorganization-2026-08. GATE_RESULTS.tsv records the final exact
commands, results, timings, job summaries, candidate hashes, and the disposable
R0004-integrated replay.

Two preliminary full-replay harness invocations reached green architecture
gates but stopped while rendering Lean output through the Windows console:
one locale decode error and one console encode error. The capture path was
corrected, and the final exact replay returned zero with every gate green.
Separately, the first staged whitespace check found five evidence Markdown
files with an extra blank line at EOF; those files were corrected before the
passing staged result recorded in GATE_RESULTS.tsv.

This evidence describes one immutable worker delivery only. It does not claim
C0002 acceptance or integration into main.
