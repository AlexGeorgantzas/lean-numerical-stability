# R07 worker delivery

This directory is the immutable-worker evidence packet for R07, Matrix Powers and
functional calculus. It is based on checkpoint C0005 and code commit
`ad92bbfae62d538f3e52829a269a846688a8e213`. The activated planning control is
B0010 at control commit `35cb1a7c5f136f291398dddd99d8012dcf38f967`.

The materialized worker result has 45 historical owners. Thirteen declaration-
bearing owners are import-only compatibility wrappers after relocation; 32
zero-declaration owners remain byte-identical to C0005. The 194 declarations
(150 public and 44 private) are routed to 30 semantic destinations. The isolated
test plan contains 102 test modules: 101 isolated targets and one aggregate.

`MATERIALIZATION.json` binds all 145 worker-rendered postimages at SHA-256
`05C738043A6D990B7E2BBBE9B200E2A4B54AB8B042AFE9A308A6ACD1FF71A5FA`.
Its deterministic materializer has SHA-256
`1C45DEF702DB5DE58963D979AD3AD90ED66F16A3F69BF396C05F8DF2FBD12112`.
The copied TSV ledgers bind the reviewed planning inputs byte-for-byte.
`RETENTION.tsv` records each historical owner, and `CHANGED_PATHS.md` records
the complete 166-path delivery set: 43 production paths, 102 test paths, and 21
delivery-evidence paths. The checkers are read-only in the worker tree; request
replay uses a disposable clone. That replay first authenticates immutable
R0011, then separately exercises the four-path supplemental correction recorded
in `R0011-CORRECTION.patch`. The correction remains an integrator request, not a
worker edit or approval.

All required worker gates are green. `GATE_RESULTS.tsv` records each gate
invocation or artifact-bound exact roster, exit code, transcript SHA-256, and
bound artifact or checker SHA-256, including the final disposable-clone replay
under checker SHA-256
`3CB016BFD47123252222C3821004B7B774C0DC30A04AAD5944B8D1FE4C6DA103`.
That replay uses a short disposable root with a fail-closed Windows MAX_PATH
guard, confines Mathlib's official content-addressed cache to the overlay,
audits the disposable `.lake` and `.cache` trees for links, reparse points,
hardlinks, and unsupported files after cache retrieval and after the build,
then runs `lake build NumStability NumStabilityTest` and `lake test`.

The full disposable replay used materialization
`D62CAF8DAC747AEE902D4A6D532F1A5E451D764A126A9410754D10202B10542F`.
The staged whitespace gate subsequently exposed one extra terminal blank line
in 48 generated test modules. The materializer was corrected and those exact
48 modules now differ only by deletion of that final blank line; production
bytes are unchanged. The final materialization is
`05C738043A6D990B7E2BBBE9B200E2A4B54AB8B042AFE9A308A6ACD1FF71A5FA`.
All 48 final-byte test modules, including the R07 aggregate, passed a targeted
build with transcript SHA-256
`E51564268739D08081E48344B7AFCEBA62B988AEE9E01B60607855F738847BB3`,
and the post-normalization structural replay passed under checker SHA-256
`8A60B0494FEDCF4573CF1A50B019486BE42F8FA844FAEB33C09B34E4F2EEA2F8`.
The ledger therefore preserves the full pre-normalization build/test and the
exact final-byte bridge separately rather than claiming a second full replay.
A later final-tree `lake test` attempt was intentionally stopped after it
expanded into rebuilding unchanged dependencies; it is recorded as superseded,
not as a gate result. The earlier complete `lake test` and the exact 48-module
final-byte bridge are the applicable evidence.

The ledger also preserves four superseded non-green attempts as historical
evidence: one cold build completed before a CP1252 decode failure, one early
cold rebuild was intentionally stopped when the independently audited cache
route became available, the first cached replay reached cache retrieval before
a CP1252 output-encoding failure, and the next cached replay reached
12036/12038 targets before ten test-output paths crossed legacy Windows
MAX_PATH. The first three are harness outcomes, not claimed Lean failures; the
fourth is recorded as an environment-induced build failure whose cause was
independently isolated by path audit and focused R07 build. None replaces the
final green replay. This delivery does not integrate R0011, edit shared files,
accept R07, accept a checkpoint, retire the branch, or push main.
