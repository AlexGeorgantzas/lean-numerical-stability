#!/usr/bin/env bash
# Private, auditable HighamBench one-pair shard launcher.
#
# This file is a runbook, not a submission: run it only through the exact
# `sbatch` command reported with the review that introduced it.  It never
# refreshes the benchmark snapshot, never uses --force, never removes prior
# artifacts, and never performs a public release.

#SBATCH --job-name=highambench-pair-shard
#SBATCH --account=kfountou_group
#SBATCH --partition=ALL
#SBATCH --nodes=1
#SBATCH --ntasks=1
#SBATCH --cpus-per-task=4
#SBATCH --sockets-per-node=1
#SBATCH --cores-per-socket=2
#SBATCH --threads-per-core=2
#SBATCH --mem=32G
#SBATCH --gres=gpu:0
#SBATCH --time=04:00:00
#SBATCH --chdir=/u501/m2fetrat/MyCodes/lean-fp-analysis-main
#SBATCH --output=/u501/m2fetrat/MyCodes/lean-fp-analysis-main/paper_bencmark/scratch_pad/slurm-%x-%j.log

set -Eeuo pipefail
umask 077
export PYTHONNOUSERSITE=1
export TZ=UTC

readonly PROJECT_ROOT="/u501/m2fetrat/MyCodes/lean-fp-analysis-main"
readonly BENCHMARK_ROOT="${PROJECT_ROOT}/paper_bencmark/highambench"
readonly SCRATCH_ROOT="${PROJECT_ROOT}/paper_bencmark/scratch_pad"
readonly PAPER_ID="${HIGHAMBENCH_PAPER_ID:?set HIGHAMBENCH_PAPER_ID}"
readonly PAIR_ID="${HIGHAMBENCH_PAIR_ID:?set HIGHAMBENCH_PAIR_ID}"
readonly SHARDS_ROOT="${HIGHAMBENCH_SHARDS_ROOT:-${SCRATCH_ROOT}/highambench_${PAPER_ID,,}_actual_ultra_shards}"
readonly RESULT_ROOT="${SHARDS_ROOT}/${PAIR_ID}"

readonly PYTHON="/usr/bin/python3.10"
readonly CODEX="${SCRATCH_ROOT}/highambench_environment/codex-0.146.0-alpha.9.2"
readonly AUTH_FILE="/u501/m2fetrat/.codex/auth.json"
readonly OFFLINE_SHELL="${SCRATCH_ROOT}/highambench_environment/offline-shell"
readonly TOOLCHAIN_ROOT="/u501/m2fetrat/.elan/toolchains/leanprover--lean4---v4.29.0-rc3"
readonly PACKAGES_ROOT="${PROJECT_ROOT}/.lake/packages"
readonly PACKAGES_RUNTIME_ROOT="${SCRATCH_ROOT}/highambench_environment/packages_runtime"
readonly SHARED_OLEAN_ROOT="${SCRATCH_ROOT}/highambench_environment/shared_olean"
readonly LIBRARY_SOURCE="${PROJECT_ROOT}/NumStability"
readonly LIBRARY_ROOT_FILE="${PROJECT_ROOT}/NumStability.lean"
readonly LIBRARY_OLEAN="${SCRATCH_ROOT}/highambench_environment/numstability_olean"
readonly RELEASE_MANIFEST="${BENCHMARK_ROOT}/metadata/release_files.json"

readonly ULTRA_TOOL="${BENCHMARK_ROOT}/tools/run_ultra_orchestration_canary.py"
readonly TOKEN_TOOL="${BENCHMARK_ROOT}/tools/run_token_control_canary.py"
readonly MATRIX_TOOL="${BENCHMARK_ROOT}/tools/run_matrix.py"
readonly CAMPAIGN_TOOL="${SCRATCH_ROOT}/manage_highambench_pair_shard.py"

readonly MANIFEST="${BENCHMARK_ROOT}/metadata/manifest.json"
readonly CONFIG="${BENCHMARK_ROOT}/metadata/config.json"
readonly ENVIRONMENT="${BENCHMARK_ROOT}/metadata/environment.json"
readonly ULTRA_EVIDENCE="${BENCHMARK_ROOT}/metadata/evidence/ultra_orchestration_live_canary.json"
readonly TOKEN_EVIDENCE="${BENCHMARK_ROOT}/metadata/evidence/token_control_live_canary.json"
readonly SPECIFICATION_PDF="${SCRATCH_ROOT}/HighamBench_Simple_Two_Condition_Specification.pdf"

readonly EXPECTED_MANIFEST_SHA256="5a1eeb84c4214a3dd95386a912047bc6e2914621e65439e1d694aa5892ad408b"
readonly EXPECTED_SPECIFICATION_SHA256="59dfc314d4f9afecbbc6131c3c693624b09cc9e908f0e157efa468675ff56915"
readonly EXPECTED_PYTHON_SHA256="d6bca2b84e73c7775a0dd5e6a76899cfe4ee62863d7c8f88513811d1fda23f49"
readonly EXPECTED_CODEX_SHA256="d13cfcda217421fb20d0aa6aa80819a62483a72e4a7fd52743675ca20d86377c"
readonly EXPECTED_PYTHON_VERSION="3.10.12"
readonly EXPECTED_CODEX_VERSION="0.146.0-alpha.9.2"
readonly MODEL="gpt-5.6-sol"
readonly REASONING_EFFORT="ultra"
readonly HARDWARE_MATCHING_POLICY="same-authenticated-slurm-allocation-within-pair-v1"
readonly VETTED_NODES_CSV="watgpu108,watgpu508,watgpu808"
readonly RUN_LIMIT_SECONDS=1800
readonly TOKEN_LIMIT=5000000
readonly PROMPT_STARTUP_SECONDS=120
readonly ALLOCATION_GUARD_SECONDS=600
readonly EXPECTED_POST_SUBMISSION_VALIDATION_RESERVE_SECONDS=369

# run_matrix reserves two startup windows and the frozen post-submission
# validation interval for each unfinished assignment, then adds the separate
# general guard.  The exact pair reservation is derived from both frozen
# metadata copies below; it is not inferred from the 600-second general guard.

die() {
  printf 'FATAL: %s\n' "$*" >&2
  exit 2
}

case "$PAPER_ID" in
  P05)
    PAPER_FILENAME="P05_IMPROVED BACKWARD ERROR BOUNDS FOR LU ANDCHOLESKY FACTORIZATIONS.pdf"
    EXPECTED_PAPER_SHA256="dd8b525c0eabc509a68b325ee5008cf6f1d4ef262bef8ba54e1947fe3cdb3db6"
    ;;
  P11)
    PAPER_FILENAME="P11_A note on the error analysis of classical Gram–Schmidt.pdf"
    EXPECTED_PAPER_SHA256="72b7521848be07971a6721ea0356bb898c63e21b8ad3aa109fee8f41517284a5"
    ;;
  P15)
    PAPER_FILENAME="P15_Solving block low-rank linear systems by LU factorization is numerically stable.pdf"
    EXPECTED_PAPER_SHA256="a5cb8eb779c1571f1549ea6838c7f2269302c960fb4ea21f8410060811270cd7"
    ;;
  P20)
    PAPER_FILENAME="P20_ERROR ANALYSIS OF MATRIX MULTIPLICATION WITHNARROW RANGE FLOATING-POINT ARITHMETIC.pdf"
    EXPECTED_PAPER_SHA256="ad830de20a73ff77b6e457921892b3250ba9ff70f487501979ee3f1c5f3f31e2"
    ;;
  *) die "unsupported paper ID: ${PAPER_ID}" ;;
esac
readonly PAPER_FILENAME EXPECTED_PAPER_SHA256
readonly PAPER_PDF="${PROJECT_ROOT}/paper_bencmark/reference_papers/${PAPER_FILENAME}"
[[ "$PAIR_ID" =~ ^${PAPER_ID}-T[123]-rep-0[123]$ ]] || die "pair ID is not canonical for ${PAPER_ID}: ${PAIR_ID}"
[[ "$SHARDS_ROOT" == "${SCRATCH_ROOT}/highambench_${PAPER_ID,,}_actual_ultra_shards" ]] || die "shards root is not the exact paper-scoped root"
CAMPAIGN_ARGS=(
  --paper-id "$PAPER_ID"
  --target-pair-id "$PAIR_ID"
  --campaign-root "$RESULT_ROOT"
  --benchmark-root "$BENCHMARK_ROOT"
)
readonly -a CAMPAIGN_ARGS

note() {
  printf '[%s] %s\n' "$(/bin/date -u +'%Y-%m-%dT%H:%M:%SZ')" "$*"
}

sha256_of() {
  local path=$1
  /bin/sha256sum -- "$path" | /bin/awk '{print $1}'
}

require_regular_file() {
  local path=$1
  local label=$2
  [[ -f "$path" && ! -L "$path" ]] || die "${label} is not a regular non-symlink file: ${path}"
}

assert_sha256() {
  local path=$1
  local expected=$2
  local label=$3
  local actual
  require_regular_file "$path" "$label"
  actual=$(sha256_of "$path")
  [[ "$actual" == "$expected" ]] || die "${label} SHA-256 mismatch: expected ${expected}, got ${actual}"
}

check_help_contract() {
  local tool=$1
  shift
  local help_text
  help_text=$("$PYTHON" "$tool" --help)
  local option
  for option in "$@"; do
    [[ "$help_text" == *"${option}"* ]] || die "parser drift: $(basename "$tool") lacks ${option}"
  done
}

make_task_ledger() {
  local destination=$1
  "$PYTHON" - "$PROJECT_ROOT" "$destination" "$EXPECTED_MANIFEST_SHA256" "$PAPER_PDF" <<'PY'
import hashlib
import os
from pathlib import Path
import sys

project = Path(sys.argv[1]).resolve()
destination = Path(sys.argv[2])
expected_manifest = sys.argv[3]
paper_pdf = Path(sys.argv[4]).resolve()
benchmark = project / "paper_bencmark/highambench"

fixed = {
    benchmark / "metadata/manifest.json",
    benchmark / "metadata/run_order.json",
    project / "paper_bencmark/scratch_pad/HighamBench_Simple_Two_Condition_Specification.pdf",
    project / "paper_bencmark/scratch_pad/run_highambench_pair_shard_actual_ultra.sh",
    project / "paper_bencmark/scratch_pad/manage_highambench_pair_shard.py",
    paper_pdf,
    benchmark / "agent_prompt.md",
    benchmark / "condition_prompts/L.md",
}

for relative_tree in ("tasks", "shared", "metadata/controlled"):
    tree = benchmark / relative_tree
    if tree.is_symlink() or not tree.is_dir():
        raise SystemExit(f"frozen benchmark tree is missing or unsafe: {tree}")
    for path in tree.rglob("*"):
        if path.is_symlink():
            raise SystemExit(f"frozen benchmark tree contains a symlink: {path}")
        if path.is_file():
            fixed.add(path)

lines = []
for path in sorted(fixed, key=lambda item: item.relative_to(project).as_posix()):
    if path.is_symlink() or not path.is_file():
        raise SystemExit(f"frozen experiment input is missing or not a regular file: {path}")
    digest = hashlib.sha256(path.read_bytes()).hexdigest()
    relative = path.relative_to(project).as_posix()
    lines.append(f"{digest}  {relative}\n")
    if relative == "paper_bencmark/highambench/metadata/manifest.json" and digest != expected_manifest:
        raise SystemExit(
            f"manifest SHA-256 mismatch: expected {expected_manifest}, got {digest}"
        )

destination.parent.mkdir(parents=True, exist_ok=True)
flags = os.O_WRONLY | os.O_CREAT | os.O_EXCL
fd = os.open(destination, flags, 0o600)
try:
    with os.fdopen(fd, "w", encoding="utf-8", newline="") as stream:
        stream.writelines(lines)
        stream.flush()
        os.fsync(stream.fileno())
except BaseException:
    raise
PY
}

assert_task_ledger() {
  local ledger=$1
  "$PYTHON" - "$PROJECT_ROOT" "$ledger" "$EXPECTED_MANIFEST_SHA256" "$PAPER_PDF" <<'PY'
import hashlib
from pathlib import Path
import sys

project = Path(sys.argv[1]).resolve()
ledger = Path(sys.argv[2])
expected_manifest = sys.argv[3]
paper_pdf = Path(sys.argv[4]).resolve()
benchmark = project / "paper_bencmark/highambench"
fixed = {
    benchmark / "metadata/manifest.json",
    benchmark / "metadata/run_order.json",
    project / "paper_bencmark/scratch_pad/HighamBench_Simple_Two_Condition_Specification.pdf",
    project / "paper_bencmark/scratch_pad/run_highambench_pair_shard_actual_ultra.sh",
    project / "paper_bencmark/scratch_pad/manage_highambench_pair_shard.py",
    paper_pdf,
    benchmark / "agent_prompt.md",
    benchmark / "condition_prompts/L.md",
}
for relative_tree in ("tasks", "shared", "metadata/controlled"):
    tree = benchmark / relative_tree
    if tree.is_symlink() or not tree.is_dir():
        raise SystemExit(f"frozen benchmark tree is missing or unsafe: {tree}")
    for path in tree.rglob("*"):
        if path.is_symlink():
            raise SystemExit(f"frozen benchmark tree contains a symlink: {path}")
        if path.is_file():
            fixed.add(path)

actual = []
for path in sorted(fixed, key=lambda item: item.relative_to(project).as_posix()):
    if path.is_symlink() or not path.is_file():
        raise SystemExit(f"frozen experiment input is missing or not a regular file: {path}")
    digest = hashlib.sha256(path.read_bytes()).hexdigest()
    relative = path.relative_to(project).as_posix()
    actual.append(f"{digest}  {relative}\n")
    if relative == "paper_bencmark/highambench/metadata/manifest.json" and digest != expected_manifest:
        raise SystemExit(
            f"manifest SHA-256 mismatch: expected {expected_manifest}, got {digest}"
        )
if ledger.is_symlink() or not ledger.is_file():
    raise SystemExit(f"baseline task ledger is missing or unsafe: {ledger}")
if ledger.read_text(encoding="utf-8").splitlines(keepends=True) != actual:
    raise SystemExit("benchmark task/shared/controlled/source bytes differ from the sealed ledger")
PY
}

descriptor_status() {
  local key=$1
  local expected_path=$2
  "$PYTHON" - "$CONFIG" "$ENVIRONMENT" "$PROJECT_ROOT" "$key" "$expected_path" <<'PY'
import hashlib
import json
from pathlib import Path
import re
import sys

config = json.loads(Path(sys.argv[1]).read_text(encoding="utf-8"))
environment = json.loads(Path(sys.argv[2]).read_text(encoding="utf-8"))
project = Path(sys.argv[3]).resolve()
key = sys.argv[4]
expected_path = sys.argv[5]
left = config.get("frozen_environment", {}).get(key)
right = environment.get(key)
if left != right or not isinstance(left, dict):
    raise SystemExit(f"{key} descriptors disagree")
if set(left) != {"path", "sha256", "status"}:
    raise SystemExit(f"{key} descriptor fields are not exact")
if left["path"] != expected_path:
    raise SystemExit(f"{key} descriptor path drifted")
if left["status"] not in {"replacement_required", "passed"}:
    raise SystemExit(f"{key} has unexpected status {left['status']!r}")
if not isinstance(left["sha256"], str) or re.fullmatch(r"[0-9a-f]{64}", left["sha256"]) is None:
    raise SystemExit(f"{key} descriptor SHA-256 is invalid")
evidence = (project / left["path"]).resolve()
try:
    evidence.relative_to(project)
except ValueError as error:
    raise SystemExit(f"{key} evidence escapes project") from error
if evidence.is_symlink() or not evidence.is_file():
    raise SystemExit(f"{key} evidence is missing or unsafe")
actual = hashlib.sha256(evidence.read_bytes()).hexdigest()
if actual != left["sha256"]:
    raise SystemExit(f"{key} evidence SHA-256 is stale")
print(left["status"])
PY
}

remaining_allocation_seconds() {
  local now
  now=$(/bin/date -u +%s)
  printf '%s\n' "$((ALLOCATION_END_EPOCH - now))"
}

initialize_result_root() {
  if [[ -L "$RESULT_ROOT" ]]; then
    die "stable result root must not be a symlink: ${RESULT_ROOT}"
  fi
  if [[ -e "$RESULT_ROOT" && ! -d "$RESULT_ROOT" ]]; then
    die "stable result root is not a directory: ${RESULT_ROOT}"
  fi
  local state=existing
  if [[ ! -e "$RESULT_ROOT" ]]; then
    /bin/mkdir -p -- "$RESULT_ROOT"
    state=created
  fi
  "$PYTHON" - "$RESULT_ROOT" <<'PY'
from pathlib import Path
import re
import sys

root = Path(sys.argv[1])
if root.is_symlink() or not root.is_dir():
    raise SystemExit("stable campaign root is missing or unsafe")
allowed = {".campaign.lock", ".launcher.lock", "campaign_index.json", "pair_attempts", "runbook_audit"}
index_temp = re.compile(r"\.campaign_index\.json\.tmp-[1-9][0-9]*")
unexpected = sorted(
    path.name
    for path in root.iterdir()
    if path.name not in allowed and index_temp.fullmatch(path.name) is None
)
if unexpected:
    raise SystemExit(f"stable campaign root has unexpected entries: {unexpected}")
for path in root.iterdir():
    if index_temp.fullmatch(path.name) is not None and (
        path.is_symlink() or not path.is_file()
    ):
        raise SystemExit(
            f"campaign index temporary is not a regular non-symlink file: {path}"
        )
for name in ("pair_attempts", "runbook_audit"):
    path = root / name
    if path.exists() and (path.is_symlink() or not path.is_dir()):
        raise SystemExit(f"campaign path is unsafe: {path}")
for name in (".campaign.lock", ".launcher.lock", "campaign_index.json"):
    path = root / name
    if path.exists() and (path.is_symlink() or not path.is_file()):
        raise SystemExit(f"campaign file is unsafe: {path}")
PY
  printf '%s\n' "$state"
}

AUDIT_ACTIVE=0
INITIAL_LEDGER=""
BEFORE_LEDGER=""
AFTER_LEDGER=""

assert_experiment_snapshot() {
  assert_task_ledger "$INITIAL_LEDGER"
  assert_task_ledger "$BEFORE_LEDGER"
  /bin/cmp -s -- "$INITIAL_LEDGER" "$BEFORE_LEDGER" || die "per-job task ledger differs from the stable initial experiment ledger"
}

finish_audit() {
  local original_rc=$?
  local audit_rc=0
  trap - EXIT
  if [[ "$AUDIT_ACTIVE" == 1 ]]; then
    set +e
    make_task_ledger "$AFTER_LEDGER"
    audit_rc=$?
    if (( audit_rc == 0 )); then
      /bin/cmp -s -- "$BEFORE_LEDGER" "$AFTER_LEDGER"
      audit_rc=$?
    fi
    if (( audit_rc == 0 )); then
      /bin/cmp -s -- "$INITIAL_LEDGER" "$AFTER_LEDGER"
      audit_rc=$?
    fi
    if (( audit_rc == 0 )); then
      note "stable-initial/before/after experiment ledgers are byte-identical: ${INITIAL_LEDGER} ${BEFORE_LEDGER} ${AFTER_LEDGER}"
    else
      printf 'FATAL: stable-initial/before/after experiment ledgers differ or could not be written\n' >&2
      original_rc=97
    fi
  fi
  exit "$original_rc"
}
trap finish_audit EXIT

cd "$PROJECT_ROOT"

[[ -n "${SLURM_JOB_ID:-}" && "$SLURM_JOB_ID" =~ ^[0-9]+$ ]] || die "this runbook requires a numeric SLURM_JOB_ID"
readonly JOB_TAG="slurm-${SLURM_JOB_ID}"
readonly ULTRA_CANARY_ROOT="${SCRATCH_ROOT}/highambench_ultra_orchestration_canary_${JOB_TAG}"
readonly TOKEN_CANARY_ROOT="${SCRATCH_ROOT}/highambench_token_control_canary_${JOB_TAG}"
readonly DEADLINE_GATE_ROOT="${SCRATCH_ROOT}/highambench_zero_provider_deadline_gate_${JOB_TAG}"

for transient_root in "$ULTRA_CANARY_ROOT" "$TOKEN_CANARY_ROOT" "$DEADLINE_GATE_ROOT"; do
  [[ ! -e "$transient_root" && ! -L "$transient_root" ]] || die "job-specific root must be absent at job start: ${transient_root}"
done

# These two hashes are checked before invoking either interpreter or Codex.
# A mismatch cannot reach a provider call.
assert_sha256 "$PYTHON" "$EXPECTED_PYTHON_SHA256" "frozen /usr/bin/python3.10"
assert_sha256 "$CODEX" "$EXPECTED_CODEX_SHA256" "pinned Codex binary"

python_version=$("$PYTHON" --version 2>&1)
[[ "$python_version" == "Python ${EXPECTED_PYTHON_VERSION}" ]] || die "Python version mismatch: ${python_version}"
codex_version=$("$CODEX" --version 2>&1)
[[ "$codex_version" == *"codex-cli ${EXPECTED_CODEX_VERSION}"* ]] || die "Codex version mismatch: ${codex_version}"

assert_sha256 "$MANIFEST" "$EXPECTED_MANIFEST_SHA256" "central benchmark manifest"
assert_sha256 "$SPECIFICATION_PDF" "$EXPECTED_SPECIFICATION_SHA256" "HighamBench specification PDF"
assert_sha256 "$PAPER_PDF" "$EXPECTED_PAPER_SHA256" "${PAPER_ID} source PDF"

for required_path in \
  "$AUTH_FILE" "$OFFLINE_SHELL" "$LIBRARY_ROOT_FILE" "$RELEASE_MANIFEST" \
  "$ULTRA_TOOL" "$TOKEN_TOOL" "$MATRIX_TOOL" \
  "$CAMPAIGN_TOOL"; do
  require_regular_file "$required_path" "required frozen input"
done
for required_directory in \
  "$TOOLCHAIN_ROOT" "$PACKAGES_ROOT" "$PACKAGES_RUNTIME_ROOT" \
  "$SHARED_OLEAN_ROOT" "$LIBRARY_SOURCE" "$LIBRARY_OLEAN"; do
  [[ -d "$required_directory" && ! -L "$required_directory" ]] || die "required frozen directory is missing or unsafe: ${required_directory}"
done

# Assert that this script still matches the current parsers before any hosted
# request.  Canary artifact schemas/counts remain owned by their authenticators;
# the runbook deliberately does not hardcode them.
check_help_contract "$ULTRA_TOOL" --results-root --canary-time-limit-seconds --verify-only
check_help_contract "$TOKEN_TOOL" --results-root --canary-token-limit --canary-time-limit-seconds --verify-only
check_help_contract "$MATRIX_TOOL" \
  --allocation-end-epoch \
  --allocation-guard-seconds \
  --post-submission-validation-reserve-seconds \
  --stop-after-paper \
  --only-pair-id
check_help_contract "$CAMPAIGN_TOOL" --paper-id --target-pair-id initialize status verify recover-active recover-staging begin commit record-exit archive-failed

POST_SUBMISSION_VALIDATION_RESERVE_SECONDS=$("$PYTHON" - "$CONFIG" "$ENVIRONMENT" \
  "$EXPECTED_PYTHON_SHA256" "$EXPECTED_CODEX_SHA256" \
  "$EXPECTED_PYTHON_VERSION" "$EXPECTED_CODEX_VERSION" \
  "$EXPECTED_POST_SUBMISSION_VALIDATION_RESERVE_SECONDS" <<'PY'
import json
from pathlib import Path
import sys

config = json.loads(Path(sys.argv[1]).read_text(encoding="utf-8"))
environment = json.loads(Path(sys.argv[2]).read_text(encoding="utf-8"))
expected_python_sha, expected_codex_sha = sys.argv[3:5]
expected_python_version, expected_codex_version = sys.argv[5:7]
expected_validation_reserve = int(sys.argv[7])
frozen = config.get("frozen_environment", {})
runtime_python = environment.get("runtime", {}).get("python", {})
agent = environment.get("agent", {})
checks = {
    "config Python SHA-256": (frozen.get("python_binary_sha256"), expected_python_sha),
    "environment Python SHA-256": (runtime_python.get("binary_sha256"), expected_python_sha),
    "config Codex SHA-256": (frozen.get("agent_binary_sha256"), expected_codex_sha),
    "environment Codex SHA-256": (agent.get("binary_sha256"), expected_codex_sha),
    "config Python version": (frozen.get("python_version"), expected_python_version),
    "environment Python version": (runtime_python.get("version"), expected_python_version),
    "config Codex version": (frozen.get("agent_version"), expected_codex_version),
    "environment Codex version": (agent.get("version"), expected_codex_version),
    "config model": (frozen.get("model_version"), "gpt-5.6-sol"),
    "environment model": (agent.get("model"), "gpt-5.6-sol"),
    "config effort": (frozen.get("model_reasoning_effort"), "ultra"),
    "environment effort": (agent.get("reasoning_effort"), "ultra"),
}
for label, (actual, expected) in checks.items():
    if actual != expected:
        raise SystemExit(f"{label} mismatch: expected {expected!r}, got {actual!r}")
limits = config.get("limits", {})
if limits.get("wall_clock_seconds") != 1800:
    raise SystemExit("frozen wall-clock limit is not 1800")
if limits.get("total_model_tokens") != 5_000_000:
    raise SystemExit("frozen token limit is not 5000000")
if limits.get("prompt_startup_timeout_seconds") != 120:
    raise SystemExit("frozen prompt-startup timeout is not 120")
config_validation_reserve = limits.get("post_submission_validation_reserve_seconds")
environment_validation_reserve = environment.get("runtime", {}).get(
    "post_submission_validation_reserve_seconds"
)
if config_validation_reserve != environment_validation_reserve:
    raise SystemExit("config/environment post-submission validation reserves disagree")
if config_validation_reserve != expected_validation_reserve:
    raise SystemExit(
        "frozen post-submission validation reserve is not "
        f"{expected_validation_reserve}: {config_validation_reserve!r}"
    )
print(config_validation_reserve)
PY
)
readonly POST_SUBMISSION_VALIDATION_RESERVE_SECONDS
readonly MATRIX_PAIR_RESERVATION_SECONDS=$((
  2 * (
    RUN_LIMIT_SECONDS
    + 2 * PROMPT_STARTUP_SECONDS
    + POST_SUBMISSION_VALIDATION_RESERVE_SECONDS
  )
  + ALLOCATION_GUARD_SECONDS
))
[[ "$MATRIX_PAIR_RESERVATION_SECONDS" == 5418 ]] || die "derived untouched-pair reservation is not 5418 seconds"
note "frozen post-submission validation reserve: ${POST_SUBMISSION_VALIDATION_RESERVE_SECONDS}s; untouched pair reservation: ${MATRIX_PAIR_RESERVATION_SECONDS}s"

# Authenticate the scheduler's actual CPU/RAM/GPU=0 grant, then resolve EndTime
# and pass its epoch explicitly to the real matrix.  SLURM_JOB_END_TIME, when
# supplied, must agree exactly.
job_record=$(/bin/scontrol show job -o "$SLURM_JOB_ID")
allocation_facts=$("$PYTHON" - \
  "$SLURM_JOB_ID" \
  "${SLURM_JOB_END_TIME:-}" \
  "${SLURM_JOB_NODELIST:-}" \
  "${SLURMD_NODENAME:-}" \
  "$VETTED_NODES_CSV" \
  "$job_record" <<'PY'
from datetime import datetime, timezone
import os
import re
import socket
import sys

(
    job_id,
    environment_epoch,
    environment_nodelist,
    slurmd_nodename,
    vetted_nodes_csv,
    record,
) = sys.argv[1:7]
vetted_nodes = vetted_nodes_csv.split(",")
if vetted_nodes != ["watgpu108", "watgpu508", "watgpu808"]:
    raise SystemExit("launcher vetted-node allowlist drifted")

def field(name: str) -> str:
    match = re.search(rf"(?:^| ){re.escape(name)}=([^ ]+)(?: |$)", record)
    if match is None:
        raise SystemExit(f"Slurm record has no {name} field")
    return match.group(1)

wanted = {
    "JobId": job_id,
    "Account": "kfountou_group",
    "NumNodes": "1",
    "NumCPUs": "4",
    "NumTasks": "1",
    "CPUs/Task": "4",
    "TimeLimit": "04:00:00",
}
for name, expected in wanted.items():
    actual = field(name)
    if actual != expected:
        raise SystemExit(f"Slurm {name} mismatch: expected {expected!r}, got {actual!r}")
partition = field("Partition")
if partition not in {"ALL", "SCHOOL", "KFOUNTOU"}:
    raise SystemExit(
        "Slurm partition is outside the exact approved forced-sharing allowlist: "
        f"{partition!r}"
    )
allocation_node = field("NodeList")
if allocation_node not in vetted_nodes:
    raise SystemExit(
        "Slurm allocated a node outside the exact vetted singleton allowlist: "
        f"{allocation_node!r}"
    )
if partition == "KFOUNTOU" and allocation_node != "watgpu108":
    raise SystemExit("KFOUNTOU allocation must resolve to its sole vetted node watgpu108")
if environment_nodelist != allocation_node:
    raise SystemExit(
        "SLURM_JOB_NODELIST disagrees with the authenticated Slurm allocation: "
        f"{environment_nodelist!r} != {allocation_node!r}"
    )
if slurmd_nodename != allocation_node:
    raise SystemExit(
        "SLURMD_NODENAME disagrees with the authenticated Slurm allocation: "
        f"{slurmd_nodename!r} != {allocation_node!r}"
    )
hostname = socket.gethostname().split(".", 1)[0]
if hostname != allocation_node:
    raise SystemExit(
        "runtime hostname disagrees with the authenticated Slurm allocation: "
        f"{hostname!r} != {allocation_node!r}"
    )
alloc_tres = field("AllocTRES")
allocations = {}
for token in alloc_tres.split(","):
    if not token or token.count("=") != 1:
        raise SystemExit(f"Slurm AllocTRES contains a malformed token: {alloc_tres!r}")
    key, value = token.split("=", 1)
    if not key or not value or key in allocations:
        raise SystemExit(f"Slurm AllocTRES is not an exact key/value map: {alloc_tres!r}")
    allocations[key] = value
if allocations.get("mem") != "32G":
    raise SystemExit(f"Slurm AllocTRES does not contain exact mem=32G: {alloc_tres}")
for key, raw_count in allocations.items():
    lowered_key = key.lower()
    if lowered_key.startswith("gres/gpu") and not key.startswith("gres/gpu"):
        raise SystemExit(f"Slurm AllocTRES contains a malformed GPU TRES key: {key!r}")
    if key.startswith("gres/gpu"):
        if re.fullmatch(r"gres/gpu(?::[A-Za-z0-9][A-Za-z0-9_.+-]*)?", key) is None:
            raise SystemExit(f"Slurm AllocTRES contains a malformed GPU TRES key: {key!r}")
        if re.fullmatch(r"(?:0|[1-9][0-9]*)", raw_count) is None or int(raw_count) != 0:
            raise SystemExit(
                f"Slurm AllocTRES allocated a nonzero or malformed GPU TRES: "
                f"{key}={raw_count} in {alloc_tres!r}"
            )

gpu_environment = {
    name: os.environ[name] if name in os.environ else None
    for name in ("SLURM_GPUS_ON_NODE", "SLURM_JOB_GPUS", "CUDA_VISIBLE_DEVICES")
}
if gpu_environment["SLURM_GPUS_ON_NODE"] not in (None, "", "0"):
    raise SystemExit(
        "SLURM_GPUS_ON_NODE reports a nonzero or malformed GPU allocation: "
        f"{gpu_environment['SLURM_GPUS_ON_NODE']!r}"
    )
for name in ("SLURM_JOB_GPUS", "CUDA_VISIBLE_DEVICES"):
    if gpu_environment[name] not in (None, ""):
        raise SystemExit(
            f"{name} exposes a GPU device index despite gpu:0: "
            f"{gpu_environment[name]!r}"
        )

end_text = field("EndTime")
try:
    parsed = datetime.fromisoformat(end_text)
except ValueError as error:
    raise SystemExit(f"cannot parse Slurm EndTime {end_text!r}") from error
if parsed.tzinfo is None:
    parsed = parsed.replace(tzinfo=timezone.utc)
epoch = int(parsed.timestamp())
if epoch <= 0:
    raise SystemExit("Slurm EndTime is not a positive epoch")
if environment_epoch:
    try:
        supplied = int(environment_epoch)
    except ValueError as error:
        raise SystemExit("SLURM_JOB_END_TIME is not an integer") from error
    if supplied != epoch:
        raise SystemExit(
            f"SLURM_JOB_END_TIME {supplied} disagrees with scontrol EndTime epoch {epoch}"
        )
print(f"{allocation_node}\t{epoch}")
PY
)
IFS=$'\t' read -r ALLOCATION_NODE ALLOCATION_END_EPOCH <<< "$allocation_facts"
readonly ALLOCATION_NODE ALLOCATION_END_EPOCH
[[ "$ALLOCATION_NODE" == watgpu108 || "$ALLOCATION_NODE" == watgpu508 || "$ALLOCATION_NODE" == watgpu808 ]] || die "authenticated allocation node is outside the vetted allowlist: ${ALLOCATION_NODE}"
[[ "$ALLOCATION_END_EPOCH" =~ ^[0-9]+$ ]] || die "authenticated allocation end epoch is malformed: ${ALLOCATION_END_EPOCH}"
(( ALLOCATION_END_EPOCH > $(/bin/date -u +%s) )) || die "actual Slurm allocation end is not in the future"
note "hardware policy ${HARDWARE_MATCHING_POLICY}; authenticated singleton node ${ALLOCATION_NODE}; allocation end epoch ${ALLOCATION_END_EPOCH}"

result_root_state=$(initialize_result_root)
[[ "$result_root_state" == created || "$result_root_state" == existing ]] || die "invalid stable result-root state: ${result_root_state}"
# Hold one nonblocking kernel lock for this launcher's entire lifetime.  This
# prevents a queued/duplicate job from recovering an attempt that is still
# being mutated by the owning job.  The kernel releases the lock on job death.
exec 9>"${RESULT_ROOT}/.launcher.lock"
/usr/bin/flock -n 9 || die "another ${PAIR_ID} shard launcher currently owns ${RESULT_ROOT}"
# Atomic index writes can leave one exact regular top-level temporary if a job
# is killed before rename.  Only after taking the whole-launcher lock, preserve
# those bytes (and a first-ever unsealed initial ledger) in runbook_audit so the
# stable root is reusable without discarding crash evidence.
"$PYTHON" "$CAMPAIGN_TOOL" "${CAMPAIGN_ARGS[@]}" \
  recover-staging \
  --slurm-job-id "$SLURM_JOB_ID" >/dev/null
/bin/mkdir -p -- "${RESULT_ROOT}/runbook_audit"
readonly INITIAL_LEDGER="${RESULT_ROOT}/runbook_audit/benchmark_task_checksums.initial.sha256"
readonly BEFORE_LEDGER="${RESULT_ROOT}/runbook_audit/benchmark_task_checksums.before.${JOB_TAG}.sha256"
readonly AFTER_LEDGER="${RESULT_ROOT}/runbook_audit/benchmark_task_checksums.after.${JOB_TAG}.sha256"
if [[ "$result_root_state" == created || ! -e "$INITIAL_LEDGER" ]]; then
  if [[ "$result_root_state" == existing ]]; then
    "$PYTHON" - "$RESULT_ROOT" "$JOB_TAG" <<'PY'
from pathlib import Path
import re
import sys

root = Path(sys.argv[1])
job_tag = sys.argv[2]
if (root / "campaign_index.json").exists() or (root / "campaign_index.json").is_symlink():
    raise SystemExit("campaign index exists without its stable initial ledger")
attempts = root / "pair_attempts"
if attempts.exists() and (attempts.is_symlink() or not attempts.is_dir() or any(attempts.rglob("*"))):
    raise SystemExit("pair-attempt state exists without its stable initial ledger")
audit = root / "runbook_audit"
allowed = {
    f"benchmark_task_checksums.before.{job_tag}.sha256",
    f"benchmark_task_checksums.after.{job_tag}.sha256",
}
preserved = (
    re.compile(
        r"campaign_index_write\.interrupted-pid-[1-9][0-9]*\."
        r"recovered-slurm-[1-9][0-9]*\.json"
    ),
    re.compile(
        r"benchmark_task_checksums\.initial\.interrupted\."
        r"recovered-slurm-[1-9][0-9]*\.sha256"
    ),
)
if audit.is_symlink() or not audit.is_dir() or any(
    path.is_symlink()
    or not path.is_file()
    or (
        path.name not in allowed
        and not any(pattern.fullmatch(path.name) for pattern in preserved)
    )
    for path in audit.iterdir()
):
    raise SystemExit("runbook audit state exists without its stable initial ledger")
PY
  fi
  make_task_ledger "$INITIAL_LEDGER"
  /bin/chmod 0444 -- "$INITIAL_LEDGER"
  note "sealed write-once initial experiment ledger: ${INITIAL_LEDGER}"
else
  [[ -f "$INITIAL_LEDGER" && ! -L "$INITIAL_LEDGER" ]] || die "resumable result root lacks its stable initial experiment ledger"
fi
[[ "$(/bin/stat -c '%a' -- "$INITIAL_LEDGER")" == 444 ]] || die "stable initial experiment ledger is not sealed mode 0444"
assert_task_ledger "$INITIAL_LEDGER"
make_task_ledger "$BEFORE_LEDGER"
AUDIT_ACTIVE=1
assert_experiment_snapshot
note "sealed before-run experiment ledger and matched stable baseline: ${BEFORE_LEDGER}"

COMMON_FROZEN_ARGS=(
  --benchmark-root "$BENCHMARK_ROOT"
  --project-root "$PROJECT_ROOT"
  --codex "$CODEX"
  --auth-file "$AUTH_FILE"
  --offline-shell "$OFFLINE_SHELL"
  --toolchain-root "$TOOLCHAIN_ROOT"
  --packages-root "$PACKAGES_ROOT"
  --packages-runtime-root "$PACKAGES_RUNTIME_ROOT"
  --shared-olean-root "$SHARED_OLEAN_ROOT"
  --library-source "$LIBRARY_SOURCE"
  --library-root-file "$LIBRARY_ROOT_FILE"
  --library-olean "$LIBRARY_OLEAN"
  --release-manifest "$RELEASE_MANIFEST"
  --agent-id codex-cli
  --agent-version "$EXPECTED_CODEX_VERSION"
  --model "$MODEL"
  --reasoning-effort "$REASONING_EFFORT"
  --time-limit-seconds "$RUN_LIMIT_SECONDS"
  --token-limit "$TOKEN_LIMIT"
  --prompt-startup-timeout-seconds "$PROMPT_STARTUP_SECONDS"
  --post-submission-validation-reserve-seconds "$POST_SUBMISSION_VALIDATION_RESERVE_SECONDS"
  --agent-network-verified
)

ultra_status=$(descriptor_status \
  ultra_orchestration_canary \
  paper_bencmark/highambench/metadata/evidence/ultra_orchestration_live_canary.json)
token_status=$(descriptor_status \
  token_control_canary \
  paper_bencmark/highambench/metadata/evidence/token_control_live_canary.json)
note "initial canary descriptors: Ultra=${ultra_status}, token=${token_status}"

# Pair shards may run concurrently, so none may mutate global canary metadata.
# A separate serial priming job must promote both attestations first.
[[ "$ultra_status" == passed && "$token_status" == passed ]] || \
  die "pair shards require both frozen canary descriptors already passed"
note "both canary descriptors passed; authenticating frozen evidence only"
"$PYTHON" "$ULTRA_TOOL" \
  "${COMMON_FROZEN_ARGS[@]}" \
  --results-root "$ULTRA_CANARY_ROOT" \
  --verify-only "$ULTRA_EVIDENCE"

"$PYTHON" "$TOKEN_TOOL" \
  "${COMMON_FROZEN_ARGS[@]}" \
  --results-root "$TOKEN_CANARY_ROOT" \
  --verify-only "$TOKEN_EVIDENCE"

assert_experiment_snapshot

# Rehearse ordinary matrix startup against an already-expired explicit
# deadline.  The only accepted result is exit 75 plus a deadline status and no
# attempt/final artifacts.  This exercises the current, post-promotion frozen
# snapshot and allocation gate without contacting the provider.
note "running zero-provider expired-deadline matrix gate"
set +e
"$PYTHON" "$MATRIX_TOOL" \
  "${COMMON_FROZEN_ARGS[@]}" \
  --results-root "$DEADLINE_GATE_ROOT" \
  --only-pair-id "$PAIR_ID" \
  --allocation-end-epoch 1 \
  --allocation-guard-seconds "$ALLOCATION_GUARD_SECONDS"
deadline_gate_rc=$?
set -e
[[ "$deadline_gate_rc" == 75 ]] || die "expired-deadline gate exited ${deadline_gate_rc}, expected 75"
"$PYTHON" - \
  "$DEADLINE_GATE_ROOT" \
  "$MATRIX_PAIR_RESERVATION_SECONDS" \
  "$POST_SUBMISSION_VALIDATION_RESERVE_SECONDS" <<'PY'
import json
from pathlib import Path
import sys

root = Path(sys.argv[1])
expected_pair_reservation = float(sys.argv[2])
expected_validation_reserve = float(sys.argv[3])
status = json.loads((root / "last_chunk_status.json").read_text(encoding="utf-8"))
if status.get("status") != "stopped_before_allocation_deadline":
    raise SystemExit(f"expired-deadline gate has wrong status: {status.get('status')!r}")
if status.get("allocation_end_epoch") != 1:
    raise SystemExit("expired-deadline gate did not bind epoch 1")
if status.get("unfinished_runs_in_next_pair") != 2:
    raise SystemExit("expired-deadline gate did not reserve an untouched two-run pair")
if status.get("required_seconds") != expected_pair_reservation:
    raise SystemExit(
        "expired-deadline gate reservation disagrees with frozen launcher arithmetic: "
        f"{status.get('required_seconds')!r} != {expected_pair_reservation!r}"
    )
if status.get("post_submission_validation_reserve_seconds") != expected_validation_reserve:
    raise SystemExit("expired-deadline gate did not record the frozen post-submission reserve")
for directory_name in ("records", "attempts"):
    directory = root / directory_name
    if any(path.is_file() or path.is_symlink() for path in directory.rglob("*")):
        raise SystemExit(f"expired-deadline gate unexpectedly created {directory_name} artifacts")
runs = root / "runs.jsonl"
if runs.exists() and runs.read_text(encoding="utf-8").strip():
    raise SystemExit("expired-deadline gate unexpectedly recorded a hosted run")
PY
note "zero-provider expired-deadline matrix gate passed"

assert_experiment_snapshot
note "initializing/authenticating the isolated ${PAIR_ID} atomic-pair shard"
"$PYTHON" "$CAMPAIGN_TOOL" "${CAMPAIGN_ARGS[@]}" \
  initialize >/dev/null

campaign_state=$("$PYTHON" "$CAMPAIGN_TOOL" "${CAMPAIGN_ARGS[@]}" \
  status)
if [[ "$("$PYTHON" -c 'import json,sys; print("yes" if json.load(sys.stdin).get("active_pair_attempt") is not None else "no")' <<< "$campaign_state")" == yes ]]; then
  note "recovering a path-stable pair attempt left active by an earlier job"
  "$PYTHON" "$CAMPAIGN_TOOL" "${CAMPAIGN_ARGS[@]}" \
    recover-active >/dev/null
fi

while true; do
  campaign_state=$("$PYTHON" "$CAMPAIGN_TOOL" "${CAMPAIGN_ARGS[@]}" \
    status)
  pair_id=$("$PYTHON" -c 'import json,sys; print(json.load(sys.stdin).get("next_pair_id") or "")' <<< "$campaign_state")
  [[ -n "$pair_id" ]] || break

  remaining=$(remaining_allocation_seconds)
  if (( remaining < MATRIX_PAIR_RESERVATION_SECONDS )); then
    note "clean campaign checkpoint: ${remaining}s remain, below the ${MATRIX_PAIR_RESERVATION_SECONDS}s untouched-pair reservation; next pair ${pair_id}"
    exit 75
  fi

  pair_root=$("$PYTHON" "$CAMPAIGN_TOOL" "${CAMPAIGN_ARGS[@]}" \
    begin \
    --pair-id "$pair_id" \
    --slurm-job-id "$SLURM_JOB_ID" \
    --allocation-node "$ALLOCATION_NODE")
  note "running atomic pair ${pair_id} at permanent root ${pair_root}"
  set +e
  "$PYTHON" "$MATRIX_TOOL" \
    "${COMMON_FROZEN_ARGS[@]}" \
    --results-root "$pair_root" \
    --only-pair-id "$pair_id" \
    --allocation-end-epoch "$ALLOCATION_END_EPOCH" \
    --allocation-guard-seconds "$ALLOCATION_GUARD_SECONDS"
  matrix_rc=$?
  set -e
  assert_experiment_snapshot
  "$PYTHON" "$CAMPAIGN_TOOL" "${CAMPAIGN_ARGS[@]}" \
    record-exit \
    --pair-id "$pair_id" \
    --slurm-job-id "$SLURM_JOB_ID" \
    --matrix-exit-code "$matrix_rc" >/dev/null

  if [[ "$matrix_rc" == 0 ]]; then
    "$PYTHON" "$CAMPAIGN_TOOL" "${CAMPAIGN_ARGS[@]}" \
      commit \
      --pair-id "$pair_id" \
      --slurm-job-id "$SLURM_JOB_ID" >/dev/null
    note "committed complete atomic pair ${pair_id}; its permanent root will never move"
    continue
  fi

  if [[ "$matrix_rc" == 75 ]]; then
    "$PYTHON" "$CAMPAIGN_TOOL" "${CAMPAIGN_ARGS[@]}" \
      archive-failed \
      --pair-id "$pair_id" \
      --slurm-job-id "$SLURM_JOB_ID" \
      --matrix-exit-code "$matrix_rc" \
      --outcome allocation_deadline_before_pair >/dev/null
    note "archived authenticated zero-work deadline attempt for ${pair_id}; resubmit the script"
    exit 75
  fi

  "$PYTHON" "$CAMPAIGN_TOOL" "${CAMPAIGN_ARGS[@]}" \
    archive-failed \
    --pair-id "$pair_id" \
    --slurm-job-id "$SLURM_JOB_ID" \
    --matrix-exit-code "$matrix_rc" \
    --outcome matrix_error >/dev/null
  note "archived failed atomic pair attempt ${pair_id}; a later job will rerun both N and L"
  exit 2
done

"$PYTHON" "$CAMPAIGN_TOOL" "${CAMPAIGN_ARGS[@]}" \
  verify >/dev/null
note "${PAIR_ID} committed; shard manager authenticated exactly two final records"
assert_experiment_snapshot
note "${PAIR_ID} actual Ultra measurement complete; aggregation/reporting deferred; no public release"
exit 0
