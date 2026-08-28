#!/usr/bin/env bash
# Serial, non-scored bootstrap for the frozen HighamBench live canaries.
#
# Run once after a snapshot refresh and make every pair-shard job depend on its
# successful completion.  This job holds the sole global bootstrap lock,
# promotes Ultra before Token, supports safe retry after a partial promotion,
# and never invokes the benchmark matrix or creates a scored pair root.

#SBATCH --job-name=highambench-canary-bootstrap
#SBATCH --account=kfountou_group
#SBATCH --partition=KFOUNTOU
#SBATCH --nodelist=watgpu108
#SBATCH --nodes=1
#SBATCH --ntasks=1
#SBATCH --cpus-per-task=4
#SBATCH --sockets-per-node=1
#SBATCH --cores-per-socket=2
#SBATCH --threads-per-core=2
#SBATCH --mem=32G
#SBATCH --gres=gpu:0
#SBATCH --time=03:00:00
#SBATCH --chdir=/u501/m2fetrat/MyCodes/lean-fp-analysis-main
#SBATCH --output=/u501/m2fetrat/MyCodes/lean-fp-analysis-main/paper_bencmark/scratch_pad/slurm-%x-%j.log

set -Eeuo pipefail
umask 077
export PYTHONNOUSERSITE=1
export TZ=UTC

readonly PROJECT_ROOT="/u501/m2fetrat/MyCodes/lean-fp-analysis-main"
readonly BENCHMARK_ROOT="${PROJECT_ROOT}/paper_bencmark/highambench"
readonly SCRATCH_ROOT="${PROJECT_ROOT}/paper_bencmark/scratch_pad"
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
readonly PROMOTE_TOOL="${BENCHMARK_ROOT}/tools/promote_live_canary.py"
readonly CONFIG="${BENCHMARK_ROOT}/metadata/config.json"
readonly ENVIRONMENT="${BENCHMARK_ROOT}/metadata/environment.json"
readonly ULTRA_EVIDENCE="${BENCHMARK_ROOT}/metadata/evidence/ultra_orchestration_live_canary.json"
readonly TOKEN_EVIDENCE="${BENCHMARK_ROOT}/metadata/evidence/token_control_live_canary.json"

readonly EXPECTED_MANIFEST_SHA256="5a1eeb84c4214a3dd95386a912047bc6e2914621e65439e1d694aa5892ad408b"
readonly EXPECTED_PYTHON_SHA256="d6bca2b84e73c7775a0dd5e6a76899cfe4ee62863d7c8f88513811d1fda23f49"
readonly EXPECTED_CODEX_SHA256="d13cfcda217421fb20d0aa6aa80819a62483a72e4a7fd52743675ca20d86377c"
readonly EXPECTED_PYTHON_VERSION="3.10.12"
readonly EXPECTED_CODEX_VERSION="0.146.0-alpha.9.2"
readonly MODEL="gpt-5.6-sol"
readonly REASONING_EFFORT="ultra"
readonly RUN_LIMIT_SECONDS=1800
readonly TOKEN_LIMIT=5000000
readonly PROMPT_STARTUP_SECONDS=120
readonly POST_SUBMISSION_VALIDATION_RESERVE_SECONDS=369
readonly CANARY_TIME_LIMIT_SECONDS=300
readonly TOKEN_CANARY_LIMIT=180000
readonly BEFORE_ULTRA_MINIMUM_SECONDS=1800
readonly BEFORE_TOKEN_MINIMUM_SECONDS=900

die() {
  printf 'FATAL: %s\n' "$*" >&2
  exit 2
}

note() {
  printf '[%s] %s\n' "$(/bin/date -u +'%Y-%m-%dT%H:%M:%SZ')" "$*"
}

sha256_of() {
  /bin/sha256sum -- "$1" | /bin/awk '{print $1}'
}

require_regular_file() {
  [[ -f "$1" && ! -L "$1" ]] || die "$2 is missing, linked, or not regular: $1"
}

assert_sha256() {
  require_regular_file "$1" "$3"
  local actual
  actual=$(sha256_of "$1")
  [[ "$actual" == "$2" ]] || die "$3 SHA-256 mismatch: expected $2, got ${actual}"
}

check_help_contract() {
  local tool=$1
  shift
  local help_text option
  help_text=$("$PYTHON" "$tool" --help)
  for option in "$@"; do
    [[ "$help_text" == *"${option}"* ]] || die "parser drift: $(basename "$tool") lacks ${option}"
  done
}

descriptor_status() {
  "$PYTHON" - "$CONFIG" "$ENVIRONMENT" "$PROJECT_ROOT" "$1" "$2" <<'PY'
import hashlib
import json
from pathlib import Path
import re
import sys

config = json.loads(Path(sys.argv[1]).read_text(encoding="utf-8"))
environment = json.loads(Path(sys.argv[2]).read_text(encoding="utf-8"))
project = Path(sys.argv[3]).resolve()
key, expected_path = sys.argv[4:6]
left = config.get("frozen_environment", {}).get(key)
right = environment.get(key)
if left != right or not isinstance(left, dict):
    raise SystemExit(f"{key} descriptors disagree")
if set(left) != {"path", "sha256", "status"} or left.get("path") != expected_path:
    raise SystemExit(f"{key} descriptor identity is not exact")
if left.get("status") not in {"replacement_required", "passed"}:
    raise SystemExit(f"{key} descriptor status is invalid")
digest = left.get("sha256")
if not isinstance(digest, str) or re.fullmatch(r"[0-9a-f]{64}", digest) is None:
    raise SystemExit(f"{key} descriptor digest is invalid")
evidence = (project / expected_path).resolve()
try:
    evidence.relative_to(project)
except ValueError as error:
    raise SystemExit(f"{key} evidence escapes project") from error
if evidence.is_symlink() or not evidence.is_file():
    raise SystemExit(f"{key} evidence is missing or unsafe")
if hashlib.sha256(evidence.read_bytes()).hexdigest() != digest:
    raise SystemExit(f"{key} evidence digest is stale")
print(left["status"])
PY
}

immutable_ledger() {
  local mode=$1
  local ledger=$2
  "$PYTHON" - "$PROJECT_ROOT" "$ledger" "$mode" "$EXPECTED_MANIFEST_SHA256" <<'PY'
import hashlib
import json
import os
from pathlib import Path
import re
import sys

project = Path(sys.argv[1]).resolve()
ledger = Path(sys.argv[2])
mode = sys.argv[3]
expected_manifest = sys.argv[4]
benchmark = project / "paper_bencmark/highambench"
release_path = benchmark / "metadata/release_files.json"
release = json.loads(release_path.read_text(encoding="utf-8"))
entries = release.get("files")
if not isinstance(entries, list) or not entries:
    raise SystemExit("release manifest file list is missing")
mutable = {
    "metadata/config.json",
    "metadata/environment.json",
    "metadata/release_files.json",
    "metadata/evidence/ultra_orchestration_live_canary.json",
    "metadata/evidence/token_control_live_canary.json",
}
fixed = set()
seen = set()
for entry in entries:
    if not isinstance(entry, dict) or set(entry) != {"path", "sha256", "bytes"}:
        raise SystemExit("release-manifest entry fields are not exact")
    relative = entry.get("path")
    digest = entry.get("sha256")
    size = entry.get("bytes")
    if (
        not isinstance(relative, str)
        or not relative
        or relative in seen
        or Path(relative).is_absolute()
        or any(part in {"", ".", ".."} for part in Path(relative).parts)
        or not isinstance(digest, str)
        or re.fullmatch(r"[0-9a-f]{64}", digest) is None
        or isinstance(size, bool)
        or not isinstance(size, int)
        or size < 0
    ):
        raise SystemExit("release-manifest entry is malformed")
    seen.add(relative)
    path = (benchmark / relative).resolve()
    try:
        path.relative_to(benchmark.resolve())
    except ValueError as error:
        raise SystemExit("release file escapes benchmark root") from error
    if path.is_symlink() or not path.is_file():
        raise SystemExit(f"release file is missing or unsafe: {path}")
    payload = path.read_bytes()
    if len(payload) != size or hashlib.sha256(payload).hexdigest() != digest:
        raise SystemExit(f"release file disagrees with release manifest: {relative}")
    if relative not in mutable:
        fixed.add(path)

extras = {
    project / "paper_bencmark/scratch_pad/run_highambench_canary_bootstrap_actual_ultra.sh",
    project / "paper_bencmark/scratch_pad/run_highambench_pair_shard_actual_ultra.sh",
    project / "paper_bencmark/scratch_pad/manage_highambench_pair_shard.py",
    project / "paper_bencmark/scratch_pad/aggregate_highambench_pair_shards.py",
    project / "paper_bencmark/scratch_pad/HighamBench_Simple_Two_Condition_Specification.pdf",
}
for prefix in ("P05_", "P11_", "P15_", "P20_"):
    matches = list((project / "paper_bencmark/reference_papers").glob(prefix + "*.pdf"))
    if len(matches) != 1:
        raise SystemExit(f"expected exactly one source PDF for {prefix[:-1]}")
    extras.add(matches[0])
fixed.update(extras)

lines = []
for path in sorted(fixed, key=lambda item: item.relative_to(project).as_posix()):
    if path.is_symlink() or not path.is_file():
        raise SystemExit(f"immutable bootstrap input is missing or unsafe: {path}")
    relative = path.relative_to(project).as_posix()
    digest = hashlib.sha256(path.read_bytes()).hexdigest()
    lines.append(f"{digest}  {relative}\n")
    if relative == "paper_bencmark/highambench/metadata/manifest.json" and digest != expected_manifest:
        raise SystemExit("central manifest SHA-256 drifted")
payload = "".join(lines)
if mode == "create":
    fd = os.open(ledger, os.O_WRONLY | os.O_CREAT | os.O_EXCL, 0o600)
    with os.fdopen(fd, "w", encoding="utf-8", newline="") as stream:
        stream.write(payload)
        stream.flush()
        os.fsync(stream.fileno())
elif mode == "verify":
    if ledger.is_symlink() or not ledger.is_file() or ledger.read_text(encoding="utf-8") != payload:
        raise SystemExit("immutable release/task/bootstrap surface changed")
else:
    raise SystemExit("invalid ledger operation")
PY
}

verify_metadata_parity() {
  "$PYTHON" - "$BENCHMARK_ROOT" <<'PY'
import hashlib
import json
from pathlib import Path
import sys

root = Path(sys.argv[1]).resolve()
sys.path.insert(0, str(root / "tools"))
import run_matrix

config = json.loads((root / "metadata/config.json").read_text(encoding="utf-8"))
environment = json.loads((root / "metadata/environment.json").read_text(encoding="utf-8"))
frozen = config.get("frozen_environment")
if not isinstance(frozen, dict):
    raise SystemExit("config frozen environment is missing")
bundle = run_matrix.environment_bundle_digest(config, environment)
if frozen.get("environment_bundle_sha256") != bundle or environment.get("environment_bundle_sha256") != bundle:
    raise SystemExit("environment bundle digest is stale")
environment_id = environment.get("environment_id")
if frozen.get("environment_id") != environment_id or not isinstance(environment_id, str) or not environment_id.endswith("-" + bundle[:16]):
    raise SystemExit("environment ID is stale")
release_digest = hashlib.sha256((root / "metadata/release_files.json").read_bytes()).hexdigest()
if frozen.get("release_manifest_sha256") != release_digest or environment.get("release_manifest_sha256") != release_digest:
    raise SystemExit("release-manifest binding is stale")
print(f"{environment_id} {bundle} {release_digest}")
PY
}

remaining_allocation_seconds() {
  printf '%s\n' "$((ALLOCATION_END_EPOCH - $(/bin/date -u +%s)))"
}

require_remaining_seconds() {
  local remaining
  remaining=$(remaining_allocation_seconds)
  (( remaining >= $2 )) || die "refusing $1: ${remaining}s remain, at least $2 required"
  note "$1: ${remaining}s remain"
}

cd "$PROJECT_ROOT"
[[ -n "${SLURM_JOB_ID:-}" && "$SLURM_JOB_ID" =~ ^[1-9][0-9]*$ ]] || die "bootstrap requires a numeric nonzero SLURM_JOB_ID"

readonly GLOBAL_LOCK="${SCRATCH_ROOT}/.highambench-canary-bootstrap.lock"
[[ ! -L "$GLOBAL_LOCK" ]] || die "global bootstrap lock is a symlink"
exec 8>>"$GLOBAL_LOCK"
[[ -f "$GLOBAL_LOCK" && ! -L "$GLOBAL_LOCK" && "$GLOBAL_LOCK" -ef /proc/self/fd/8 ]] || die "global bootstrap lock identity is unsafe"
/usr/bin/flock -n 8 || die "another canary bootstrap owns the global lock"

readonly BOOTSTRAP_ROOT="${SCRATCH_ROOT}/highambench_canary_bootstrap_slurm-${SLURM_JOB_ID}"
readonly ULTRA_CANARY_ROOT="${BOOTSTRAP_ROOT}/ultra"
readonly TOKEN_CANARY_ROOT="${BOOTSTRAP_ROOT}/token"
readonly IMMUTABLE_LEDGER="${BOOTSTRAP_ROOT}/immutable_inputs.sha256"
[[ ! -e "$BOOTSTRAP_ROOT" && ! -L "$BOOTSTRAP_ROOT" ]] || die "job-specific bootstrap root already exists: ${BOOTSTRAP_ROOT}"
/bin/mkdir -- "$BOOTSTRAP_ROOT"

assert_sha256 "$PYTHON" "$EXPECTED_PYTHON_SHA256" "frozen Python"
assert_sha256 "$CODEX" "$EXPECTED_CODEX_SHA256" "pinned Codex"
[[ "$("$PYTHON" --version 2>&1)" == "Python ${EXPECTED_PYTHON_VERSION}" ]] || die "Python version drifted"
[[ "$("$CODEX" --version 2>&1)" == *"codex-cli ${EXPECTED_CODEX_VERSION}"* ]] || die "Codex version drifted"

for path in "$AUTH_FILE" "$OFFLINE_SHELL" "$LIBRARY_ROOT_FILE" "$RELEASE_MANIFEST" "$ULTRA_TOOL" "$TOKEN_TOOL" "$PROMOTE_TOOL" "$CONFIG" "$ENVIRONMENT" "$ULTRA_EVIDENCE" "$TOKEN_EVIDENCE"; do
  require_regular_file "$path" "required bootstrap input"
done
for directory in "$TOOLCHAIN_ROOT" "$PACKAGES_ROOT" "$PACKAGES_RUNTIME_ROOT" "$SHARED_OLEAN_ROOT" "$LIBRARY_SOURCE" "$LIBRARY_OLEAN"; do
  [[ -d "$directory" && ! -L "$directory" ]] || die "required bootstrap directory is missing or unsafe: ${directory}"
done
check_help_contract "$ULTRA_TOOL" --results-root --canary-time-limit-seconds --verify-only
check_help_contract "$TOKEN_TOOL" --results-root --canary-token-limit --canary-time-limit-seconds --verify-only
check_help_contract "$PROMOTE_TOOL" --ultra-orchestration-attestation --token-control-attestation

job_record=$(/bin/scontrol show job -o "$SLURM_JOB_ID")
ALLOCATION_END_EPOCH=$("$PYTHON" - "$SLURM_JOB_ID" "${SLURM_JOB_NODELIST:-}" "${SLURMD_NODENAME:-}" "$job_record" <<'PY'
from datetime import datetime, timezone
import os
import re
import socket
import sys

job_id, environment_node, slurmd_node, record = sys.argv[1:5]
def field(name):
    match = re.search(rf"(?:^| ){re.escape(name)}=([^ ]+)(?: |$)", record)
    if match is None:
        raise SystemExit(f"Slurm record lacks {name}")
    return match.group(1)
for name, expected in {
    "JobId": job_id,
    "Account": "kfountou_group",
    "Partition": "KFOUNTOU",
    "NodeList": "watgpu108",
    "NumNodes": "1",
    "NumCPUs": "4",
    "NumTasks": "1",
    "CPUs/Task": "4",
    "TimeLimit": "03:00:00",
}.items():
    if field(name) != expected:
        raise SystemExit(f"Slurm {name} drifted")
if environment_node != "watgpu108" or slurmd_node != "watgpu108" or socket.gethostname().split(".", 1)[0] != "watgpu108":
    raise SystemExit("runtime node does not match authenticated allocation")
allocations = dict(token.split("=", 1) for token in field("AllocTRES").split(",") if token.count("=") == 1)
if allocations.get("mem") != "32G":
    raise SystemExit("Slurm memory grant drifted")
for key, value in allocations.items():
    if key.startswith("gres/gpu") and (not value.isdigit() or int(value) != 0):
        raise SystemExit("Slurm allocated a GPU")
for name in ("SLURM_JOB_GPUS", "CUDA_VISIBLE_DEVICES"):
    if os.environ.get(name) not in (None, ""):
        raise SystemExit(f"{name} exposes a GPU")
end = datetime.fromisoformat(field("EndTime"))
if end.tzinfo is None:
    end = end.replace(tzinfo=timezone.utc)
print(int(end.timestamp()))
PY
)
readonly ALLOCATION_END_EPOCH
[[ "$ALLOCATION_END_EPOCH" =~ ^[1-9][0-9]*$ ]] || die "authenticated allocation end is malformed"
(( ALLOCATION_END_EPOCH > $(/bin/date -u +%s) )) || die "allocation already expired"

immutable_ledger create "$IMMUTABLE_LEDGER"
/bin/chmod 0444 -- "$IMMUTABLE_LEDGER"
[[ "$(/bin/stat -c '%a' -- "$IMMUTABLE_LEDGER")" == 444 ]] || die "immutable ledger is not sealed"
immutable_ledger verify "$IMMUTABLE_LEDGER"
note "sealed immutable release/task/bootstrap surface"
note "initial metadata parity: $(verify_metadata_parity)"

COMMON_ARGS=(
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
readonly -a COMMON_ARGS

ultra_status=$(descriptor_status ultra_orchestration_canary paper_bencmark/highambench/metadata/evidence/ultra_orchestration_live_canary.json)
token_status=$(descriptor_status token_control_canary paper_bencmark/highambench/metadata/evidence/token_control_live_canary.json)
[[ "$ultra_status" != replacement_required || "$token_status" != passed ]] || die "invalid transition: Token is passed while Ultra requires replacement"
note "initial canary status: Ultra=${ultra_status}, Token=${token_status}"

if [[ "$ultra_status" == replacement_required ]]; then
  require_remaining_seconds "Ultra canary" "$BEFORE_ULTRA_MINIMUM_SECONDS"
  immutable_ledger verify "$IMMUTABLE_LEDGER"
  "$PYTHON" "$ULTRA_TOOL" "${COMMON_ARGS[@]}" \
    --results-root "$ULTRA_CANARY_ROOT" \
    --canary-time-limit-seconds "$CANARY_TIME_LIMIT_SECONDS"
  "$PYTHON" "$PROMOTE_TOOL" \
    --benchmark-root "$BENCHMARK_ROOT" \
    --project-root "$PROJECT_ROOT" \
    --ultra-orchestration-attestation "${ULTRA_CANARY_ROOT}/ultra_orchestration_canary_attestation.json"
  immutable_ledger verify "$IMMUTABLE_LEDGER"
  [[ "$(descriptor_status ultra_orchestration_canary paper_bencmark/highambench/metadata/evidence/ultra_orchestration_live_canary.json)" == passed ]] || die "Ultra promotion did not pass"
  [[ "$(descriptor_status token_control_canary paper_bencmark/highambench/metadata/evidence/token_control_live_canary.json)" == replacement_required ]] || die "Ultra promotion changed Token status"
  note "post-Ultra metadata parity: $(verify_metadata_parity)"
fi

note "authenticating passed Ultra evidence without provider work"
"$PYTHON" "$ULTRA_TOOL" "${COMMON_ARGS[@]}" \
  --results-root "$BOOTSTRAP_ROOT" \
  --verify-only "$ULTRA_EVIDENCE"

token_status=$(descriptor_status token_control_canary paper_bencmark/highambench/metadata/evidence/token_control_live_canary.json)
if [[ "$token_status" == replacement_required ]]; then
  require_remaining_seconds "Token canary" "$BEFORE_TOKEN_MINIMUM_SECONDS"
  immutable_ledger verify "$IMMUTABLE_LEDGER"
  "$PYTHON" "$TOKEN_TOOL" "${COMMON_ARGS[@]}" \
    --results-root "$TOKEN_CANARY_ROOT" \
    --canary-token-limit "$TOKEN_CANARY_LIMIT" \
    --canary-time-limit-seconds "$CANARY_TIME_LIMIT_SECONDS"
  "$PYTHON" "$PROMOTE_TOOL" \
    --benchmark-root "$BENCHMARK_ROOT" \
    --project-root "$PROJECT_ROOT" \
    --token-control-attestation "${TOKEN_CANARY_ROOT}/token_control_canary_attestation.json"
  immutable_ledger verify "$IMMUTABLE_LEDGER"
  note "post-Token metadata parity: $(verify_metadata_parity)"
fi

[[ "$(descriptor_status ultra_orchestration_canary paper_bencmark/highambench/metadata/evidence/ultra_orchestration_live_canary.json)" == passed ]] || die "final Ultra descriptor is not passed"
[[ "$(descriptor_status token_control_canary paper_bencmark/highambench/metadata/evidence/token_control_live_canary.json)" == passed ]] || die "final Token descriptor is not passed"
note "authenticating both final frozen canaries without provider work"
"$PYTHON" "$ULTRA_TOOL" "${COMMON_ARGS[@]}" --results-root "$BOOTSTRAP_ROOT" --verify-only "$ULTRA_EVIDENCE"
"$PYTHON" "$TOKEN_TOOL" "${COMMON_ARGS[@]}" --results-root "$BOOTSTRAP_ROOT" --canary-token-limit "$TOKEN_CANARY_LIMIT" --verify-only "$TOKEN_EVIDENCE"
immutable_ledger verify "$IMMUTABLE_LEDGER"
note "final metadata parity: $(verify_metadata_parity)"
note "canary bootstrap complete; retained audit/evidence root: ${BOOTSTRAP_ROOT}"
exit 0
