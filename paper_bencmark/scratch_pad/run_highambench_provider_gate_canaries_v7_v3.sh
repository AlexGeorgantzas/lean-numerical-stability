#!/usr/bin/env bash
# Standalone, non-scored preparation job for the frozen HighamBench provider
# gate canaries.  Submit this file only after the snapshot refresh and before
# the protected P01 runbook.  It regenerates/promotes Ultra V7 first, then
# Token V3, authenticates both promoted artifacts, and exercises only the
# expired-deadline (zero-provider) matrix gate.
#
# Successful and failed job-specific roots are evidence and are never removed
# or overwritten here.  If a root already exists, preserve/archive it outside
# this job and submit a fresh allocation so that a new SLURM_JOB_ID supplies
# new paths.  This script never invokes refresh_snapshot.py, never uses
# --force, and never starts a scored matrix root.

#SBATCH --job-name=highambench-provider-gate-prep
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
#SBATCH --time=12:00:00
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
readonly MATRIX_TOOL="${BENCHMARK_ROOT}/tools/run_matrix.py"

readonly MANIFEST="${BENCHMARK_ROOT}/metadata/manifest.json"
readonly CONFIG="${BENCHMARK_ROOT}/metadata/config.json"
readonly ENVIRONMENT="${BENCHMARK_ROOT}/metadata/environment.json"
readonly ULTRA_EVIDENCE="${BENCHMARK_ROOT}/metadata/evidence/ultra_orchestration_live_canary.json"
readonly TOKEN_EVIDENCE="${BENCHMARK_ROOT}/metadata/evidence/token_control_live_canary.json"
readonly SPECIFICATION_PDF="${SCRATCH_ROOT}/HighamBench_Simple_Two_Condition_Specification.pdf"
readonly P01_PAPER_PDF="${PROJECT_ROOT}/paper_bencmark/reference_papers/P01_THE ACCURACY OF FLOATING POINT SUMMATION.pdf"
readonly PROTECTED_RUNBOOK="${SCRATCH_ROOT}/run_highambench_p01_actual_ultra.sh"

readonly EXPECTED_MANIFEST_SHA256="5a1eeb84c4214a3dd95386a912047bc6e2914621e65439e1d694aa5892ad408b"
readonly EXPECTED_SPECIFICATION_SHA256="59dfc314d4f9afecbbc6131c3c693624b09cc9e908f0e157efa468675ff56915"
readonly EXPECTED_P01_PAPER_SHA256="d5ad99fac5022da54dbe02721ea57116df3cec15badddd7c96c344328718fea7"
readonly EXPECTED_PYTHON_SHA256="d6bca2b84e73c7775a0dd5e6a76899cfe4ee62863d7c8f88513811d1fda23f49"
readonly EXPECTED_CODEX_SHA256="d13cfcda217421fb20d0aa6aa80819a62483a72e4a7fd52743675ca20d86377c"
readonly EXPECTED_PROTECTED_RUNBOOK_SHA256="4a361fd5c7475cd02e0ccb101249c34cfa1997a2e20cdba9c14f6c9409fb2fcc"
readonly EXPECTED_PROTECTED_SURFACE_SHA256="6f1f72adffd0ced6908de9c1e9454b8f4b50bcc4b71b0b1f1248d4bb417160bd"
readonly EXPECTED_PROTECTED_SURFACE_FILE_COUNT=288
readonly EXPECTED_PYTHON_VERSION="3.10.12"
readonly EXPECTED_CODEX_VERSION="0.146.0-alpha.9.2"

readonly MODEL="gpt-5.6-sol"
readonly REASONING_EFFORT="ultra"
readonly RUN_LIMIT_SECONDS=1800
readonly TOKEN_LIMIT=2000000
readonly PROMPT_STARTUP_SECONDS=120
readonly POST_SUBMISSION_VALIDATION_RESERVE_SECONDS=369
readonly ALLOCATION_GUARD_SECONDS=600
readonly CANARY_TIME_LIMIT_SECONDS=300
readonly TOKEN_CANARY_LIMIT=180000
readonly MATRIX_PAIR_RESERVATION_SECONDS=5418
readonly BEFORE_ULTRA_MINIMUM_SECONDS=2400
readonly BEFORE_TOKEN_MINIMUM_SECONDS=1500

die() {
  printf 'FATAL: %s\n' "$*" >&2
  exit 2
}

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

protected_surface_digest() {
  "$PYTHON" - "$PROJECT_ROOT" "$EXPECTED_MANIFEST_SHA256" <<'PY'
import hashlib
from pathlib import Path
import sys

project = Path(sys.argv[1]).resolve()
expected_manifest = sys.argv[2]
benchmark = project / "paper_bencmark/highambench"
fixed = {
    benchmark / "metadata/manifest.json",
    benchmark / "metadata/run_order.json",
    project / "paper_bencmark/scratch_pad/HighamBench_Simple_Two_Condition_Specification.pdf",
    project / "paper_bencmark/scratch_pad/run_highambench_p01_actual_ultra.sh",
    project / "paper_bencmark/reference_papers/P01_THE ACCURACY OF FLOATING POINT SUMMATION.pdf",
    benchmark / "agent_prompt.md",
    benchmark / "condition_prompts/L.md",
}
for relative_tree in ("tasks", "shared", "metadata/controlled"):
    tree = benchmark / relative_tree
    if tree.is_symlink() or not tree.is_dir():
        raise SystemExit(f"protected tree is missing or unsafe: {tree}")
    for path in tree.rglob("*"):
        if path.is_symlink():
            raise SystemExit(f"protected tree contains a symlink: {path}")
        if path.is_file():
            fixed.add(path)

lines = []
for path in sorted(fixed, key=lambda item: item.relative_to(project).as_posix()):
    if path.is_symlink() or not path.is_file():
        raise SystemExit(f"protected input is missing or unsafe: {path}")
    digest = hashlib.sha256(path.read_bytes()).hexdigest()
    relative = path.relative_to(project).as_posix()
    lines.append(f"{digest}  {relative}\n")
    if relative == "paper_bencmark/highambench/metadata/manifest.json" and digest != expected_manifest:
        raise SystemExit(
            f"manifest SHA-256 mismatch: expected {expected_manifest}, got {digest}"
        )
payload = "".join(lines).encode("utf-8")
print(f"{len(lines)} {hashlib.sha256(payload).hexdigest()}")
PY
}

assert_protected_surface() {
  local record count digest
  assert_sha256 "$PROTECTED_RUNBOOK" "$EXPECTED_PROTECTED_RUNBOOK_SHA256" "protected P01 runbook"
  record=$(protected_surface_digest)
  read -r count digest <<<"$record"
  [[ "$count" == "$EXPECTED_PROTECTED_SURFACE_FILE_COUNT" ]] || die "protected surface file count changed: expected ${EXPECTED_PROTECTED_SURFACE_FILE_COUNT}, got ${count}"
  [[ "$digest" == "$EXPECTED_PROTECTED_SURFACE_SHA256" ]] || die "protected surface digest changed: expected ${EXPECTED_PROTECTED_SURFACE_SHA256}, got ${digest}"
}

verify_metadata_parity() {
  "$PYTHON" - "$BENCHMARK_ROOT" <<'PY'
import json
from pathlib import Path
import sys

root = Path(sys.argv[1]).resolve()
sys.path.insert(0, str(root / "tools"))
import run_matrix

config = json.loads((root / "metadata/config.json").read_text(encoding="utf-8"))
environment = json.loads(
    (root / "metadata/environment.json").read_text(encoding="utf-8")
)
frozen = config.get("frozen_environment")
if not isinstance(frozen, dict):
    raise SystemExit("config frozen_environment is not an object")

bundle = run_matrix.environment_bundle_digest(config, environment)
if frozen.get("environment_bundle_sha256") != bundle:
    raise SystemExit("config environment-bundle digest is stale")
if environment.get("environment_bundle_sha256") != bundle:
    raise SystemExit("environment bundle digest is stale")
environment_id = environment.get("environment_id")
if frozen.get("environment_id") != environment_id:
    raise SystemExit("config/environment IDs disagree")
if not isinstance(environment_id, str) or not environment_id.endswith("-" + bundle[:16]):
    raise SystemExit("environment ID is not derived from the current bundle")

provider_gate = environment.get("provider_token_gate")
if not isinstance(provider_gate, dict):
    raise SystemExit("provider-token-gate environment record is missing")
if run_matrix.canonical_document_digest(provider_gate) != frozen.get(
    "provider_token_gate_sha256"
):
    raise SystemExit("provider-token-gate environment-record digest is stale")
actual_provider_gate = run_matrix.provider_token_gate_environment_record(root)
if provider_gate != actual_provider_gate:
    raise SystemExit("provider-token-gate source/catalog/transport freeze drifted")
if provider_gate.get("protocol") != "highambench-provider-token-gate-v2":
    raise SystemExit("provider-token-gate protocol is not v2")
static = provider_gate.get("static_configuration")
if not isinstance(static, dict):
    raise SystemExit("provider-token-gate static configuration is missing")
if static.get("counted_request_kinds") != ["turn", "compaction"]:
    raise SystemExit("provider-token-gate counted request-kind allowlist drifted")
if provider_gate.get("model_catalog", {}).get("response_bound") != 272000:
    raise SystemExit("provider-token-gate response bound drifted")
if provider_gate.get("transport_provenance", {}).get("connection_factory_mode") != "explicit_tls":
    raise SystemExit("provider-token-gate transport is not production explicit TLS")

limits = config.get("limits", {})
expected_limits = {
    "wall_clock_seconds": 1800,
    "total_model_tokens": 2_000_000,
    "prompt_startup_timeout_seconds": 120,
    "post_submission_validation_reserve_seconds": 369,
}
for key, expected in expected_limits.items():
    if limits.get(key) != expected:
        raise SystemExit(f"frozen limit {key} is not {expected}")
agent = environment.get("agent", {})
expected_agent = {
    "id": "codex-cli",
    "version": "0.146.0-alpha.9.2",
    "binary_sha256": "d13cfcda217421fb20d0aa6aa80819a62483a72e4a7fd52743675ca20d86377c",
    "model": "gpt-5.6-sol",
    "reasoning_effort": "ultra",
}
for key, expected in expected_agent.items():
    if agent.get(key) != expected:
        raise SystemExit(f"frozen agent field {key} is not {expected!r}")
print(f"{environment_id} {bundle}")
PY
}

remaining_allocation_seconds() {
  local now
  now=$(/bin/date -u +%s)
  printf '%s\n' "$((ALLOCATION_END_EPOCH - now))"
}

require_remaining_seconds() {
  local label=$1
  local required=$2
  local remaining
  remaining=$(remaining_allocation_seconds)
  (( remaining >= required )) || die "refusing ${label}: ${remaining}s remain, at least ${required}s required"
  note "${label}: ${remaining}s remain; minimum is ${required}s"
}

cd "$PROJECT_ROOT"

[[ -n "${SLURM_JOB_ID:-}" && "$SLURM_JOB_ID" =~ ^[0-9]+$ ]] || die "this preparation script requires a numeric SLURM_JOB_ID"
readonly PREP_TAG="prep-slurm-${SLURM_JOB_ID}"
readonly ULTRA_CANARY_ROOT="${SCRATCH_ROOT}/highambench_ultra_orchestration_canary_${PREP_TAG}"
readonly TOKEN_CANARY_ROOT="${SCRATCH_ROOT}/highambench_token_control_canary_${PREP_TAG}"
readonly DEADLINE_GATE_ROOT="${SCRATCH_ROOT}/highambench_zero_provider_deadline_gate_${PREP_TAG}"

# Also reserve the paths that the unchanged protected runbook would derive if
# it were invoked in this same allocation.  Preparation never writes them.
readonly PROTECTED_ULTRA_ROOT="${SCRATCH_ROOT}/highambench_ultra_orchestration_canary_slurm-${SLURM_JOB_ID}"
readonly PROTECTED_TOKEN_ROOT="${SCRATCH_ROOT}/highambench_token_control_canary_slurm-${SLURM_JOB_ID}"
readonly PROTECTED_DEADLINE_ROOT="${SCRATCH_ROOT}/highambench_zero_provider_deadline_gate_slurm-${SLURM_JOB_ID}"

for transient_root in \
  "$ULTRA_CANARY_ROOT" "$TOKEN_CANARY_ROOT" "$DEADLINE_GATE_ROOT" \
  "$PROTECTED_ULTRA_ROOT" "$PROTECTED_TOKEN_ROOT" "$PROTECTED_DEADLINE_ROOT"; do
  [[ ! -e "$transient_root" && ! -L "$transient_root" ]] || die "job-specific root already exists; preserve/archive it and use a fresh job ID: ${transient_root}"
done

# Authenticate the scheduler grant and obtain the allocation deadline without
# trusting a caller-supplied duration.  This is the only Slurm query made by
# the future job itself.
job_record=$(/bin/scontrol show job -o "$SLURM_JOB_ID")
ALLOCATION_END_EPOCH=$("$PYTHON" - "$SLURM_JOB_ID" "${SLURM_JOB_END_TIME:-}" "$job_record" <<'PY'
from datetime import datetime, timezone
import os
import re
import sys

job_id, environment_epoch, record = sys.argv[1:4]

def field(name: str) -> str:
    match = re.search(rf"(?:^| ){re.escape(name)}=([^ ]+)(?: |$)", record)
    if match is None:
        raise SystemExit(f"Slurm record has no {name} field")
    return match.group(1)

wanted = {
    "JobId": job_id,
    "Account": "kfountou_group",
    "Partition": "KFOUNTOU",
    "NodeList": "watgpu108",
    "NumNodes": "1",
    "NumCPUs": "4",
    "NumTasks": "1",
    "CPUs/Task": "4",
    "TimeLimit": "12:00:00",
}
for name, expected in wanted.items():
    actual = field(name)
    if actual != expected:
        raise SystemExit(f"Slurm {name} mismatch: expected {expected!r}, got {actual!r}")

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
print(epoch)
PY
)
readonly ALLOCATION_END_EPOCH
(( ALLOCATION_END_EPOCH > $(/bin/date -u +%s) )) || die "actual Slurm allocation end is not in the future"

# Every check below completes before the first hosted request.
assert_sha256 "$PYTHON" "$EXPECTED_PYTHON_SHA256" "frozen /usr/bin/python3.10"
assert_sha256 "$CODEX" "$EXPECTED_CODEX_SHA256" "pinned Codex binary"
assert_sha256 "$MANIFEST" "$EXPECTED_MANIFEST_SHA256" "central benchmark manifest"
assert_sha256 "$SPECIFICATION_PDF" "$EXPECTED_SPECIFICATION_SHA256" "HighamBench specification PDF"
assert_sha256 "$P01_PAPER_PDF" "$EXPECTED_P01_PAPER_SHA256" "P01 source PDF"
assert_protected_surface

python_version=$("$PYTHON" --version 2>&1)
[[ "$python_version" == "Python ${EXPECTED_PYTHON_VERSION}" ]] || die "Python version mismatch: ${python_version}"
codex_version=$("$CODEX" --version 2>&1)
[[ "$codex_version" == *"codex-cli ${EXPECTED_CODEX_VERSION}"* ]] || die "Codex version mismatch: ${codex_version}"

for required_path in \
  "$AUTH_FILE" "$OFFLINE_SHELL" "$LIBRARY_ROOT_FILE" "$RELEASE_MANIFEST" \
  "$ULTRA_TOOL" "$TOKEN_TOOL" "$PROMOTE_TOOL" "$MATRIX_TOOL" \
  "$CONFIG" "$ENVIRONMENT" "$ULTRA_EVIDENCE" "$TOKEN_EVIDENCE"; do
  require_regular_file "$required_path" "required frozen input"
done
for required_directory in \
  "$TOOLCHAIN_ROOT" "$PACKAGES_ROOT" "$PACKAGES_RUNTIME_ROOT" \
  "$SHARED_OLEAN_ROOT" "$LIBRARY_SOURCE" "$LIBRARY_OLEAN"; do
  [[ -d "$required_directory" && ! -L "$required_directory" ]] || die "required frozen directory is missing or unsafe: ${required_directory}"
done

metadata_record=$(verify_metadata_parity)
note "authenticated metadata/provider-gate parity: ${metadata_record}"

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
[[ "$ultra_status" == replacement_required ]] || die "preparation requires the Ultra V7 descriptor to be replacement_required, got ${ultra_status}"
[[ "$token_status" == replacement_required ]] || die "preparation requires the Token V3 descriptor to be replacement_required, got ${token_status}"
note "pre-promotion descriptors are exact replacement_required records"

# Token V3 verification/regeneration bypasses only its own descriptor, so the
# freshly promoted Ultra V7 evidence must exist before Token V3 starts.
require_remaining_seconds "Ultra V7 generation" "$BEFORE_ULTRA_MINIMUM_SECONDS"
assert_protected_surface
note "running non-scored Ultra V7 orchestration canary"
"$PYTHON" "$ULTRA_TOOL" \
  "${COMMON_FROZEN_ARGS[@]}" \
  --results-root "$ULTRA_CANARY_ROOT" \
  --canary-time-limit-seconds "$CANARY_TIME_LIMIT_SECONDS"

note "promoting authenticated Ultra V7 evidence"
"$PYTHON" "$PROMOTE_TOOL" \
  --benchmark-root "$BENCHMARK_ROOT" \
  --project-root "$PROJECT_ROOT" \
  --ultra-orchestration-attestation \
    "${ULTRA_CANARY_ROOT}/ultra_orchestration_canary_attestation.json"

[[ "$(descriptor_status ultra_orchestration_canary paper_bencmark/highambench/metadata/evidence/ultra_orchestration_live_canary.json)" == passed ]] || die "Ultra V7 promotion did not produce a passed descriptor"
[[ "$(descriptor_status token_control_canary paper_bencmark/highambench/metadata/evidence/token_control_live_canary.json)" == replacement_required ]] || die "Ultra V7 promotion unexpectedly changed the Token V3 descriptor"
metadata_record=$(verify_metadata_parity)
note "post-Ultra metadata/provider-gate parity: ${metadata_record}"
assert_protected_surface

note "authenticating promoted Ultra V7 in verify-only mode"
"$PYTHON" "$ULTRA_TOOL" \
  "${COMMON_FROZEN_ARGS[@]}" \
  --results-root "$ULTRA_CANARY_ROOT" \
  --verify-only "$ULTRA_EVIDENCE"

require_remaining_seconds "Token V3 generation" "$BEFORE_TOKEN_MINIMUM_SECONDS"
assert_protected_surface
note "running non-scored Token V3 compaction-crossing canary at the fixed 180000-token cap"
"$PYTHON" "$TOKEN_TOOL" \
  "${COMMON_FROZEN_ARGS[@]}" \
  --results-root "$TOKEN_CANARY_ROOT" \
  --canary-token-limit "$TOKEN_CANARY_LIMIT" \
  --canary-time-limit-seconds "$CANARY_TIME_LIMIT_SECONDS"

note "promoting authenticated Token V3 evidence"
"$PYTHON" "$PROMOTE_TOOL" \
  --benchmark-root "$BENCHMARK_ROOT" \
  --project-root "$PROJECT_ROOT" \
  --token-control-attestation \
    "${TOKEN_CANARY_ROOT}/token_control_canary_attestation.json"

[[ "$(descriptor_status ultra_orchestration_canary paper_bencmark/highambench/metadata/evidence/ultra_orchestration_live_canary.json)" == passed ]] || die "Token V3 promotion invalidated the Ultra V7 descriptor"
[[ "$(descriptor_status token_control_canary paper_bencmark/highambench/metadata/evidence/token_control_live_canary.json)" == passed ]] || die "Token V3 promotion did not produce a passed descriptor"
metadata_record=$(verify_metadata_parity)
note "post-Token metadata/provider-gate parity: ${metadata_record}"
assert_protected_surface

# Re-authenticate both frozen files against the final, twice-promoted metadata.
# These branches are provider-free and mirror the branches the unchanged
# protected runbook will take later.
note "authenticating final Ultra V7 evidence in verify-only mode"
"$PYTHON" "$ULTRA_TOOL" \
  "${COMMON_FROZEN_ARGS[@]}" \
  --results-root "$ULTRA_CANARY_ROOT" \
  --verify-only "$ULTRA_EVIDENCE"

note "authenticating final Token V3 evidence in verify-only mode"
"$PYTHON" "$TOKEN_TOOL" \
  "${COMMON_FROZEN_ARGS[@]}" \
  --results-root "$TOKEN_CANARY_ROOT" \
  --canary-token-limit "$TOKEN_CANARY_LIMIT" \
  --verify-only "$TOKEN_EVIDENCE"

# Exercise ordinary matrix startup only through an already-expired deadline.
# Exit 75 plus an empty artifact surface proves this path made zero provider
# attempts; no scored results root is named or created anywhere in this file.
note "running zero-provider expired-deadline matrix gate"
set +e
"$PYTHON" "$MATRIX_TOOL" \
  "${COMMON_FROZEN_ARGS[@]}" \
  --results-root "$DEADLINE_GATE_ROOT" \
  --stop-after-paper P01 \
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
status_path = root / "last_chunk_status.json"
if status_path.is_symlink() or not status_path.is_file():
    raise SystemExit("expired-deadline gate status is missing or unsafe")
status = json.loads(status_path.read_text(encoding="utf-8"))
if status.get("status") != "stopped_before_allocation_deadline":
    raise SystemExit(f"expired-deadline gate has wrong status: {status.get('status')!r}")
if status.get("allocation_end_epoch") != 1:
    raise SystemExit("expired-deadline gate did not bind epoch 1")
if status.get("unfinished_runs_in_next_pair") != 2:
    raise SystemExit("expired-deadline gate did not reserve an untouched two-run pair")
if status.get("required_seconds") != expected_pair_reservation:
    raise SystemExit(
        "expired-deadline gate reservation disagrees with frozen arithmetic: "
        f"{status.get('required_seconds')!r} != {expected_pair_reservation!r}"
    )
if status.get("post_submission_validation_reserve_seconds") != expected_validation_reserve:
    raise SystemExit("expired-deadline gate did not record the frozen validation reserve")
for directory_name in ("records", "attempts"):
    directory = root / directory_name
    if any(path.is_file() or path.is_symlink() for path in directory.rglob("*")):
        raise SystemExit(f"expired-deadline gate unexpectedly created {directory_name} artifacts")
runs = root / "runs.jsonl"
if runs.exists() and runs.read_text(encoding="utf-8").strip():
    raise SystemExit("expired-deadline gate unexpectedly recorded a hosted run")
PY

[[ "$(descriptor_status ultra_orchestration_canary paper_bencmark/highambench/metadata/evidence/ultra_orchestration_live_canary.json)" == passed ]] || die "final Ultra V7 descriptor is not passed"
[[ "$(descriptor_status token_control_canary paper_bencmark/highambench/metadata/evidence/token_control_live_canary.json)" == passed ]] || die "final Token V3 descriptor is not passed"
metadata_record=$(verify_metadata_parity)
assert_sha256 "$MANIFEST" "$EXPECTED_MANIFEST_SHA256" "central benchmark manifest after promotions"
assert_protected_surface

note "provider-gate preparation complete: Ultra V7 then Token V3 promoted and independently verified"
note "final metadata/provider-gate parity: ${metadata_record}"
note "retained Ultra evidence root: ${ULTRA_CANARY_ROOT}"
note "retained Token evidence root: ${TOKEN_CANARY_ROOT}"
note "retained zero-provider gate root: ${DEADLINE_GATE_ROOT}"
note "protected P01 runbook and ${EXPECTED_PROTECTED_SURFACE_FILE_COUNT}-file input surface remain byte-identical"
exit 0
