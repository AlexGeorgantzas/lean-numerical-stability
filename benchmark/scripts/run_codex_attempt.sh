#!/usr/bin/env bash
set -euo pipefail

workspace="${1:-}"
condition="${2:-}"
canonical_task="${3:-}"
result_root="${4:-}"

if [[ -z "${workspace}" || -z "${condition}" || -z "${canonical_task}" ]]; then
  echo "usage: benchmark/scripts/run_codex_attempt.sh <workspace> <condition> <canonical-task-file> [result-root]" >&2
  exit 2
fi

script_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
repo_root="$(cd "${script_dir}/../.." && pwd)"
source "${script_dir}/shared_lake_packages.sh"

if [[ ! -d "${workspace}" ]]; then
  echo "missing workspace: ${workspace}" >&2
  exit 2
fi

if [[ ! -f "${workspace}/SOLVER_PROMPT.md" ]]; then
  echo "missing solver prompt: ${workspace}/SOLVER_PROMPT.md" >&2
  exit 2
fi

if [[ ! -f "${canonical_task}" ]]; then
  echo "missing canonical task file: ${canonical_task}" >&2
  exit 2
fi

case "${condition}" in
  condition_a|condition_c) ;;
  *)
    echo "condition must be condition_a or condition_c" >&2
    exit 2
    ;;
esac

if [[ -z "${result_root}" ]]; then
  run_id="$(basename "$(dirname "$(dirname "${workspace}")")")"
  result_root="$(benchmark_result_root_for_run_id "${repo_root}" "${run_id}")"
fi

result_dir="${result_root}/${condition}"
mkdir -p "${result_dir}"

if find "${workspace}" \( -name '.codex' -o -name '.claude' -o -name 'thesis' -o -name 'benchmark' \) -print -quit | grep -q .; then
  echo "refusing to run: workspace contains forbidden memory/meta path" >&2
  find "${workspace}" \( -name '.codex' -o -name '.claude' -o -name 'thesis' -o -name 'benchmark' \) -print >&2
  exit 1
fi

timestamp="$(date -u +%Y-%m-%dT%H:%M:%SZ)"
codex_bin="$(command -v codex)"
real_lake_bin="$(command -v lake)"
real_lean_bin="$(command -v lean)"
commit="$(git -C "${repo_root}" rev-parse HEAD)"
branch="$(git -C "${repo_root}" branch --show-current)"
timeout_seconds="${BENCHMARK_CODEX_TIMEOUT_SECONDS:-1200}"
shared_packages="$(benchmark_shared_lake_packages_dir "${repo_root}")"
elan_home="${ELAN_HOME:-${HOME}/.elan}"
solver_prompt_variant="${BENCHMARK_SOLVER_PROMPT_VARIANT:-standard}"
codex_model="${BENCHMARK_CODEX_MODEL:-}"
codex_reasoning_effort="${BENCHMARK_CODEX_REASONING_EFFORT:-}"
codex_home="$(mktemp -d "${TMPDIR:-/tmp}/codex-benchmark-home.XXXXXX")"
solver_home="${codex_home}/home"
cleanup_codex_home() {
  rm -rf "${codex_home}"
}
trap cleanup_codex_home EXIT

if [[ ! -f "${HOME}/.codex/auth.json" ]]; then
  echo "missing Codex auth at ${HOME}/.codex/auth.json" >&2
  exit 2
fi
if [[ ! -d "${elan_home}" ]]; then
  echo "missing ELAN_HOME/toolchain directory: ${elan_home}" >&2
  exit 2
fi
case "${codex_reasoning_effort}" in
  ""|low|medium|high|xhigh) ;;
  *)
    echo "invalid BENCHMARK_CODEX_REASONING_EFFORT: ${codex_reasoning_effort}" >&2
    echo "expected one of: low, medium, high, xhigh" >&2
    exit 2
    ;;
esac
cp "${HOME}/.codex/auth.json" "${codex_home}/auth.json"
chmod 700 "${codex_home}"
chmod 600 "${codex_home}/auth.json"
mkdir -p "${solver_home}/.cache"
chmod 700 "${solver_home}"

solver_bin="${workspace}/.benchmark_bin"
solver_env="${workspace}/.benchmark_env"
mkdir -p "${solver_bin}" "${solver_env}"

(
  cd "${workspace}"
  "${real_lake_bin}" env sh -c 'printf "%s" "$LEAN_PATH"'
) > "${solver_env}/LEAN_PATH"

cat > "${solver_bin}/lake" <<EOF
#!/usr/bin/env bash
set -euo pipefail

script_dir="\$(cd "\$(dirname "\${BASH_SOURCE[0]}")" && pwd)"
workspace="\$(cd "\${script_dir}/.." && pwd)"
lean_path_file="\${workspace}/.benchmark_env/LEAN_PATH"

if [[ ! -f "\${lean_path_file}" ]]; then
  echo "missing benchmark Lean environment: \${lean_path_file}" >&2
  exit 2
fi

export LEAN_PATH="\$(cat "\${lean_path_file}")"

case "\${1:-}" in
  build)
    if [[ "\${2:-}" == "BenchmarkTask" ]]; then
      shift 2
      if [[ "\$#" -ne 0 ]]; then
        echo "benchmark lake wrapper supports only: lake build BenchmarkTask" >&2
        exit 2
      fi
      exec "${real_lean_bin}" "\${workspace}/BenchmarkTask.lean"
    fi
    ;;
  lean)
    shift
    exec "${real_lean_bin}" "\$@"
    ;;
  env)
    if [[ "\${2:-}" == "lean" ]]; then
      shift 2
      exec "${real_lean_bin}" "\$@"
    fi
    ;;
esac

exec "${real_lake_bin}" "\$@"
EOF
chmod +x "${solver_bin}/lake"

cat > "${result_dir}/attempt_metadata.md" <<EOF
# Attempt Metadata

- condition: \`${condition}\`
- workspace: \`${workspace}\`
- source_branch: \`${branch}\`
- source_commit: \`${commit}\`
- started_at_utc: \`${timestamp}\`
- codex_bin: \`${codex_bin}\`
- codex_model: \`${codex_model:-<cli-default>}\`
- codex_reasoning_effort: \`${codex_reasoning_effort:-<cli-default>}\`
- solver_prompt_variant: \`${solver_prompt_variant}\`
- codex_mode: \`auth-only temporary CODEX_HOME; temporary HOME/XDG_CACHE_HOME; host ELAN_HOME for Lean toolchain only; workspace-local lake wrapper first on PATH for solver-side BenchmarkTask typechecking; shared third-party Lake package cache added with --add-dir; optional --model from BENCHMARK_CODEX_MODEL; optional -c model_reasoning_effort from BENCHMARK_CODEX_REASONING_EFFORT; --disable plugins --disable memories --ask-for-approval never exec --ephemeral --ignore-user-config --ignore-rules --skip-git-repo-check\`
- elan_home: \`${elan_home}\`
- shared_lake_packages_add_dir: \`${shared_packages}\`
- solver_lake_wrapper: \`${solver_bin}/lake\`
- timeout_seconds: \`${timeout_seconds}\`
EOF

cp "${workspace}/SOLVER_PROMPT.md" "${result_dir}/SOLVER_PROMPT.md"
cp "${canonical_task}" "${result_dir}/CanonicalTask.lean"

codex_exec_args=(
  --ephemeral
  --ignore-user-config
  --ignore-rules
  --skip-git-repo-check
  --sandbox workspace-write
  --cd "${workspace}"
  --add-dir "${shared_packages}"
  --json
  --output-last-message "${result_dir}/codex_last_message.txt"
)

if [[ -n "${codex_model}" ]]; then
  codex_exec_args=(--model "${codex_model}" "${codex_exec_args[@]}")
fi

if [[ -n "${codex_reasoning_effort}" ]]; then
  codex_exec_args=(-c "model_reasoning_effort=\"${codex_reasoning_effort}\"" "${codex_exec_args[@]}")
fi

set +e
"${script_dir}/run_with_timeout.py" \
  --timeout-seconds "${timeout_seconds}" \
  --timeout-file "${result_dir}/timeout.txt" \
  --stdout "${result_dir}/codex_events.jsonl" \
  --stderr "${result_dir}/codex_stderr.log" \
  -- \
  env \
    "CODEX_HOME=${codex_home}" \
    "HOME=${solver_home}" \
    "XDG_CACHE_HOME=${solver_home}/.cache" \
    "ELAN_HOME=${elan_home}" \
    "PATH=${solver_bin}:${PATH}" \
    "${codex_bin}" \
    --disable plugins \
    --disable memories \
    --ask-for-approval never \
    exec \
    "${codex_exec_args[@]}" \
    - < "${workspace}/SOLVER_PROMPT.md"
codex_status=$?
if [[ -f "${result_dir}/timeout.txt" ]]; then
  codex_status=124
fi
set -e

echo "${codex_status}" > "${result_dir}/codex_exit_code.txt"

cp "${workspace}/BenchmarkTask.lean" "${result_dir}/BenchmarkTask.after.lean"
find "${workspace}" -path "${workspace}/.lake" -prune -o \( -type f -o -type l \) -print | sort > "${result_dir}/workspace_files.txt"
diff -u "${canonical_task}" "${workspace}/BenchmarkTask.lean" > "${result_dir}/BenchmarkTask.diff" || true

set +e
"${script_dir}/validate_attempt.sh" "${workspace}" "${canonical_task}" \
  > "${result_dir}/validation.log" \
  2>&1
validation_status=$?
set -e

echo "${validation_status}" > "${result_dir}/validation_exit_code.txt"

finished_at="$(date -u +%Y-%m-%dT%H:%M:%SZ)"
cat >> "${result_dir}/attempt_metadata.md" <<EOF
- finished_at_utc: \`${finished_at}\`
- codex_exit_code: \`${codex_status}\`
- validation_exit_code: \`${validation_status}\`
EOF

if [[ "${validation_status}" -eq 0 ]]; then
  echo "attempt passed validation: ${result_dir}"
else
  echo "attempt failed validation: ${result_dir}"
fi

exit 0
