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
  run_id="$(basename "$(dirname "$(dirname "$(dirname "${workspace}")")")")"
  result_root="${repo_root}/benchmark/results/${run_id}"
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
commit="$(git -C "${repo_root}" rev-parse HEAD)"
branch="$(git -C "${repo_root}" branch --show-current)"

cat > "${result_dir}/attempt_metadata.md" <<EOF
# Attempt Metadata

- condition: \`${condition}\`
- workspace: \`${workspace}\`
- source_branch: \`${branch}\`
- source_commit: \`${commit}\`
- started_at_utc: \`${timestamp}\`
- codex_bin: \`${codex_bin}\`
- codex_mode: \`--ask-for-approval never exec --ephemeral --ignore-user-config --ignore-rules --skip-git-repo-check\`
EOF

cp "${workspace}/SOLVER_PROMPT.md" "${result_dir}/SOLVER_PROMPT.md"
cp "${canonical_task}" "${result_dir}/CanonicalTask.lean"

set +e
codex --ask-for-approval never exec \
  --ephemeral \
  --ignore-user-config \
  --ignore-rules \
  --skip-git-repo-check \
  --sandbox workspace-write \
  --cd "${workspace}" \
  --json \
  --output-last-message "${result_dir}/codex_last_message.txt" \
  - < "${workspace}/SOLVER_PROMPT.md" \
  > "${result_dir}/codex_events.jsonl" \
  2> "${result_dir}/codex_stderr.log"
codex_status=$?
set -e

echo "${codex_status}" > "${result_dir}/codex_exit_code.txt"

cp "${workspace}/BenchmarkTask.lean" "${result_dir}/BenchmarkTask.after.lean"
find "${workspace}" -path "${workspace}/.lake" -prune -o -type f -print | sort > "${result_dir}/workspace_files.txt"
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
