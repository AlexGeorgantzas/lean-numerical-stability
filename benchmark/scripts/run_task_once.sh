#!/usr/bin/env bash
set -euo pipefail

task="${1:-T01_ScaledDot}"
run_root="${2:-/tmp/lean-fp-benchmark-runs/${task}-$(date +%Y%m%d-%H%M%S)}"

script_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
repo_root="$(cd "${script_dir}/../.." && pwd)"

# shellcheck source=benchmark/scripts/shared_lake_packages.sh
source "${script_dir}/shared_lake_packages.sh"

timeout_seconds="${BENCHMARK_CODEX_TIMEOUT_SECONDS:-1200}"
solver_prompt_variant="${BENCHMARK_SOLVER_PROMPT_VARIANT:-standard}"
codex_model="${BENCHMARK_CODEX_MODEL:-}"
codex_reasoning_effort="${BENCHMARK_CODEX_REASONING_EFFORT:-}"
task_file="${repo_root}/benchmark/tasks/${task}/Task.lean"
result_root="$(benchmark_result_root_for_run_id "${repo_root}" "$(basename "${run_root}")")"

"${script_dir}/prepare_solver_run.sh" "${task}" "${run_root}"
"${script_dir}/archive_preflight_run.sh" "${run_root}" "${result_root}"

BENCHMARK_CODEX_TIMEOUT_SECONDS="${timeout_seconds}" \
BENCHMARK_SOLVER_PROMPT_VARIANT="${solver_prompt_variant}" \
BENCHMARK_CODEX_MODEL="${codex_model}" \
BENCHMARK_CODEX_REASONING_EFFORT="${codex_reasoning_effort}" \
  "${script_dir}/run_codex_attempt.sh" \
  "${run_root}/condition_a/${task}" condition_a "${task_file}" "${result_root}"

BENCHMARK_CODEX_TIMEOUT_SECONDS="${timeout_seconds}" \
BENCHMARK_SOLVER_PROMPT_VARIANT="${solver_prompt_variant}" \
BENCHMARK_CODEX_MODEL="${codex_model}" \
BENCHMARK_CODEX_REASONING_EFFORT="${codex_reasoning_effort}" \
  "${script_dir}/run_codex_attempt.sh" \
  "${run_root}/condition_c/${task}" condition_c "${task_file}" "${result_root}"

"${script_dir}/analyze_run.sh" "${result_root}"
"${script_dir}/cleanup_run_workspaces.sh" "${run_root}"

echo "benchmark run complete:"
echo "  ${result_root}"
