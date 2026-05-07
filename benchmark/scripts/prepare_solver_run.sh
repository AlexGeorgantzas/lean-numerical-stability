#!/usr/bin/env bash
set -euo pipefail

task="${1:-T01_ScaledDot}"
run_root="${2:-/tmp/lean-fp-benchmark-runs/${task}-$(date +%Y%m%d-%H%M%S)}"

script_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
repo_root="$(cd "${script_dir}/../.." && pwd)"

# shellcheck source=benchmark/scripts/shared_lake_packages.sh
source "${script_dir}/shared_lake_packages.sh"

task_file="${repo_root}/benchmark/tasks/${task}/Task.lean"

if [[ ! -f "${task_file}" ]]; then
  echo "missing task file: ${task_file}" >&2
  exit 1
fi

benchmark_require_free_space "${run_root}" "${BENCHMARK_MIN_FREE_GB:-8}"

"${script_dir}/generate_task_workspace.sh" "${task}" "${run_root}"

condition_a="${run_root}/condition_a/${task}"
condition_c="${run_root}/condition_c/${task}"
condition_c_snapshot="$(benchmark_condition_c_snapshot_dir "${repo_root}")"
meta_dir="${run_root}/meta"
mkdir -p "${meta_dir}"

task_sha="$(shasum -a 256 "${task_file}" | awk '{print $1}')"
commit="$(git -C "${repo_root}" rev-parse HEAD)"
branch="$(git -C "${repo_root}" branch --show-current)"
timestamp="$(date -u +%Y-%m-%dT%H:%M:%SZ)"

cat > "${meta_dir}/run_metadata.md" <<EOF
# Benchmark Run Metadata

- task: \`${task}\`
- source_branch: \`${branch}\`
- source_commit: \`${commit}\`
- generated_at_utc: \`${timestamp}\`
- task_sha256: \`${task_sha}\`
- condition_a_workspace: \`${condition_a}\`
- condition_c_workspace: \`${condition_c}\`
- condition_c_snapshot: \`${condition_c_snapshot}\`
- shared_lake_packages: \`$(benchmark_shared_lake_packages_dir "${repo_root}")\`

The task files in both condition workspaces must remain byte-identical before
the solver starts.
EOF

cat > "${meta_dir}/solver_prompt.md" <<'EOF'
You are solving a Lean 4 benchmark task in this generated workspace.

Work only inside the current workspace. Prove the theorem in
`BenchmarkTask.lean` by replacing the `sorry` proof with a complete Lean proof.

Rules:
- Treat the current workspace as the whole benchmark environment.
- You may inspect files and symlinks that are already present as entries in
  the current workspace, such as `public_library`, `README.md`, `docs`, or
  `examples` when they exist.
- Do not inspect the original repository, user home directories, global caches,
  previous result directories, or manually discovered paths outside the
  workspace.
- Do not add manual `LEAN_PATH`, `--root`, or other search paths. Use the
  imports and Lake package configuration already present in the workspace.
- Only edit the proof body of the theorem in `BenchmarkTask.lean`.
- Do not change imports, task-local definitions, namespaces, or the theorem
  statement.
- Put any helper reasoning inside the theorem proof.
- Do not add `axiom`, `opaque`, `unsafe`, `admit`, or `sorry`.
- After editing, run `lake build BenchmarkTask`.
EOF

cp "${meta_dir}/solver_prompt.md" "${condition_a}/SOLVER_PROMPT.md"
cp "${meta_dir}/solver_prompt.md" "${condition_c}/SOLVER_PROMPT.md"

shasum -a 256 \
  "${condition_a}/BenchmarkTask.lean" \
  "${condition_c}/BenchmarkTask.lean" \
  "${task_file}" > "${meta_dir}/task_hashes.txt"

echo "preflight build: Condition A"
(cd "${condition_a}" && lake build BenchmarkTask) 2>&1 | tee "${meta_dir}/preflight_condition_a.log"

if [[ "${BENCHMARK_COPY_DEPS_FROM_CONDITION_A:-0}" == "1" &&
      -d "${condition_a}/.lake/packages" &&
      ! -e "${condition_c}/.lake/packages" ]]; then
  echo "copying third-party dependency packages from Condition A to Condition C"
  mkdir -p "${condition_c}/.lake"
  cp -R "${condition_a}/.lake/packages" "${condition_c}/.lake/packages"
fi

echo "preflight build: Condition C"
(cd "${condition_c}" && lake build BenchmarkTask) 2>&1 | tee "${meta_dir}/preflight_condition_c.log"

echo
echo "prepared run root:"
echo "  ${run_root}"
echo
echo "solver prompts:"
echo "  ${condition_a}/SOLVER_PROMPT.md"
echo "  ${condition_c}/SOLVER_PROMPT.md"
echo
echo "post-attempt validation:"
echo "  ${script_dir}/validate_attempt.sh ${condition_a} ${task_file}"
echo "  ${script_dir}/validate_attempt.sh ${condition_c} ${task_file}"
