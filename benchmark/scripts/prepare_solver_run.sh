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
solver_prompt_variant="${BENCHMARK_SOLVER_PROMPT_VARIANT:-standard}"
codex_model="${BENCHMARK_CODEX_MODEL:-}"
codex_reasoning_effort="${BENCHMARK_CODEX_REASONING_EFFORT:-}"

cat > "${meta_dir}/run_metadata.md" <<EOF
# Benchmark Run Metadata

- task: \`${task}\`
- solver_prompt_variant: \`${solver_prompt_variant}\`
- codex_model: \`${codex_model:-<cli-default>}\`
- codex_reasoning_effort: \`${codex_reasoning_effort:-<cli-default>}\`
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

case "${solver_prompt_variant}" in
  standard)
    cat > "${meta_dir}/solver_prompt.md" <<'EOF'
You are solving a Lean 4 benchmark task in this generated workspace.

Work only inside the current workspace. Prove the theorem in
`BenchmarkTask.lean` by replacing the `sorry` proof with a complete Lean proof.

Rules:
- Treat the current workspace as the whole benchmark environment.
- You may inspect files and symlinks that are already present as entries in
  the current workspace, such as `public_library`, `README.md`, or `docs`
  when they exist.
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
    ;;
  persistent)
    cat > "${meta_dir}/solver_prompt.md" <<'EOF'
You are solving a Lean 4 benchmark task in this generated workspace.

Work only inside the current workspace. Prove the theorem in
`BenchmarkTask.lean` by replacing the `sorry` proof with a complete Lean proof.

This is a persistence benchmark. Do not stop after one failed proof idea. Keep
working until `lake build BenchmarkTask` succeeds or the external timeout stops
the attempt.

Persistence requirements:
- Do not leave the original `sorry`.
- Removing `sorry` is not enough. A proof attempt only counts when
  `lake build BenchmarkTask` succeeds.
- If there are no `sorry`s but Lean still reports errors or unsolved goals,
  continue editing until those errors are resolved.
- Do not end with a final message saying the proof is incomplete while there is
  still time to try alternatives.
- If `lake build BenchmarkTask` fails, read the Lean errors, revise the proof,
  and run `lake build BenchmarkTask` again.
- If a theorem name is unavailable, search the files visible in this workspace
  for alternatives, then try another proof route.
- Prefer a small complete proof over a large speculative proof. If one route
  becomes stuck, replace it with a different route rather than stopping.
- Only finish when the proof validates locally with `lake build BenchmarkTask`,
  or when the external timeout terminates the run.

Rules:
- Treat the current workspace as the whole benchmark environment.
- You may inspect files and symlinks that are already present as entries in
  the current workspace, such as `public_library`, `README.md`, or `docs`
  when they exist.
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
- After every proof attempt, run `lake build BenchmarkTask` and use the errors
  to continue.
EOF
    ;;
  *)
    echo "unknown BENCHMARK_SOLVER_PROMPT_VARIANT: ${solver_prompt_variant}" >&2
    echo "expected: standard or persistent" >&2
    exit 2
    ;;
esac

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
