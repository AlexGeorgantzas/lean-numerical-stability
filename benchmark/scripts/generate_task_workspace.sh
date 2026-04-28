#!/usr/bin/env bash
set -euo pipefail

task="${1:-T01_ScaledDot}"
run_root="${2:-/tmp/lean-fp-benchmark-runs/${task}-$(date +%Y%m%d-%H%M%S)}"

script_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
repo_root="$(cd "${script_dir}/../.." && pwd)"

task_dir="${repo_root}/benchmark/tasks/${task}"
stub_dir="${repo_root}/benchmark/stubs/${task}"
condition_a_template="${repo_root}/benchmark/condition_a"
condition_c_template="${repo_root}/benchmark/condition_c"

if [[ ! -f "${task_dir}/Task.lean" ]]; then
  echo "missing task file: ${task_dir}/Task.lean" >&2
  exit 1
fi

if [[ ! -d "${stub_dir}" ]]; then
  echo "missing Condition A stub directory: ${stub_dir}" >&2
  exit 1
fi

condition_a="${run_root}/condition_a/${task}"
condition_c="${run_root}/condition_c/${task}"

rm -rf "${condition_a}" "${condition_c}"
mkdir -p "${condition_a}" "${condition_c}"

cp "${repo_root}/lean-toolchain" "${condition_a}/lean-toolchain"
cp "${repo_root}/lean-toolchain" "${condition_c}/lean-toolchain"
cp "${repo_root}/lake-manifest.json" "${condition_a}/lake-manifest.json"
cp "${repo_root}/lake-manifest.json" "${condition_c}/lake-manifest.json"
cp "${condition_a_template}/lakefile.toml" "${condition_a}/lakefile.toml"
cp "${condition_c_template}/lakefile.toml" "${condition_c}/lakefile.toml"

cp "${task_dir}/Task.lean" "${condition_a}/BenchmarkTask.lean"
cp "${task_dir}/Task.lean" "${condition_c}/BenchmarkTask.lean"

cp -R "${stub_dir}/LeanFpAnalysis" "${condition_a}/LeanFpAnalysis"

cp "${repo_root}/LeanFpAnalysis.lean" "${condition_c}/LeanFpAnalysis.lean"
cp -R "${repo_root}/LeanFpAnalysis" "${condition_c}/LeanFpAnalysis"
cp "${repo_root}/README.md" "${condition_c}/README.md"
cp -R "${repo_root}/docs" "${condition_c}/docs"
cp -R "${repo_root}/examples" "${condition_c}/examples"

if [[ "${BENCHMARK_LINK_LAKE_PACKAGES:-0}" == "1" ]]; then
  for condition_dir in "${condition_a}" "${condition_c}"; do
    mkdir -p "${condition_dir}/.lake"
    ln -s "${repo_root}/.lake/packages" "${condition_dir}/.lake/packages"
  done
fi

echo "generated:"
echo "  ${condition_a}"
echo "  ${condition_c}"
echo
echo "typecheck with:"
echo "  (cd ${condition_a} && lake build BenchmarkTask)"
echo "  (cd ${condition_c} && lake build BenchmarkTask)"
