#!/usr/bin/env bash
set -euo pipefail

task="${1:-T01_ScaledDot}"
run_root="${2:-/tmp/lean-fp-benchmark-runs/${task}-$(date +%Y%m%d-%H%M%S)}"

script_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
repo_root="$(cd "${script_dir}/../.." && pwd)"

# shellcheck source=benchmark/scripts/shared_lake_packages.sh
source "${script_dir}/shared_lake_packages.sh"

task_dir="${repo_root}/benchmark/tasks/${task}"
stub_dir="${repo_root}/benchmark/stubs/${task}"
common_stub_dir="${repo_root}/benchmark/stubs/common"
condition_a_template="${repo_root}/benchmark/condition_a"
condition_c_template="${repo_root}/benchmark/condition_c"
condition_c_snapshot="$(benchmark_condition_c_snapshot_dir "${repo_root}")"

if [[ ! -f "${task_dir}/Task.lean" ]]; then
  echo "missing task file: ${task_dir}/Task.lean" >&2
  exit 1
fi

if [[ ! -d "${stub_dir}" ]]; then
  stub_dir="${common_stub_dir}"
fi

if [[ ! -d "${stub_dir}" ]]; then
  echo "missing Condition A stub directory for ${task}, and no common stub exists" >&2
  exit 1
fi

if [[ ! -f "${condition_c_snapshot}/.benchmark_condition_c_snapshot.md" ]]; then
  "${script_dir}/setup_condition_c_snapshot.sh"
fi

condition_a="${run_root}/condition_a/${task}"
condition_c="${run_root}/condition_c/${task}"

rm -rf "${condition_a}" "${condition_c}"
mkdir -p "${condition_a}" "${condition_c}"

cp "${repo_root}/lean-toolchain" "${condition_a}/lean-toolchain"
cp "${repo_root}/lean-toolchain" "${condition_c}/lean-toolchain"
cp "${repo_root}/lake-manifest.json" "${condition_a}/lake-manifest.json"
cp "${condition_a_template}/lakefile.toml" "${condition_a}/lakefile.toml"
sed "s|@BENCHMARK_CONDITION_C_SNAPSHOT@|${condition_c_snapshot}|g" \
  "${condition_c_template}/lakefile.toml" > "${condition_c}/lakefile.toml"

cp "${task_dir}/Task.lean" "${condition_a}/BenchmarkTask.lean"
cp "${task_dir}/Task.lean" "${condition_c}/BenchmarkTask.lean"

cp -R "${stub_dir}/LeanFpAnalysis" "${condition_a}/LeanFpAnalysis"

printf '%s\n' "${condition_c_snapshot}" > "${condition_c}/.benchmark_condition_c_snapshot"
ln -s "${condition_c_snapshot}" "${condition_c}/public_library"
ln -s "${condition_c_snapshot}/README.md" "${condition_c}/README.md"
ln -s "${condition_c_snapshot}/docs" "${condition_c}/docs"
ln -s "${condition_c_snapshot}/examples" "${condition_c}/examples"

if [[ "${BENCHMARK_USE_SHARED_LAKE_PACKAGES:-1}" == "1" ]]; then
  for condition_dir in "${condition_a}" "${condition_c}"; do
    benchmark_link_shared_lake_packages "${repo_root}" "${condition_dir}"
  done
fi

echo "generated:"
echo "  ${condition_a}"
echo "  ${condition_c}"
echo "Condition C snapshot:"
echo "  ${condition_c_snapshot}"
echo
echo "typecheck with:"
echo "  (cd ${condition_a} && lake build BenchmarkTask)"
echo "  (cd ${condition_c} && lake build BenchmarkTask)"
