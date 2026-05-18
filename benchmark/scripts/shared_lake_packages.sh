#!/usr/bin/env bash

benchmark_toolchain_id() {
  local repo_root="$1"
  tr -c 'A-Za-z0-9._-' '-' < "${repo_root}/lean-toolchain" | sed 's/-$//'
}

benchmark_manifest_id() {
  local repo_root="$1"
  shasum -a 256 "${repo_root}/lake-manifest.json" | awk '{print substr($1, 1, 16)}'
}

benchmark_shared_lake_packages_dir() {
  local repo_root="$1"
  if [[ -n "${BENCHMARK_LAKE_PACKAGES_CACHE:-}" ]]; then
    echo "${BENCHMARK_LAKE_PACKAGES_CACHE}"
    return
  fi

  local cache_root="${XDG_CACHE_HOME:-${HOME}/.cache}/lean-fp-analysis/lake-packages"
  echo "${cache_root}/$(benchmark_toolchain_id "${repo_root}")-$(benchmark_manifest_id "${repo_root}")"
}

benchmark_condition_c_public_id() {
  local repo_root="$1"
  (
    cd "${repo_root}"
    git ls-files -z \
      LeanFpAnalysis.lean \
      LeanFpAnalysis \
      Main.lean \
      README.md \
      docs \
      lakefile.toml \
      lake-manifest.json \
      lean-toolchain |
      xargs -0 shasum -a 256 |
      shasum -a 256 |
      awk '{print substr($1, 1, 16)}'
  )
}

benchmark_condition_c_snapshot_dir() {
  local repo_root="$1"
  if [[ -n "${BENCHMARK_CONDITION_C_SNAPSHOT:-}" ]]; then
    echo "${BENCHMARK_CONDITION_C_SNAPSHOT}"
    return
  fi

  local cache_root="${XDG_CACHE_HOME:-${HOME}/.cache}/lean-fp-analysis/condition-c-snapshots"
  echo "${cache_root}/$(benchmark_toolchain_id "${repo_root}")-$(benchmark_condition_c_public_id "${repo_root}")"
}

benchmark_result_root_for_run_id() {
  local repo_root="$1"
  local run_id="$2"

  if [[ "${run_id}" =~ ^(.+)-([0-9]{8}-[0-9]{6})$ ]]; then
    echo "${repo_root}/benchmark/results/${BASH_REMATCH[1]}/${BASH_REMATCH[2]}"
  else
    echo "${repo_root}/benchmark/results/${run_id}"
  fi
}

benchmark_require_free_space() {
  local path="$1"
  local min_gb="${2:-8}"
  local check_path="${path}"

  while [[ ! -e "${check_path}" && "${check_path}" != "/" ]]; do
    check_path="$(dirname "${check_path}")"
  done

  local available_kib
  available_kib="$(df -Pk "${check_path}" | awk 'NR == 2 {print $4}')"
  local required_kib=$((min_gb * 1024 * 1024))

  if (( available_kib < required_kib )); then
    echo "refusing to run: only $((available_kib / 1024 / 1024)) GiB free at ${check_path}; need at least ${min_gb} GiB" >&2
    exit 1
  fi
}

benchmark_link_shared_lake_packages() {
  local repo_root="$1"
  local workspace="$2"
  local cache_dir
  cache_dir="$(benchmark_shared_lake_packages_dir "${repo_root}")"

  if [[ ! -d "${cache_dir}/mathlib" ]]; then
    echo "missing shared Lake package cache: ${cache_dir}" >&2
    echo "run: benchmark/scripts/setup_shared_lake_packages.sh" >&2
    exit 1
  fi

  mkdir -p "${workspace}/.lake"
  if [[ -L "${workspace}/.lake/packages" ]]; then
    rm "${workspace}/.lake/packages"
  elif [[ -e "${workspace}/.lake/packages" ]]; then
    echo "refusing to replace non-symlink package directory: ${workspace}/.lake/packages" >&2
    exit 1
  fi

  ln -s "${cache_dir}" "${workspace}/.lake/packages"
}
