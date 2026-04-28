#!/usr/bin/env bash
set -euo pipefail

run_root="${1:-}"
result_root="${2:-}"

if [[ -z "${run_root}" ]]; then
  echo "usage: benchmark/scripts/archive_preflight_run.sh <run-root> [result-root]" >&2
  exit 2
fi

script_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
repo_root="$(cd "${script_dir}/../.." && pwd)"

if [[ -z "${result_root}" ]]; then
  result_root="${repo_root}/benchmark/results/$(basename "${run_root}")"
fi

mkdir -p "${result_root}"

if [[ -d "${run_root}/meta" ]]; then
  mkdir -p "${result_root}/meta"
  cp -R "${run_root}/meta/." "${result_root}/meta/"
fi

echo "archived preflight metadata to:"
echo "  ${result_root}"
