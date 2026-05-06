#!/usr/bin/env bash
set -euo pipefail

workspace="${1:-}"
canonical_task="${2:-}"

if [[ -z "${workspace}" || -z "${canonical_task}" ]]; then
  echo "usage: benchmark/scripts/validate_attempt.sh <workspace> <canonical-task-file>" >&2
  exit 2
fi

attempt_task="${workspace}/BenchmarkTask.lean"

if [[ ! -f "${attempt_task}" ]]; then
  echo "missing attempted task file: ${attempt_task}" >&2
  exit 2
fi

if [[ ! -f "${canonical_task}" ]]; then
  echo "missing canonical task file: ${canonical_task}" >&2
  exit 2
fi

extract_proof_prefix() {
  awk '
    BEGIN { found = 0 }
    {
      sub(/[[:space:]]+$/, "")
      if (match($0, /:= *by/)) {
        print substr($0, 1, RSTART + RLENGTH - 1)
        found = 1
        exit
      } else {
        print
      }
    }
    END { if (found == 0) exit 1 }
  ' "$1"
}

errors=0

if ! canonical_prefix="$(extract_proof_prefix "${canonical_task}")"; then
  canonical_prefix=""
fi

if ! attempt_prefix="$(extract_proof_prefix "${attempt_task}")"; then
  attempt_prefix=""
fi

if [[ -z "${canonical_prefix}" ]]; then
  echo "validation failed: canonical task has no proof boundary" >&2
  errors=1
fi

if [[ -z "${attempt_prefix}" ]]; then
  echo "validation failed: attempted task has no proof boundary" >&2
  errors=1
fi

if [[ "${canonical_prefix}" != "${attempt_prefix}" ]]; then
  echo "validation failed: task interface changed before theorem proof body" >&2
  diff -u <(printf '%s\n' "${canonical_prefix}") <(printf '%s\n' "${attempt_prefix}") || true
  errors=1
fi

if rg -n '\b(sorry|admit|sorryAx)\b' "${attempt_task}"; then
  echo "validation failed: attempted task still contains sorry/admit/sorryAx" >&2
  errors=1
fi

while IFS= read -r lean_file; do
  if rg -n '^[[:space:]]*(axiom|opaque|unsafe)[[:space:]]' "${lean_file}"; then
    echo "validation failed: forbidden declaration in ${lean_file}" >&2
    errors=1
  fi
done < <(find "${workspace}" -path "${workspace}/.lake" -prune -o -name '*.lean' -type f -print)

if [[ -f "${workspace}/.benchmark_condition_c_snapshot" ]]; then
  snapshot_dir="$(<"${workspace}/.benchmark_condition_c_snapshot")"
  snapshot_hashes="${snapshot_dir}/.benchmark_condition_c_public_files.sha256"
  if [[ ! -f "${snapshot_hashes}" ]]; then
    echo "validation failed: missing Condition C snapshot hash file: ${snapshot_hashes}" >&2
    errors=1
  elif ! (cd "${snapshot_dir}" && shasum -a 256 -c .benchmark_condition_c_public_files.sha256); then
    echo "validation failed: Condition C snapshot changed during attempt" >&2
    errors=1
  fi
fi

if ! (cd "${workspace}" && lake build BenchmarkTask); then
  echo "validation failed: lake build BenchmarkTask failed" >&2
  errors=1
fi

if [[ "${errors}" -ne 0 ]]; then
  exit 1
fi

echo "validation passed: ${workspace}"
