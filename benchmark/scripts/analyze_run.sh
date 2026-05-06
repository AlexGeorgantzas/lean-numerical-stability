#!/usr/bin/env bash
set -euo pipefail

result_root="${1:-}"

if [[ -z "${result_root}" ]]; then
  echo "usage: benchmark/scripts/analyze_run.sh <result-root>" >&2
  exit 2
fi

if [[ ! -d "${result_root}" ]]; then
  echo "missing result root: ${result_root}" >&2
  exit 2
fi

read_field() {
  local file="$1"
  local key="$2"
  if [[ -f "${file}" ]]; then
    awk -F'`' -v key="${key}" '$0 ~ "- " key ":" { print $2; exit }' "${file}"
  fi
}

count_lines() {
  local file="$1"
  if [[ -f "${file}" ]]; then
    wc -l < "${file}" | tr -d ' '
  else
    echo 0
  fi
}

count_rg() {
  local pattern="$1"
  local file="$2"
  local matches
  if [[ -f "${file}" ]]; then
    matches="$(rg -n "${pattern}" "${file}" || true)"
    if [[ -z "${matches}" ]]; then
      echo 0
    else
      printf '%s\n' "${matches}" | wc -l | tr -d ' '
    fi
  else
    echo 0
  fi
}

summarize_condition() {
  local condition="$1"
  local dir="${result_root}/${condition}"
  local meta="${dir}/attempt_metadata.md"
  local codex_exit validation_exit timeout_status started finished
  local events diff_lines proof_lines placeholders forbidden changed_files

  codex_exit="$(cat "${dir}/codex_exit_code.txt" 2>/dev/null || echo missing)"
  validation_exit="$(cat "${dir}/validation_exit_code.txt" 2>/dev/null || echo missing)"
  timeout_status="no"
  [[ -f "${dir}/timeout.txt" ]] && timeout_status="yes"
  started="$(read_field "${meta}" "started_at_utc")"
  finished="$(read_field "${meta}" "finished_at_utc")"
  events="$(count_lines "${dir}/codex_events.jsonl")"
  diff_lines="$(count_lines "${dir}/BenchmarkTask.diff")"
  changed_files="$(count_lines "${dir}/workspace_files.txt")"
  placeholders="$(count_rg '\\b(sorry|admit|sorryAx)\\b' "${dir}/BenchmarkTask.after.lean")"
  forbidden="$(count_rg '^[[:space:]]*(axiom|opaque|unsafe)[[:space:]]' "${dir}/BenchmarkTask.after.lean")"

  proof_lines="unknown"
  if [[ -f "${dir}/BenchmarkTask.after.lean" ]]; then
    proof_lines="$(awk '
      BEGIN { in_proof = 0; count = 0 }
      /:= *by/ { in_proof = 1 }
      in_proof { count++ }
      END { print count }
    ' "${dir}/BenchmarkTask.after.lean")"
  fi

  printf '%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\n' \
    "${condition}" "${codex_exit}" "${validation_exit}" "${timeout_status}" \
    "${started:-unknown}" "${finished:-unknown}" "${events}" "${diff_lines}" \
    "${proof_lines}" "${placeholders}" "${forbidden}"
}

task="$(basename "$(dirname "${result_root}")")"
timestamp="$(basename "${result_root}")"
analysis="${result_root}/RUN_ANALYSIS.md"
metrics="${result_root}/metrics.tsv"

{
  printf 'condition\tcodex_exit\tvalidation_exit\ttimeout\tstarted_at_utc\tfinished_at_utc\tcodex_event_lines\tdiff_lines\tproof_lines\tplaceholder_count\tforbidden_decl_count\n'
  summarize_condition condition_a
  summarize_condition condition_c
} > "${metrics}"

a_validation="$(awk -F'\t' '$1 == "condition_a" { print $3 }' "${metrics}")"
c_validation="$(awk -F'\t' '$1 == "condition_c" { print $3 }' "${metrics}")"
a_timeout="$(awk -F'\t' '$1 == "condition_a" { print $4 }' "${metrics}")"
c_timeout="$(awk -F'\t' '$1 == "condition_c" { print $4 }' "${metrics}")"

{
  echo "# Run Analysis"
  echo
  echo "- task: \`${task}\`"
  echo "- run_timestamp: \`${timestamp}\`"
  echo "- result_root: \`${result_root}\`"
  echo
  echo "## Outcome"
  echo
  echo "- Condition A validation exit: \`${a_validation:-missing}\`"
  echo "- Condition A timeout: \`${a_timeout:-missing}\`"
  echo "- Condition C validation exit: \`${c_validation:-missing}\`"
  echo "- Condition C timeout: \`${c_timeout:-missing}\`"
  echo
  if [[ "${a_validation:-missing}" != "0" && "${c_validation:-missing}" == "0" ]]; then
    echo "Interpretation: Condition A failed while Condition C passed under the same run protocol."
  elif [[ "${a_validation:-missing}" == "0" && "${c_validation:-missing}" == "0" ]]; then
    echo "Interpretation: both conditions passed; this task may not separate library access from the bare environment."
  elif [[ "${a_validation:-missing}" != "0" && "${c_validation:-missing}" != "0" ]]; then
    echo "Interpretation: both conditions failed; inspect failure modes before drawing conclusions."
  else
    echo "Interpretation: Condition A passed while Condition C failed; inspect harness or task setup."
  fi
  echo
  echo "## Metrics"
  echo
  echo '```tsv'
  cat "${metrics}"
  echo '```'
  echo
  echo "## Failure Notes"
  echo
  for condition in condition_a condition_c; do
    echo
    echo "### ${condition}"
    if [[ -f "${result_root}/${condition}/timeout.txt" ]]; then
      echo
      cat "${result_root}/${condition}/timeout.txt"
    fi
    if [[ -f "${result_root}/${condition}/validation.log" ]]; then
      echo
      echo '```text'
      tail -40 "${result_root}/${condition}/validation.log"
      echo '```'
    fi
  done
} > "${analysis}"

echo "wrote run analysis:"
echo "  ${analysis}"
echo "wrote run metrics:"
echo "  ${metrics}"
