#!/usr/bin/env bash
set -euo pipefail

run_root="${1:-}"

if [[ -z "${run_root}" ]]; then
  echo "usage: benchmark/scripts/cleanup_run_workspaces.sh <run-root>" >&2
  exit 2
fi

case "${run_root}" in
  /tmp/lean-fp-benchmark-runs/*|/private/tmp/lean-fp-benchmark-runs/*) ;;
  *)
    echo "refusing to remove path outside /tmp/lean-fp-benchmark-runs: ${run_root}" >&2
    exit 1
    ;;
esac

rm -rf "${run_root}"
echo "removed benchmark workspace:"
echo "  ${run_root}"
