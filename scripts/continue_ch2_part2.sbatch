#!/bin/bash
#SBATCH --job-name=hdp-ch2p2-codex
#SBATCH --time=06:50:00
#SBATCH --cpus-per-task=4
#SBATCH --mem=32G
#SBATCH --output=slurm/ch2p2-%j.out
#SBATCH --error=slurm/ch2p2-%j.err

set -euo pipefail

REPO="/u501/m2fetrat/MyCodes/lean-fp-analysis"
HANDOFF="${REPO}/docs/ch2_part2_sbatch_handoff.md"
SOURCE_PDF="${REPO}/helper_lean_code/Chapter02_Concentration of sums of independent random variables_part2.pdf"
LOG_DIR="${REPO}/slurm"

cd "$REPO"
mkdir -p "$LOG_DIR"

export PATH="${HOME}/.elan/bin:${PATH}"
export CODEX_HOME="${CODEX_HOME:-${HOME}/.codex}"

if [[ -z "${CODEX_BIN:-}" ]]; then
  if command -v codex >/dev/null 2>&1; then
    CODEX_BIN="$(command -v codex)"
  elif [[ -x "${HOME}/.vscode-server/extensions/openai.chatgpt-26.602.71036-linux-x64/bin/linux-x86_64/codex" ]]; then
    CODEX_BIN="${HOME}/.vscode-server/extensions/openai.chatgpt-26.602.71036-linux-x64/bin/linux-x86_64/codex"
  else
    echo "Could not find Codex CLI. Set CODEX_BIN=/absolute/path/to/codex and resubmit." >&2
    exit 1
  fi
fi

LAST_MESSAGE="${LOG_DIR}/ch2p2-last-${SLURM_JOB_ID:-manual}.md"

echo "== HDP Chapter 2 part 2 Codex continuation =="
echo "Repo: $REPO"
echo "Handoff: $HANDOFF"
echo "Source PDF: $SOURCE_PDF"
echo "Codex CLI: $CODEX_BIN"
echo "Last-message output: $LAST_MESSAGE"
echo "Started: $(date -Is)"
echo

if [[ ! -r "$HANDOFF" ]]; then
  echo "Missing handoff prompt: $HANDOFF" >&2
  exit 1
fi

if [[ ! -r "$SOURCE_PDF" ]]; then
  echo "Missing Chapter 2 part 2 PDF: $SOURCE_PDF" >&2
  exit 1
fi

echo "== Tool versions =="
"$CODEX_BIN" --version
lake --version
echo

echo "== Initial git status =="
git status --short
echo

CODEX_BASE_ARGS=(
  exec
  -C "$REPO"
  --sandbox workspace-write
  --ask-for-approval never
  -c shell_environment_policy.inherit=all
  --output-last-message "$LAST_MESSAGE"
)

if [[ -n "${CODEX_RESUME_SESSION:-}" ]]; then
  echo "== Running: codex exec resume ${CODEX_RESUME_SESSION} =="
  "$CODEX_BIN" "${CODEX_BASE_ARGS[@]}" resume "$CODEX_RESUME_SESSION" - < "$HANDOFF"
elif [[ "${CODEX_RESUME_LAST:-0}" == "1" ]]; then
  echo "== Running: codex exec resume --last =="
  "$CODEX_BIN" "${CODEX_BASE_ARGS[@]}" resume --last - < "$HANDOFF"
else
  echo "== Running: codex exec with handoff prompt =="
  "$CODEX_BIN" "${CODEX_BASE_ARGS[@]}" - < "$HANDOFF"
fi

echo
echo "== Final git status =="
git status --short
echo
echo "Finished: $(date -Is)"
