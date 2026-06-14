#!/bin/bash
#SBATCH --job-name=hdp-ch2p2-followup
#SBATCH --time=96:50:00
#SBATCH --cpus-per-task=4
#SBATCH --mem=32G
#SBATCH --partition=KFOUNTOU
#SBATCH --output=slurm/ch2p2-followup-%j.out
#SBATCH --error=slurm/ch2p2-followup-%j.err

set -euo pipefail

REPO="/u501/m2fetrat/MyCodes/lean-fp-analysis"
HANDOFF="${HANDOFF:-${REPO}/handoff_docs/ch2_part2_followup_goal_handoff.md}"
SOURCE_PDF="${REPO}/helper_lean_code/Chapter02_Concentration of sums of independent random variables_part2.pdf"
SOLUTIONS_PDF="${REPO}/helper_lean_code/exercises_2_4_4_2_4_5_solutions.pdf"
LOG_DIR="${REPO}/slurm"
PREVIOUS_REPORT="${PREVIOUS_REPORT:-${REPO}/slurm/ch2p2-last-1452018.md}"
SBATCH_CODEX_HOME="${SBATCH_CODEX_HOME:-${HOME}/.codex-sbatch/ch2p2}"
CODEX_RESUME_SESSION="${CODEX_RESUME_SESSION:-}"
CODEX_RESUME_LAST="${CODEX_RESUME_LAST:-0}"
CODEX_ENABLE_GOALS="${CODEX_ENABLE_GOALS:-1}"

cd "$REPO"
mkdir -p "$LOG_DIR"

export PATH="${HOME}/.elan/bin:${PATH}"
export CODEX_HOME="${CODEX_HOME:-$SBATCH_CODEX_HOME}"
mkdir -p "$CODEX_HOME"
chmod 700 "$CODEX_HOME" 2>/dev/null || true

if command -v flock >/dev/null 2>&1; then
  exec 9>"${CODEX_HOME}/ch2p2.lock"
  flock -n 9 || {
    echo "Another ch2p2 Codex sbatch job is already using CODEX_HOME=$CODEX_HOME" >&2
    exit 1
  }
else
  echo "Warning: flock not found; continuing without CODEX_HOME lock." >&2
fi

if [[ ! -r "${CODEX_HOME}/auth.json" && -r "${HOME}/.codex/auth.json" ]]; then
  cp "${HOME}/.codex/auth.json" "${CODEX_HOME}/auth.json"
  chmod 600 "${CODEX_HOME}/auth.json" 2>/dev/null || true
fi

if [[ ! -r "${CODEX_HOME}/config.toml" && -r "${HOME}/.codex/config.toml" ]]; then
  cp "${HOME}/.codex/config.toml" "${CODEX_HOME}/config.toml"
  chmod 600 "${CODEX_HOME}/config.toml" 2>/dev/null || true
fi

if [[ -z "${CODEX_BIN:-}" ]]; then
  if command -v codex >/dev/null 2>&1; then
    CODEX_BIN="$(command -v codex)"
  else
    for candidate in "${HOME}"/.vscode-server/extensions/openai.chatgpt-*-linux-x64/bin/linux-x86_64/codex; do
      if [[ -x "$candidate" ]]; then
        CODEX_BIN="$candidate"
        break
      fi
    done
    if [[ -z "${CODEX_BIN:-}" ]]; then
      echo "Could not find Codex CLI. Set CODEX_BIN=/absolute/path/to/codex and resubmit." >&2
      exit 1
    fi
  fi
fi

LAST_MESSAGE="${LOG_DIR}/ch2p2-last-${SLURM_JOB_ID:-manual}.md"

echo "== HDP Chapter 2 part 2 Codex continuation =="
echo "Repo: $REPO"
echo "Handoff: $HANDOFF"
echo "Source PDF: $SOURCE_PDF"
echo "Solutions PDF: $SOLUTIONS_PDF"
echo "Previous report: $PREVIOUS_REPORT"
echo "Codex CLI: $CODEX_BIN"
echo "Codex home: $CODEX_HOME"
echo "Resume session: ${CODEX_RESUME_SESSION:-<none>}"
echo "Resume last: $CODEX_RESUME_LAST"
echo "Enable goals: $CODEX_ENABLE_GOALS"
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

if [[ ! -r "$SOLUTIONS_PDF" ]]; then
  echo "Missing corrected Exercises 2.4.4/2.4.5 solutions PDF: $SOLUTIONS_PDF" >&2
  exit 1
fi

if [[ ! -r "$PREVIOUS_REPORT" ]]; then
  echo "Missing previous Codex report: $PREVIOUS_REPORT" >&2
  exit 1
fi

echo "== Tool versions =="
"$CODEX_BIN" --version
"$CODEX_BIN" features list | sed -n '/^goals /p'
lake --version
echo

echo "== Initial git status =="
git status --short
echo

CODEX_BASE_ARGS=(
  --ask-for-approval never
)

if [[ "$CODEX_ENABLE_GOALS" == "1" ]]; then
  CODEX_BASE_ARGS+=(--enable goals)
fi

CODEX_BASE_ARGS+=(
  exec
  -C "$REPO"
  --sandbox workspace-write
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
