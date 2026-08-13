#!/usr/bin/env python3
"""Install the repository-owned HighamBench faithfulness skill for this user."""

from __future__ import annotations

import os
import shutil
import sys
from pathlib import Path

SCRIPT_DIR = Path(__file__).resolve().parent
AUDIT_ROOT = SCRIPT_DIR.parent
SKILL_NAME = "highambench-faithfulness-audit"
SOURCE = AUDIT_ROOT / "skill" / SKILL_NAME


def destination_root() -> Path:
    configured = os.environ.get("CODEX_HOME")
    return Path(configured).expanduser() if configured else Path.home() / ".codex"


def install() -> Path:
    if not (SOURCE / "SKILL.md").is_file():
        raise RuntimeError(f"repository skill copy is incomplete: {SOURCE}")
    destination = destination_root() / "skills" / SKILL_NAME
    for source_path in sorted(path for path in SOURCE.rglob("*") if path.is_file()):
        relative = source_path.relative_to(SOURCE)
        target_path = destination / relative
        target_path.parent.mkdir(parents=True, exist_ok=True)
        shutil.copy2(source_path, target_path)
    return destination


def main() -> int:
    try:
        destination = install()
    except (OSError, RuntimeError) as error:
        print(f"skill installation error: {error}", file=sys.stderr)
        return 2
    print(destination)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
