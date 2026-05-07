#!/usr/bin/env python3
"""Run a command with a hard process-group timeout.

This is intentionally small and dependency-free because macOS does not provide
GNU `timeout` by default.  The child is started in a new process group so a
timeout can terminate Codex and any children it spawned.
"""

from __future__ import annotations

import argparse
import os
import signal
import subprocess
import sys
from pathlib import Path


def terminate_process_group(pgid: int) -> None:
    try:
        os.killpg(pgid, signal.SIGTERM)
    except ProcessLookupError:
        return


def kill_process_group(pgid: int) -> None:
    try:
        os.killpg(pgid, signal.SIGKILL)
    except ProcessLookupError:
        return


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--timeout-seconds", type=float, required=True)
    parser.add_argument("--timeout-file", required=True)
    parser.add_argument("--stdout", required=True)
    parser.add_argument("--stderr", required=True)
    parser.add_argument("--grace-seconds", type=float, default=10.0)
    parser.add_argument("command", nargs=argparse.REMAINDER)
    args = parser.parse_args()

    command = args.command
    if command and command[0] == "--":
        command = command[1:]
    if not command:
        parser.error("missing command")

    timeout_file = Path(args.timeout_file)
    timeout_file.parent.mkdir(parents=True, exist_ok=True)

    with open(args.stdout, "w") as stdout, open(args.stderr, "w") as stderr:
        proc = subprocess.Popen(
            command,
            stdin=sys.stdin,
            stdout=stdout,
            stderr=stderr,
            start_new_session=True,
        )
        try:
            return proc.wait(timeout=args.timeout_seconds)
        except subprocess.TimeoutExpired:
            timeout_file.write_text(
                f"timed out after {args.timeout_seconds:g} seconds\n",
                encoding="utf-8",
            )
            terminate_process_group(proc.pid)
            try:
                proc.wait(timeout=args.grace_seconds)
            except subprocess.TimeoutExpired:
                kill_process_group(proc.pid)
                proc.wait()
            return 124


if __name__ == "__main__":
    raise SystemExit(main())
