#!/usr/bin/env python3
"""Compatibility entry point for the manifest-wide LaTeX report builder."""

from pathlib import Path
import sys


BENCHMARK_ROOT = Path(__file__).resolve().parents[1]
if str(BENCHMARK_ROOT) not in sys.path:
    sys.path.insert(0, str(BENCHMARK_ROOT))

from tools.render_report import main  # noqa: E402


if __name__ == "__main__":
    raise SystemExit(main())
