#!/usr/bin/env python3
"""Compatibility entry point for manifest-wide private-proof validation.

Local proof-check timing is not a benchmark score. The former one-paper timing
path has been retired; this entry point now applies the same construction check
to every manifest paper unless ``--paper-id`` is explicitly supplied.
"""

from pathlib import Path
import sys


BENCHMARK_ROOT = Path(__file__).resolve().parents[1]
if str(BENCHMARK_ROOT) not in sys.path:
    sys.path.insert(0, str(BENCHMARK_ROOT))

from tools.check_construction import main  # noqa: E402


if __name__ == "__main__":
    raise SystemExit(main())
