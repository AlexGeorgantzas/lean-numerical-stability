#!/usr/bin/env python3
"""Rebuild the deterministic, non-scientific H00-00 canary source PDF."""

from __future__ import annotations

import argparse
from pathlib import Path

from reportlab.lib.pagesizes import letter
from reportlab.pdfgen import canvas


def build(output: Path) -> None:
    output.parent.mkdir(parents=True, exist_ok=True)
    pdf = canvas.Canvas(
        str(output),
        pagesize=letter,
        invariant=1,
        pageCompression=1,
    )
    width, height = letter
    pdf.setTitle("HighamBench Infrastructure Canary H00-00")
    pdf.setAuthor("HighamBench")
    pdf.setFont("Helvetica-Bold", 18)
    pdf.drawString(72, height - 82, "HighamBench Infrastructure Canary")
    pdf.setFont("Helvetica", 11)
    pdf.drawString(72, height - 108, "Task H00-00 - synthetic setup test (not scientific evidence)")
    pdf.setLineWidth(0.6)
    pdf.line(72, height - 123, width - 72, height - 123)
    pdf.setFont("Helvetica-Bold", 13)
    pdf.drawString(72, height - 162, "Statement")
    pdf.setFont("Helvetica", 12)
    pdf.drawString(72, height - 190, "For every real number x, prove that x + 0 = x.")
    pdf.setFont("Helvetica", 10)
    pdf.drawString(
        72,
        height - 235,
        "Purpose: verify source staging, condition isolation, Lean proof validation,",
    )
    pdf.drawString(
        72,
        height - 250,
        "faithfulness auditing, token/time telemetry, and immutable result sealing.",
    )
    pdf.drawString(72, 54, "H00-00 | frozen synthetic source | page 1 of 1")
    pdf.showPage()
    pdf.save()


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("output", type=Path)
    args = parser.parse_args()
    build(args.output)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
