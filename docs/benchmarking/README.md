# Benchmark-candidate document

[`higham_exercise_candidates.tex`](higham_exercise_candidates.tex) is the
tracked source of the benchmark-candidate report. Its PDF is generated output
and is intentionally not versioned.

With a TeX distribution and `latexmk` installed, rebuild it from this directory:

```text
latexmk -pdf -interaction=nonstopmode higham_exercise_candidates.tex
```

Run `latexmk -c` afterward to remove intermediate files. Commit changes to the
TeX source, not the generated PDF or auxiliary files.
