# Licensing and provenance policy

The root [`LICENSE`](../../LICENSE) is the default MIT license for files that
do not carry a different per-file notice. A file with an explicit Apache-2.0
notice is instead governed by
[`LICENSES/Apache-2.0.txt`](../../LICENSES/Apache-2.0.txt). Moving a file never
changes its license, copyright holder, or authorship.

## Audited state

The organization audit on 2026-07-22 found 148 production Lean files with
Apache-2.0 notices. Five of those are evidenced Mathlib adaptations or
backports under `NumStability/Upstream/Lindemann`; their exact pull requests,
commit hashes, authors, and copyright holders are recorded in
[`THIRD_PARTY_NOTICES.md`](../../THIRD_PARTY_NOTICES.md).

The other Apache-marked files are repository files with explicit per-file
notices. Their notices are authoritative; they must not be converted to MIT as
a side effect of naming or architecture work.

## Required form

New original Lean files use `SPDX-License-Identifier: MIT`. Existing
Apache-2.0 files retain their attribution and use
`SPDX-License-Identifier: Apache-2.0` plus the canonical
`LICENSES/Apache-2.0.txt` reference. Compatibility wrappers contain no copied
implementation and therefore use the repository default unless they state
otherwise.

`tools/architecture/check_provenance.py` enforces license pointers and the
known upstream attribution records in CI. The separate, review-only
`normalize_apache_notices.py` utility fixes legacy license pointers without
rewriting copyright or author lines.

See [`../../CONTRIBUTING.md`](../../CONTRIBUTING.md) before adding adapted or
backported code.
