"""Shared constants and helpers for HighamBench faithfulness audits."""

from __future__ import annotations

import hashlib
from pathlib import Path

AUDIT_SCHEMA_VERSION = "highambench-faithfulness-0.2"
SUPPORTED_AUDIT_SCHEMA_VERSIONS = {
    "highambench-faithfulness-0.1",
    AUDIT_SCHEMA_VERSION,
}
TASK_ID_PATTERN = r"P\d{2}-T[123]"

CLASSIFICATIONS = (
    "faithful-equivalent",
    "faithful-stronger",
    "not-faithful-weaker",
    "not-faithful-different",
    "undetermined",
)
ACCEPTED_CLASSIFICATIONS = {"faithful-equivalent", "faithful-stronger"}

SEMANTIC_CHECKS = (
    ("S01", "source-selection", "The exact paper version, passage, and surrounding result are correct."),
    ("S02", "binders-and-types", "Every binder, type, dimension, and index set has the intended meaning."),
    ("S03", "quantifier-scope", "Quantifier order, scope, witness dependence, and Skolemization are preserved."),
    ("S04", "hypotheses", "Explicit and implicit hypotheses match, including positivity and nonzero conditions."),
    ("S05", "conclusion-completeness", "Every conclusion, conjunct, case, and dependency is present."),
    ("S06", "operators-and-definitions", "Every nontrivial operator and imported definition has been unfolded and interpreted."),
    ("S07", "exact-versus-computed", "Exact, rounded, perturbed, and computed quantities are not conflated."),
    ("S08", "algorithm-linkage", "The statement remains linked to the paper's algorithm and execution model."),
    ("S09", "norm-semantics", "Norm kind, squared versus unsquared form, and componentwise versus normwise meaning match."),
    ("S10", "constants-and-indexing", "Constants, coefficients, index offsets, and parameter dependence match."),
    ("S11", "floating-point-model", "Precision, rounding mode, exceptional values, underflow, and overflow assumptions match."),
    ("S12", "relation-strength", "Equality/inequality direction, strictness, and logical strength are correct."),
    ("S13", "error-notion", "Forward, backward, mixed, residual, and stability notions are not substituted for one another."),
    ("S14", "higher-order-terms", "First-order approximations, exact remainders, and big-O terms are handled faithfully."),
    ("S15", "specialization", "Finite, scalar, real, dimensional, or other specialization/generalization is classified correctly."),
    ("S16", "nonvacuity", "The formal hypotheses are satisfiable and the conclusion is not true for an unintended trivial reason."),
)


def sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def sha256_text(value: str) -> str:
    return hashlib.sha256(value.encode("utf-8")).hexdigest()


def implication_classification(first: str, second: str) -> str:
    """Map proposition-direction verdicts to the fixed classification."""
    if "unclear" in (first, second):
        return "undetermined"
    return {
        ("yes", "yes"): "faithful-equivalent",
        ("yes", "no"): "faithful-stronger",
        ("no", "yes"): "not-faithful-weaker",
        ("no", "no"): "not-faithful-different",
    }[(first, second)]
