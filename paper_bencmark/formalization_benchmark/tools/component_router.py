"""Task-neutral numerical component routing from a frozen declaration atlas.

This API vocabulary contains standard algorithms and lower-level deterministic
lemmas, never benchmark conclusions. It is applied identically to both atlases.
"""
from __future__ import annotations

from collections import Counter
import re
from typing import Any, Mapping


# Mathematical aliases, algorithm definitions, deterministic support.
FAMILIES: dict[str, tuple[tuple[str, ...], tuple[str, ...], tuple[str, ...]]] = {
    "dot": (("dot product", "inner product", "scalar product"),
            ("NumStability.fl_dotProduct",), ("NumStability.dotProduct_backward_error",)),
    "recursive_sum": (("recursive summation", "recursive sum", "recursive block",
                       "recursive working precision block", "sequential summation",
                       "running sum"),
            ("NumStability.fl_recursiveSum",), ("NumStability.recursiveSum_forward_error_bound",)),
    "compensated_sum": (("compensated summation", "compensated accumulation",
                         "kahan summation", "kahan sum"),
            ("NumStability.fl_kahanSum",), ()),
    "superblock_dot": (("superblock dot product", "superblocked dot product"),
            ("NumStability.fl_blockDotProduct",),
            ("NumStability.blockDotProduct_backward_error",)),
    "higher_precision_recursive_sum": (("extended-precision recursive", "higher-precision recursive",
                                       "extended precision recursive", "higher precision recursive"),
            ("NumStability.fl_higherPrecisionRecursiveSum",),
            ("NumStability.fl_higherPrecisionRecursiveSum_abs_error_le_gamma",)),
    "pairwise_sum": (("pairwise summation", "pairwise sum", "pairwise accumulation",
                      "summation tree", "balanced tree"),
            ("NumStability.fl_clog2PairwiseSum", "NumStability.fl_pairwiseSum",
             "NumStability.SumTree"),
            ("NumStability.clog2PairwiseSum_backward_error",)),
    "general_sum_tree": (("general summation", "computational tree", "computation tree"),
            ("NumStability.SumTree",), ()),
    "horner": (("horner",), ("NumStability.fl_hornerDesc",),
            ("NumStability.fl_hornerDesc_forward_error_bound",
             "NumStability.fl_hornerDesc_backward_error_coefficients")),
    "matvec": (("matrix-vector", "matrix vector", "matvec"),
            ("NumStability.fl_matVec",), ("NumStability.matVec_backward_error",)),
    "matmul": (("matrix-matrix", "matrix matrix", "matrix multiplication", "matmul"),
            ("NumStability.fl_matMul",), ()),
    "triangular_solve": (("triangular solve", "triangular system", "triangular substitution",
                           "forward substitution", "back substitution"),
            ("NumStability.fl_forwardSub", "NumStability.fl_backSub"),
            ("NumStability.triangularSolve_backward_error",)),
    "lu": (("lu factorization", "lu decomposition", "doolittle", "gaussian elimination"),
            ("NumStability.DoolittleLU",), ("NumStability.doolittle_backward_error",)),
    "cholesky": (("cholesky",), ("NumStability.fl_cholesky",),
            ("NumStability.fl_cholesky_backward_error",)),
    "householder_qr": (("householder qr", "householder reflector"),
            ("NumStability.fl_householderApply",), ()),
    "givens": (("givens rotation", "givens qr"),
            ("NumStability.fl_givensApply",), ()),
    "modified_gram_schmidt": (("modified gram schmidt", "modified gram-schmidt"),
            ("NumStability.flMGSStep",), ()),
    "fft": (("fast fourier transform", "fft"),
            ("NumStability.higham24RoundedRadix2FFT",), ()),
    "strassen": (("strassen",), ("NumStability.higham23Strassen2",), ()),
    "least_squares_backward": (
        ("least-squares backward error", "least squares backward error"),
        ("NumStability.lsNormwiseBackwardErrorMatrixOnlyEtaF",
         "NumStability.RectLSNormalEquations"),
        ("NumStability.RectLSNormalEquations.iff_isLeastSquaresMinimizer",),
    ),
    "newton_form": (("newton interpolation", "newton form"),
            ("NumStability.newtonForm",), ()),
}
BRIDGES = {
    "pairwise_sum": ("NumStability.SumTree.statisticalRunningErrorContribution_rms_le",),
    "general_sum_tree": ("NumStability.SumTree.statisticalRunningErrorContribution_rms_le",),
}
CORE = {
    "floating_point": ("NumStability.FPModel", "NumStability.gamma"),
    "probability": ("MeasureTheory.Measure", "ProbabilityTheory.iIndepFun",
                    "NumStability.FiniteProbability.eventProb",
                    "NumStability.StatisticalRoundingErrorModel"),
}
FINITE_FORMAT_CORE = (
    "NumStability.FloatingPointFormat",
    "NumStability.FloatingPointFormat.finiteSystem",
    "NumStability.FloatingPointFormat.nearestRoundingToFinite",
)
ROLE_ORDER = ("algorithm", "floating_point", "probability", "deterministic_error", "norm_or_bridge")
ROLE_QUOTAS = {"algorithm": 2, "floating_point": 5, "probability": 4,
               "deterministic_error": 1, "norm_or_bridge": 1}


def routing_anchor_text(packet: Mapping[str, Any]) -> str:
    """Use only the positive result title for anchor activation.

    Scope constraints and explanatory lines routinely name *forbidden*
    specializations. They remain visible to ranking and the formalizer, but
    must not activate an algorithm family as if it were requested.
    """
    return str(packet.get("selected_result", ""))


def _active_families(source_text: str) -> list[str]:
    # Hyphenation is orthographic, not a different algorithm family:
    # "Gaussian-elimination solution" must match "gaussian elimination".
    source = " ".join(re.sub(r"[-‐‑‒–—]", " ", source_text.casefold()).split())
    return [family for family, (aliases, _, _) in FAMILIES.items()
            if any(re.search(r"(?<![a-z])" + re.escape(
                " ".join(re.sub(r"[-‐‑‒–—]", " ", alias.casefold()).split())
            ) + r"(?![a-z])", source) for alias in aliases)]


def _needs_finite_format(source_text: str) -> bool:
    """Recognize a public finite-format interface from positive title terms.

    This does not infer the target theorem or inspect task identifiers. The
    ordinary generic FP/gamma cards remain available alongside these cards.
    """
    source = " ".join(re.sub(r"[-‐‑‒–—]", " ", source_text.casefold()).split())
    return any(phrase in source for phrase in (
        "nearest rounding", "rounding to nearest", "faithful rounding",
        "unit in the first place", "subnormal", "representable",
    ))


def _fallback_role(record: Mapping[str, Any]) -> str | None:
    name = str(record.get("name", "")).casefold()
    module = str(record.get("module", "")).casefold()
    kind = str(record.get("kind", ""))
    if any(word in name for word in ("finiteprobability", "statisticalrounding", "eventprob")):
        return "probability"
    if name.endswith(".fpmodel") or (
        name.endswith(".gamma") and ("round" in module or "floating" in module)
    ):
        return "floating_point"
    if kind in {"def", "abbrev", "inductive", "structure"} and (
        ".algorithms." in module or name.startswith("fl_") or ".fl_" in name
    ):
        return "algorithm"
    if kind in {"theorem", "lemma"} and any(word in name for word in (
        "backward_error", "forward_error", "error_bound", "residual"
    )):
        return "deterministic_error"
    # Broad norm/condition words occur in unrelated source-specific results.
    # Until a generic, checked public interface exists, leave this slot empty.
    return None


def select_component_roots(
    ranked: list[dict[str, Any]], *, records: list[dict[str, Any]],
    source_text: str, limit: int, strict_stochastic_roles: bool = False,
) -> list[dict[str, Any]]:
    """Prefer exact public API components, then bounded lexical fallback."""
    if limit < 1 or limit > 12:
        raise ValueError("component root limit must be between 1 and 12")
    active = _active_families(source_text)
    wants_probability = any(word in source_text.casefold() for word in
                            ("probability", "probabilistic", "random", "stochastic", "expectation"))
    by_name = {str(item["record"]["name"]): item for item in ranked}
    # Anchor lookup is against the complete frozen atlas. A foundational
    # definition need not lexically resemble the source to be relevant.
    for record in records:
        name = str(record["name"])
        if name not in by_name:
            by_name[name] = {
                "record": record, "score": 0.0,
                "matched_terms": [], "field_matches": {},
            }
    wanted: dict[str, list[str]] = {role: [] for role in ROLE_ORDER}
    for family in active:
        _, algorithms, support = FAMILIES[family]
        wanted["algorithm"].extend(algorithms)
        wanted["deterministic_error"].extend(support)
        if not strict_stochastic_roles or wants_probability:
            wanted["norm_or_bridge"].extend(BRIDGES.get(family, ()))
    if _needs_finite_format(source_text):
        wanted["floating_point"].extend(FINITE_FORMAT_CORE)
    wanted["floating_point"].extend(CORE["floating_point"])
    if wants_probability:
        wanted["probability"].extend(CORE["probability"])

    selected: list[dict[str, Any]] = []
    selected_names: set[str] = set()
    role_counts: Counter[str] = Counter()

    def add(item: dict[str, Any], role: str, anchor: bool) -> None:
        name = str(item["record"]["name"])
        if (name in selected_names or role_counts[role] >= ROLE_QUOTAS[role]
                or len(selected) >= limit):
            return
        selected.append({**item, "component_role": role, "api_anchor": anchor})
        selected_names.add(name)
        role_counts[role] += 1

    for role in ROLE_ORDER:
        for name in wanted[role]:
            if name in by_name:
                add(by_name[name], role, True)

    # Absent declarations cannot be fabricated. The same condition-neutral
    # fallback works for Mathlib-only and union-corpus retrieval.
    for role in ROLE_ORDER:
        if strict_stochastic_roles and role == "probability" and not wants_probability:
            continue
        if role_counts[role]:
            continue
        if not active and role in {"algorithm", "deterministic_error"}:
            continue
        for item in ranked:
            record = item["record"]
            if _fallback_role(record) != role:
                continue
            short = str(record["name"]).rsplit(".", 1)[-1]
            if len(short) > 48:
                continue
            if role in {"algorithm", "deterministic_error"}:
                normalized_name = re.sub(r"[^a-z]", "", short.casefold())
                family_tokens = {
                    re.sub(r"[^a-z]", "", alias.casefold())
                    for family in active for alias in FAMILIES[family][0]
                }
                if not any(token in normalized_name for token in family_tokens):
                    continue
            # Signature-only matches often rank unrelated paper-specific
            # theorems; fallback must match the public name itself.
            name_matches = item.get("field_matches", {}).get("name", [])
            if not name_matches:
                continue
            add(item, role, False)
            if role_counts[role] >= ROLE_QUOTAS[role] or len(selected) >= limit:
                break
    return selected
