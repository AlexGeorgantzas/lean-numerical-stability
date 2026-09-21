"""One-agent, fail-closed faithfulness screen for Design-16 development.

This module deliberately does not replace :mod:`audit_controller`.  It is a
cheap gate for consumed development tasks: one fresh condition-blind judge,
complete dependency coverage, the complete 16-item checklist, and a binary
decision.  Scientific candidates still require the full multi-role audit.
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path
import shutil
import sys
from typing import Any

from audit_controller import AuditController, audit_evidence_manifest
from common import BenchmarkError, load_json, sha256_file, utc_now, write_json_atomic
from deployment import load_deployment
from lean_sandbox import compiler_command, extractor_command
from prepare_candidate_audit import CandidateAuditError, prepare_candidate_audit


ROOT = Path(__file__).resolve().parents[1]
SCREEN_ROOT = ROOT / "design16" / "audit"
SCREEN_PROMPT = SCREEN_ROOT / "prompts" / "faithfulness_screen.md"
SCREEN_SCHEMA = SCREEN_ROOT / "schemas" / "faithfulness_screen.schema.json"
SEMANTIC_CHECK_IDS = [f"S{index:02d}" for index in range(1, 17)]
FAITHFUL_CLASSIFICATIONS = {"faithful-equivalent", "faithful-stronger"}
CLASSIFICATION_BY_IMPLICATIONS = {
    ("yes", "yes"): "faithful-equivalent",
    ("yes", "no"): "faithful-stronger",
    ("no", "yes"): "unfaithful-weaker",
    ("no", "no"): "unfaithful-different",
}


def _nonempty_text(value: Any) -> bool:
    return isinstance(value, str) and bool(value.strip())


def _text_list(value: Any) -> bool:
    return isinstance(value, list) and all(_nonempty_text(item) for item in value)


def _dependency_identity(dossier: dict[str, Any]) -> list[tuple[str, str]]:
    if dossier.get("schema_version") != "candidate-semantic-dossier-1":
        raise BenchmarkError("Design-16 screen requires a blinded semantic dossier")
    dependencies = dossier.get("dependencies")
    if not isinstance(dependencies, list) or not dependencies:
        raise BenchmarkError("blinded semantic dossier has no dependency inventory")
    identities: list[tuple[str, str]] = []
    for index, dependency in enumerate(dependencies, start=1):
        expected_id = f"D{index:03d}"
        if (
            not isinstance(dependency, dict)
            or dependency.get("id") != expected_id
            or not _nonempty_text(dependency.get("name"))
        ):
            raise BenchmarkError(
                f"blinded semantic dossier dependency is malformed: {expected_id}"
            )
        identities.append((expected_id, dependency["name"]))
    return identities


def _validate_mismatches(value: Any) -> None:
    fields = {"paper_requirement", "candidate_mismatch", "severity"}
    if not isinstance(value, list):
        raise BenchmarkError("screen mismatches are malformed")
    for mismatch in value:
        if (
            not isinstance(mismatch, dict)
            or set(mismatch) != fields
            or mismatch.get("severity") not in {"critical", "major", "minor"}
            or not _nonempty_text(mismatch.get("paper_requirement"))
            or not _nonempty_text(mismatch.get("candidate_mismatch"))
        ):
            raise BenchmarkError("screen mismatch record is malformed")


def validate_screen_output(
    value: dict[str, Any],
    *,
    paper_sha256: str,
    semantic_sha256: str,
    dependencies: list[tuple[str, str]],
) -> None:
    """Validate completeness and the fail-closed binary screen policy."""

    expected_fields = {
        "schema_version",
        "role",
        "paper_sha256",
        "candidate_semantic_sha256",
        "dependency_coverage",
        "semantic_checklist",
        "domain_assessment",
        "implications",
        "classification",
        "verdict",
        "mismatches",
        "rationale",
    }
    if (
        not isinstance(value, dict)
        or set(value) != expected_fields
        or value.get("schema_version")
        != "formalization-design16-faithfulness-screen-1"
        or value.get("role") != "condition-blind-faithfulness-screen"
        or value.get("paper_sha256") != paper_sha256
        or value.get("candidate_semantic_sha256") != semantic_sha256
        or not _nonempty_text(value.get("rationale"))
    ):
        raise BenchmarkError("Design-16 screen output failed its top-level contract")

    coverage = value.get("dependency_coverage")
    dependency_fields = {
        "id",
        "name",
        "interpretation",
        "effect_on_target",
        "paper_match",
        "status",
    }
    if not isinstance(coverage, list) or len(coverage) != len(dependencies):
        raise BenchmarkError("screen omitted one or more dependency records")
    for record, (dependency_id, dependency_name) in zip(
        coverage, dependencies, strict=True
    ):
        if (
            not isinstance(record, dict)
            or set(record) != dependency_fields
            or record.get("id") != dependency_id
            or record.get("name") != dependency_name
            or record.get("status") not in {"pass", "fail", "not-applicable"}
            or any(
                not _nonempty_text(record.get(field))
                for field in dependency_fields - {"status"}
            )
        ):
            raise BenchmarkError(
                f"screen dependency record does not match {dependency_id}"
            )

    checklist = value.get("semantic_checklist")
    check_fields = {
        "id",
        "status",
        "paper_evidence",
        "candidate_evidence",
        "reasoning",
    }
    if not isinstance(checklist, list) or len(checklist) != 16:
        raise BenchmarkError("screen omitted one or more mandatory semantic checks")
    for record, check_id in zip(checklist, SEMANTIC_CHECK_IDS, strict=True):
        if (
            not isinstance(record, dict)
            or set(record) != check_fields
            or record.get("id") != check_id
            or record.get("status") not in {"pass", "fail", "not-applicable"}
            or any(
                not _nonempty_text(record.get(field))
                for field in check_fields - {"id", "status"}
            )
        ):
            raise BenchmarkError(f"screen semantic check is malformed: {check_id}")

    domain = value.get("domain_assessment")
    domain_fields = {
        "covers_every_source_case",
        "source_cases_omitted",
        "unjustified_extra_candidate_assumptions",
        "vacuity_risks",
        "genuine_added_strength",
        "reasoning",
    }
    if (
        not isinstance(domain, dict)
        or set(domain) != domain_fields
        or not isinstance(domain.get("covers_every_source_case"), bool)
        or not all(
            _text_list(domain.get(field))
            for field in (
                "source_cases_omitted",
                "unjustified_extra_candidate_assumptions",
                "vacuity_risks",
                "genuine_added_strength",
            )
        )
        or not _nonempty_text(domain.get("reasoning"))
    ):
        raise BenchmarkError("screen domain assessment is malformed")

    implications = value.get("implications")
    implication_fields = {"candidate_implies_source", "source_implies_candidate"}
    if not isinstance(implications, dict) or set(implications) != implication_fields:
        raise BenchmarkError("screen implication record is malformed")
    verdicts: list[str] = []
    for direction in ("candidate_implies_source", "source_implies_candidate"):
        record = implications.get(direction)
        if (
            not isinstance(record, dict)
            or set(record) != {"verdict", "reasoning"}
            or record.get("verdict") not in {"yes", "no"}
            or not _nonempty_text(record.get("reasoning"))
        ):
            raise BenchmarkError(f"screen implication is malformed: {direction}")
        verdicts.append(record["verdict"])

    expected_classification = CLASSIFICATION_BY_IMPLICATIONS[tuple(verdicts)]
    classification = value.get("classification")
    verdict = value.get("verdict")
    if classification != expected_classification:
        raise BenchmarkError("screen classification contradicts its implications")
    expected_verdict = (
        "faithful" if classification in FAITHFUL_CLASSIFICATIONS else "unfaithful"
    )
    if verdict != expected_verdict:
        raise BenchmarkError("screen verdict contradicts its classification")
    _validate_mismatches(value.get("mismatches"))

    restrictions = [
        *domain["source_cases_omitted"],
        *domain["unjustified_extra_candidate_assumptions"],
        *domain["vacuity_risks"],
    ]
    recorded_failures = [
        record for record in [*coverage, *checklist] if record["status"] == "fail"
    ]
    if verdict == "faithful":
        if (
            not domain["covers_every_source_case"]
            or restrictions
            or recorded_failures
            or value["mismatches"]
        ):
            raise BenchmarkError(
                "screen accepted despite a domain restriction, vacuity risk, or failure"
            )
        if classification == "faithful-stronger" and not domain["genuine_added_strength"]:
            raise BenchmarkError("screen claimed strengthening without genuine added strength")
        if classification == "faithful-equivalent" and domain["genuine_added_strength"]:
            raise BenchmarkError("equivalent screen result claims unmatched added strength")
    else:
        if not value["mismatches"]:
            raise BenchmarkError("unfaithful screen result has no concrete mismatch")
        if not domain["covers_every_source_case"] and not (
            domain["source_cases_omitted"]
            or domain["unjustified_extra_candidate_assumptions"]
            or domain["vacuity_risks"]
        ):
            raise BenchmarkError(
                "screen denied full-domain coverage without identifying the restriction"
            )


def _copy_read_only(source: Path, destination: Path) -> None:
    if not source.is_file() or source.is_symlink():
        raise BenchmarkError(f"Design-16 screen input is missing or unsafe: {source}")
    destination.parent.mkdir(parents=True, exist_ok=True)
    shutil.copyfile(source, destination)
    destination.chmod(0o400)


class Design16FaithfulnessScreen(AuditController):
    """Run one fresh condition-blind judge and seal its development decision."""

    def run_screen(
        self,
        *,
        task_id: str,
        paper_path: Path,
        paper_sha256: str,
        source_packet: Path,
        dossier_path: Path,
        semantic_sha256: str,
        screen_root: Path,
    ) -> dict[str, Any]:
        if screen_root.exists() or screen_root.is_symlink():
            raise BenchmarkError("Design-16 screen root must not already exist")
        if sha256_file(paper_path) != paper_sha256:
            raise BenchmarkError("Design-16 screen paper hash changed")
        dossier = load_json(dossier_path)
        if dossier.get("semantic_sha256") != semantic_sha256:
            raise BenchmarkError("Design-16 screen semantic hash changed")
        dependencies = _dependency_identity(dossier)

        workspace = screen_root / "workspace"
        workspace.mkdir(parents=True, mode=0o700)
        _copy_read_only(paper_path, workspace / "paper.pdf")
        _copy_read_only(source_packet, workspace / "source_packet.md")
        _copy_read_only(dossier_path, workspace / "blind_semantic_dossier.json")
        prompt = (
            SCREEN_PROMPT.read_text(encoding="utf-8")
            + f"\n\nPaper SHA-256: `{paper_sha256}`\n"
            + f"Candidate semantic SHA-256: `{semantic_sha256}`\n"
        )
        output, telemetry = self._fresh_role(
            role="condition-blind-faithfulness-screen",
            prompt=prompt,
            workspace=workspace,
            role_root=screen_root / "role",
            schema=SCREEN_SCHEMA,
            validate=lambda value: validate_screen_output(
                value,
                paper_sha256=paper_sha256,
                semantic_sha256=semantic_sha256,
                dependencies=dependencies,
            ),
        )
        write_json_atomic(screen_root / "judgment.json", output, mode=0o400)
        decision = {
            "schema_version": "formalization-design16-faithfulness-screen-decision-1",
            "scientific_status": "DEVELOPMENT_SCREEN_ONLY_NOT_SCIENTIFIC_AUDIT",
            "task_id": task_id,
            "paper_sha256": paper_sha256,
            "candidate_semantic_sha256": semantic_sha256,
            "completed_at_utc": utc_now(),
            "verdict": output["verdict"],
            "accepted": output["verdict"] == "faithful",
            "classification": output["classification"],
            "implications": output["implications"],
            "domain_assessment": output["domain_assessment"],
            "mismatches": output["mismatches"],
            "rationale": output["rationale"],
            "condition_blind": True,
            "attempt_blind": True,
            "fresh_stateless_judge": True,
            "auditor_telemetry": telemetry,
            "auditor_tokens_excluded_from_benchmark": True,
            "full_scientific_audit_required": True,
            "omitted_full_audit_roles": [
                "independent-source-contract",
                "blind-translation",
                "independent-roundtrip-judge",
                "conditional-adjudicator",
            ],
            "evidence_manifest": audit_evidence_manifest(screen_root),
        }
        write_json_atomic(screen_root / "decision.json", decision, mode=0o400)
        return decision


def run_cli(args: argparse.Namespace) -> dict[str, Any]:
    """Prepare a blind dossier, then run the paid one-agent screen.

    Dossier extraction and the judge are logged separately.  The private
    semantic manifest never enters the judge workspace.
    """

    output_root = args.output_root.expanduser().resolve()
    if output_root.exists() or output_root.is_symlink():
        raise BenchmarkError("Design-16 screen output root must not already exist")
    output_root.mkdir(parents=True, mode=0o700)
    deployment = load_deployment(args.deployment)
    candidate = args.candidate.expanduser().resolve()
    paper = args.paper.expanduser().resolve()
    source_packet = args.source_packet.expanduser().resolve()
    condition = args.condition.upper()
    if condition not in {"N", "L"}:
        raise BenchmarkError("Design-16 screen condition must be N or L")
    if not paper.is_file() or paper.is_symlink():
        raise BenchmarkError("Design-16 screen paper is missing or unsafe")
    if not source_packet.is_file() or source_packet.is_symlink():
        raise BenchmarkError("Design-16 screen source packet is missing or unsafe")

    preparation_root = output_root / "preparation"
    preparation_root.mkdir(mode=0o700)
    scratch = preparation_root / "scratch"
    scratch.mkdir(mode=0o700)
    helper = Path(__file__).with_name("declaration_dossier.lean")
    blind, private = prepare_candidate_audit(
        candidate,
        compiler_command=compiler_command(deployment, condition),
        extractor_command=extractor_command(deployment, condition, helper),
        compiler_environment={},
        extractor_environment={},
        scratch_root=scratch,
        timeout_seconds=float(args.validation_timeout_seconds),
    )
    dossier_path = preparation_root / "blind_semantic_dossier.json"
    private_path = preparation_root / "private_semantic_manifest.json"
    write_json_atomic(private_path, private, mode=0o400)
    write_json_atomic(dossier_path, blind, mode=0o400)
    semantic_sha256 = blind.get("semantic_sha256")
    if (
        not isinstance(semantic_sha256, str)
        or private.get("blind_semantic_sha256") != semantic_sha256
    ):
        raise BenchmarkError("Design-16 prepared dossier hash contract failed")

    screen = Design16FaithfulnessScreen(
        codex_binary=deployment.codex_binary,
        code_mode_host_sha256=deployment.code_mode_host_sha256,
        auth_file=deployment.auth_file,
        model=args.model,
        reasoning_effort=args.reasoning_effort,
        timeout_seconds=float(args.timeout_seconds),
        maximum_infrastructure_retries=int(args.infrastructure_retries),
        bwrap_binary=deployment.bwrap_binary,
        offline_shell=deployment.offline_shell,
        toolchain_root=deployment.toolchain_root,
        packages_root=deployment.packages_root,
    )
    decision = screen.run_screen(
        task_id=args.task_id,
        paper_path=paper,
        paper_sha256=sha256_file(paper),
        source_packet=source_packet,
        dossier_path=dossier_path,
        semantic_sha256=semantic_sha256,
        screen_root=output_root / "screen",
    )
    result = {
        "schema_version": "formalization-design16-faithfulness-screen-run-1",
        "scientific_status": "DEVELOPMENT_SCREEN_ONLY_NOT_SCIENTIFIC_AUDIT",
        "task_id": args.task_id,
        "candidate_sha256": private["candidate"]["sha256"],
        "candidate_semantic_sha256": semantic_sha256,
        "blind_dossier_sha256": sha256_file(dossier_path),
        "private_manifest_sha256": sha256_file(private_path),
        "decision": decision,
        "output_root": str(output_root),
    }
    write_json_atomic(output_root / "result.json", result, mode=0o400)
    return result


def make_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--deployment", type=Path, required=True)
    parser.add_argument("--task-id", required=True)
    parser.add_argument("--candidate", type=Path, required=True)
    parser.add_argument("--paper", type=Path, required=True)
    parser.add_argument("--source-packet", type=Path, required=True)
    parser.add_argument("--output-root", type=Path, required=True)
    parser.add_argument("--condition", choices=("N", "L", "n", "l"), required=True)
    parser.add_argument("--model", default="gpt-6-astra")
    parser.add_argument("--reasoning-effort", default="high")
    parser.add_argument("--timeout-seconds", type=float, default=7200)
    parser.add_argument("--validation-timeout-seconds", type=float, default=600)
    parser.add_argument(
        "--infrastructure-retries",
        type=int,
        default=1,
        help="fresh retries after malformed/infrastructure output (default: one)",
    )
    return parser


def main() -> int:
    try:
        result = run_cli(make_parser().parse_args())
    except CandidateAuditError as error:
        print(
            f"Design-16 faithfulness screen dossier failed ({error.failure_code}): {error}",
            file=sys.stderr,
        )
        return 1 if error.failure_code in {"RULE_VIOLATION", "COMPILATION_FAILURE"} else 2
    except (BenchmarkError, OSError, ValueError) as error:
        print(f"Design-16 faithfulness screen error: {error}", file=sys.stderr)
        return 2
    print(json.dumps(result, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
