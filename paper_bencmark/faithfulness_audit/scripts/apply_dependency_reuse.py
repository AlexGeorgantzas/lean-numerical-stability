#!/usr/bin/env python3
"""Build compact, hash-verified dependency review packets from prior audit roles."""

from __future__ import annotations

import argparse
import json
import re
import sys
from pathlib import Path
from typing import Any

try:
    from .common import AUDIT_SCHEMA_VERSION, sha256_file, sha256_text
    from .prepare_audit import REPOSITORY_ROOT
    from .validate_agent_output import validate_role
    from .validate_audit import load_json, task_paths, validate
except ImportError:  # Direct script execution.
    from common import AUDIT_SCHEMA_VERSION, sha256_file, sha256_text  # type: ignore
    from prepare_audit import REPOSITORY_ROOT  # type: ignore
    from validate_agent_output import validate_role  # type: ignore
    from validate_audit import load_json, task_paths, validate  # type: ignore


DEPENDENCY_HEADING = re.compile(r"(?m)^### (D\d{3}): `([^`]+)`\s*$")


def write_json(path: Path, value: Any) -> None:
    path.write_text(
        json.dumps(value, indent=2, sort_keys=True, ensure_ascii=True) + "\n",
        encoding="utf-8",
    )


def digest_record(value: dict[str, Any]) -> str:
    return sha256_text(
        json.dumps(value, sort_keys=True, ensure_ascii=True, separators=(",", ":"))
    )


def output_record(output: dict[str, Any], item_id: str) -> dict[str, Any] | None:
    for record in output.get("dependency_coverage", []):
        if isinstance(record, dict) and record.get("id") == item_id:
            return record
    return None


def reuse_entries(manifest: dict[str, Any], role: str) -> dict[str, dict[str, Any]]:
    input_key = f"dependency_reuse_{role}"
    record = manifest.get("inputs", {}).get(input_key)
    if not isinstance(record, dict) or not isinstance(record.get("path"), str):
        return {}
    cache = load_json(REPOSITORY_ROOT / record["path"])
    return {
        entry["id"]: entry
        for entry in cache.get("entries", [])
        if isinstance(entry, dict) and isinstance(entry.get("id"), str)
    }


def resolved_meaning(
    record: dict[str, Any],
    cached: dict[str, dict[str, Any]],
    role: str,
) -> str | None:
    direct_key = "interpretation" if role == "direct" else "meaning"
    value = record.get(direct_key)
    if isinstance(value, str) and value:
        return value
    cached_record = cached.get(str(record.get("id")))
    cached_value = cached_record.get(direct_key) if cached_record else None
    return cached_value if isinstance(cached_value, str) and cached_value else None


def collect_sources(
    source_task_ids: list[str], roles: set[str]
) -> dict[str, dict[str, Any]]:
    by_fingerprint: dict[str, dict[str, Any]] = {}
    for task_id in source_task_ids:
        if "blind" in roles:
            validate_role(task_id, "blind-translation")
        if "direct" in roles:
            validate_role(task_id, "direct-judge")
        _, audit_dir = task_paths(task_id)
        manifest = load_json(audit_dir / "manifest.json")
        blind_path = audit_dir / "agent_outputs" / "blind_translation.json"
        direct_path = audit_dir / "agent_outputs" / "direct_judge.json"
        blind = load_json(blind_path) if "blind" in roles else {}
        direct = load_json(direct_path) if "direct" in roles else {}
        blind_cached = reuse_entries(manifest, "blind") if "blind" in roles else {}
        direct_cached = reuse_entries(manifest, "direct") if "direct" in roles else {}
        for dependency in manifest.get("dependencies", []):
            if not isinstance(dependency, dict):
                continue
            fingerprint = dependency.get("semantic_sha256")
            if not isinstance(fingerprint, str) or fingerprint in by_fingerprint:
                continue
            item_id = dependency.get("id")
            source: dict[str, Any] = {
                "semantic_sha256": fingerprint,
                "source_task_id": task_id,
                "source_dependency_id": item_id,
            }
            if "blind" in roles:
                blind_record = output_record(blind, str(item_id))
                if blind_record is None or blind_record.get("status") != "understood":
                    continue
                meaning = resolved_meaning(blind_record, blind_cached, "blind")
                if meaning is None:
                    continue
                source.update(
                    {
                        "meaning": meaning,
                        "source_blind_output_sha256": sha256_file(blind_path),
                    }
                )
            if "direct" in roles:
                direct_record = output_record(direct, str(item_id))
                if direct_record is None or direct_record.get("status") not in {
                    "pass",
                    "not-applicable",
                }:
                    continue
                interpretation = resolved_meaning(
                    direct_record, direct_cached, "direct"
                )
                if interpretation is None:
                    continue
                source.update(
                    {
                        "interpretation": interpretation,
                        "source_direct_output_sha256": sha256_file(direct_path),
                    }
                )
            if not roles:
                continue
            by_fingerprint[fingerprint] = source
    return by_fingerprint


def dossier_sections(text: str) -> tuple[str, dict[str, str]]:
    matches = list(DEPENDENCY_HEADING.finditer(text))
    if not matches:
        raise RuntimeError("dossier has no dependency sections")
    region_end = text.find("\n## Complete local imported sources", matches[-1].end())
    if region_end == -1:
        region_end = len(text)
    sections: dict[str, str] = {}
    for index, match in enumerate(matches):
        end = matches[index + 1].start() if index + 1 < len(matches) else region_end
        sections[match.group(1)] = text[match.start() : end].rstrip()
    return text[: matches[0].start()], sections


def render_direct_reuse(dependency: dict[str, Any], entry: dict[str, Any]) -> str:
    return "\n".join(
        [
            f"### {dependency['id']}: `{dependency['name']}`",
            "",
            f"- Role: `{dependency['role']}`",
            f"- Owner module: `{dependency['owner_module']}`",
            f"- Declaration kind: `{dependency['kind']}`",
            f"- Semantic SHA-256: `{dependency['semantic_sha256']}`",
            f"- Reuse SHA-256: `{entry['reuse_sha256']}`",
            "",
            "Hash-verified prior interpretation:",
            "",
            entry["interpretation"],
            "",
            (
                "Reuse covers declaration meaning only. Re-evaluate this dependency's "
                "effect on the current target and its match to the current paper result."
            ),
        ]
    )


def render_blind_reuse(dependency: dict[str, Any], entry: dict[str, Any]) -> str:
    return "\n".join(
        [
            f"### {dependency['id']}: `{dependency['blind_name']}`",
            "",
            f"- Semantic SHA-256: `{dependency['semantic_sha256']}`",
            f"- Reuse SHA-256: `{entry['reuse_sha256']}`",
            "",
            "Hash-verified prior meaning:",
            "",
            entry["meaning"],
            "",
            "Reuse covers definition meaning only. Determine its effect on this proposition.",
        ]
    )


def apply_reuse(
    target_task_id: str,
    source_task_ids: list[str],
    *,
    role: str = "direct",
) -> tuple[int, int]:
    validate(target_task_id, "prepared")
    _, audit_dir = task_paths(target_task_id)
    manifest_path = audit_dir / "manifest.json"
    manifest = load_json(manifest_path)
    if manifest.get("schema_version") != AUDIT_SCHEMA_VERSION:
        raise RuntimeError("dependency reuse requires a v0.2 target audit")
    roles = {"direct", "blind"} if role == "both" else {role}
    for selected_role, filename in (
        ("direct", "direct_judge.json"),
        ("blind", "blind_translation.json"),
    ):
        if selected_role in roles and (audit_dir / "agent_outputs" / filename).exists():
            raise RuntimeError(
                f"cannot rewrite the {selected_role} review packet after {filename} exists"
            )
    available = collect_sources(source_task_ids, roles)
    dependencies = [item for item in manifest.get("dependencies", []) if isinstance(item, dict)]

    direct_entries: list[dict[str, Any]] = []
    blind_entries: list[dict[str, Any]] = []
    for dependency in dependencies:
        source = available.get(str(dependency.get("semantic_sha256")))
        if source is None:
            continue
        if "direct" in roles:
            direct_payload = {
                "semantic_sha256": source["semantic_sha256"],
                "interpretation": source["interpretation"],
                "source_direct_output_sha256": source[
                    "source_direct_output_sha256"
                ],
            }
            direct_entries.append(
                {
                    "id": dependency["id"],
                    "name": dependency["name"],
                    "semantic_sha256": source["semantic_sha256"],
                    "interpretation": source["interpretation"],
                    "source_task_id": source["source_task_id"],
                    "source_dependency_id": source["source_dependency_id"],
                    "source_direct_output_sha256": source[
                        "source_direct_output_sha256"
                    ],
                    "reuse_sha256": digest_record(direct_payload),
                }
            )
        if "blind" in roles:
            blind_payload = {
                "semantic_sha256": source["semantic_sha256"],
                "meaning": source["meaning"],
                "source_blind_output_sha256": source[
                    "source_blind_output_sha256"
                ],
            }
            blind_entries.append(
                {
                    "id": dependency["id"],
                    "name": dependency["blind_name"],
                    "semantic_sha256": source["semantic_sha256"],
                    "meaning": source["meaning"],
                    "source_blind_output_sha256": source[
                        "source_blind_output_sha256"
                    ],
                    "reuse_sha256": digest_record(blind_payload),
                }
            )

    direct_by_id = {entry["id"]: entry for entry in direct_entries}
    blind_by_id = {entry["id"]: entry for entry in blind_entries}
    inputs_dir = audit_dir / "inputs"
    direct_cache_path = inputs_dir / "dependency_reuse_direct.json"
    blind_cache_path = inputs_dir / "dependency_reuse_blind.json"
    direct_review_path = inputs_dir / "direct_review_packet.md"
    blind_review_path = inputs_dir / "blind_review_packet.md"
    records: dict[str, Path] = {}
    if direct_entries:
        write_json(
            direct_cache_path,
            {
                "schema_version": AUDIT_SCHEMA_VERSION,
                "role": "direct-dependency-reuse",
                "target_task_id": target_task_id.upper(),
                "entries": direct_entries,
            },
        )
        direct_text = (inputs_dir / "declaration_dossier.md").read_text(
            encoding="utf-8"
        )
        direct_prefix, direct_sections = dossier_sections(direct_text)
        direct_parts = [direct_prefix.rstrip(), ""]
        for dependency in dependencies:
            item_id = dependency["id"]
            direct_parts.extend(
                [
                    render_direct_reuse(dependency, direct_by_id[item_id])
                    if item_id in direct_by_id
                    else direct_sections[item_id],
                    "",
                ]
            )
        direct_review_path.write_text(
            "\n".join(direct_parts).rstrip() + "\n", encoding="utf-8"
        )
        records.update(
            {
                "dependency_reuse_direct": direct_cache_path,
                "direct_review_packet": direct_review_path,
            }
        )
    if blind_entries:
        write_json(
            blind_cache_path,
            {
                "schema_version": AUDIT_SCHEMA_VERSION,
                "role": "blind-dependency-reuse",
                "entries": blind_entries,
            },
        )
        blind_text = (inputs_dir / "blind_dossier.md").read_text(encoding="utf-8")
        blind_prefix, blind_sections = dossier_sections(blind_text)
        blind_parts = [blind_prefix.rstrip(), ""]
        for dependency in dependencies:
            item_id = dependency["id"]
            blind_parts.extend(
                [
                    render_blind_reuse(dependency, blind_by_id[item_id])
                    if item_id in blind_by_id
                    else blind_sections[item_id],
                    "",
                ]
            )
        blind_review_path.write_text(
            "\n".join(blind_parts).rstrip() + "\n", encoding="utf-8"
        )
        records.update(
            {
                "dependency_reuse_blind": blind_cache_path,
                "blind_review_packet": blind_review_path,
            }
        )
    for key, path in records.items():
        manifest["inputs"][key] = {
            "path": path.relative_to(REPOSITORY_ROOT).as_posix(),
            "sha256": sha256_file(path),
        }
    reuse = manifest.setdefault(
        "dependency_reuse",
        {"source_task_ids": [], "direct_count": 0, "blind_count": 0},
    )
    reuse["source_task_ids"] = list(
        dict.fromkeys([*reuse.get("source_task_ids", []), *source_task_ids])
    )
    if "direct" in roles:
        reuse["direct_count"] = len(direct_entries)
    if "blind" in roles:
        reuse["blind_count"] = len(blind_entries)
    if reuse.get("direct_count") == 0 and reuse.get("blind_count") == 0:
        manifest.pop("dependency_reuse", None)
    write_json(manifest_path, manifest)
    validate(target_task_id, "prepared")
    return len(direct_entries), len(blind_entries)


def make_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("target_task_id")
    parser.add_argument("--source", action="append", required=True, dest="source_task_ids")
    parser.add_argument(
        "--role",
        choices=("direct", "blind", "both"),
        default="direct",
        help="review packet to compact (default: direct)",
    )
    return parser


def main() -> int:
    args = make_parser().parse_args()
    try:
        direct_count, blind_count = apply_reuse(
            args.target_task_id.upper(),
            [item.upper() for item in args.source_task_ids],
            role=args.role,
        )
    except Exception as error:
        print(f"dependency reuse error: {error}", file=sys.stderr)
        return 2
    print(
        json.dumps(
            {"direct_reused": direct_count, "blind_reused": blind_count},
            indent=2,
        )
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
