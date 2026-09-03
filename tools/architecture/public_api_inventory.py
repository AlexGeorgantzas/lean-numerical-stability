#!/usr/bin/env python3
"""Environment-backed public-API inventory and drift gate (EVID-05).

Input is the format-3 stream of `declaration_dependencies.lean`: for every authored project
declaration a `declaration` row (name, module, kind, visibility) and an `api` row (documentation
presence and trimmed-doc hash, elaborated-type hash, body hash, parent relation, reducibility,
instance priority, simp membership, protected and noncomputable flags).

  --write      digests the stream into docs/architecture/public-api-inventory.json: one row per
               public declaration owned by a reusable- or source-tier module, with the fields above.
  (default)    DRIFT GATE: compares a fresh stream with the accepted inventory. Any row that is
               added, removed, or changed in type, body, documentation, reducibility, instance
               priority, simp membership, protected or noncomputable status fails unless
               docs/architecture/public-api-changes.json carries a reviewed record naming that
               exact row and the exact field deltas.
  --self-test  mutation fixtures: every tracked field is mutated in turn and must fail without an
               authorization record and pass with one naming exactly that delta.

usage:
  python public_api_inventory.py --tsv FORMAT3.tsv [--commit SHA] [--write]
  python public_api_inventory.py --self-test
"""
from __future__ import annotations

import argparse
import hashlib
import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
INVENTORY = "docs/architecture/public-api-inventory.json"
CHANGES = "docs/architecture/public-api-changes.json"
TIERS = "docs/architecture/tiers.json"
SCOPE_TIERS = ("reusable", "source")
API_FIELDS = ("documented", "doc_hash", "type_hash", "body_hash", "parent", "reducibility",
              "instance", "simp", "protected", "noncomputable")
TRACKED = ("kind", "module") + API_FIELDS


def load_role(root: Path):
    manifest = json.loads((root / TIERS).read_text(encoding="utf-8"))
    exact = manifest["exact"]
    prefixes = [(r["prefix"].rstrip("."), r["tier"]) for r in manifest["prefixes"]]

    def role(module: str) -> str:
        if module in exact:
            return exact[module]
        best = None
        for prefix, tier in prefixes:
            if module == prefix or module.startswith(prefix + "."):
                if best is None or len(prefix) > len(best[0]):
                    best = (prefix, tier)
        return best[1] if best else "unclassified"

    return role


def read_format3(lines) -> dict[str, dict]:
    rows: dict[str, dict] = {}
    fmt = None
    for number, raw in enumerate(lines, start=1):
        fields = raw.rstrip("\n\r").split("\t")
        if fields[:1] == ["format"]:
            fmt = fields[1] if len(fields) == 2 else None
            if fmt != "3":
                raise SystemExit(f"line {number}: format {fmt!r}, expected 3")
        elif fields[:1] == ["declaration"]:
            if len(fields) != 5:
                raise SystemExit(f"line {number}: declaration rows have 5 fields, got {len(fields)}")
            rows[fields[1]] = {"name": fields[1], "module": fields[2], "kind": fields[3], "visibility": fields[4]}
        elif fields[:1] == ["api"]:
            if len(fields) != 12:
                raise SystemExit(f"line {number}: api rows have 12 fields, got {len(fields)}")
            row = rows.get(fields[1])
            if row is None:
                raise SystemExit(f"line {number}: api row precedes its declaration: {fields[1]}")
            row.update(zip(API_FIELDS, fields[2:]))
            row["documented"] = row["documented"] == "documented"
        elif fields[:1] == ["edge"]:
            continue
        elif fields == [""]:
            continue
        else:
            raise SystemExit(f"line {number}: malformed row")
    if fmt is None:
        raise SystemExit("no format header")
    return rows


def digest(rows: dict[str, dict], role) -> dict:
    entries = {}
    for name, row in rows.items():
        if row.get("visibility") != "public" or "type_hash" not in row:
            continue
        tier = role(row["module"])
        if tier not in SCOPE_TIERS:
            continue
        entries[name] = {"module": row["module"], "tier": tier, "kind": row["kind"],
                         **{f: row[f] for f in API_FIELDS}}
    modules: dict[str, dict] = {}
    for name, e in entries.items():
        m = modules.setdefault(e["module"], {"tier": e["tier"], "public": 0, "documented": 0, "lines": []})
        m["public"] += 1
        m["documented"] += 1 if e["documented"] else 0
        m["lines"].append(f"{name}|{e['kind']}|{e['type_hash']}")
    for m in modules.values():
        lines = sorted(m.pop("lines"))
        m["api_digest"] = hashlib.sha256("\n".join(lines).encode("utf-8")).hexdigest()
    total = len(entries)
    documented = sum(1 for e in entries.values() if e["documented"])
    return {
        "schema_version": 1,
        "source": "declaration_dependencies.lean format 3 (environment-backed)",
        "scope_tiers": list(SCOPE_TIERS),
        "tracked_fields": list(TRACKED),
        "totals": {"modules": len(modules), "public_declarations": total, "documented": documented,
                   "coverage_percent": round(100 * documented / total, 2) if total else None},
        "modules": dict(sorted(modules.items())),
        "declarations": dict(sorted(entries.items())),
    }


def drift(accepted: dict, fresh: dict, changes: list[dict]) -> list[str]:
    """Every difference between accepted and fresh must be authorized by an exact change record."""
    problems: list[str] = []
    authorized: dict[str, dict] = {}
    for record in changes:
        for field in ("declaration", "change", "reviewer", "status", "rationale"):
            if not record.get(field):
                problems.append(f"{CHANGES}: a record lacks {field}")
        if record.get("status") not in (None, "accepted"):
            problems.append(f"{CHANGES}: record for {record.get('declaration')} is not accepted")
        authorized[record.get("declaration", "")] = record
    old, new = accepted["declarations"], fresh["declarations"]
    for name in sorted(set(old) - set(new)):
        rec = authorized.get(name)
        if not rec or rec["change"] != "removed":
            problems.append(f"{name}: removed from the public API without an accepted removal record")
    for name in sorted(set(new) - set(old)):
        rec = authorized.get(name)
        if not rec or rec["change"] != "added":
            problems.append(f"{name}: added to the public API without an accepted addition record")
    for name in sorted(set(old) & set(new)):
        deltas = {f: [old[name][f], new[name][f]] for f in TRACKED if old[name][f] != new[name][f]}
        if not deltas:
            continue
        rec = authorized.get(name)
        if not rec or rec["change"] != "modified":
            problems.append(f"{name}: changed {sorted(deltas)} without an accepted modification record")
            continue
        if rec.get("deltas") != deltas:
            problems.append(f"{name}: the accepted record authorizes {rec.get('deltas')} but the tree shows {deltas}")
    for name, rec in authorized.items():
        if rec["change"] == "removed" and name in new:
            problems.append(f"{name}: an accepted removal record exists but the declaration is still present")
        if rec["change"] == "added" and name not in new:
            problems.append(f"{name}: an accepted addition record exists but the declaration is absent")
        if rec["change"] == "modified" and name in new and name in old and old[name] == new[name]:
            problems.append(f"{name}: an accepted modification record exists but nothing changed; remove the stale record")
    return problems


def sample_stream(**over) -> list[str]:
    base = {"documented": "documented", "doc_hash": "11", "type_hash": "21", "body_hash": "31", "parent": "-",
            "reducibility": "semireducible", "instance": "-", "simp": "-", "protected": "-", "noncomputable": "-"}
    base.update(over)
    api = "\t".join(["api", "R.a"] + [base[f] for f in API_FIELDS])
    return ["format\t3", "declaration\tR.a\tR.M\ttheorem\tpublic", api,
            "declaration\tR.hidden\tR.M\ttheorem\tprivate",
            "api\tR.hidden\tundocumented\t0\t1\t2\t-\tsemireducible\t-\t-\t-\t-",
            "declaration\tA.x\tA.M\tdefinition\tpublic",
            "api\tA.x\tundocumented\t0\t3\t4\t-\treducible\t-\t-\t-\t-"]


def self_test() -> list[str]:
    failures: list[str] = []
    role = lambda m: "reusable" if m.startswith("R.") else "aggregate"
    accepted = digest(read_format3(sample_stream()), role)
    if accepted["totals"] != {"modules": 1, "public_declarations": 1, "documented": 1, "coverage_percent": 100.0}:
        failures.append(f"self-test: totals {accepted['totals']} (private and aggregate rows must be excluded)")
    if drift(accepted, accepted, []):
        failures.append("self-test: an unchanged inventory must pass")
    mutations = {"type_hash": "99", "body_hash": "99", "doc_hash": "99", "documented": "undocumented",
                 "reducibility": "irreducible", "instance": "instance:1000", "simp": "simp",
                 "protected": "protected", "noncomputable": "noncomputable", "parent": "projection-of:R.S"}
    for field, value in mutations.items():
        fresh = digest(read_format3(sample_stream(**{field: value})), role)
        if not drift(accepted, fresh, []):
            failures.append(f"self-test: {field} drift must fail without an authorization record")
            continue
        deltas = {field: [accepted["declarations"]["R.a"][field], fresh["declarations"]["R.a"][field]]}
        record = {"declaration": "R.a", "change": "modified", "deltas": deltas, "reviewer": "t", "status": "accepted", "rationale": "fixture"}
        if drift(accepted, fresh, [record]):
            failures.append(f"self-test: {field} drift must pass with an exact authorization record")
        wrong = dict(record, deltas={field: [accepted["declarations"]["R.a"][field], "something-else"]})
        if not drift(accepted, fresh, [wrong]):
            failures.append(f"self-test: {field} drift must fail when the record authorizes a different delta")
    # removal and addition
    removed = digest(read_format3([l for l in sample_stream() if "R.a" not in l]), role)
    if not drift(accepted, removed, []):
        failures.append("self-test: a removed public declaration must fail without a removal record")
    if drift(accepted, removed, [{"declaration": "R.a", "change": "removed", "reviewer": "t", "status": "accepted", "rationale": "fixture"}]):
        failures.append("self-test: an accepted removal record must let the removal pass")
    if not drift(removed, accepted, []):
        failures.append("self-test: an added public declaration must fail without an addition record")
    stale = [{"declaration": "R.a", "change": "modified", "deltas": {"type_hash": ["21", "99"]}, "reviewer": "t", "status": "accepted", "rationale": "old"}]
    if not drift(accepted, accepted, stale):
        failures.append("self-test: a stale modification record must be rejected")
    return failures


def main(argv: list[str]) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--self-test", action="store_true")
    parser.add_argument("--tsv", type=Path)
    parser.add_argument("--commit", default=None)
    parser.add_argument("--write", action="store_true", help=f"write {INVENTORY} (acceptance only)")
    args = parser.parse_args(argv)
    problems = self_test()
    if args.self_test or problems:
        for p in problems:
            print(f"error: {p}", file=sys.stderr)
        if not problems:
            print("public-API inventory self-test passed: scope filtering, and mutation fixtures for type, body, "
                  "documentation, reducibility, instance priority, simp, protected, noncomputable and parent drift, "
                  "plus removal, addition, wrong-delta and stale-record cases")
        return 1 if problems else 0
    if args.tsv is None:
        parser.error("--tsv is required")
    with args.tsv.open(encoding="utf-8") as stream:
        fresh = digest(read_format3(stream), load_role(ROOT))
    fresh["generated_at_commit"] = args.commit
    if args.write:
        (ROOT / INVENTORY).write_text(json.dumps(fresh, indent=1) + "\n", encoding="utf-8")
        print(f"wrote {INVENTORY}: {fresh['totals']}")
        return 0
    accepted_path = ROOT / INVENTORY
    if not accepted_path.is_file():
        # Until acceptance writes the inventory there is nothing to drift from. This is reported,
        # not hidden: the run still proves the stream parses and reports the live totals.
        print(f"notice: no accepted inventory at {INVENTORY} yet; drift gate not armed. Live environment: "
              f"{fresh['totals']['public_declarations']:,} public declarations in {fresh['totals']['modules']} "
              f"modules, {fresh['totals']['coverage_percent']}% documented. Acceptance writes the inventory with --write.")
        return 0
    accepted = json.loads(accepted_path.read_text(encoding="utf-8"))
    changes_path = ROOT / CHANGES
    changes = json.loads(changes_path.read_text(encoding="utf-8"))["changes"] if changes_path.is_file() else []
    problems = drift(accepted, fresh, changes)
    if problems:
        for p in problems:
            print(f"error: {p}", file=sys.stderr)
        return 1
    print(f"public-API inventory unchanged: {fresh['totals']['public_declarations']:,} public declarations in "
          f"{fresh['totals']['modules']} modules, {fresh['totals']['coverage_percent']}% documented; "
          f"{len(changes)} accepted change record(s) applied")
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
