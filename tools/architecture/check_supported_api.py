#!/usr/bin/env python3
"""Freeze and verify NumStability's explicitly exercised supported API.

The supported declaration set is intentionally narrower than the Lean-visible
environment.  A declaration enters this baseline only when a one-import test
reachable from ``NumStabilityTest`` explicitly names it in ``#check`` or
``#synth``.  The checker separately hashes every authored public project name
reachable from each documented entry point.  That guard catches accidental new
visibility without declaring every visible implementation helper to be API.

Type evidence comes from Lean's elaborated environment, not a source regex.  A
small embedded extractor emits the owner, declaration kind, visibility, and
``repr`` of each selected declaration's elaborated type.  A reversible payload
escape preserves that representation byte-for-byte for its SHA-256 digest.

Live GitHub review authentication remains the responsibility of the exact
``check_completion_phase.py`` trust root.  This checker validates the recorded
owner-comment schema and hard-binds both that checker and the exact workflow
that runs it before the supported-API lifecycle check.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import re
import subprocess
import sys
import tempfile
import unicodedata
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Iterable, Mapping, Sequence


ROOT = Path(__file__).resolve().parents[2]
DEFAULT_BASELINE = ROOT / "docs" / "architecture" / "supported-api.json"
DEFAULT_REVIEW = (
    ROOT
    / "docs"
    / "architecture"
    / "phases"
    / "2026-08-repository-reorganization-completion"
    / "reviews"
    / "C0008-supported-api.json"
)
DEFAULT_ACTIVATION_REVIEW = (
    ROOT
    / "docs"
    / "architecture"
    / "phases"
    / "2026-08-repository-reorganization-completion"
    / "reviews"
    / "C0007-bounded-planned-control.json"
)
SUPPORTED_API_REVIEW_RELATIVE = (
    "docs/architecture/phases/2026-08-repository-reorganization-completion/"
    "reviews/C0008-supported-api.json"
)
FULL_TESTS_CORRECTION_RELATIVE = (
    "docs/architecture/phases/2026-08-repository-reorganization-completion/"
    "reviews/C0007-full-tests-evidence-correction.json"
)
BOUNDED_AUTHORIZATION_RELATIVE = (
    "docs/architecture/phases/2026-08-repository-reorganization-completion/"
    "reviews/C0007-bounded-epoch-operator-authorization.json"
)
SUPPORTED_API_BASELINE_RELATIVE = "docs/architecture/supported-api.json"
COMPLETION_CHECKER_RELATIVE = "tools/architecture/check_completion_phase.py"
SUPPORTED_API_CHECKER_RELATIVE = "tools/architecture/check_supported_api.py"
WORKFLOW_RELATIVE = ".github/workflows/lean_action_ci.yml"
PLANNED_PATH_SET_SHA256 = (
    "F27C9B79FD8F365F28EDE87FA3F2689678F929E1EE74BAB4820EDCB9A7A39BFC"
)
EXACT_ACTIVATION_SUPERSEDES = (
    "docs/architecture/phases/2026-08-repository-reorganization-completion/"
    "reviews/I01-approval.json",
    "docs/architecture/phases/2026-08-repository-reorganization-completion/"
    "reviews/CODE03-approval.json",
    FULL_TESTS_CORRECTION_RELATIVE,
    SUPPORTED_API_REVIEW_RELATIVE,
)
TIER_MANIFEST = ROOT / "docs" / "architecture" / "tiers.json"
TEST_ROOT = "NumStabilityTest"
PROJECT_PREFIX = "NumStability"
SCHEMA_VERSION = 1
TYPE_NORMALIZATION = "lean-expr-repr-exact-percent-escaped-v1"
C0007_CODE_SHA = "4e26820d1f4989ec4ec77b7113085f593570e11b"
C0007_TIER_MANIFEST_SHA256 = (
    "3695B84D0644E447765FD5CF30FDD9FF65FBEC794276F494EC3FC2D3709C4C1E"
)
C0007_PRODUCTION_SOURCE_TREE_SHA256 = (
    "C3EAA8D96E6F51C59EB371E43FE87A7E3D93516EE47EFEF3B989972ABE1F1631"
)
C0007_TEST_SOURCE_TREE_SHA256 = (
    "BBBF60B1D329DA8C35B8C1F5B5BC51329F507BF8E794CA5B87BFA91561DFDE6F"
)
R0014_TIER_MANIFEST_SHA256 = (
    "96D8329E018769925658FD7BC8392F8005210C83665333B333EB03EFD2B0F6F6"
)
PLANNED_CONTROL_WORKFLOW_SHA256 = (
    "1080F77A2934E4B0F350A8A484B96F2CC9B86D94B5A2FF8BCB441ECEF3C78AEC"
)
GITHUB_REVIEW_SOURCE_IDENTITY = {
    "author_association": "OWNER",
    "author_database_id": 144732584,
    "author_login": "AlexGeorgantzas",
    "author_node_id": "U_kgDOCKBxqA",
    "author_type": "User",
    "performed_via_github_app": None,
    "provider": "github_issue_comment",
    "repository_api_url": (
        "https://api.github.com/repos/AlexGeorgantzas/lean-numerical-stability"
    ),
    "repository_database_id": 1171530090,
    "repository_full_name": "AlexGeorgantzas/lean-numerical-stability",
    "repository_node_id": "R_kgDORdQhag",
}
R0014_ARTIFACT_SHA256 = {
    "docs/architecture/phases/2026-08-repository-reorganization-completion/requests/R0014.json": (
        "F5A402E3FE4DEB8066B87657B86A2BB21FD744859E48DDA53A69C815B2F61A8B"
    ),
    "docs/architecture/phases/2026-08-repository-reorganization-completion/requests/R0014.patch": (
        "3AC31AFC44B697FF830E0CF393FF1725F18B49022ABCF81D83742220FCCB3A88"
    ),
    "docs/architecture/phases/2026-08-repository-reorganization-completion/requests/R0014-postimages.tsv": (
        "42F4ED7EFE7C611DE214A0E6FE4ABADA11034632A9086952EADCD1A8AA33A1C9"
    ),
    "docs/architecture/phases/2026-08-repository-reorganization-completion/reviews/I01-changed-paths.tsv": (
        "32D0E95A1F3AC0230647B86C94E3AFF869546BDDEA62678657C93EF22233AFC4"
    ),
}
IMPLEMENTATION_POSTIMAGE_LEDGERS = {
    "docs/architecture/phases/2026-08-repository-reorganization-completion/requests/R0014-postimages.tsv": (
        "42F4ED7EFE7C611DE214A0E6FE4ABADA11034632A9086952EADCD1A8AA33A1C9"
    ),
    "docs/architecture/phases/2026-08-repository-reorganization-completion/requests/R0015-postimages.tsv": (
        "F92A484CAFBB2F8885A14CE5A7A0A9DB4A774888757797BB836254D4600BED8D"
    ),
}
VISIBILITY_EXCLUSION_POLICY = (
    "exclude Lean-private, Lean-reserved/internal, numeric-name, leading-underscore, "
    "and compiler-generated match-detail declarations from the authored-public guard; "
    "these names are not stable source-addressable authored API. Selected declarations "
    "remain fail-closed and record public/protected status individually"
)
DECLARATION_POLICY = (
    "one exact whole-line, fully consumed Lean identifier after #check/#synth in a "
    "one-import test reachable from NumStabilityTest, with its owner reachable from "
    "the imported surface through Lean-exported imports; malformed or trailing "
    "project-bearing targets fail closed"
)
VISIBILITY_GUARD_POLICY = (
    "exact authored-public project-name set reachable from the union of exact-C0007 "
    "and planned-control documented entrypoints using Lean 4 export semantics "
    "(legacy ordinary imports export; module-mode requires public import); guard rows "
    "do not promote non-selected names to supported API"
)

IMPORT_RE = re.compile(
    r"(?m)^[ \t]*(?P<modifiers>(?:(?:public|private|meta)\s+)*)import[ \t]+"
    r"(?:(?P<import_all>all)[ \t]+)?"
    r"(?P<module>[A-Za-z0-9_'.]+)"
)
MODULE_MODE_RE = re.compile(r"(?m)^[ \t]*module(?:[ \t]|$)")
API_COMMAND_LINE_RE = re.compile(r"^[ \t]*#(?:check|synth)\b(?P<target>.*)$")
IDENTIFIER_DELIMITERS = frozenset("(){}[],:;@")
LEAN_KEYWORDS = frozenset(
    {
        "abbrev", "axiom", "by", "class", "def", "deriving", "do", "else",
        "end", "example", "export", "extends", "for", "forall", "from", "fun",
        "if", "import", "in", "inductive", "infix", "infixl", "infixr", "instance",
        "let", "macro", "match", "namespace", "notation", "opaque", "open", "private",
        "protected", "public", "section", "set_option", "structure", "syntax", "theorem",
        "then", "universe", "variable", "where", "with",
    }
)

# These names are the curated union of entrypoints documented at exact C0007 and
# by the bounded planned-control public-doc rewrite (including the planned
# FloatingPoint.Model minimal-import example).  Generation also unions in the
# exact reusable_entrypoints array from the C0007 tiers.json preimage.
CURATED_DOCUMENTED_ENTRYPOINTS = (
    "NumStability",
    "NumStability.Algorithms",
    "NumStability.Algorithms.FastMatMul",
    "NumStability.Algorithms.FastMatMul.Recurrences",
    "NumStability.Algorithms.LinearSystems",
    "NumStability.Algorithms.Summation",
    "NumStability.Algorithms.Sylvester",
    "NumStability.All",
    "NumStability.Analysis",
    "NumStability.Analysis.Asymptotics",
    "NumStability.Analysis.Conditioning",
    "NumStability.Analysis.Equidistribution",
    "NumStability.Analysis.FirstOrder",
    "NumStability.Analysis.LeadingDigits",
    "NumStability.Analysis.LinearOperators",
    "NumStability.Analysis.MatrixNorms",
    "NumStability.Analysis.Norms.Core",
    "NumStability.Analysis.OperatorNorms",
    "NumStability.Analysis.Probability",
    "NumStability.Analysis.Probability.Gaussian",
    "NumStability.Analysis.Probability.Haar",
    "NumStability.Analysis.SingularValues",
    "NumStability.Analysis.Summation",
    "NumStability.Analysis.VectorNorms",
    "NumStability.Core",
    "NumStability.FloatingPoint",
    "NumStability.FloatingPoint.IEEE",
    "NumStability.FloatingPoint.Model",
    "NumStability.Higham",
    "NumStability.Source",
    "NumStability.Source.Higham",
)
HISTORICAL_ROOT_SURFACES = frozenset({"NumStability", "NumStability.Higham"})

# R0014/I01 is a reviewed, atomic additive extension of the C0007 test
# selection contract.  Four names were already selected at C0007; only
# problem2_9Source is promoted into the supported set.  These nine occurrences
# are deliberately data, not a permissive pattern.
APPROVED_I01_TEST_EVIDENCE = (
    (
        "NumStability.RectPNormPair.oneColumnValueRect",
        "NumStabilityTest.Reorganization.I01.Aggregate.NumStability_Algorithms_NormEstimation_PNorm_All",
        "NumStability.Algorithms.NormEstimation.PNorm.All",
        "canonical",
        1,
    ),
    (
        "NumStability.FloatingPointFormat.binary64MantissaExtendedLocalFormat",
        "NumStabilityTest.Reorganization.I01.Aggregate.NumStability_Source_Higham_Chapter02_Problem09_DoubleRounding_Counterexample",
        "NumStability.Source.Higham.Chapter02.Problem09.DoubleRounding.Counterexample",
        "canonical",
        1,
    ),
    (
        "NumStability.FloatingPointFormat.problem2_9Source",
        "NumStabilityTest.Reorganization.I01.Aggregate.NumStability_Source_Higham_Chapter02_Problem09_DoubleRounding_Counterexample",
        "NumStability.Source.Higham.Chapter02.Problem09.DoubleRounding.Counterexample",
        "canonical",
        1,
    ),
    (
        "NumStability.FloatingPointFormat.problem2_9_direct_double_ne_double_rounded_extended64",
        "NumStabilityTest.Reorganization.I01.Aggregate.NumStability_Source_Higham_Chapter02_Problem09_DoubleRounding_Counterexample",
        "NumStability.Source.Higham.Chapter02.Problem09.DoubleRounding.Counterexample",
        "canonical",
        1,
    ),
    (
        "NumStability.FloatingPointFormat.binary64MantissaExtendedLocalFormat",
        "NumStabilityTest.Reorganization.I01.Canonical.NumStability_Source_Higham_Chapter02_Problem09_DoubleRounding_Counterexample_Inputs",
        "NumStability.Source.Higham.Chapter02.Problem09.DoubleRounding.Counterexample.Inputs",
        "canonical",
        1,
    ),
    (
        "NumStability.FloatingPointFormat.problem2_9Source",
        "NumStabilityTest.Reorganization.I01.Canonical.NumStability_Source_Higham_Chapter02_Problem09_DoubleRounding_Counterexample_Inputs",
        "NumStability.Source.Higham.Chapter02.Problem09.DoubleRounding.Counterexample.Inputs",
        "canonical",
        1,
    ),
    (
        "NumStability.summable_infNorm_matPow",
        "NumStabilityTest.Reorganization.I01.Canonical.NumStability_Source_Higham_Chapter17_Results_Series",
        "NumStability.Source.Higham.Chapter17.Results.Series",
        "canonical",
        1,
    ),
    (
        "NumStability.FloatingPointFormat.binary64MantissaExtendedLocalFormat",
        "NumStabilityTest.Reorganization.I01.OldOnly.NumStability_Analysis_DoubleRounding",
        "NumStability.Analysis.DoubleRounding",
        "historical",
        1,
    ),
    (
        "NumStability.FloatingPointFormat.problem2_9Source",
        "NumStabilityTest.Reorganization.I01.OldOnly.NumStability_Analysis_DoubleRounding",
        "NumStability.Analysis.DoubleRounding",
        "historical",
        1,
    ),
)
APPROVED_I01_NEW_FQNS = frozenset(
    {"NumStability.FloatingPointFormat.problem2_9Source"}
)
APPROVED_I01_OWNER_DESTINATIONS = {
    "NumStability.FloatingPointFormat.binary64MantissaExtendedLocalFormat": (
        "NumStability.Source.Higham.Chapter02.Problem09.DoubleRounding.Counterexample.Inputs"
    ),
    "NumStability.FloatingPointFormat.problem2_9Source": (
        "NumStability.Source.Higham.Chapter02.Problem09.DoubleRounding.Counterexample.Inputs"
    ),
}


LEAN_EXTRACTOR_SOURCE = r'''import Lean

open Lean

namespace NumStabilitySupportedApi

private def isProjectModule (moduleName : Name) : Bool :=
  let text := moduleName.toString
  text == "NumStability" || text.startsWith "NumStability."

private def isGeneratedMatchComponent (part : String) : Bool :=
  part.startsWith "match_" && (Name.mkSimple part).isInternalDetail

private def hasCompilerGeneratedComponent : Name → Bool
  | .anonymous => false
  | .num _ _ => true
  | .str parent part =>
      part.startsWith "_" || isGeneratedMatchComponent part ||
        hasCompilerGeneratedComponent parent

private def isCompilerGeneratedDetail (name : Name) : Bool :=
  hasCompilerGeneratedComponent (privateToUserName name)

private def shouldIncludeVisible (env : Environment) (name : Name) : Bool :=
  !isPrivateName name && !isReservedName env name &&
    !isCompilerGeneratedDetail name

private def declarationKind : ConstantInfo → String
  | .axiomInfo _ => "axiom"
  | .defnInfo _ => "definition"
  | .thmInfo _ => "theorem"
  | .opaqueInfo _ => "opaque"
  | .quotInfo _ => "quotient"
  | .inductInfo _ => "inductive"
  | .ctorInfo _ => "constructor"
  | .recInfo _ => "recursor"

private def declarationVisibility (name : Name) : String :=
  if isPrivateName name then
    "private"
  else if name.isInternalDetail then
    "internal"
  else
    "public"

private structure ProjectDeclaration where
  name : Name
  moduleName : Name
  info : ConstantInfo

private def collectProjectDeclarations (env : Environment) : Array ProjectDeclaration := Id.run do
  let mut result := #[]
  for h : moduleIdx in *...env.header.moduleData.size do
    let moduleName := env.header.moduleNames[moduleIdx]!
    if isProjectModule moduleName then
      let data := env.header.moduleData[moduleIdx]
      for name in data.constNames, info in data.constants do
        if env.getModuleIdxFor? name == some moduleIdx then
          result := result.push { name, moduleName, info }
  return result.qsort fun left right => left.name.toString < right.name.toString

private def nameFromComponents (text : String) : Name :=
  text.splitOn "\t" |>.foldl (fun name part => Name.str name part) Name.anonymous

private def sanitize (text : String) : String :=
  text.replace "\t" " " |>.replace "\r" " " |>.replace "\n" " "

-- Keep elaborated type evidence byte-exact while retaining a line-oriented TSV.
-- Escaping percent first makes this mapping injective and exactly reversible.
private def encodePayload (text : String) : String :=
  text.replace "%" "%25" |>.replace "\t" "%09" |>.replace "\r" "%0D"
    |>.replace "\n" "%0A"

private def writeFields (handle : IO.FS.Handle) (fields : Array String) : IO Unit :=
  handle.putStrLn <| String.intercalate "\t" (fields.toList.map sanitize)

private unsafe def extract
    (namesPath importsPath outputPath : System.FilePath) : IO Unit := do
  initSearchPath (← findSysroot)
  let namesText ← IO.FS.readFile namesPath
  let selected : NameSet := namesText.splitOn "\n" |>.foldl (init := {}) fun names line =>
    let line := line.trim
    if line.isEmpty then names else names.insert (nameFromComponents line)
  let importsText ← IO.FS.readFile importsPath
  let imports : Array Import := importsText.splitOn "\n" |>.foldl (init := #[]) fun imports line =>
    let line := line.trim
    if line.isEmpty then imports else imports.push { module := nameFromComponents line }
  if imports.isEmpty then
    throw <| IO.userError "environment extractor requires at least one entrypoint"
  withImportModules imports {} fun env => do
    let declarations := collectProjectDeclarations env
    IO.FS.withFile outputPath IO.FS.Mode.write fun handle => do
      writeFields handle #["format", "1"]
      for declaration in declarations do
        if shouldIncludeVisible env declaration.name then
          writeFields handle #[
            "visible",
            declaration.name.toString,
            declaration.moduleName.toString
          ]
        if selected.contains declaration.name then
          writeFields handle #[
            "selected",
            declaration.name.toString,
            declaration.moduleName.toString,
            declarationKind declaration.info,
            if isProtected env declaration.name then "true" else "false",
            declarationVisibility declaration.name,
            encodePayload (reprStr declaration.info.type)
          ]

unsafe def run (args : List String) : IO UInt32 := do
  match args with
  | [namesPath, importsPath, outputPath] =>
      extract namesPath importsPath outputPath
      return 0
  | _ =>
      IO.eprintln "usage: extractor NAMES.txt IMPORTS.txt OUTPUT.tsv"
      return 2

end NumStabilitySupportedApi

unsafe def main (args : List String) : IO UInt32 :=
  NumStabilitySupportedApi.run args
'''


class ContractError(RuntimeError):
    """A supported-API contract cannot be derived or checked."""


@dataclass(frozen=True)
class Module:
    name: str
    path: Path
    imports: tuple[str, ...]
    exported_imports: tuple[str, ...]


@dataclass(frozen=True)
class TestSelection:
    fqn: str
    test_modules: tuple[str, ...]
    canonical_surfaces: tuple[str, ...]
    historical_surfaces: tuple[str, ...]
    test_evidence: tuple[tuple[str, str, str, int], ...]


@dataclass(frozen=True)
class EnvironmentDeclaration:
    fqn: str
    owner_module: str
    kind: str
    protected: bool
    visibility: str
    normalized_type_sha256: str


@dataclass(frozen=True)
class EnvironmentSnapshot:
    selected: Mapping[str, EnvironmentDeclaration]
    public_names_by_owner: Mapping[str, tuple[str, ...]]


def sha256_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest().upper()


def canonical_json_sha256(value: Any) -> str:
    payload = json.dumps(
        value, ensure_ascii=False, sort_keys=True, separators=(",", ":")
    ).encode("utf-8")
    return sha256_bytes(payload)


def decode_type_payload(value: str) -> str:
    """Reverse the extractor's injective percent escape, rejecting corruption."""
    mapping = {"25": "%", "09": "\t", "0D": "\r", "0A": "\n"}
    output: list[str] = []
    index = 0
    while index < len(value):
        if value[index] != "%":
            output.append(value[index])
            index += 1
            continue
        code = value[index + 1 : index + 3]
        if len(code) != 2 or code not in mapping:
            raise ContractError(
                f"invalid exact type-evidence escape at offset {index}: {value[index:index + 3]!r}"
            )
        output.append(mapping[code])
        index += 3
    return "".join(output)


def implementation_postimage_rows() -> list[dict[str, str]]:
    rows: list[dict[str, str]] = []
    for relative, expected_digest in sorted(IMPLEMENTATION_POSTIMAGE_LEDGERS.items()):
        path = ROOT / relative
        actual_digest = sha256_bytes(path.read_bytes())
        if actual_digest != expected_digest:
            raise ContractError(
                f"atomic implementation ledger drift: {relative}: expected "
                f"{expected_digest}, got {actual_digest}"
            )
        lines = path.read_text(encoding="utf-8-sig").splitlines()
        if not lines or lines[0].split("\t") != [
            "path",
            "preimage_blob_oid",
            "preimage_sha256",
            "postimage_sha256",
        ]:
            raise ContractError(f"invalid postimage ledger header: {relative}")
        for line_number, line in enumerate(lines[1:], 2):
            fields = line.split("\t")
            if len(fields) != 4:
                raise ContractError(f"{relative}:{line_number}: expected four fields")
            path_text, _, preimage, postimage = fields
            if not path_text or not re.fullmatch(r"[0-9A-F]{64}", postimage):
                raise ContractError(f"{relative}:{line_number}: invalid path/postimage")
            if preimage != "-" and not re.fullmatch(r"[0-9A-F]{64}", preimage):
                raise ContractError(f"{relative}:{line_number}: invalid preimage")
            rows.append(
                {
                    "path": path_text,
                    "preimage_sha256": preimage,
                    "postimage_sha256": postimage,
                }
            )
    paths = [row["path"] for row in rows]
    if len(paths) != 14 or len(set(paths)) != 14:
        raise ContractError(
            f"atomic R0014/R0015 path inventory must contain 14 unique paths, got {len(paths)}"
        )
    return sorted(rows, key=lambda row: row["path"])


def implementation_path_set_sha256() -> str:
    paths = [row["path"] for row in implementation_postimage_rows()]
    return sha256_bytes(("\n".join(paths) + "\n").encode("utf-8"))


def classify_implementation_state() -> str:
    rows = implementation_postimage_rows()
    pre_matches: list[bool] = []
    post_matches: list[bool] = []
    diagnostics: list[str] = []
    for row in rows:
        path = ROOT / row["path"]
        current = sha256_bytes(path.read_bytes()) if path.is_file() else "-"
        pre_matches.append(current == row["preimage_sha256"])
        post_matches.append(current == row["postimage_sha256"])
        if current not in {row["preimage_sha256"], row["postimage_sha256"]}:
            diagnostics.append(f"{row['path']}={current}")
    if all(pre_matches):
        state = "staging"
    elif all(post_matches):
        state = "completion"
    else:
        pre_count = sum(pre_matches)
        post_count = sum(post_matches)
        details = "; ".join(diagnostics[:5])
        raise ContractError(
            "partial or ambiguous atomic R0014/R0015 implementation state: "
            f"{pre_count}/14 exact preimages, {post_count}/14 exact postimages"
            + (f"; other bytes: {details}" if details else "")
        )

    paths = [row["path"] for row in rows]
    try:
        diff = subprocess.run(
            ("git", "diff", "--name-only", C0007_CODE_SHA, "--", *paths),
            cwd=ROOT,
            check=False,
            text=True,
            encoding="utf-8",
            errors="replace",
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
        )
        status = subprocess.run(
            (
                "git",
                "status",
                "--porcelain=v1",
                "--untracked-files=all",
                "--",
                *paths,
            ),
            cwd=ROOT,
            check=False,
            text=True,
            encoding="utf-8",
            errors="replace",
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
        )
    except FileNotFoundError as error:
        raise ContractError("required executable not found: git") from error
    if diff.returncode or status.returncode:
        raise ContractError(
            "cannot classify atomic Git state: "
            + "\n".join(
                part.strip()
                for part in (diff.stderr, status.stderr)
                if part.strip()
            )
        )
    changed = {
        line.strip().replace("\\", "/")
        for line in diff.stdout.splitlines()
        if line.strip()
    }
    expected_changed = set() if state == "staging" else set(paths)
    if changed != expected_changed:
        raise ContractError(
            f"atomic {state} Git diff mismatch: expected {sorted(expected_changed)!r}, "
            f"got {sorted(changed)!r}"
        )
    status_lines = [line for line in status.stdout.splitlines() if line.strip()]
    if state == "staging" and status_lines:
        raise ContractError("staging state has dirty atomic paths: " + "; ".join(status_lines))
    if state == "completion":
        invalid_status = [
            line
            for line in status_lines
            if len(line) < 3 or line[:2] == "??" or line[1] != " "
        ]
        if invalid_status:
            raise ContractError(
                "completion implementation must be committed or staged, not untracked/unstaged: "
                + "; ".join(invalid_status)
            )
    return state


def remove_lean_comments(text: str) -> str:
    """Replace nested Lean comments while preserving strings and newlines."""

    result: list[str] = []
    index = 0
    block_depth = 0
    in_string = False
    escaped = False
    while index < len(text):
        pair = text[index : index + 2]
        char = text[index]
        if block_depth:
            if pair == "/-":
                block_depth += 1
                result.extend("  ")
                index += 2
            elif pair == "-/":
                block_depth -= 1
                result.extend("  ")
                index += 2
            else:
                result.append("\n" if char == "\n" else " ")
                index += 1
            continue
        if in_string:
            result.append(char)
            if escaped:
                escaped = False
            elif char == "\\":
                escaped = True
            elif char == '"':
                in_string = False
            index += 1
            continue
        if pair == "/-":
            block_depth = 1
            result.extend("  ")
            index += 2
        elif pair == "--":
            newline = text.find("\n", index + 2)
            if newline == -1:
                result.extend(" " * (len(text) - index))
                break
            result.extend(" " * (newline - index))
            result.append("\n")
            index = newline + 1
        else:
            result.append(char)
            if char == '"':
                in_string = True
            index += 1
    if block_depth:
        raise ContractError("unterminated Lean block comment")
    return "".join(result)


def is_lean_identifier_char(char: str, *, initial: bool) -> bool:
    category = unicodedata.category(char)
    if char == "_" or category.startswith("L"):
        return True
    if initial:
        return False
    return (
        char in "'?!"
        or category.startswith("N")
        or category.startswith("M")
    )


def is_bare_lean_component(component: str) -> bool:
    return bool(component) and component not in LEAN_KEYWORDS and all(
        is_lean_identifier_char(char, initial=index == 0)
        for index, char in enumerate(component)
    )


def parse_lean_name_component(text: str, index: int) -> tuple[str, int] | None:
    """Parse one ordinary or guillemet-escaped Lean name component."""

    if index >= len(text):
        return None
    if text[index] == "«":
        end = text.find("»", index + 1)
        if end == -1:
            raise ContractError("unterminated Lean guillemet identifier")
        component = text[index + 1 : end]
        if not component:
            raise ContractError("empty Lean guillemet identifier")
        return component, end + 1
    start = index
    while index < len(text):
        char = text[index]
        if char == "." or char.isspace() or char in IDENTIFIER_DELIMITERS:
            break
        if char in "«»":
            raise ContractError("misplaced Lean guillemet in identifier")
        index += 1
    if index == start:
        return None
    component = text[start:index]
    if not is_bare_lean_component(component):
        raise ContractError(f"invalid bare Lean identifier component: {component!r}")
    return component, index


def parse_lean_qualified_name(text: str, index: int) -> tuple[tuple[str, ...], int] | None:
    """Parse a dotted Lean name without imposing an ASCII identifier alphabet."""

    first = parse_lean_name_component(text, index)
    if first is None:
        return None
    component, index = first
    components = [component]
    while index < len(text) and text[index] == ".":
        next_index = index + 1
        # ``foo.{u}`` is a universe instantiation, not another name component.
        if next_index >= len(text) or text[next_index].isspace() or text[next_index] in IDENTIFIER_DELIMITERS:
            break
        parsed = parse_lean_name_component(text, next_index)
        if parsed is None:
            break
        component, index = parsed
        components.append(component)
    return tuple(components), index


def render_lean_name(components: Sequence[str]) -> str:
    """Render components using Lean's ordinary spelling when no escape is needed."""

    rendered: list[str] = []
    for component in components:
        if is_bare_lean_component(component):
            rendered.append(component)
        else:
            rendered.append(f"«{component}»")
    return ".".join(rendered)


def split_rendered_lean_name(name: str) -> tuple[str, ...]:
    parsed = parse_lean_qualified_name(name, 0)
    if parsed is None:
        raise ContractError(f"invalid Lean name: {name!r}")
    components, end = parsed
    if end != len(name):
        raise ContractError(f"trailing text in Lean name: {name!r}")
    return components


def namespace_of_rendered_lean_name(name: str) -> str:
    components = split_rendered_lean_name(name)
    if len(components) < 2:
        return ""
    return render_lean_name(components[:-1])


def explicit_api_names(text: str) -> tuple[str, ...]:
    """Return exact whole-command project FQNs, failing closed on ambiguity."""

    result: list[str] = []
    for line_number, line in enumerate(text.splitlines(), 1):
        match = API_COMMAND_LINE_RE.fullmatch(line)
        if match is None:
            continue
        target = match.group("target").strip()
        if not target:
            raise ContractError(
                f"line {line_number}: #check/#synth target must be on the command line"
            )
        project_bearing = PROJECT_PREFIX in target
        if target.startswith("@"):
            target = target[1:].lstrip()
        try:
            parsed = parse_lean_qualified_name(target, 0)
        except ContractError as error:
            if project_bearing:
                raise ContractError(
                    f"line {line_number}: malformed project #check/#synth target: {error}"
                ) from error
            continue
        if parsed is None:
            if project_bearing:
                raise ContractError(
                    f"line {line_number}: cannot parse project #check/#synth target"
                )
            continue
        components, end = parsed
        if len(components) < 2 or components[0] != PROJECT_PREFIX:
            if project_bearing:
                raise ContractError(
                    f"line {line_number}: project name is not the exact assertion target"
                )
            continue
        if target[end:].strip():
            raise ContractError(
                f"line {line_number}: trailing text after project #check/#synth target: "
                f"{target[end:].strip()!r}"
            )
        result.append(render_lean_name(components))
    return tuple(result)


def module_name(path: Path) -> str:
    return ".".join(path.with_suffix("").parts)


def lean_source_paths() -> list[Path]:
    paths: list[Path] = []
    for root_name in ("NumStability", "NumStabilityTest"):
        root_file = ROOT / f"{root_name}.lean"
        if root_file.is_file():
            paths.append(root_file)
        root_dir = ROOT / root_name
        if root_dir.is_dir():
            paths.extend(sorted(root_dir.rglob("*.lean")))
    return paths


def parse_import_edges(uncommented: str) -> tuple[tuple[str, ...], tuple[str, ...]]:
    """Return all and re-exported imports under Lean 4 module-mode rules."""
    import_rows = tuple(
        (
            match.group("module"),
            frozenset(match.group("modifiers").split()),
        )
        for match in IMPORT_RE.finditer(uncommented)
    )
    imports = tuple(target for target, _ in import_rows)
    module_mode = bool(MODULE_MODE_RE.search(uncommented))
    exported_imports = tuple(
        target
        for target, modifiers in import_rows
        if "public" in modifiers
        or (not module_mode and "private" not in modifiers)
    )
    return imports, exported_imports


def scan_modules() -> dict[str, Module]:
    modules: dict[str, Module] = {}
    for path in lean_source_paths():
        relative = path.relative_to(ROOT)
        name = module_name(relative)
        text = path.read_text(encoding="utf-8-sig")
        uncommented = remove_lean_comments(text)
        imports, exported_imports = parse_import_edges(uncommented)
        if name in modules:
            raise ContractError(f"duplicate Lean module: {name}")
        modules[name] = Module(
            name=name,
            path=path,
            imports=imports,
            exported_imports=exported_imports,
        )
    return modules


def import_closure(
    modules: Mapping[str, Module], roots: Iterable[str], *, exported_only: bool
) -> set[str]:
    result: set[str] = set()
    pending = list(roots)
    while pending:
        name = pending.pop()
        if name in result:
            continue
        result.add(name)
        module = modules.get(name)
        if module is not None:
            edges = module.exported_imports if exported_only else module.imports
            pending.extend(target for target in edges if target in modules)
    return result


def all_import_closure(
    modules: Mapping[str, Module], roots: Iterable[str]
) -> set[str]:
    """Build/discovery closure, including private module-mode imports."""
    return import_closure(modules, roots, exported_only=False)


def exported_api_closure(
    modules: Mapping[str, Module], roots: Iterable[str]
) -> set[str]:
    """Downstream-visible closure under Lean 4 module import semantics."""
    return import_closure(modules, roots, exported_only=True)


def tier_for(module: str, manifest: Mapping[str, Any]) -> str | None:
    exact = manifest.get("exact", {})
    if module in exact:
        return exact[module]
    matches = [
        (str(row["prefix"]), str(row["tier"]))
        for row in manifest.get("prefixes", [])
        if module.startswith(str(row.get("prefix", "")))
    ]
    if not matches:
        return None
    longest = max(len(prefix) for prefix, _ in matches)
    tiers = {tier for prefix, tier in matches if len(prefix) == longest}
    if len(tiers) != 1:
        raise ContractError(f"ambiguous tier prefixes for {module}: {sorted(tiers)}")
    return next(iter(tiers))


def is_historical_surface(module: str, tiers: Mapping[str, Any]) -> bool:
    return module in HISTORICAL_ROOT_SURFACES or tier_for(module, tiers) == "compatibility"


def contract_row_key(row: Mapping[str, Any]) -> tuple[str, str, str, str]:
    return (
        str(row.get("declaration", "")),
        str(row.get("test_module", "")),
        str(row.get("surface", "")),
        str(row.get("surface_kind", "")),
    )


def sorted_contract_rows(rows: Iterable[Mapping[str, Any]]) -> list[dict[str, Any]]:
    return [dict(row) for row in sorted(rows, key=contract_row_key)]


def test_evidence_json(
    evidence: Iterable[tuple[str, str, str, int]],
) -> list[dict[str, Any]]:
    return [
        {
            "assertion_occurrences": occurrences,
            "surface": surface,
            "surface_kind": surface_kind,
            "test_module": test_module,
        }
        for test_module, surface, surface_kind, occurrences in evidence
    ]


def derive_test_selections(
    modules: Mapping[str, Module], tiers: Mapping[str, Any]
) -> tuple[dict[str, TestSelection], dict[str, Any]]:
    reachable_tests = all_import_closure(modules, (TEST_ROOT,))
    by_name: dict[str, dict[str, set[str]]] = {}
    contract_rows: list[dict[str, Any]] = []
    selected_test_modules: set[str] = set()
    assertion_count = 0

    for test_module in sorted(reachable_tests):
        if not test_module.startswith("NumStabilityTest."):
            continue
        module = modules.get(test_module)
        if module is None or len(module.imports) != 1:
            continue
        surface = module.imports[0]
        if surface not in modules or not (
            surface == PROJECT_PREFIX or surface.startswith(f"{PROJECT_PREFIX}.")
        ):
            continue
        text = module.path.read_text(encoding="utf-8-sig")
        uncommented = remove_lean_comments(text)
        assertions = explicit_api_names(uncommented)
        if not assertions:
            continue
        selected_test_modules.add(test_module)
        assertion_count += len(assertions)
        historical = is_historical_surface(surface, tiers)
        for fqn in assertions:
            state = by_name.setdefault(
                fqn,
                {
                    "tests": set(),
                    "canonical": set(),
                    "historical": set(),
                    "evidence": {},
                },
            )
            state["tests"].add(test_module)
            state["historical" if historical else "canonical"].add(surface)
            evidence_key = (
                test_module,
                surface,
                "historical" if historical else "canonical",
            )
            state["evidence"][evidence_key] = state["evidence"].get(evidence_key, 0) + 1

    selections = {
        fqn: TestSelection(
            fqn=fqn,
            test_modules=tuple(sorted(state["tests"])),
            canonical_surfaces=tuple(sorted(state["canonical"])),
            historical_surfaces=tuple(sorted(state["historical"])),
            test_evidence=tuple(
                sorted((*evidence, occurrences) for evidence, occurrences in state["evidence"].items())
            ),
        )
        for fqn, state in sorted(by_name.items())
    }
    for fqn, selection in selections.items():
        for test_module, surface, surface_kind, occurrences in selection.test_evidence:
            contract_rows.append(
                {
                    "assertion_occurrences": occurrences,
                    "declaration": fqn,
                    "surface": surface,
                    "surface_kind": surface_kind,
                    "test_module": test_module,
                }
            )
    derivation = {
        "assertion_count": assertion_count,
        "contract_sha256": canonical_json_sha256(sorted_contract_rows(contract_rows)),
        "isolated_test_module_count": len(selected_test_modules),
        "selected_declaration_count": len(selections),
        "test_root": TEST_ROOT,
    }
    return selections, derivation


def documented_entrypoints(tiers: Mapping[str, Any]) -> tuple[str, ...]:
    reusable = tiers.get("reusable_entrypoints")
    if not isinstance(reusable, list) or not all(isinstance(item, str) for item in reusable):
        raise ContractError("tiers.json has no valid reusable_entrypoints array")
    return tuple(sorted(set(CURATED_DOCUMENTED_ENTRYPOINTS) | set(reusable)))


def source_tree_sha256(modules: Mapping[str, Module], prefix: str) -> str:
    digest = hashlib.sha256()
    for name, module in sorted(modules.items()):
        if name != prefix and not name.startswith(f"{prefix}."):
            continue
        relative = module.path.relative_to(ROOT).as_posix()
        text = module.path.read_text(encoding="utf-8-sig")
        normalized = text.replace("\r\n", "\n").replace("\r", "\n")
        digest.update(relative.encode("utf-8"))
        digest.update(b"\0")
        digest.update(normalized.encode("utf-8"))
        digest.update(b"\0")
    return digest.hexdigest().upper()


_ENVIRONMENT_BUILD_VERIFIED = False
_ALLOWED_DIRTY_GOVERNED_PATHS: set[str] = set()


def allow_exact_implementation_dirty_paths(enabled: bool) -> None:
    global _ALLOWED_DIRTY_GOVERNED_PATHS
    _ALLOWED_DIRTY_GOVERNED_PATHS = (
        {row["path"] for row in implementation_postimage_rows()} if enabled else set()
    )


def ensure_environment_built() -> None:
    """Build the clean exact-HEAD test root before consulting environment data."""

    global _ENVIRONMENT_BUILD_VERIFIED
    if _ENVIRONMENT_BUILD_VERIFIED:
        return
    governed_paths = (
        "NumStability.lean",
        "NumStability",
        "NumStabilityTest.lean",
        "NumStabilityTest",
        "lake-manifest.json",
        "lakefile.toml",
        "lean-toolchain",
    )
    try:
        cleanliness = subprocess.run(
            (
                "git",
                "status",
                "--porcelain=v1",
                "--untracked-files=all",
                "--",
                *governed_paths,
            ),
            cwd=ROOT,
            check=False,
            text=True,
            encoding="utf-8",
            errors="replace",
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
        )
    except FileNotFoundError as error:
        raise ContractError("required executable not found: git") from error
    dirty_paths = {
        line[3:].strip().replace("\\", "/")
        for line in cleanliness.stdout.splitlines()
        if len(line) >= 4
    }
    unexpected_dirty = sorted(dirty_paths - _ALLOWED_DIRTY_GOVERNED_PATHS)
    if cleanliness.returncode or unexpected_dirty:
        details = "\n".join(
            part.strip()
            for part in (cleanliness.stdout, cleanliness.stderr)
            if part.strip()
        )
        raise ContractError(
            "environment extraction requires a clean exact-HEAD production/test/toolchain "
            "scope (the exact atomic implementation postimages may be staged)\n"
            + ("unexpected paths: " + ", ".join(unexpected_dirty) + "\n" if unexpected_dirty else "")
            + details
        )
    try:
        result = subprocess.run(
            ("lake", "build", "NumStabilityTest"),
            cwd=ROOT,
            check=False,
            text=True,
            encoding="utf-8",
            errors="replace",
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
        )
    except FileNotFoundError as error:
        raise ContractError("required executable not found: lake") from error
    if result.returncode:
        details = "\n".join(
            part.strip() for part in (result.stdout, result.stderr) if part.strip()
        )
        raise ContractError(
            f"required exact-HEAD NumStabilityTest build failed ({result.returncode}):\n{details}"
        )
    _ENVIRONMENT_BUILD_VERIFIED = True


def run_environment_extractor(
    selected_names: Sequence[str], entrypoints: Sequence[str]
) -> EnvironmentSnapshot:
    ensure_environment_built()
    extractor_sha = sha256_bytes(LEAN_EXTRACTOR_SOURCE.encode("utf-8"))
    with tempfile.TemporaryDirectory(prefix="numstability-supported-api-") as temp_name:
        temp = Path(temp_name)
        extractor = temp / "extract_supported_api.lean"
        names = temp / "selected-names.txt"
        imports = temp / "documented-entrypoints.txt"
        output = temp / "environment.tsv"
        extractor.write_text(LEAN_EXTRACTOR_SOURCE, encoding="utf-8", newline="\n")
        encoded_names = [
            "\t".join(split_rendered_lean_name(name))
            for name in sorted(set(selected_names))
        ]
        if any("\t" in component or "\n" in component or "\r" in component
               for name in selected_names for component in split_rendered_lean_name(name)):
            raise ContractError("selected Lean name contains an unsupported control character")
        names.write_text("\n".join(encoded_names) + "\n", encoding="utf-8")
        encoded_entrypoints = [
            "\t".join(split_rendered_lean_name(name))
            for name in sorted(set(entrypoints))
        ]
        if not encoded_entrypoints:
            raise ContractError("environment extraction requires documented entrypoints")
        if any(
            "\t" in component or "\n" in component or "\r" in component
            for name in entrypoints
            for component in split_rendered_lean_name(name)
        ):
            raise ContractError(
                "documented entrypoint contains an unsupported control character"
            )
        imports.write_text(
            "\n".join(encoded_entrypoints) + "\n", encoding="utf-8"
        )
        command = (
            "lake",
            "env",
            "lean",
            "--run",
            str(extractor),
            str(names),
            str(imports),
            str(output),
        )
        try:
            result = subprocess.run(
                command,
                cwd=ROOT,
                check=False,
                text=True,
                encoding="utf-8",
                errors="replace",
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
            )
        except FileNotFoundError as error:
            raise ContractError("required executable not found: lake") from error
        if result.returncode:
            details = "\n".join(part.strip() for part in (result.stdout, result.stderr) if part.strip())
            raise ContractError(
                f"Lean environment extractor failed ({result.returncode}):\n{details}"
            )
        if not output.is_file():
            raise ContractError("Lean environment extractor produced no output")

        selected: dict[str, EnvironmentDeclaration] = {}
        visible_by_owner: dict[str, list[str]] = {}
        format_seen = False
        for line_number, line in enumerate(output.read_text(encoding="utf-8").splitlines(), 1):
            fields = line.split("\t")
            if fields == ["format", "1"]:
                if format_seen:
                    raise ContractError("duplicate environment format row")
                format_seen = True
            elif len(fields) == 3 and fields[0] == "visible":
                _, fqn, owner = fields
                visible_by_owner.setdefault(owner, []).append(fqn)
            elif len(fields) == 7 and fields[0] == "selected":
                _, fqn, owner, kind, protected_text, visibility, type_repr = fields
                if fqn in selected:
                    raise ContractError(f"duplicate selected environment row: {fqn}")
                if protected_text not in {"true", "false"}:
                    raise ContractError(
                        f"invalid protected flag for {fqn}: {protected_text!r}"
                    )
                selected[fqn] = EnvironmentDeclaration(
                    fqn=fqn,
                    owner_module=owner,
                    kind=kind,
                    protected=protected_text == "true",
                    visibility=visibility,
                    normalized_type_sha256=sha256_bytes(
                        decode_type_payload(type_repr).encode("utf-8")
                    ),
                )
            else:
                raise ContractError(
                    f"invalid environment row {line_number}: {fields[:3]!r}"
                )
        if not format_seen:
            raise ContractError("environment output has no format row")
        missing = sorted(set(selected_names) - set(selected))
        if missing:
            sample = ", ".join(missing[:10])
            suffix = " ..." if len(missing) > 10 else ""
            raise ContractError(
                f"{len(missing)} checked declarations are absent from the Lean environment: "
                f"{sample}{suffix}"
            )
        return EnvironmentSnapshot(
            selected=selected,
            public_names_by_owner={
                owner: tuple(sorted(set(names)))
                for owner, names in sorted(visible_by_owner.items())
            },
        )


def entrypoint_closures(
    modules: Mapping[str, Module], entrypoints: Sequence[str]
) -> dict[str, set[str]]:
    missing = [name for name in entrypoints if name not in modules]
    if missing:
        raise ContractError("missing documented entrypoints: " + ", ".join(missing))
    return {name: exported_api_closure(modules, (name,)) for name in entrypoints}


def reachable_entrypoints_for_owner(
    owner: str, closures: Mapping[str, set[str]]
) -> list[str]:
    return sorted(name for name, reachable in closures.items() if owner in reachable)


def require_owner_reachable_from_evidence_surfaces(
    fqn: str,
    owner: str,
    selection: TestSelection,
    modules: Mapping[str, Module],
    surface_closures: Mapping[str, set[str]],
) -> None:
    for surface in sorted(
        set(selection.canonical_surfaces) | set(selection.historical_surfaces)
    ):
        if surface not in modules:
            raise ContractError(f"{fqn}: evidence surface is not a module: {surface}")
        if owner not in surface_closures[surface]:
            raise ContractError(
                f"{fqn}: owner {owner} is not reachable from sole imported evidence "
                f"surface {surface}"
            )


def evidence_surface_closures(
    modules: Mapping[str, Module], selections: Mapping[str, TestSelection]
) -> dict[str, set[str]]:
    surfaces = sorted(
        {
            surface
            for selection in selections.values()
            for surface in (
                *selection.canonical_surfaces,
                *selection.historical_surfaces,
            )
        }
    )
    missing = [surface for surface in surfaces if surface not in modules]
    if missing:
        raise ContractError("evidence surfaces are not modules: " + ", ".join(missing))
    return {
        surface: exported_api_closure(modules, (surface,))
        for surface in surfaces
    }


def visible_names_for_modules(
    module_names: set[str], public_names_by_owner: Mapping[str, tuple[str, ...]]
) -> list[str]:
    return sorted(
        name
        for owner in sorted(module_names)
        for name in public_names_by_owner.get(owner, ())
    )


def visibility_guard(
    closures: Mapping[str, set[str]],
    public_names_by_owner: Mapping[str, tuple[str, ...]],
) -> list[dict[str, Any]]:
    result: list[dict[str, Any]] = []
    for entrypoint, reachable in sorted(closures.items()):
        names = visible_names_for_modules(reachable, public_names_by_owner)
        result.append(
            {
                "entrypoint": entrypoint,
                "public_authored_declaration_count": len(names),
                "public_authored_names_sha256": canonical_json_sha256(names),
            }
        )
    return result


def require_exact_c0007_generation_state(
    modules: Mapping[str, Module], checkpoint_code_sha: str
) -> None:
    if checkpoint_code_sha != C0007_CODE_SHA:
        raise ContractError(
            f"baseline generation is restricted to exact C0007 SHA {C0007_CODE_SHA}"
        )
    governed_paths = (
        "NumStability.lean",
        "NumStability",
        "NumStabilityTest.lean",
        "NumStabilityTest",
        "docs/architecture/tiers.json",
        "lake-manifest.json",
        "lakefile.toml",
        "lean-toolchain",
    )
    commands = (
        ("git", "diff", "--quiet", C0007_CODE_SHA, "--", *governed_paths),
        (
            "git",
            "status",
            "--porcelain=v1",
            "--untracked-files=all",
            "--",
            *governed_paths,
        ),
    )
    for command in commands:
        try:
            result = subprocess.run(
                command,
                cwd=ROOT,
                check=False,
                text=True,
                encoding="utf-8",
                errors="replace",
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
            )
        except FileNotFoundError as error:
            raise ContractError("required executable not found: git") from error
        if result.returncode or (command[1] == "status" and result.stdout.strip()):
            details = "\n".join(
                part.strip() for part in (result.stdout, result.stderr) if part.strip()
            )
            raise ContractError(
                "baseline generation requires production, tests, and tiers.json to "
                f"match exact C0007 bytes; command failed: {' '.join(command)}"
                + (f"\n{details}" if details else "")
            )
    reachable = all_import_closure(modules, (TEST_ROOT,))
    unexpected = sorted(
        {
            test_module
            for _, test_module, _, _, _ in APPROVED_I01_TEST_EVIDENCE
        }
        & reachable
    )
    if unexpected:
        raise ContractError(
            "C0007 baseline generation refused after I01 activation: "
            + ", ".join(unexpected)
        )


def build_contract(
    *,
    checkpoint_id: str,
    checkpoint_code_sha: str,
) -> dict[str, Any]:
    tiers = json.loads(TIER_MANIFEST.read_text(encoding="utf-8"))
    modules = scan_modules()
    require_exact_c0007_generation_state(modules, checkpoint_code_sha)
    selections, test_derivation = derive_test_selections(modules, tiers)
    entrypoints = documented_entrypoints(tiers)
    env = run_environment_extractor(tuple(selections), entrypoints)
    closures = entrypoint_closures(modules, entrypoints)
    surface_closures = evidence_surface_closures(modules, selections)

    declarations: list[dict[str, Any]] = []
    for fqn, selection in sorted(selections.items()):
        declaration = env.selected[fqn]
        if declaration.visibility != "public":
            raise ContractError(
                f"explicit supported declaration is not public: {fqn} ({declaration.visibility})"
            )
        require_owner_reachable_from_evidence_surfaces(
            fqn, declaration.owner_module, selection, modules, surface_closures
        )
        declarations.append(
            {
                "canonical_surfaces": list(selection.canonical_surfaces),
                "expected_entrypoint_reachability": reachable_entrypoints_for_owner(
                    declaration.owner_module, closures
                ),
                "fqn": fqn,
                "historical_surfaces": list(selection.historical_surfaces),
                "kind": declaration.kind,
                "namespace": namespace_of_rendered_lean_name(fqn),
                "owner_module": declaration.owner_module,
                "protected": declaration.protected,
                "test_evidence": test_evidence_json(selection.test_evidence),
                "test_modules": list(selection.test_modules),
                "type_evidence": {
                    "normalization": TYPE_NORMALIZATION,
                    "sha256": declaration.normalized_type_sha256,
                },
                "visibility": declaration.visibility,
            }
        )

    return {
        "baseline": {
            "checkpoint_code_sha": checkpoint_code_sha,
            "checkpoint_id": checkpoint_id,
            "production_source_tree_sha256": source_tree_sha256(modules, "NumStability"),
            "test_source_tree_sha256": source_tree_sha256(modules, "NumStabilityTest"),
        },
        "declarations": declarations,
        "derivation": {
            **test_derivation,
            "declaration_policy": DECLARATION_POLICY,
            "documented_entrypoints": list(entrypoints),
            "checker_sha256": sha256_bytes(Path(__file__).read_bytes()),
            "environment_extractor_sha256": sha256_bytes(
                LEAN_EXTRACTOR_SOURCE.encode("utf-8")
            ),
            "protected_selected_declaration_count": sum(
                1 for row in declarations if row["protected"]
            ),
            "tier_manifest_sha256": sha256_bytes(TIER_MANIFEST.read_bytes()),
            "toolchain_inputs": {
                name: sha256_bytes((ROOT / name).read_bytes())
                for name in ("lake-manifest.json", "lakefile.toml", "lean-toolchain")
            },
            "type_normalization": TYPE_NORMALIZATION,
            "visibility_exclusion_policy": VISIBILITY_EXCLUSION_POLICY,
            "visibility_guard_policy": VISIBILITY_GUARD_POLICY,
        },
        "record_kind": "supported_api_baseline",
        "schema_version": SCHEMA_VERSION,
        "visibility_guard": visibility_guard(closures, env.public_names_by_owner),
    }


def require_sorted_unique_strings(value: Any, label: str, failures: list[str]) -> list[str]:
    if not isinstance(value, list) or not all(isinstance(item, str) for item in value):
        failures.append(f"{label}: expected a string array")
        return []
    if value != sorted(set(value)):
        failures.append(f"{label}: must be sorted and duplicate-free")
    return list(value)


def evidence_key(row: Mapping[str, Any]) -> tuple[str, str, str]:
    return (
        str(row.get("test_module", "")),
        str(row.get("surface", "")),
        str(row.get("surface_kind", "")),
    )


def validate_test_evidence(
    row: Mapping[str, Any], label: str, failures: list[str]
) -> list[dict[str, Any]]:
    value = row.get("test_evidence")
    if not isinstance(value, list):
        failures.append(f"{label}.test_evidence: expected array")
        return []
    result: list[dict[str, Any]] = []
    keys: list[tuple[str, str, str]] = []
    for index, evidence in enumerate(value):
        evidence_label = f"{label}.test_evidence[{index}]"
        if not isinstance(evidence, dict):
            failures.append(f"{evidence_label}: expected object")
            continue
        if set(evidence) != {
            "assertion_occurrences",
            "surface",
            "surface_kind",
            "test_module",
        }:
            failures.append(f"{evidence_label}: unexpected or missing fields")
        test_module = evidence.get("test_module")
        surface = evidence.get("surface")
        surface_kind = evidence.get("surface_kind")
        occurrences = evidence.get("assertion_occurrences")
        if not isinstance(test_module, str) or not test_module.startswith(
            "NumStabilityTest."
        ):
            failures.append(f"{evidence_label}.test_module: expected project test module")
        if not isinstance(surface, str) or not (
            surface == PROJECT_PREFIX or surface.startswith(f"{PROJECT_PREFIX}.")
        ):
            failures.append(f"{evidence_label}.surface: expected project surface")
        if surface_kind not in {"canonical", "historical"}:
            failures.append(f"{evidence_label}.surface_kind: expected canonical/historical")
        if not isinstance(occurrences, int) or isinstance(occurrences, bool) or occurrences < 1:
            failures.append(f"{evidence_label}.assertion_occurrences: expected positive int")
        result.append(dict(evidence))
        keys.append(evidence_key(evidence))
    if keys != sorted(set(keys)):
        failures.append(f"{label}.test_evidence: must be sorted and key-unique")
    expected_tests = sorted(
        {str(evidence.get("test_module")) for evidence in result}
    )
    expected_canonical = sorted(
        {
            str(evidence.get("surface"))
            for evidence in result
            if evidence.get("surface_kind") == "canonical"
        }
    )
    expected_historical = sorted(
        {
            str(evidence.get("surface"))
            for evidence in result
            if evidence.get("surface_kind") == "historical"
        }
    )
    if row.get("test_modules") != expected_tests:
        failures.append(f"{label}.test_modules: inconsistent with test_evidence")
    if row.get("canonical_surfaces") != expected_canonical:
        failures.append(f"{label}.canonical_surfaces: inconsistent with test_evidence")
    if row.get("historical_surfaces") != expected_historical:
        failures.append(f"{label}.historical_surfaces: inconsistent with test_evidence")
    return result


def contract_rows_from_declarations(declarations: Any) -> list[dict[str, Any]]:
    result: list[dict[str, Any]] = []
    if not isinstance(declarations, list):
        return result
    for declaration in declarations:
        if not isinstance(declaration, dict) or not isinstance(declaration.get("fqn"), str):
            continue
        evidence = declaration.get("test_evidence")
        if not isinstance(evidence, list):
            continue
        for item in evidence:
            if not isinstance(item, dict):
                continue
            result.append(
                {
                    "assertion_occurrences": item.get("assertion_occurrences"),
                    "declaration": declaration["fqn"],
                    "surface": item.get("surface"),
                    "surface_kind": item.get("surface_kind"),
                    "test_module": item.get("test_module"),
                }
            )
    return sorted_contract_rows(result)


def reconstructed_derivation(declarations: Any) -> dict[str, Any]:
    rows = contract_rows_from_declarations(declarations)
    return {
        "assertion_count": sum(
            int(row["assertion_occurrences"])
            for row in rows
            if isinstance(row.get("assertion_occurrences"), int)
        ),
        "contract_sha256": canonical_json_sha256(rows),
        "isolated_test_module_count": len({row["test_module"] for row in rows}),
        "selected_declaration_count": len(declarations) if isinstance(declarations, list) else 0,
        "test_root": TEST_ROOT,
    }


def validate_baseline_schema(baseline: Mapping[str, Any]) -> list[str]:
    failures: list[str] = []
    if set(baseline) != {
        "baseline",
        "declarations",
        "derivation",
        "record_kind",
        "schema_version",
        "visibility_guard",
    }:
        failures.append("baseline: unexpected or missing top-level fields")
    if baseline.get("schema_version") != SCHEMA_VERSION:
        failures.append(
            f"schema_version: expected {SCHEMA_VERSION}, got {baseline.get('schema_version')!r}"
        )
    if baseline.get("record_kind") != "supported_api_baseline":
        failures.append("record_kind: expected supported_api_baseline")
    derivation = baseline.get("derivation")
    if not isinstance(derivation, dict):
        failures.append("derivation: expected object")
        derivation = {}
    expected_derivation_fields = {
        "assertion_count",
        "checker_sha256",
        "contract_sha256",
        "declaration_policy",
        "documented_entrypoints",
        "environment_extractor_sha256",
        "isolated_test_module_count",
        "protected_selected_declaration_count",
        "selected_declaration_count",
        "test_root",
        "tier_manifest_sha256",
        "toolchain_inputs",
        "type_normalization",
        "visibility_exclusion_policy",
        "visibility_guard_policy",
    }
    if set(derivation) != expected_derivation_fields:
        failures.append("derivation: unexpected or missing fields")
    baseline_facts = baseline.get("baseline")
    if not isinstance(baseline_facts, dict) or set(baseline_facts) != {
        "checkpoint_code_sha",
        "checkpoint_id",
        "production_source_tree_sha256",
        "test_source_tree_sha256",
    }:
        failures.append("baseline facts: unexpected or missing fields")
    else:
        if baseline_facts.get("checkpoint_code_sha") != C0007_CODE_SHA:
            failures.append("baseline.checkpoint_code_sha: expected exact C0007")
        if baseline_facts.get("checkpoint_id") != "C0007":
            failures.append("baseline.checkpoint_id: expected C0007")
        expected_source_hashes = {
            "production_source_tree_sha256": C0007_PRODUCTION_SOURCE_TREE_SHA256,
            "test_source_tree_sha256": C0007_TEST_SOURCE_TREE_SHA256,
        }
        for field, expected in expected_source_hashes.items():
            if baseline_facts.get(field) != expected:
                failures.append(
                    f"baseline.{field}: expected exact C0007 {expected}, "
                    f"got {baseline_facts.get(field)!r}"
                )
    entrypoints = require_sorted_unique_strings(
        derivation.get("documented_entrypoints"),
        "derivation.documented_entrypoints",
        failures,
    )
    if derivation.get("type_normalization") != TYPE_NORMALIZATION:
        failures.append(
            f"derivation.type_normalization: expected {TYPE_NORMALIZATION}"
        )
    if derivation.get("visibility_exclusion_policy") != VISIBILITY_EXCLUSION_POLICY:
        failures.append("derivation.visibility_exclusion_policy: unsupported exclusion policy")
    if derivation.get("declaration_policy") != DECLARATION_POLICY:
        failures.append("derivation.declaration_policy: unsupported selection policy")
    if derivation.get("visibility_guard_policy") != VISIBILITY_GUARD_POLICY:
        failures.append("derivation.visibility_guard_policy: unsupported guard policy")
    expected_input_hashes = {
        "checker_sha256": sha256_bytes(Path(__file__).read_bytes()),
        "environment_extractor_sha256": sha256_bytes(
            LEAN_EXTRACTOR_SOURCE.encode("utf-8")
        ),
        "tier_manifest_sha256": C0007_TIER_MANIFEST_SHA256,
    }
    for field, expected in expected_input_hashes.items():
        if derivation.get(field) != expected:
            failures.append(
                f"derivation.{field}: pinned input drift: expected {expected}, "
                f"got {derivation.get(field)!r}"
            )
    expected_toolchain_inputs = {
        name: sha256_bytes((ROOT / name).read_bytes())
        for name in ("lake-manifest.json", "lakefile.toml", "lean-toolchain")
    }
    if derivation.get("toolchain_inputs") != expected_toolchain_inputs:
        failures.append("derivation.toolchain_inputs: pinned toolchain input drift")
    declarations = baseline.get("declarations")
    if not isinstance(declarations, list):
        failures.append("declarations: expected array")
        declarations = []
    fqns: list[str] = []
    for index, row in enumerate(declarations):
        label = f"declarations[{index}]"
        if not isinstance(row, dict):
            failures.append(f"{label}: expected object")
            continue
        if set(row) != {
            "canonical_surfaces",
            "expected_entrypoint_reachability",
            "fqn",
            "historical_surfaces",
            "kind",
            "namespace",
            "owner_module",
            "protected",
            "test_evidence",
            "test_modules",
            "type_evidence",
            "visibility",
        }:
            failures.append(f"{label}: unexpected or missing fields")
        fqn = row.get("fqn")
        if not isinstance(fqn, str) or not fqn.startswith("NumStability."):
            failures.append(f"{label}.fqn: expected NumStability FQN")
            continue
        fqns.append(fqn)
        if row.get("namespace") != namespace_of_rendered_lean_name(fqn):
            failures.append(f"{label}.namespace: inconsistent with FQN")
        if row.get("visibility") != "public":
            failures.append(f"{label}.visibility: supported rows must be public")
        if not isinstance(row.get("protected"), bool):
            failures.append(f"{label}.protected: expected boolean")
        for field in ("kind", "owner_module"):
            if not isinstance(row.get(field), str) or not row.get(field):
                failures.append(f"{label}.{field}: expected nonempty string")
        for field in (
            "canonical_surfaces",
            "historical_surfaces",
            "test_modules",
            "expected_entrypoint_reachability",
        ):
            require_sorted_unique_strings(row.get(field), f"{label}.{field}", failures)
        validate_test_evidence(row, label, failures)
        unknown_entrypoints = sorted(
            set(row.get("expected_entrypoint_reachability", [])) - set(entrypoints)
        )
        if unknown_entrypoints:
            failures.append(
                f"{label}.expected_entrypoint_reachability: unknown entries "
                + ", ".join(unknown_entrypoints)
            )
        evidence = row.get("type_evidence")
        if not isinstance(evidence, dict):
            failures.append(f"{label}.type_evidence: expected object")
        else:
            if set(evidence) != {"normalization", "sha256"}:
                failures.append(f"{label}.type_evidence: unexpected or missing fields")
            if evidence.get("normalization") != TYPE_NORMALIZATION:
                failures.append(f"{label}.type_evidence.normalization: unsupported")
            digest = evidence.get("sha256")
            if not isinstance(digest, str) or not re.fullmatch(r"[0-9A-F]{64}", digest):
                failures.append(f"{label}.type_evidence.sha256: expected uppercase SHA-256")
    if fqns != sorted(set(fqns)):
        failures.append("declarations: FQNs must be sorted and duplicate-free")
    expected_derivation = reconstructed_derivation(declarations)
    for field, expected in expected_derivation.items():
        if derivation.get(field) != expected:
            failures.append(
                f"derivation.{field}: expected reconstructed value {expected!r}, "
                f"got {derivation.get(field)!r}"
            )
    expected_protected_count = sum(
        1 for row in declarations if isinstance(row, dict) and row.get("protected") is True
    )
    if derivation.get("protected_selected_declaration_count") != expected_protected_count:
        failures.append(
            "derivation.protected_selected_declaration_count: does not match declarations"
        )

    guard = baseline.get("visibility_guard")
    if not isinstance(guard, list):
        failures.append("visibility_guard: expected array")
        guard = []
    guard_names: list[str] = []
    for index, row in enumerate(guard):
        label = f"visibility_guard[{index}]"
        if not isinstance(row, dict):
            failures.append(f"{label}: expected object")
            continue
        if set(row) != {
            "entrypoint",
            "public_authored_declaration_count",
            "public_authored_names_sha256",
        }:
            failures.append(f"{label}: unexpected or missing fields")
        entrypoint = row.get("entrypoint")
        if not isinstance(entrypoint, str):
            failures.append(f"{label}.entrypoint: expected string")
            continue
        guard_names.append(entrypoint)
        count = row.get("public_authored_declaration_count")
        if not isinstance(count, int) or isinstance(count, bool) or count < 0:
            failures.append(f"{label}.public_authored_declaration_count: expected nonnegative int")
        digest = row.get("public_authored_names_sha256")
        if not isinstance(digest, str) or not re.fullmatch(r"[0-9A-F]{64}", digest):
            failures.append(f"{label}.public_authored_names_sha256: expected uppercase SHA-256")
    if guard_names != entrypoints:
        failures.append("visibility_guard: entrypoints do not exactly match documented entrypoints")
    return failures


def index_rows(rows: Any, key: str) -> dict[str, Mapping[str, Any]]:
    if not isinstance(rows, list):
        return {}
    return {
        str(row[key]): row
        for row in rows
        if isinstance(row, dict) and isinstance(row.get(key), str)
    }


def approved_i01_evidence_json() -> list[dict[str, Any]]:
    return sorted_contract_rows(
        {
            "assertion_occurrences": occurrences,
            "declaration": declaration,
            "surface": surface,
            "surface_kind": surface_kind,
            "test_module": test_module,
        }
        for declaration, test_module, surface, surface_kind, occurrences in APPROVED_I01_TEST_EVIDENCE
    )


def pinned_artifact_rows(mapping: Mapping[str, str]) -> list[dict[str, str]]:
    rows: list[dict[str, str]] = []
    for relative, expected in sorted(mapping.items()):
        actual = sha256_bytes((ROOT / relative).read_bytes())
        if actual != expected:
            raise ContractError(
                f"pinned artifact drift: {relative}: expected {expected}, got {actual}"
            )
        rows.append({"path": relative, "sha256": expected})
    return rows


def declaration_row_from_evidence(
    declaration: EnvironmentDeclaration,
    evidence_rows: Sequence[Mapping[str, Any]],
    closures: Mapping[str, set[str]],
) -> dict[str, Any]:
    evidence = sorted(
        (
            str(row["test_module"]),
            str(row["surface"]),
            str(row["surface_kind"]),
            int(row["assertion_occurrences"]),
        )
        for row in evidence_rows
    )
    return {
        "canonical_surfaces": sorted(
            {surface for _, surface, kind, _ in evidence if kind == "canonical"}
        ),
        "expected_entrypoint_reachability": reachable_entrypoints_for_owner(
            declaration.owner_module, closures
        ),
        "fqn": declaration.fqn,
        "historical_surfaces": sorted(
            {surface for _, surface, kind, _ in evidence if kind == "historical"}
        ),
        "kind": declaration.kind,
        "namespace": namespace_of_rendered_lean_name(declaration.fqn),
        "owner_module": declaration.owner_module,
        "protected": declaration.protected,
        "test_evidence": test_evidence_json(evidence),
        "test_modules": sorted({test_module for test_module, _, _, _ in evidence}),
        "type_evidence": {
            "normalization": TYPE_NORMALIZATION,
            "sha256": declaration.normalized_type_sha256,
        },
        "visibility": declaration.visibility,
    }


def derive_exact_c0007_review_environment_facts(
    baseline: Mapping[str, Any],
    modules: Mapping[str, Module] | None = None,
) -> tuple[list[dict[str, Any]], list[dict[str, Any]]]:
    """Freshly derive the R0014 declaration and owner facts at exact C0007.

    In particular, ``problem2_9Source`` is an existing C0007 declaration that was
    not selected by the C0007 test contract.  Its pending-review row therefore
    cannot be trusted merely because it is structurally valid or self-hashed by
    the review.  Re-extracting every declaration whose owner may move binds the
    additive row's kind, protection, visibility, type and pre-move owner, while
    the C0007 export closures bind its documented-entrypoint reachability.
    """

    if modules is None:
        modules = scan_modules()
    require_exact_c0007_generation_state(
        modules, str(baseline.get("baseline", {}).get("checkpoint_code_sha", ""))
    )
    expected_baseline_facts = {
        "checkpoint_code_sha": C0007_CODE_SHA,
        "checkpoint_id": "C0007",
        "production_source_tree_sha256": source_tree_sha256(modules, "NumStability"),
        "test_source_tree_sha256": source_tree_sha256(modules, "NumStabilityTest"),
    }
    if baseline.get("baseline") != expected_baseline_facts:
        raise ContractError(
            "baseline checkpoint/source facts do not match exact C0007 review inputs"
        )
    entrypoints = tuple(baseline["derivation"]["documented_entrypoints"])
    closures = entrypoint_closures(modules, entrypoints)
    env = run_environment_extractor(
        sorted(APPROVED_I01_OWNER_DESTINATIONS), entrypoints
    )
    approved_rows = approved_i01_evidence_json()
    declaration_rows = []
    for fqn in sorted(APPROVED_I01_NEW_FQNS):
        declaration = env.selected[fqn]
        if declaration.visibility != "public":
            raise ContractError(f"reviewed additive declaration is not public: {fqn}")
        declaration_rows.append(
            declaration_row_from_evidence(
                declaration,
                [row for row in approved_rows if row["declaration"] == fqn],
                closures,
            )
        )
    approved_owner_moves = [
        {
            "fqn": fqn,
            "from_owner_module": env.selected[fqn].owner_module,
            "to_owner_module": destination,
        }
        for fqn, destination in sorted(APPROVED_I01_OWNER_DESTINATIONS.items())
    ]
    return declaration_rows, approved_owner_moves


def validate_review_environment_facts(
    review: Mapping[str, Any],
    expected_declarations: Sequence[Mapping[str, Any]],
    expected_owner_moves: Sequence[Mapping[str, Any]],
) -> list[str]:
    """Compare pending review facts with independently derived C0007 facts."""

    failures: list[str] = []
    if review.get("approved_additive_declarations") != list(expected_declarations):
        failures.append(
            "review.approved_additive_declarations: metadata does not exact-match "
            "the freshly extracted C0007 environment"
        )
    if review.get("approved_owner_moves") != list(expected_owner_moves):
        failures.append(
            "review.approved_owner_moves: from-owner facts do not exact-match the "
            "freshly extracted C0007 environment"
        )
    return failures


def validate_review_against_exact_c0007_environment(
    review: Mapping[str, Any], baseline: Mapping[str, Any]
) -> list[str]:
    """Fail closed on forged pending machine facts before I01 activation."""

    expected_declarations, expected_owner_moves = (
        derive_exact_c0007_review_environment_facts(baseline)
    )
    return validate_review_environment_facts(
        review, expected_declarations, expected_owner_moves
    )


def build_additive_review(baseline: Mapping[str, Any]) -> dict[str, Any]:
    failures = validate_baseline_schema(baseline)
    if failures:
        raise ContractError("cannot review an invalid baseline:\n" + "\n".join(failures))
    declaration_rows, approved_owner_moves = (
        derive_exact_c0007_review_environment_facts(baseline)
    )
    approved_rows = approved_i01_evidence_json()
    request_artifacts = pinned_artifact_rows(R0014_ARTIFACT_SHA256)
    implementation_ledgers = pinned_artifact_rows(IMPLEMENTATION_POSTIMAGE_LEDGERS)
    return {
        "activation_policy": "atomic_when_any_approved_test_module_is_reachable",
        "approved_additive_declarations": declaration_rows,
        "approved_additive_test_evidence": approved_rows,
        "approved_owner_moves": approved_owner_moves,
        "baseline_checkpoint_id": "C0007",
        "baseline_inputs": {
            "baseline_manifest_sha256": canonical_json_sha256(baseline),
            "checker_sha256": baseline["derivation"]["checker_sha256"],
            "checkpoint_code_sha": baseline["baseline"]["checkpoint_code_sha"],
            "environment_extractor_sha256": baseline["derivation"]
            ["environment_extractor_sha256"],
            "production_source_tree_sha256": baseline["baseline"]
            ["production_source_tree_sha256"],
            "test_source_tree_sha256": baseline["baseline"]["test_source_tree_sha256"],
            "tier_manifest_sha256": baseline["derivation"]["tier_manifest_sha256"],
            "toolchain_inputs": baseline["derivation"]["toolchain_inputs"],
        },
        "baseline_manifest_sha256": canonical_json_sha256(baseline),
        "checkpoint_id": "C0008",
        "activation_scope": {
            "approved_additive_declarations_sha256": canonical_json_sha256(
                declaration_rows
            ),
            "approved_additive_test_evidence_sha256": canonical_json_sha256(
                approved_rows
            ),
            "approved_assertion_occurrence_count": sum(
                row["assertion_occurrences"] for row in approved_rows
            ),
            "approved_new_selected_declaration_count": len(declaration_rows),
            "approved_one_import_module_count": len(
                {row["test_module"] for row in approved_rows}
            ),
            "approved_owner_move_count": len(approved_owner_moves),
            "approved_owner_moves_sha256": canonical_json_sha256(
                approved_owner_moves
            ),
            "approved_tier_manifest_sha256": R0014_TIER_MANIFEST_SHA256,
            "implementation_commit_sha": None,
            "implementation_id": "I01",
            "implementation_path_count": 14,
            "implementation_path_set_sha256": implementation_path_set_sha256(),
            "implementation_postimage_ledgers": implementation_ledgers,
            "planned_control_commit_sha": None,
            "request_id": "R0014",
            "request_artifacts": request_artifacts,
        },
        "decision": None,
        "machine_generated_by": "tools/architecture/check_supported_api.py",
        "primary_human_review_required": True,
        "rationale": (
            "Machine-derived candidate facts for freezing C0007 and, only after independent "
            "primary-human approval, authorizing the atomic R0014/I01 addition: five "
            "one-import modules, nine #check occurrences, and one newly selected existing "
            "declaration."
        ),
        "record_kind": "supported_api_freeze_review",
        "reviewed_at_utc": None,
        "reviewer": None,
        "requested_reviewer_role": "primary-human",
        "schema_version": SCHEMA_VERSION,
    }


def validate_review_schema(
    review: Mapping[str, Any], baseline: Mapping[str, Any]
) -> list[str]:
    failures: list[str] = []
    expected_fields = {
        "activation_policy",
        "activation_scope",
        "approved_additive_declarations",
        "approved_additive_test_evidence",
        "approved_owner_moves",
        "baseline_checkpoint_id",
        "baseline_inputs",
        "baseline_manifest_sha256",
        "checkpoint_id",
        "decision",
        "machine_generated_by",
        "primary_human_review_required",
        "rationale",
        "record_kind",
        "reviewed_at_utc",
        "reviewer",
        "requested_reviewer_role",
        "schema_version",
    }
    if set(review) != expected_fields:
        failures.append("review: unexpected or missing top-level fields")
    expected_scalars = {
        "activation_policy": "atomic_when_any_approved_test_module_is_reachable",
        "baseline_checkpoint_id": "C0007",
        "baseline_manifest_sha256": canonical_json_sha256(baseline),
        "checkpoint_id": "C0008",
        "machine_generated_by": "tools/architecture/check_supported_api.py",
        "primary_human_review_required": True,
        "record_kind": "supported_api_freeze_review",
        "requested_reviewer_role": "primary-human",
        "schema_version": SCHEMA_VERSION,
    }
    for field, expected in expected_scalars.items():
        if review.get(field) != expected:
            failures.append(
                f"review.{field}: expected {expected!r}, got {review.get(field)!r}"
            )
    expected_baseline_inputs = {
        "baseline_manifest_sha256": canonical_json_sha256(baseline),
        "checker_sha256": baseline.get("derivation", {}).get("checker_sha256"),
        "checkpoint_code_sha": baseline.get("baseline", {}).get("checkpoint_code_sha"),
        "environment_extractor_sha256": baseline.get("derivation", {}).get(
            "environment_extractor_sha256"
        ),
        "production_source_tree_sha256": baseline.get("baseline", {}).get(
            "production_source_tree_sha256"
        ),
        "test_source_tree_sha256": baseline.get("baseline", {}).get(
            "test_source_tree_sha256"
        ),
        "tier_manifest_sha256": baseline.get("derivation", {}).get(
            "tier_manifest_sha256"
        ),
        "toolchain_inputs": baseline.get("derivation", {}).get("toolchain_inputs"),
    }
    if review.get("baseline_inputs") != expected_baseline_inputs:
        failures.append("review.baseline_inputs: does not exact-bind C0007 inputs")
    if not isinstance(review.get("rationale"), str) or not review.get("rationale"):
        failures.append("review.rationale: expected nonempty string")
    decision = review.get("decision")
    if decision is not None:
        failures.append("review.decision: machine fact record must remain null/pending")
    if review.get("reviewer") is not None or review.get("reviewed_at_utc") is not None:
        failures.append("review: machine fact record must not claim a reviewer or review time")

    approved_evidence = review.get("approved_additive_test_evidence")
    if approved_evidence != approved_i01_evidence_json():
        failures.append("review.approved_additive_test_evidence: not the exact R0014/I01 delta")
    approved_declarations = review.get("approved_additive_declarations")
    if not isinstance(approved_declarations, list):
        failures.append("review.approved_additive_declarations: expected array")
        approved_declarations = []
    indexed = index_rows(approved_declarations, "fqn")
    if set(indexed) != APPROVED_I01_NEW_FQNS or len(indexed) != len(approved_declarations):
        failures.append(
            "review.approved_additive_declarations: expected exactly problem2_9Source"
        )
    approved_owner_moves = review.get("approved_owner_moves")
    if not isinstance(approved_owner_moves, list):
        failures.append("review.approved_owner_moves: expected array")
        approved_owner_moves = []
    owner_move_index = index_rows(approved_owner_moves, "fqn")
    if set(owner_move_index) != set(APPROVED_I01_OWNER_DESTINATIONS) or len(
        owner_move_index
    ) != len(approved_owner_moves):
        failures.append("review.approved_owner_moves: expected exact two-row R0014 map")
    if approved_owner_moves != sorted(
        approved_owner_moves,
        key=lambda row: str(row.get("fqn", "")) if isinstance(row, dict) else "",
    ):
        failures.append("review.approved_owner_moves: rows must be sorted by FQN")
    baseline_rows = index_rows(baseline.get("declarations"), "fqn")
    reviewed_new_rows = index_rows(approved_declarations, "fqn")
    approved_evidence_fqns = {
        row["declaration"]
        for row in approved_i01_evidence_json()
    }
    missing_existing = sorted(
        (approved_evidence_fqns - APPROVED_I01_NEW_FQNS) - set(baseline_rows)
    )
    if missing_existing:
        failures.append(
            "review additive evidence expects declarations absent from C0007 baseline: "
            + ", ".join(missing_existing)
        )
    for fqn, destination in APPROVED_I01_OWNER_DESTINATIONS.items():
        row = owner_move_index.get(fqn, {})
        source_row = baseline_rows.get(fqn) or reviewed_new_rows.get(fqn) or {}
        if row != {
            "fqn": fqn,
            "from_owner_module": source_row.get("owner_module"),
            "to_owner_module": destination,
        }:
            failures.append(f"review.approved_owner_moves: invalid exact mapping for {fqn}")
    activation_scope = review.get("activation_scope")
    expected_scope = {
        "approved_additive_declarations_sha256": canonical_json_sha256(
            approved_declarations
        ),
        "approved_additive_test_evidence_sha256": canonical_json_sha256(
            approved_evidence if isinstance(approved_evidence, list) else []
        ),
        "approved_assertion_occurrence_count": 9,
        "approved_new_selected_declaration_count": 1,
        "approved_one_import_module_count": 5,
        "approved_owner_move_count": 2,
        "approved_owner_moves_sha256": canonical_json_sha256(approved_owner_moves),
        "approved_tier_manifest_sha256": R0014_TIER_MANIFEST_SHA256,
        "implementation_path_count": 14,
        "implementation_path_set_sha256": implementation_path_set_sha256(),
        "implementation_postimage_ledgers": pinned_artifact_rows(
            IMPLEMENTATION_POSTIMAGE_LEDGERS
        ),
        "implementation_id": "I01",
        "request_id": "R0014",
        "request_artifacts": pinned_artifact_rows(R0014_ARTIFACT_SHA256),
    }
    if not isinstance(activation_scope, dict):
        failures.append("review.activation_scope: expected object")
        activation_scope = {}
    expected_activation_scope_fields = set(expected_scope) | {
        "implementation_commit_sha",
        "planned_control_commit_sha",
    }
    if set(activation_scope) != expected_activation_scope_fields:
        failures.append("review.activation_scope: unexpected or missing fields")
    for field, expected in expected_scope.items():
        if activation_scope.get(field) != expected:
            failures.append(
                f"review.activation_scope.{field}: expected {expected!r}, "
                f"got {activation_scope.get(field)!r}"
            )
    for field in ("implementation_commit_sha", "planned_control_commit_sha"):
        value = activation_scope.get(field)
        if value is not None:
            failures.append(f"review.activation_scope.{field}: pending review requires null")
    baseline_entrypoints = set(
        baseline.get("derivation", {}).get("documented_entrypoints", [])
    )
    for index, row in enumerate(approved_declarations):
        label = f"review.approved_additive_declarations[{index}]"
        if not isinstance(row, dict):
            failures.append(f"{label}: expected object")
            continue
        if set(row) != {
            "canonical_surfaces",
            "expected_entrypoint_reachability",
            "fqn",
            "historical_surfaces",
            "kind",
            "namespace",
            "owner_module",
            "protected",
            "test_evidence",
            "test_modules",
            "type_evidence",
            "visibility",
        }:
            failures.append(f"{label}: unexpected or missing fields")
        fqn = row.get("fqn")
        if not isinstance(fqn, str):
            failures.append(f"{label}.fqn: expected string")
            continue
        if row.get("namespace") != namespace_of_rendered_lean_name(fqn):
            failures.append(f"{label}.namespace: inconsistent with FQN")
        if row.get("visibility") != "public":
            failures.append(f"{label}.visibility: expected public")
        if not isinstance(row.get("protected"), bool):
            failures.append(f"{label}.protected: expected boolean")
        evidence = validate_test_evidence(row, label, failures)
        expected_evidence = [
            {
                key: value
                for key, value in approved.items()
                if key != "declaration"
            }
            for approved in approved_i01_evidence_json()
            if approved["declaration"] == fqn
        ]
        if evidence != expected_evidence:
            failures.append(f"{label}.test_evidence: not exact approved rows")
        for field in ("kind", "owner_module"):
            if not isinstance(row.get(field), str) or not row.get(field):
                failures.append(f"{label}.{field}: expected nonempty string")
        reachability = require_sorted_unique_strings(
            row.get("expected_entrypoint_reachability"),
            f"{label}.expected_entrypoint_reachability",
            failures,
        )
        if set(reachability) - baseline_entrypoints:
            failures.append(f"{label}.expected_entrypoint_reachability: unknown entrypoint")
        type_evidence = row.get("type_evidence")
        if not isinstance(type_evidence, dict) or set(type_evidence) != {
            "normalization",
            "sha256",
        } or type_evidence.get(
            "normalization"
        ) != TYPE_NORMALIZATION or not isinstance(type_evidence.get("sha256"), str) or not re.fullmatch(
            r"[0-9A-F]{64}", str(type_evidence.get("sha256", ""))
        ):
            failures.append(f"{label}.type_evidence: invalid exact elaborated type evidence")
    return failures


def validate_activation_attestation(
    contract: Mapping[str, Any],
    *,
    baseline_path: Path,
    review_path: Path,
    mode: str,
) -> list[str]:
    failures: list[str] = []
    reviews = contract.get("reviews")
    if not isinstance(reviews, dict):
        return ["activation contract reviews: expected object"]
    activation = reviews.get("activation")
    if not isinstance(activation, dict):
        return ["activation contract reviews.activation: expected object"]
    expected_keys = {
        "action_performer_id",
        "attestation_kind",
        "ci_is_semantic_review",
        "decision",
        "generator_id",
        "reviewed_at",
        "reviewed_commit_sha",
        "reviewed_contract_blob_oid",
        "reviewed_tree_sha",
        "reviewer_id",
        "reviewer_kind",
        "scope",
        "source",
        "status",
        "supersedes_pending_reviews",
    }
    if set(activation) != expected_keys:
        failures.append("activation contract reviews.activation: unexpected or missing keys")
    exact_values = {
        "action_performer_id": "codex-local",
        "attestation_kind": "github_repository_owner_issue_comment_v1",
        "ci_is_semantic_review": False,
        "generator_id": "codex-local",
        "reviewer_id": "primary-human",
        "reviewer_kind": "human",
    }
    for field, expected in exact_values.items():
        if activation.get(field) != expected:
            failures.append(
                f"activation contract {field}: expected {expected!r}, "
                f"got {activation.get(field)!r}"
            )
    if activation.get("generator_id") == activation.get("reviewer_id"):
        failures.append("activation contract generator cannot equal primary-human reviewer")

    status = activation.get("status")
    pending = status == "pending"
    approved = status == "approved"
    if mode == "staging":
        if not (pending or approved):
            failures.append(
                "staging activation contract status must be exact pending or approved"
            )
    elif mode == "completion":
        if not approved:
            failures.append(
                "completion activation contract requires exact primary-human approval"
            )
    else:
        failures.append(f"unsupported activation validation mode: {mode!r}")

    reviewed_fields = (
        "decision",
        "reviewed_at",
        "reviewed_commit_sha",
        "reviewed_contract_blob_oid",
        "reviewed_tree_sha",
    )

    supersedes = activation.get("supersedes_pending_reviews")
    if supersedes != list(EXACT_ACTIVATION_SUPERSEDES):
        failures.append(
            "activation contract must use the exact ordered four-review supersession set"
        )

    scope = activation.get("scope")
    expected_scope_keys = {
        "artifact_inventory_sha256",
        "authorization_sha256",
        "completion_checker_sha256",
        "full_tests_correction_sha256",
        "implementation_path_set_sha256",
        "packet_snapshot_sha256",
        "planned_path_set_sha256",
        "review_purpose",
        "supported_api_baseline_sha256",
        "supported_api_checker_sha256",
        "supported_api_review_sha256",
        "workflow_sha256",
    }
    if not isinstance(scope, dict):
        failures.append("activation contract scope: expected object")
        scope = {}
    elif set(scope) != expected_scope_keys:
        failures.append("activation contract scope: unexpected or missing keys")
    if scope.get("review_purpose") != "P activation for atomic R0014/R0015 implementation":
        failures.append("activation contract scope.review_purpose: wrong purpose")
    for field in expected_scope_keys - {"review_purpose"}:
        value = scope.get(field)
        if not isinstance(value, str) or not re.fullmatch(r"[0-9A-F]{64}", value):
            failures.append(f"activation contract scope.{field}: expected uppercase SHA-256")
    artifacts = contract.get("artifacts")
    artifact_sha_by_path: dict[str, str] = {}
    if not isinstance(artifacts, list) or not all(
        isinstance(row, dict)
        and isinstance(row.get("path"), str)
        and isinstance(row.get("sha256"), str)
        for row in artifacts
    ):
        failures.append("activation contract artifacts: expected artifact inventory")
        artifacts = []
    else:
        artifact_paths = [str(row["path"]) for row in artifacts]
        if len(artifact_paths) != len(set(artifact_paths)):
            failures.append("activation contract artifacts: duplicate paths")
        artifact_sha_by_path = {
            str(row["path"]): str(row["sha256"]) for row in artifacts
        }

    packets = contract.get("packets")
    if not isinstance(packets, list):
        failures.append("activation contract packets: expected array")
        packets = []
    authority = contract.get("authority")
    if not isinstance(authority, dict):
        failures.append("activation contract authority: expected object")
        authority = {}
    path_census = contract.get("path_census")
    if not isinstance(path_census, dict):
        failures.append("activation contract path_census: expected object")
        path_census = {}
    implementation_census = path_census.get("implementation")
    if not isinstance(implementation_census, dict):
        failures.append("activation contract path_census.implementation: expected object")
        implementation_census = {}
    planned_census = path_census.get("planned_control")
    if not isinstance(planned_census, dict):
        failures.append("activation contract path_census.planned_control: expected object")
        planned_census = {}
    workflow = contract.get("workflow")
    if not isinstance(workflow, dict):
        failures.append("activation contract workflow: expected object")
        workflow = {}
    if workflow.get("github_issues_read_permission") is not True:
        failures.append("activation contract workflow must grant exact GitHub issues read access")

    workflow_path = ROOT / WORKFLOW_RELATIVE
    current_workflow_sha256 = sha256_bytes(workflow_path.read_bytes())
    if current_workflow_sha256 != PLANNED_CONTROL_WORKFLOW_SHA256:
        failures.append(
            "current planned-control workflow drift: expected exact "
            f"{PLANNED_CONTROL_WORKFLOW_SHA256}, got {current_workflow_sha256}"
        )
    current_file_hashes = {
        COMPLETION_CHECKER_RELATIVE: sha256_bytes(
            (ROOT / COMPLETION_CHECKER_RELATIVE).read_bytes()
        ),
        SUPPORTED_API_CHECKER_RELATIVE: sha256_bytes(Path(__file__).read_bytes()),
        SUPPORTED_API_BASELINE_RELATIVE: sha256_bytes(baseline_path.read_bytes()),
        SUPPORTED_API_REVIEW_RELATIVE: sha256_bytes(review_path.read_bytes()),
        FULL_TESTS_CORRECTION_RELATIVE: sha256_bytes(
            (ROOT / FULL_TESTS_CORRECTION_RELATIVE).read_bytes()
        ),
        BOUNDED_AUTHORIZATION_RELATIVE: sha256_bytes(
            (ROOT / BOUNDED_AUTHORIZATION_RELATIVE).read_bytes()
        ),
        WORKFLOW_RELATIVE: current_workflow_sha256,
    }
    for relative, expected in current_file_hashes.items():
        if artifact_sha_by_path.get(relative) != expected:
            failures.append(
                f"activation contract artifact {relative}: expected current {expected}, "
                f"got {artifact_sha_by_path.get(relative)!r}"
            )
    exact_scope_hashes = {
        "artifact_inventory_sha256": canonical_json_sha256(artifacts),
        "authorization_sha256": authority.get("authorization_sha256"),
        "completion_checker_sha256": current_file_hashes[
            COMPLETION_CHECKER_RELATIVE
        ],
        "full_tests_correction_sha256": current_file_hashes[
            FULL_TESTS_CORRECTION_RELATIVE
        ],
        "implementation_path_set_sha256": implementation_path_set_sha256(),
        "packet_snapshot_sha256": canonical_json_sha256(packets),
        "planned_path_set_sha256": PLANNED_PATH_SET_SHA256,
        "supported_api_baseline_sha256": current_file_hashes[
            SUPPORTED_API_BASELINE_RELATIVE
        ],
        "supported_api_checker_sha256": current_file_hashes[
            SUPPORTED_API_CHECKER_RELATIVE
        ],
        "supported_api_review_sha256": current_file_hashes[
            SUPPORTED_API_REVIEW_RELATIVE
        ],
        "workflow_sha256": PLANNED_CONTROL_WORKFLOW_SHA256,
    }
    if authority.get("authorization_sha256") != current_file_hashes[
        BOUNDED_AUTHORIZATION_RELATIVE
    ]:
        failures.append(
            "activation contract authority.authorization_sha256 must match current authorization"
        )
    if implementation_census.get("path_set_sha256") != implementation_path_set_sha256():
        failures.append(
            "activation contract implementation census path set must match exact 14-path set"
        )
    if planned_census.get("path_set_sha256") != PLANNED_PATH_SET_SHA256:
        failures.append("activation contract planned-control path set drift")
    if workflow.get("sha256") != PLANNED_CONTROL_WORKFLOW_SHA256:
        failures.append("activation contract workflow.sha256 drift")
    for field, expected in exact_scope_hashes.items():
        if scope.get(field) != expected:
            failures.append(
                f"activation contract scope.{field}: expected exact {expected}, "
                f"got {scope.get(field)!r}"
            )

    source = activation.get("source")
    source_keys = {
        "author_association",
        "author_database_id",
        "author_login",
        "author_node_id",
        "author_type",
        "comment_api_url",
        "comment_database_id",
        "comment_html_url",
        "comment_node_id",
        "created_at",
        "issue_api_url",
        "issue_database_id",
        "issue_html_url",
        "issue_node_id",
        "issue_number",
        "message",
        "message_sha256",
        "performed_via_github_app",
        "provider",
        "repository_api_url",
        "repository_database_id",
        "repository_full_name",
        "repository_node_id",
        "updated_at",
    }
    if not isinstance(source, dict):
        failures.append("activation contract source: expected object")
        source = {}
    elif set(source) != source_keys:
        failures.append("activation contract source: unexpected or missing keys")
    for field, expected in GITHUB_REVIEW_SOURCE_IDENTITY.items():
        if source.get(field) != expected:
            failures.append(
                f"activation contract source.{field}: expected {expected!r}, "
                f"got {source.get(field)!r}"
            )

    event_fields = (
        "comment_api_url",
        "comment_database_id",
        "comment_html_url",
        "comment_node_id",
        "created_at",
        "issue_api_url",
        "issue_database_id",
        "issue_html_url",
        "issue_node_id",
        "issue_number",
        "message",
        "message_sha256",
        "updated_at",
    )
    if pending:
        for field in reviewed_fields:
            if activation.get(field) is not None:
                failures.append(f"pending activation contract {field} must be null")
        for field in event_fields:
            if source.get(field) is not None:
                failures.append(f"pending activation contract source.{field} must be null")
    elif approved:
        if activation.get("decision") != "approved":
            failures.append("approved activation contract decision must be 'approved'")
        lifecycle = contract.get("lifecycle")
        if not isinstance(lifecycle, dict):
            failures.append("approved activation contract requires lifecycle object")
            lifecycle = {}
        lifecycle_bindings = {
            "reviewed_commit_sha": "planned_commit_sha",
            "reviewed_tree_sha": "planned_tree_sha",
            "reviewed_contract_blob_oid": "planned_contract_blob_oid",
        }
        for reviewed_field, lifecycle_field in lifecycle_bindings.items():
            if activation.get(reviewed_field) != lifecycle.get(lifecycle_field):
                failures.append(
                    f"activation contract {reviewed_field} must exact-bind "
                    f"lifecycle.{lifecycle_field}"
                )
        for field in (
            "reviewed_commit_sha",
            "reviewed_contract_blob_oid",
            "reviewed_tree_sha",
        ):
            value = activation.get(field)
            if not isinstance(value, str) or not re.fullmatch(r"[0-9a-f]{40}", value):
                failures.append(
                    f"activation contract {field}: expected lowercase Git object id"
                )
        rfc3339 = re.compile(
            r"\d{4}-\d{2}-\d{2}T\d{2}:\d{2}:\d{2}(?:\.\d+)?Z"
        )
        reviewed_at = activation.get("reviewed_at")
        created_at = source.get("created_at")
        updated_at = source.get("updated_at")
        for field, value in (
            ("reviewed_at", reviewed_at),
            ("source.created_at", created_at),
            ("source.updated_at", updated_at),
        ):
            if not isinstance(value, str) or not rfc3339.fullmatch(value):
                failures.append(
                    f"activation contract {field}: expected UTC RFC3339 timestamp"
                )
        if not (reviewed_at == created_at == updated_at):
            failures.append(
                "activation contract approved review/comment timestamps must be exact and unedited"
            )

        issue_number = source.get("issue_number")
        issue_database_id = source.get("issue_database_id")
        comment_database_id = source.get("comment_database_id")
        for field, value in (
            ("issue_number", issue_number),
            ("issue_database_id", issue_database_id),
            ("comment_database_id", comment_database_id),
        ):
            if type(value) is not int or value <= 0:
                failures.append(
                    f"activation contract source.{field}: expected positive integer"
                )
        for field in ("issue_node_id", "comment_node_id"):
            value = source.get(field)
            if not isinstance(value, str) or not value:
                failures.append(
                    f"activation contract source.{field}: expected nonempty string"
                )
        repository_api_url = GITHUB_REVIEW_SOURCE_IDENTITY["repository_api_url"]
        repository_full_name = GITHUB_REVIEW_SOURCE_IDENTITY["repository_full_name"]
        if type(issue_number) is int and issue_number > 0:
            expected_issue_api_url = f"{repository_api_url}/issues/{issue_number}"
            expected_issue_html_url = (
                f"https://github.com/{repository_full_name}/issues/{issue_number}"
            )
            if source.get("issue_api_url") != expected_issue_api_url:
                failures.append("activation contract source.issue_api_url: relation mismatch")
            if source.get("issue_html_url") != expected_issue_html_url:
                failures.append("activation contract source.issue_html_url: relation mismatch")
            if type(comment_database_id) is int and comment_database_id > 0:
                expected_comment_api_url = (
                    f"{repository_api_url}/issues/comments/{comment_database_id}"
                )
                expected_comment_html_url = (
                    f"{expected_issue_html_url}#issuecomment-{comment_database_id}"
                )
                if source.get("comment_api_url") != expected_comment_api_url:
                    failures.append(
                        "activation contract source.comment_api_url: relation mismatch"
                    )
                if source.get("comment_html_url") != expected_comment_html_url:
                    failures.append(
                        "activation contract source.comment_html_url: relation mismatch"
                    )

        scope_sha256 = canonical_json_sha256(scope)
        expected_message = (
            "I, primary-human, independently reviewed and approve "
            f"{scope.get('review_purpose')} at commit "
            f"{activation.get('reviewed_commit_sha')}, tree "
            f"{activation.get('reviewed_tree_sha')}, contract blob "
            f"{activation.get('reviewed_contract_blob_oid')}, and scope SHA-256 "
            f"{scope_sha256}. I confirm that CI is evidence, not semantic review, "
            "and authorize only the exact bounded next transition."
        )
        if source.get("message") != expected_message:
            failures.append("activation contract source.message: exact attestation mismatch")
        if source.get("message_sha256") != sha256_bytes(
            expected_message.encode("utf-8")
        ):
            failures.append("activation contract source.message_sha256: content mismatch")
    return failures


def activation_authorization_state(
    contract: Mapping[str, Any] | None,
    *,
    baseline_path: Path,
    review_path: Path,
    mode: str,
    contract_path: Path,
) -> tuple[list[str], bool]:
    """Validate the lifecycle activation record and return exact approval state."""
    if contract is None:
        return ([f"missing lifecycle activation contract: {contract_path}"], False)
    failures = validate_activation_attestation(
        contract,
        baseline_path=baseline_path,
        review_path=review_path,
        mode=mode,
    )
    reviews = contract.get("reviews")
    activation = reviews.get("activation") if isinstance(reviews, dict) else None
    approved = (
        not failures
        and isinstance(activation, dict)
        and activation.get("status") == "approved"
        and activation.get("decision") == "approved"
    )
    return failures, approved


def merged_expected_declarations(
    baseline: Mapping[str, Any], review: Mapping[str, Any], *, active: bool
) -> list[dict[str, Any]]:
    rows = json.loads(json.dumps(baseline["declarations"]))
    if not active:
        return rows
    indexed = {row["fqn"]: row for row in rows}
    for new_row in review["approved_additive_declarations"]:
        indexed[new_row["fqn"]] = json.loads(json.dumps(new_row))
    for approved in review["approved_additive_test_evidence"]:
        fqn = approved["declaration"]
        if fqn in APPROVED_I01_NEW_FQNS:
            continue
        row = indexed[fqn]
        evidence = {
            key: value for key, value in approved.items() if key != "declaration"
        }
        row["test_evidence"].append(evidence)
        row["test_evidence"].sort(key=evidence_key)
        row["test_modules"] = sorted(
            {item["test_module"] for item in row["test_evidence"]}
        )
        row["canonical_surfaces"] = sorted(
            {
                item["surface"]
                for item in row["test_evidence"]
                if item["surface_kind"] == "canonical"
            }
        )
        row["historical_surfaces"] = sorted(
            {
                item["surface"]
                for item in row["test_evidence"]
                if item["surface_kind"] == "historical"
            }
        )
    for owner_move in review["approved_owner_moves"]:
        indexed[owner_move["fqn"]]["owner_module"] = owner_move["to_owner_module"]
    return [indexed[fqn] for fqn in sorted(indexed)]


def compare_contracts(
    baseline: Mapping[str, Any],
    current: Mapping[str, Any],
    review: Mapping[str, Any],
    *,
    mode: str = "staging",
    activation_approved: bool = False,
) -> list[str]:
    """Compare two valid-ish contract snapshots; owner moves are informational."""

    failures: list[str] = []
    approved_modules = {
        row["test_module"] for row in review["approved_additive_test_evidence"]
    }
    present_activation_modules = set(current.get("review_activation_modules", []))
    active = bool(present_activation_modules)
    if mode == "staging" and active:
        failures.append("staging mode requires zero reachable I01 supported-API modules")
    if mode == "completion" and not active:
        failures.append("completion mode requires the atomic I01 supported-API delta")
    if mode not in {"staging", "completion"}:
        failures.append(f"unsupported effective comparison mode: {mode!r}")
    if active and not activation_approved:
        failures.append(
            "reviewed additive delta is active but lacks exact independent primary-human approval"
        )
    if active and present_activation_modules != approved_modules:
        failures.append(
            "reviewed additive delta is only partially activated: expected modules "
            f"{sorted(approved_modules)!r}, got {sorted(present_activation_modules)!r}"
        )
    expected_declarations = merged_expected_declarations(
        baseline, review, active=active
    )
    base_rows = index_rows(expected_declarations, "fqn")
    current_rows = index_rows(current.get("declarations"), "fqn")
    missing = sorted(set(base_rows) - set(current_rows))
    added = sorted(set(current_rows) - set(base_rows))
    for fqn in missing:
        failures.append(f"{fqn}: supported declaration removed or renamed")
    for fqn in added:
        failures.append(f"{fqn}: unreviewed newly selected declaration")

    for fqn in sorted(set(base_rows) & set(current_rows)):
        expected = base_rows[fqn]
        actual = current_rows[fqn]
        for field, description in (
            ("kind", "declaration kind"),
            ("namespace", "namespace"),
            ("owner_module", "owner module"),
            ("protected", "protected status"),
            ("visibility", "visibility"),
            ("canonical_surfaces", "canonical surface"),
            ("historical_surfaces", "historical surface"),
            ("test_modules", "isolated test ownership"),
            ("test_evidence", "exact test assertion evidence"),
            ("expected_entrypoint_reachability", "entrypoint reachability"),
            ("type_evidence", "exact elaborated type"),
        ):
            if actual.get(field) != expected.get(field):
                failures.append(
                    f"{fqn}: {description} drift: expected {expected.get(field)!r}, "
                    f"got {actual.get(field)!r}"
                )

    expected_derivation = reconstructed_derivation(expected_declarations)
    current_derivation = current.get("derivation", {})
    expected_tier_sha = (
        review["activation_scope"]["approved_tier_manifest_sha256"]
        if active
        else baseline["derivation"]["tier_manifest_sha256"]
    )
    if current_derivation.get("tier_manifest_sha256") != expected_tier_sha:
        failures.append(
            "tier manifest drift: expected exact "
            f"{expected_tier_sha}, got {current_derivation.get('tier_manifest_sha256')!r}"
        )
    expected_entrypoints = baseline.get("derivation", {}).get(
        "documented_entrypoints"
    )
    if current_derivation.get("documented_entrypoints") != expected_entrypoints:
        failures.append(
            "documented entrypoint set drift: expected "
            f"{expected_entrypoints!r}, got "
            f"{current_derivation.get('documented_entrypoints')!r}"
        )
    for field, expected in expected_derivation.items():
        if current_derivation.get(field) != expected:
            failures.append(
                f"test derivation {field} drift: expected {expected!r}, "
                f"got {current_derivation.get(field)!r}"
            )
    expected_protected_count = sum(
        1 for row in expected_declarations if row.get("protected") is True
    )
    if current_derivation.get("protected_selected_declaration_count") != expected_protected_count:
        failures.append(
            "protected selected declaration count drift: expected "
            f"{expected_protected_count}, got "
            f"{current_derivation.get('protected_selected_declaration_count')!r}"
        )

    base_guard = index_rows(baseline.get("visibility_guard"), "entrypoint")
    current_guard = index_rows(current.get("visibility_guard"), "entrypoint")
    if set(base_guard) != set(current_guard):
        failures.append(
            "visibility guard entrypoints drifted: "
            f"expected {sorted(base_guard)!r}, got {sorted(current_guard)!r}"
        )
    for entrypoint in sorted(set(base_guard) & set(current_guard)):
        expected = base_guard[entrypoint]
        actual = current_guard[entrypoint]
        for field in (
            "public_authored_declaration_count",
            "public_authored_names_sha256",
        ):
            if actual.get(field) != expected.get(field):
                failures.append(
                    f"{entrypoint}: unreviewed public visibility drift in {field}: "
                    f"expected {expected.get(field)!r}, got {actual.get(field)!r}"
                )
    return failures


def current_contract_from_baseline(
    baseline: Mapping[str, Any], review: Mapping[str, Any]
) -> dict[str, Any]:
    schema_failures = validate_baseline_schema(baseline)
    if schema_failures:
        raise ContractError("invalid baseline:\n" + "\n".join(schema_failures))

    tiers = json.loads(TIER_MANIFEST.read_text(encoding="utf-8"))
    modules = scan_modules()
    selections, derivation = derive_test_selections(modules, tiers)
    current_entrypoints = documented_entrypoints(tiers)
    derivation["documented_entrypoints"] = list(current_entrypoints)
    derivation["tier_manifest_sha256"] = sha256_bytes(TIER_MANIFEST.read_bytes())
    reachable_tests = all_import_closure(modules, (TEST_ROOT,))
    approved_modules = {
        row["test_module"] for row in review["approved_additive_test_evidence"]
    }
    baseline_rows = index_rows(baseline["declarations"], "fqn")
    selected_names = sorted(set(baseline_rows) | set(selections))
    env = run_environment_extractor(selected_names, current_entrypoints)
    closures = entrypoint_closures(modules, current_entrypoints)
    surface_closures = evidence_surface_closures(modules, selections)

    rows: list[dict[str, Any]] = []
    for fqn, selection in sorted(selections.items()):
        declaration = env.selected[fqn]
        require_owner_reachable_from_evidence_surfaces(
            fqn, declaration.owner_module, selection, modules, surface_closures
        )
        rows.append(
            {
                "canonical_surfaces": list(selection.canonical_surfaces),
                "expected_entrypoint_reachability": reachable_entrypoints_for_owner(
                    declaration.owner_module, closures
                ),
                "fqn": fqn,
                "historical_surfaces": list(selection.historical_surfaces),
                "kind": declaration.kind,
                "namespace": namespace_of_rendered_lean_name(fqn),
                "owner_module": declaration.owner_module,
                "protected": declaration.protected,
                "test_evidence": test_evidence_json(selection.test_evidence),
                "test_modules": list(selection.test_modules),
                "type_evidence": {
                    "normalization": TYPE_NORMALIZATION,
                    "sha256": declaration.normalized_type_sha256,
                },
                "visibility": declaration.visibility,
            }
        )
    return {
        "declarations": rows,
        "derivation": {
            **derivation,
            "protected_selected_declaration_count": sum(
                1 for row in rows if row["protected"]
            ),
        },
        "review_activation_modules": sorted(approved_modules & reachable_tests),
        "visibility_guard": visibility_guard(closures, env.public_names_by_owner),
    }


def synthetic_contract() -> dict[str, Any]:
    names = [
        "NumStability.FloatingPointFormat.problem2_9Source",
        "NumStability.demo",
    ]
    declarations = [
            {
                "canonical_surfaces": ["NumStability.Core"],
                "expected_entrypoint_reachability": ["NumStability", "NumStability.Core"],
                "fqn": "NumStability.demo",
                "historical_surfaces": ["NumStability.Legacy"],
                "kind": "definition",
                "namespace": "NumStability",
                "owner_module": "NumStability.Demo",
                "protected": False,
                "test_evidence": [
                    {
                        "assertion_occurrences": 1,
                        "surface": "NumStability.Core",
                        "surface_kind": "canonical",
                        "test_module": "NumStabilityTest.Import.Demo",
                    },
                    {
                        "assertion_occurrences": 1,
                        "surface": "NumStability.Legacy",
                        "surface_kind": "historical",
                        "test_module": "NumStabilityTest.OldOnly.Demo",
                    },
                ],
                "test_modules": [
                    "NumStabilityTest.Import.Demo",
                    "NumStabilityTest.OldOnly.Demo",
                ],
                "type_evidence": {
                    "normalization": TYPE_NORMALIZATION,
                    "sha256": "A" * 64,
                },
                "visibility": "public",
            }
        ]
    derivation = reconstructed_derivation(declarations)
    derivation.update(
        {
            "documented_entrypoints": [],
            "protected_selected_declaration_count": 0,
            "tier_manifest_sha256": "synthetic-tier",
        }
    )
    return {
        "declarations": declarations,
        "derivation": derivation,
        "review_activation_modules": [],
        "visibility_guard": [
            {
                "entrypoint": "NumStability",
                "public_authored_declaration_count": 2,
                "public_authored_names_sha256": canonical_json_sha256(names),
            },
            {
                "entrypoint": "NumStability.Core",
                "public_authored_declaration_count": 2,
                "public_authored_names_sha256": canonical_json_sha256(names),
            },
        ],
    }


def synthetic_review() -> dict[str, Any]:
    return {
        "activation_scope": {
            "approved_tier_manifest_sha256": "synthetic-tier"
        },
        "approved_additive_declarations": [
            {
                "canonical_surfaces": ["NumStability.All"],
                "expected_entrypoint_reachability": ["NumStability"],
                "fqn": "NumStability.FloatingPointFormat.problem2_9Source",
                "historical_surfaces": [],
                "kind": "definition",
                "namespace": "NumStability.FloatingPointFormat",
                "owner_module": "NumStability.PreexistingInputs",
                "protected": False,
                "test_evidence": [
                    {
                        "assertion_occurrences": 1,
                        "surface": "NumStability.All",
                        "surface_kind": "canonical",
                        "test_module": "NumStabilityTest.Reorganization.I01.New",
                    }
                ],
                "test_modules": ["NumStabilityTest.Reorganization.I01.New"],
                "type_evidence": {
                    "normalization": TYPE_NORMALIZATION,
                    "sha256": "B" * 64,
                },
                "visibility": "public",
            }
        ],
        "approved_additive_test_evidence": [
            {
                "assertion_occurrences": 1,
                "declaration": "NumStability.demo",
                "surface": "NumStability.All",
                "surface_kind": "canonical",
                "test_module": "NumStabilityTest.Reorganization.I01.First",
            },
            {
                "assertion_occurrences": 1,
                "declaration": "NumStability.demo",
                "surface": "NumStability.Analysis",
                "surface_kind": "canonical",
                "test_module": "NumStabilityTest.Reorganization.I01.Second",
            },
            {
                "assertion_occurrences": 1,
                "declaration": "NumStability.FloatingPointFormat.problem2_9Source",
                "surface": "NumStability.All",
                "surface_kind": "canonical",
                "test_module": "NumStabilityTest.Reorganization.I01.New",
            },
        ],
        "approved_owner_moves": [
            {
                "fqn": "NumStability.demo",
                "from_owner_module": "NumStability.Demo",
                "to_owner_module": "NumStability.Canonical.Demo",
            },
            {
                "fqn": "NumStability.FloatingPointFormat.problem2_9Source",
                "from_owner_module": "NumStability.PreexistingInputs",
                "to_owner_module": "NumStability.Canonical.Inputs",
            }
        ],
        "decision": "APPROVE",
    }


def self_test() -> None:
    baseline = synthetic_contract()
    review = synthetic_review()
    current = json.loads(json.dumps(baseline))
    assert not compare_contracts(baseline, current, review)

    # A schema-valid pending row is not evidence of its own C0007 provenance.
    # The staging gate compares it with independently extracted environment facts,
    # including the pre-move owner for every declaration in the exact move map.
    expected_review_declarations = json.loads(
        json.dumps(review["approved_additive_declarations"])
    )
    expected_review_owner_moves = json.loads(
        json.dumps(review["approved_owner_moves"])
    )
    assert not validate_review_environment_facts(
        review, expected_review_declarations, expected_review_owner_moves
    )
    tampered_new_type = json.loads(json.dumps(review))
    tampered_new_type["approved_additive_declarations"][0]["type_evidence"][
        "sha256"
    ] = "C" * 64
    assert validate_review_environment_facts(
        tampered_new_type,
        expected_review_declarations,
        expected_review_owner_moves,
    )
    tampered_new_owner = json.loads(json.dumps(review))
    tampered_new_owner["approved_additive_declarations"][0][
        "owner_module"
    ] = "NumStability.ForgedOwner"
    tampered_new_owner["approved_owner_moves"][1][
        "from_owner_module"
    ] = "NumStability.ForgedOwner"
    assert validate_review_environment_facts(
        tampered_new_owner,
        expected_review_declarations,
        expected_review_owner_moves,
    )

    # Every documented surface is loaded into the extractor environment, including
    # advertised entrypoints that are intentionally outside the NumStability root
    # closure.  This prevents an empty/missing owner from hashing as an empty guard.
    regression_entrypoints = documented_entrypoints(
        {"reusable_entrypoints": ["NumStability.Core"]}
    )
    assert "NumStability.Core" in regression_entrypoints
    assert "NumStability.Higham" in regression_entrypoints
    assert "NumStability.Analysis.Norms.Core" in regression_entrypoints
    assert "NumStability.FloatingPoint.Model" in regression_entrypoints
    assert "withImportModules imports" in LEAN_EXTRACTOR_SOURCE
    assert "importsPath" in LEAN_EXTRACTOR_SOURCE

    module_imports, module_exports = parse_import_edges(
        "module\nimport NumStability.Private\n"
        "public import NumStability.Public\n"
    )
    assert module_imports == (
        "NumStability.Private",
        "NumStability.Public",
    )
    assert module_exports == ("NumStability.Public",)
    assert parse_import_edges("import NumStability.LegacyChild\n") == (
        ("NumStability.LegacyChild",),
        ("NumStability.LegacyChild",),
    )
    assert parse_import_edges("module\nimport all NumStability.PrivateAll\n") == (
        ("NumStability.PrivateAll",),
        (),
    )
    closure_fixture = {
        "Root": Module(
            "Root", Path("Root.lean"), ("Private", "Public"), ("Public",)
        ),
        "Private": Module(
            "Private", Path("Private.lean"), ("PrivateLeaf",), ("PrivateLeaf",)
        ),
        "PrivateLeaf": Module(
            "PrivateLeaf", Path("PrivateLeaf.lean"), (), ()
        ),
        "Public": Module(
            "Public", Path("Public.lean"), ("PublicLeaf",), ("PublicLeaf",)
        ),
        "PublicLeaf": Module("PublicLeaf", Path("PublicLeaf.lean"), (), ()),
    }
    assert all_import_closure(closure_fixture, ("Root",)) == set(closure_fixture)
    assert exported_api_closure(closure_fixture, ("Root",)) == {
        "Root",
        "Public",
        "PublicLeaf",
    }

    # The type-evidence transport is injective: literal whitespace and percent-like
    # text survive round trips and therefore cannot collapse to the same hash.
    encoded_type_payload = "String %25 literal%09tab%0Dcr%0Alf λ"
    assert decode_type_payload(encoded_type_payload) == "String % literal\ttab\rcr\nlf λ"
    for invalid_payload in ("%", "%0", "%20", "bad%ZZ"):
        try:
            decode_type_payload(invalid_payload)
        except ContractError:
            pass
        else:
            raise AssertionError(
                f"invalid type-evidence escape was accepted: {invalid_payload!r}"
            )
    assert sha256_bytes('String "a b"'.encode("utf-8")) != sha256_bytes(
        'String "a  b"'.encode("utf-8")
    )

    # Lifecycle activation is state-aware but always fail-closed: P accepts the
    # exact pending record, A/T accepts an exact human approval while the code is
    # still at its preimage, and I requires that same exact approval.
    with tempfile.TemporaryDirectory(prefix="supported-api-lifecycle-test-") as temp_name:
        temp = Path(temp_name)
        baseline_path = temp / "baseline.json"
        review_path = temp / "review.json"
        contract_path = temp / "contract.json"
        baseline_path.write_bytes(b"baseline fixture\n")
        review_path.write_bytes(b"review fixture\n")
        artifact_hashes = {
            COMPLETION_CHECKER_RELATIVE: sha256_bytes(
                (ROOT / COMPLETION_CHECKER_RELATIVE).read_bytes()
            ),
            SUPPORTED_API_CHECKER_RELATIVE: sha256_bytes(Path(__file__).read_bytes()),
            SUPPORTED_API_BASELINE_RELATIVE: sha256_bytes(baseline_path.read_bytes()),
            SUPPORTED_API_REVIEW_RELATIVE: sha256_bytes(review_path.read_bytes()),
            FULL_TESTS_CORRECTION_RELATIVE: sha256_bytes(
                (ROOT / FULL_TESTS_CORRECTION_RELATIVE).read_bytes()
            ),
            BOUNDED_AUTHORIZATION_RELATIVE: sha256_bytes(
                (ROOT / BOUNDED_AUTHORIZATION_RELATIVE).read_bytes()
            ),
            WORKFLOW_RELATIVE: PLANNED_CONTROL_WORKFLOW_SHA256,
        }
        artifacts = [
            {"path": path, "sha256": digest}
            for path, digest in sorted(artifact_hashes.items())
        ]
        packets = [{"fixture": "exact packet snapshot"}]
        scope = {
            "artifact_inventory_sha256": canonical_json_sha256(artifacts),
            "authorization_sha256": artifact_hashes[BOUNDED_AUTHORIZATION_RELATIVE],
            "completion_checker_sha256": artifact_hashes[
                COMPLETION_CHECKER_RELATIVE
            ],
            "full_tests_correction_sha256": artifact_hashes[
                FULL_TESTS_CORRECTION_RELATIVE
            ],
            "implementation_path_set_sha256": implementation_path_set_sha256(),
            "packet_snapshot_sha256": canonical_json_sha256(packets),
            "planned_path_set_sha256": PLANNED_PATH_SET_SHA256,
            "review_purpose": "P activation for atomic R0014/R0015 implementation",
            "supported_api_baseline_sha256": artifact_hashes[
                SUPPORTED_API_BASELINE_RELATIVE
            ],
            "supported_api_checker_sha256": artifact_hashes[
                SUPPORTED_API_CHECKER_RELATIVE
            ],
            "supported_api_review_sha256": artifact_hashes[
                SUPPORTED_API_REVIEW_RELATIVE
            ],
            "workflow_sha256": PLANNED_CONTROL_WORKFLOW_SHA256,
        }
        pending_source = {
            **GITHUB_REVIEW_SOURCE_IDENTITY,
            "comment_api_url": None,
            "comment_database_id": None,
            "comment_html_url": None,
            "comment_node_id": None,
            "created_at": None,
            "issue_api_url": None,
            "issue_database_id": None,
            "issue_html_url": None,
            "issue_node_id": None,
            "issue_number": None,
            "message": None,
            "message_sha256": None,
            "updated_at": None,
        }
        pending_activation = {
            "action_performer_id": "codex-local",
            "attestation_kind": "github_repository_owner_issue_comment_v1",
            "ci_is_semantic_review": False,
            "decision": None,
            "generator_id": "codex-local",
            "reviewed_at": None,
            "reviewed_commit_sha": None,
            "reviewed_contract_blob_oid": None,
            "reviewed_tree_sha": None,
            "reviewer_id": "primary-human",
            "reviewer_kind": "human",
            "scope": scope,
            "source": pending_source,
            "status": "pending",
            "supersedes_pending_reviews": list(EXACT_ACTIVATION_SUPERSEDES),
        }
        pending_contract = {
            "artifacts": artifacts,
            "authority": {
                "authorization_sha256": artifact_hashes[
                    BOUNDED_AUTHORIZATION_RELATIVE
                ]
            },
            "lifecycle": {
                "planned_commit_sha": None,
                "planned_contract_blob_oid": None,
                "planned_tree_sha": None,
            },
            "packets": packets,
            "path_census": {
                "implementation": {
                    "path_set_sha256": implementation_path_set_sha256()
                },
                "planned_control": {"path_set_sha256": PLANNED_PATH_SET_SHA256},
            },
            "reviews": {"activation": pending_activation},
            "workflow": {
                "github_issues_read_permission": True,
                "sha256": PLANNED_CONTROL_WORKFLOW_SHA256,
            },
        }
        pending_failures, pending_approved = activation_authorization_state(
            pending_contract,
            baseline_path=baseline_path,
            review_path=review_path,
            mode="staging",
            contract_path=contract_path,
        )
        assert not pending_failures and not pending_approved
        completion_pending_failures, completion_pending_approved = (
            activation_authorization_state(
                pending_contract,
                baseline_path=baseline_path,
                review_path=review_path,
                mode="completion",
                contract_path=contract_path,
            )
        )
        assert completion_pending_failures and not completion_pending_approved

        approved_contract = json.loads(json.dumps(pending_contract))
        approved = approved_contract["reviews"]["activation"]
        approved_contract["lifecycle"].update(
            {
                "planned_commit_sha": "a" * 40,
                "planned_contract_blob_oid": "b" * 40,
                "planned_tree_sha": "c" * 40,
            }
        )
        approved.update(
            {
                "decision": "approved",
                "reviewed_at": "2026-08-25T12:00:01Z",
                "reviewed_commit_sha": "a" * 40,
                "reviewed_contract_blob_oid": "b" * 40,
                "reviewed_tree_sha": "c" * 40,
                "status": "approved",
            }
        )
        approved_message = (
            "I, primary-human, independently reviewed and approve "
            f"{scope['review_purpose']} at commit {'a' * 40}, tree {'c' * 40}, "
            f"contract blob {'b' * 40}, and scope SHA-256 "
            f"{canonical_json_sha256(scope)}. I confirm that CI is evidence, not "
            "semantic review, and authorize only the exact bounded next transition."
        )
        approved["source"].update(
            {
                "comment_api_url": (
                    f"{GITHUB_REVIEW_SOURCE_IDENTITY['repository_api_url']}"
                    "/issues/comments/2002"
                ),
                "comment_database_id": 2002,
                "comment_html_url": (
                    "https://github.com/"
                    f"{GITHUB_REVIEW_SOURCE_IDENTITY['repository_full_name']}"
                    "/issues/17#issuecomment-2002"
                ),
                "comment_node_id": "IC_fixture",
                "created_at": "2026-08-25T12:00:01Z",
                "issue_api_url": (
                    f"{GITHUB_REVIEW_SOURCE_IDENTITY['repository_api_url']}/issues/17"
                ),
                "issue_database_id": 1001,
                "issue_html_url": (
                    "https://github.com/"
                    f"{GITHUB_REVIEW_SOURCE_IDENTITY['repository_full_name']}/issues/17"
                ),
                "issue_node_id": "I_fixture",
                "issue_number": 17,
                "message": approved_message,
                "message_sha256": sha256_bytes(approved_message.encode("utf-8")),
                "updated_at": "2026-08-25T12:00:01Z",
            }
        )
        for lifecycle_mode in ("staging", "completion"):
            approved_failures, approved_state = activation_authorization_state(
                approved_contract,
                baseline_path=baseline_path,
                review_path=review_path,
                mode=lifecycle_mode,
                contract_path=contract_path,
            )
            assert not approved_failures and approved_state

        tampered_source_contract = json.loads(json.dumps(approved_contract))
        tampered_source_contract["reviews"]["activation"]["source"][
            "author_login"
        ] = "not-the-repository-owner"
        tampered_source_failures, tampered_source_approved = (
            activation_authorization_state(
                tampered_source_contract,
                baseline_path=baseline_path,
                review_path=review_path,
                mode="completion",
                contract_path=contract_path,
            )
        )
        assert tampered_source_failures and not tampered_source_approved
        edited_comment_contract = json.loads(json.dumps(approved_contract))
        edited_source = edited_comment_contract["reviews"]["activation"]["source"]
        edited_source["message"] += " edited"
        edited_source["message_sha256"] = sha256_bytes(
            edited_source["message"].encode("utf-8")
        )
        edited_comment_failures, edited_comment_approved = (
            activation_authorization_state(
                edited_comment_contract,
                baseline_path=baseline_path,
                review_path=review_path,
                mode="completion",
                contract_path=contract_path,
            )
        )
        assert edited_comment_failures and not edited_comment_approved
        wrong_lifecycle_contract = json.loads(json.dumps(approved_contract))
        wrong_lifecycle_contract["lifecycle"]["planned_tree_sha"] = "d" * 40
        wrong_lifecycle_failures, wrong_lifecycle_approved = (
            activation_authorization_state(
                wrong_lifecycle_contract,
                baseline_path=baseline_path,
                review_path=review_path,
                mode="completion",
                contract_path=contract_path,
            )
        )
        assert wrong_lifecycle_failures and not wrong_lifecycle_approved
        wrong_supersedes_contract = json.loads(json.dumps(pending_contract))
        wrong_supersedes_contract["reviews"]["activation"][
            "supersedes_pending_reviews"
        ] = [SUPPORTED_API_REVIEW_RELATIVE]
        wrong_supersedes_failures, wrong_supersedes_approved = (
            activation_authorization_state(
                wrong_supersedes_contract,
                baseline_path=baseline_path,
                review_path=review_path,
                mode="staging",
                contract_path=contract_path,
            )
        )
        assert wrong_supersedes_failures and not wrong_supersedes_approved
        detached_artifact_contract = json.loads(json.dumps(pending_contract))
        detached_artifact_contract["artifacts"][0]["sha256"] = "0" * 64
        detached_artifact_failures, detached_artifact_approved = (
            activation_authorization_state(
                detached_artifact_contract,
                baseline_path=baseline_path,
                review_path=review_path,
                mode="staging",
                contract_path=contract_path,
            )
        )
        assert detached_artifact_failures and not detached_artifact_approved
        weak_workflow_contract = json.loads(json.dumps(pending_contract))
        weak_workflow_contract["workflow"]["github_issues_read_permission"] = False
        weak_workflow_failures, weak_workflow_approved = activation_authorization_state(
            weak_workflow_contract,
            baseline_path=baseline_path,
            review_path=review_path,
            mode="staging",
            contract_path=contract_path,
        )
        assert weak_workflow_failures and not weak_workflow_approved

        missing_failures, missing_approved = activation_authorization_state(
            None,
            baseline_path=baseline_path,
            review_path=review_path,
            mode="staging",
            contract_path=contract_path,
        )
        assert missing_failures and not missing_approved
        malformed_contract = json.loads(json.dumps(pending_contract))
        malformed_contract["reviews"]["activation"]["scope"][
            "supported_api_checker_sha256"
        ] = "0" * 64
        malformed_failures, malformed_approved = activation_authorization_state(
            malformed_contract,
            baseline_path=baseline_path,
            review_path=review_path,
            mode="staging",
            contract_path=contract_path,
        )
        assert malformed_failures and not malformed_approved

    tokenized = explicit_api_names(
        "\n".join(
            (
                "#check @NumStability.ValueResult?_add_finite_negInf",
                "#check NumStability.adaptedBasis_mem_E₁",
                "#check NumStability.OneNormState.γ",
                "#check NumStability.run!",
                "#check NumStability.«quoted component».ok!",
            )
        )
    )
    assert tokenized == (
        "NumStability.ValueResult?_add_finite_negInf",
        "NumStability.adaptedBasis_mem_E₁",
        "NumStability.OneNormState.γ",
        "NumStability.run!",
        "NumStability.«quoted component».ok!",
    )
    assert namespace_of_rendered_lean_name(
        "NumStability.«quoted.component».ok!"
    ) == "NumStability.«quoted.component»"
    for malformed in (
        "#check NumStability.bad + 1",
        "#check NumStability.«unterminated",
        "#check (NumStability.bad)",
        "#check NumStability.bad)",
        "#check\n  NumStability.bad",
    ):
        try:
            explicit_api_names(malformed)
        except ContractError:
            pass
        else:
            raise AssertionError(f"malformed project target was accepted: {malformed}")

    # Owner movement is frozen unless it is one of the exact reviewed mappings.
    moved = json.loads(json.dumps(baseline))
    moved["declarations"][0]["owner_module"] = "NumStability.Canonical.Demo"
    assert any(
        "owner module drift" in item
        for item in compare_contracts(baseline, moved, review)
    )

    removed = json.loads(json.dumps(baseline))
    removed["declarations"] = []
    removed["derivation"] = reconstructed_derivation([])
    assert any(
        "removed or renamed" in item
        for item in compare_contracts(baseline, removed, review)
    )

    renamed = json.loads(json.dumps(baseline))
    renamed["declarations"][0]["fqn"] = "NumStability.renamedDemo"
    renamed["declarations"][0]["namespace"] = "NumStability"
    renamed["derivation"] = reconstructed_derivation(renamed["declarations"])
    rename_failures = compare_contracts(baseline, renamed, review)
    assert any("removed or renamed" in item for item in rename_failures)
    assert any("unreviewed newly selected" in item for item in rename_failures)

    for field, value, needle in (
        ("kind", "theorem", "declaration kind drift"),
        ("namespace", "Other", "namespace drift"),
        ("protected", True, "protected status drift"),
        ("visibility", "private", "visibility drift"),
        ("canonical_surfaces", [], "canonical surface drift"),
        ("historical_surfaces", [], "historical surface drift"),
        ("expected_entrypoint_reachability", ["NumStability"], "entrypoint reachability drift"),
    ):
        changed = json.loads(json.dumps(baseline))
        changed["declarations"][0][field] = value
        assert any(needle in item for item in compare_contracts(baseline, changed, review))

    changed_type = json.loads(json.dumps(baseline))
    changed_type["declarations"][0]["type_evidence"]["sha256"] = "B" * 64
    assert any(
        "exact elaborated type drift" in item
        for item in compare_contracts(baseline, changed_type, review)
    )

    newly_visible = json.loads(json.dumps(baseline))
    newly_visible["visibility_guard"][0]["public_authored_declaration_count"] = 2
    newly_visible["visibility_guard"][0]["public_authored_names_sha256"] = canonical_json_sha256(
        ["NumStability.demo", "NumStability.unreviewed"]
    )
    assert any(
        "unreviewed public visibility drift" in item
        for item in compare_contracts(baseline, newly_visible, review)
    )

    # The reviewed additive change is atomic and exact.
    active = json.loads(json.dumps(baseline))
    active["declarations"] = merged_expected_declarations(baseline, review, active=True)
    active["derivation"] = reconstructed_derivation(active["declarations"])
    active["derivation"].update(
        {
            "documented_entrypoints": [],
            "protected_selected_declaration_count": 0,
            "tier_manifest_sha256": "synthetic-tier",
        }
    )
    active["review_activation_modules"] = sorted(
        {row["test_module"] for row in review["approved_additive_test_evidence"]}
    )
    assert not compare_contracts(
        baseline, active, review, mode="completion", activation_approved=True
    )

    pending_review = json.loads(json.dumps(review))
    pending_review["decision"] = None
    assert any(
        "lacks exact independent primary-human approval" in item
        for item in compare_contracts(
            baseline, active, pending_review, mode="completion"
        )
    )

    wrong_owner = json.loads(json.dumps(active))
    wrong_owner["declarations"][0]["owner_module"] = "NumStability.Other"
    assert any(
        "owner module drift" in item
        for item in compare_contracts(
            baseline,
            wrong_owner,
            review,
            mode="completion",
            activation_approved=True,
        )
    )

    partial = json.loads(json.dumps(active))
    partial["review_activation_modules"] = partial["review_activation_modules"][:1]
    assert any(
        "partially activated" in item
        for item in compare_contracts(
            baseline,
            partial,
            review,
            mode="completion",
            activation_approved=True,
        )
    )

    missing_evidence = json.loads(json.dumps(active))
    missing_demo = next(
        row for row in missing_evidence["declarations"] if row["fqn"] == "NumStability.demo"
    )
    missing_demo["test_evidence"] = [
        item
        for item in missing_demo["test_evidence"]
        if item["test_module"] != "NumStabilityTest.Reorganization.I01.Second"
    ]
    evidence = missing_demo["test_evidence"]
    missing_demo["test_modules"] = sorted(
        {item["test_module"] for item in evidence}
    )
    missing_demo["canonical_surfaces"] = sorted(
        {item["surface"] for item in evidence if item["surface_kind"] == "canonical"}
    )
    missing_demo["historical_surfaces"] = sorted(
        {item["surface"] for item in evidence if item["surface_kind"] == "historical"}
    )
    missing_evidence["derivation"] = reconstructed_derivation(
        missing_evidence["declarations"]
    )
    missing_evidence["derivation"].update(
        {
            "documented_entrypoints": [],
            "protected_selected_declaration_count": 0,
            "tier_manifest_sha256": "synthetic-tier",
        }
    )
    assert any(
        "exact test assertion evidence drift" in item
        for item in compare_contracts(
            baseline,
            missing_evidence,
            review,
            mode="completion",
            activation_approved=True,
        )
    )

    unreviewed = json.loads(json.dumps(active))
    unreviewed_demo = next(
        row for row in unreviewed["declarations"] if row["fqn"] == "NumStability.demo"
    )
    unreviewed_demo["test_evidence"].append(
        {
            "assertion_occurrences": 1,
            "surface": "NumStability.Unreviewed",
            "surface_kind": "canonical",
            "test_module": "NumStabilityTest.Unreviewed",
        }
    )
    unreviewed_demo["test_evidence"].sort(key=evidence_key)
    unreviewed_demo["canonical_surfaces"].append(
        "NumStability.Unreviewed"
    )
    unreviewed_demo["canonical_surfaces"].sort()
    unreviewed_demo["test_modules"].append(
        "NumStabilityTest.Unreviewed"
    )
    unreviewed_demo["test_modules"].sort()
    unreviewed["derivation"] = reconstructed_derivation(unreviewed["declarations"])
    assert any(
        "exact test assertion evidence drift" in item
        for item in compare_contracts(
            baseline,
            unreviewed,
            review,
            mode="completion",
            activation_approved=True,
        )
    )


def load_json(path: Path) -> dict[str, Any]:
    try:
        value = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as error:
        raise ContractError(f"cannot read {path}: {error}") from error
    if not isinstance(value, dict):
        raise ContractError(f"{path}: expected a JSON object")
    return value


def write_json(path: Path, value: Mapping[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(
        json.dumps(value, ensure_ascii=False, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
        newline="\n",
    )


def parse_args(argv: Sequence[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--baseline", type=Path, default=DEFAULT_BASELINE)
    parser.add_argument("--review", type=Path, default=DEFAULT_REVIEW)
    parser.add_argument(
        "--activation-review", type=Path, default=DEFAULT_ACTIVATION_REVIEW
    )
    parser.add_argument(
        "--mode",
        choices=("staging", "completion", "lifecycle"),
        default="lifecycle",
    )
    parser.add_argument("--self-test", action="store_true")
    parser.add_argument(
        "--write-baseline",
        action="store_true",
        help="write a new C0007-derived baseline; never used by CI verification",
    )
    parser.add_argument(
        "--write-review",
        action="store_true",
        help="write pending C0008 machine facts bound to an existing baseline",
    )
    parser.add_argument("--checkpoint-id", default="C0007")
    parser.add_argument(
        "--checkpoint-code-sha",
        default=C0007_CODE_SHA,
    )
    return parser.parse_args(argv)


def main(argv: Sequence[str] | None = None) -> int:
    args = parse_args(sys.argv[1:] if argv is None else argv)
    try:
        self_test()
        if args.self_test:
            print(
                "supported-API checker self-test passed: full Unicode/?/!/quoted tokenizer, "
                "full documented-entrypoint import union, Lean module-mode exported closure, "
                "exact type-payload round trip, "
                "malformed-target rejection, exact atomic additive delta, pending-attestation, "
                "fresh C0007 additive type/owner fact tamper rejection, "
                "P-pending/A-T-approved/I-approved lifecycle states, recorded GitHub "
                "owner/comment and lifecycle/artifact/workflow tamper rejection, "
                "missing/malformed activation rejection, removal, rename, "
                "kind, namespace, owner, "
                "protected/type/visibility, surface, reachability, and accidental-visibility cases"
            )
            return 0
        baseline_path = args.baseline
        if not baseline_path.is_absolute():
            baseline_path = ROOT / baseline_path
        review_path = args.review
        if not review_path.is_absolute():
            review_path = ROOT / review_path
        activation_path = args.activation_review
        if not activation_path.is_absolute():
            activation_path = ROOT / activation_path
        if args.write_baseline and args.write_review:
            raise ContractError("--write-baseline and --write-review are mutually exclusive")
        if args.write_baseline:
            value = build_contract(
                checkpoint_id=args.checkpoint_id,
                checkpoint_code_sha=args.checkpoint_code_sha,
            )
            failures = validate_baseline_schema(value)
            if failures:
                raise ContractError("generated invalid baseline:\n" + "\n".join(failures))
            write_json(baseline_path, value)
            print(
                f"wrote supported-API baseline: {len(value['declarations'])} declarations, "
                f"{len(value['visibility_guard'])} entrypoints, {baseline_path}"
            )
            return 0

        baseline = load_json(baseline_path)
        schema_failures = validate_baseline_schema(baseline)
        if schema_failures:
            for failure in schema_failures:
                print(f"error: {failure}", file=sys.stderr)
            return 1
        if args.write_review:
            if classify_implementation_state() != "staging":
                raise ContractError("pending review generation requires exact pre-I01 state")
            value = build_additive_review(baseline)
            failures = validate_review_schema(value, baseline)
            if failures:
                raise ContractError("generated invalid review:\n" + "\n".join(failures))
            write_json(review_path, value)
            print(
                "wrote pending supported-API review facts: 5 modules, 9 assertions, "
                f"1 additive declaration, 2 owner moves, {review_path}"
            )
            return 0

        review = load_json(review_path)
        review_failures = validate_review_schema(review, baseline)
        if review_failures:
            for failure in review_failures:
                print(f"error: {failure}", file=sys.stderr)
            return 1

        implementation_state = classify_implementation_state()
        effective_mode = (
            implementation_state if args.mode == "lifecycle" else args.mode
        )
        state_failures: list[str] = []
        if args.mode != "lifecycle" and implementation_state != args.mode:
            state_failures.append(
                f"{args.mode} mode requires exact {args.mode} 14-path state, "
                f"but found {implementation_state}"
            )
        allow_exact_implementation_dirty_paths(effective_mode == "completion")

        # P/A/T run against the exact C0007 governed tree.  Re-extract the two
        # declarations whose owners may move before accepting even a pending
        # activation record, so a review cannot self-authorize forged metadata for
        # the previously unselected problem2_9Source declaration.  At I the exact
        # human-approved activation hash-binds this already-gated immutable review.
        c0007_review_failures = (
            validate_review_against_exact_c0007_environment(review, baseline)
            if effective_mode == "staging"
            else []
        )

        activation_contract = load_json(activation_path) if activation_path.is_file() else None
        activation_failures, activation_approved = activation_authorization_state(
            activation_contract,
            baseline_path=baseline_path,
            review_path=review_path,
            mode=effective_mode,
            contract_path=activation_path,
        )

        current = current_contract_from_baseline(baseline, review)
        failures = state_failures + c0007_review_failures + activation_failures + compare_contracts(
            baseline,
            current,
            review,
            mode=effective_mode,
            activation_approved=activation_approved,
        )
        if failures:
            for failure in failures:
                print(f"error: {failure}", file=sys.stderr)
            return 1
        expected_declarations = merged_expected_declarations(
            baseline, review, active=effective_mode == "completion"
        )
        owner_moves = (
            len(review["approved_owner_moves"])
            if effective_mode == "completion"
            else 0
        )
        print(
            f"supported-API {args.mode} contract passed as {effective_mode}: "
            f"{len(expected_declarations)} explicitly selected declarations, "
            f"{len(baseline['visibility_guard'])} exact entrypoint visibility guards, "
            f"{owner_moves} exact reviewed owner moves"
        )
        return 0
    except (ContractError, OSError, subprocess.SubprocessError, ValueError) as error:
        print(f"error: {error}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
