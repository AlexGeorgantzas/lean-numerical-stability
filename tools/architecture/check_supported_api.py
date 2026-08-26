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
import codecs
import hashlib
import json
import math
import os
import re
import stat
import subprocess
import sys
import tempfile
import unicodedata
from dataclasses import dataclass
from pathlib import Path, PurePosixPath
from typing import Any, Callable, Iterable, Mapping, Sequence


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
BOUNDED_MANIFEST_RELATIVE = (
    "docs/architecture/phases/2026-08-repository-reorganization-completion/"
    "reviews/C0007-bounded-epoch-authorized-paths.tsv"
)
SUPPORTED_API_BASELINE_RELATIVE = "docs/architecture/supported-api.json"
COMPLETION_CHECKER_RELATIVE = "tools/architecture/check_completion_phase.py"
SUPPORTED_API_CHECKER_RELATIVE = "tools/architecture/check_supported_api.py"
WORKFLOW_RELATIVE = ".github/workflows/lean_action_ci.yml"
CI_ONLY_RECOVERY_AUTHORIZATION_ID = "C0007-P-CI-recovery-only-v1"
CI_ONLY_RECOVERY_AUTHORIZATION_SHA256 = (
    "CC73A05B3B78D1C2E40C8EA18A5690F697F17FB30960D099BC1E88BCF49B8A76"
)
CI_ONLY_RECOVERY_MANIFEST_SHA256 = (
    "E0892856B09B6B0E3A44E6FE49A303918D1BCF88743F5328E6A8E996C689E6C0"
)
CI_ONLY_RECOVERY_PATH_SET_SHA256 = (
    "3CF30300730F9BD37AB532D1C99E387EC32ECB5B98B51F33C0ED04DE4953089A"
)
CI_ONLY_RECOVERY_PREIMAGE_FREEZE_SHA256 = (
    "A7C7DBB77711DCDA7BA31AC720D1710E05E48F007523A0EACD583AA213BB49FC"
)
CI_ONLY_RECOVERY_MANIFEST_ROW_COUNT = 8
CI_ONLY_RECOVERY_PATHS = (
    WORKFLOW_RELATIVE,
    BOUNDED_MANIFEST_RELATIVE,
    BOUNDED_AUTHORIZATION_RELATIVE,
    DEFAULT_ACTIVATION_REVIEW.relative_to(ROOT).as_posix(),
    SUPPORTED_API_REVIEW_RELATIVE,
    SUPPORTED_API_BASELINE_RELATIVE,
    COMPLETION_CHECKER_RELATIVE,
    SUPPORTED_API_CHECKER_RELATIVE,
)
CI_ONLY_RECOVERY_MANIFEST_BYTES = (
    "path\tpacket_id\tstage\toperation\n"
    ".github/workflows/lean_action_ci.yml\tCI01R1\tci_recovery_control\tmodify\n"
    "docs/architecture/phases/2026-08-repository-reorganization-completion/"
    "reviews/C0007-bounded-epoch-authorized-paths.tsv\tCI01R1\t"
    "ci_recovery_control\tmodify\n"
    "docs/architecture/phases/2026-08-repository-reorganization-completion/"
    "reviews/C0007-bounded-epoch-operator-authorization.json\tCI01R1\t"
    "ci_recovery_control\tmodify\n"
    "docs/architecture/phases/2026-08-repository-reorganization-completion/"
    "reviews/C0007-bounded-planned-control.json\tCI01R1\t"
    "ci_recovery_control\tmodify\n"
    "docs/architecture/phases/2026-08-repository-reorganization-completion/"
    "reviews/C0008-supported-api.json\tCI01R1\tci_recovery_control\tmodify\n"
    "docs/architecture/supported-api.json\tCI01R1\tci_recovery_control\tmodify\n"
    "tools/architecture/check_completion_phase.py\tCI01R1\t"
    "ci_recovery_control\tmodify\n"
    "tools/architecture/check_supported_api.py\tCI01R1\t"
    "ci_recovery_control\tmodify\n"
).encode("utf-8")
CI_ONLY_RECOVERY_CONTRACT_SCHEMA_VERSION = 4
CI_ONLY_RECOVERY_CONTRACT_KIND = "c0007_bounded_ci_only_recovery_control"
CI_ONLY_RECOVERY_CONTROL_ID = "C0007-P-CI-recovery-control-v1"
CI_ONLY_RECOVERY_STATE = "ci_recovery_pending"
CI_ONLY_RECOVERY_WORKFLOW_SHA256 = (
    "7FCCF4C8B274A9C8DC919ADC271F4D48B3416863192872706CF444DF3E419158"
)
CI_ONLY_RECOVERY_ARTIFACT_PATH_SET_SHA256 = (
    "F01D66DD09B3F2E59DCC4012A58338CB5BC2F26E2B88E7BBF8BC605BA82947BB"
)
CI_ONLY_RECOVERY_HISTORICAL_PACKET_PATH_SET_SHA256 = (
    "39534A6720B99C39263A261CC71E5DD262AD3F71ED40B875AB28B52BE0D1B674"
)
CI_ONLY_RECOVERY_ARTIFACT_PATHS = tuple(
    path
    for path in CI_ONLY_RECOVERY_PATHS
    if path != DEFAULT_ACTIVATION_REVIEW.relative_to(ROOT).as_posix()
)
CI_ONLY_RECOVERY_ARTIFACT_BASE_BLOB_OIDS = {
    WORKFLOW_RELATIVE: "5f00c1b987ca16f9cfebb6b1c65d9c71b8349107",
    BOUNDED_MANIFEST_RELATIVE: "201c9e3a26bb10721041ac660e0c9f112163b98c",
    BOUNDED_AUTHORIZATION_RELATIVE: "4957e833be3f7243bc47f69f14d05a7043642147",
    SUPPORTED_API_REVIEW_RELATIVE: "41935ddd2eefe1602003eb663c7d3befd4cca0c4",
    SUPPORTED_API_BASELINE_RELATIVE: "c26fe1fadc0468b9f53975cc198320481a975a6b",
    COMPLETION_CHECKER_RELATIVE: "35fbb23ac3666ecb2dfc432b08165233978a7271",
    SUPPORTED_API_CHECKER_RELATIVE: "37b3f76c35a3c5662b73668ad799901be15f6368",
}
CI_ONLY_RECOVERY_CONTROL_HEAD_SHA = "8960f2a980be22166f321c4ba452eb547529b1fd"
CI_ONLY_RECOVERY_CONTROL_TREE_SHA = "70cee1e77e1311129b00aeb0945770483d1aa5db"
FAILED_P_COMMIT_SHA = "1d454ecb8dc80dc4ece21ebc26eec29b8f9a6ae9"
FAILED_P_TREE_SHA = "ce9760fc7a49e69e98551e992c27fd11f9b247b1"
FAILED_P_CONTRACT_BLOB_OID = "6c1f59211399c626c7727952c16ea63e504270c8"
FAILED_P_CONTRACT_SHA256 = (
    "D8C0E5ED51C075A93A16376967E501B670B16B06C91E96D1D1600351CFAA141D"
)
FAILED_P_AUTHORIZATION_BLOB_OID = "4957e833be3f7243bc47f69f14d05a7043642147"
FAILED_P_MANIFEST_BLOB_OID = "201c9e3a26bb10721041ac660e0c9f112163b98c"
FAILED_P_WORKFLOW_BLOB_OID = "5f00c1b987ca16f9cfebb6b1c65d9c71b8349107"
FAILED_P_COMPLETION_CHECKER_BLOB_OID = (
    "35fbb23ac3666ecb2dfc432b08165233978a7271"
)
FAILED_P_COMPLETION_CHECKER_SHA256 = (
    "9D82E21737C783923F6A02954703E499B01697970834AF054E08A5B63C511552"
)
FAILED_P_RUN_ID = 32966438799
FAILED_P_RUN_NUMBER = 8950
FAILED_P_JOB_ID = 98169864308
FAILED_P_CHECK_SUITE_ID = 89298169052
FAILED_P_JOB_LOG_BYTE_COUNT = 20201
FAILED_P_JOB_LOG_SHA256 = (
    "8383047A0845BAA625BCC3ACA3AE5FCD744F80AD9D7A4647B0371B23EB41D16D"
)
FAILED_P_FAILURE_REASON = (
    "actions checkout created a no-.git origin URL and a branch remote override "
    "rejected by remote.identity"
)
# Exact frozen digest of the companion completion-phase checker. Lifecycle
# validation fails closed on either a malformed constant or live checker drift.
CI_RECOVERY_COMPLETION_CHECKER_SHA256 = (
    "7C149108C32A728D50A23441FD49B446CEDE1D87EA5CA7F8051476F09F734BBC"
)

# These records remain immutable evidence from failed P.  They are not current
# CI-recovery authority and must never be folded into the seven-artifact current
# recovery scope merely because their historical bytes are still present.
HISTORICAL_TERMINAL_V2_AUTHORIZATION_ID = (
    "C0007-M13-I01-CODE03-terminal-v2"
)
HISTORICAL_TERMINAL_V2_AUTHORIZATION_SHA256 = (
    "9BD67B6336BA9D2943552AA09D19F580EC4A8A9298E85BC846854A201CB15129"
)
HISTORICAL_P_PACKET_ARTIFACTS = {
    "docs/architecture/phases/2026-08-repository-reorganization-completion/"
    "requests/R0014-review.md": {
        "blob_oid": "54927c2c2937583da407cb5fa5eb8db69bdebe03",
        "byte_count": 6256,
        "sha256": "69BFB58422DBEA48EF29DB39B74A70ED063453C7250F7E0A9F90ED9FF9400EB1",
    },
    "docs/architecture/phases/2026-08-repository-reorganization-completion/"
    "requests/R0015-review.md": {
        "blob_oid": "3a1b2543c8e54f4e8bba0febcb6b1526ace68553",
        "byte_count": 7572,
        "sha256": "1E3C8382E4185B5543D754EA35F7CA23A1426D01525C47A9A44CFE6BB5621376",
    },
    "docs/architecture/phases/2026-08-repository-reorganization-completion/"
    "reviews/CODE03-approval.json": {
        "blob_oid": "a96907ce457cea2de02cb45a70485b3129f8c9af",
        "byte_count": 6101,
        "sha256": "CF4EF2EA8E00562D61F706033E757359D8440E55804498BE34BD7CFA86DA5488",
    },
    "docs/architecture/phases/2026-08-repository-reorganization-completion/"
    "reviews/I01-approval.json": {
        "blob_oid": "cdd37abb449d9a800015792c6ac59891f0036168",
        "byte_count": 4964,
        "sha256": "8B3CC920221E9786785D1D56DB2105964063CB50929DBFAAAD49B1E29A4070B8",
    },
    "docs/architecture/phases/2026-08-repository-reorganization-completion/"
    "reviews/I01-selection-overlap.md": {
        "blob_oid": "90abd450b609c91f4b6f773ac3db0df6ba484398",
        "byte_count": 4211,
        "sha256": "5A0A4852AD84095CFBFC973ACF37E45C8C0AA5FB09D8E8728356CC30C1AF43A9",
    },
}
HISTORICAL_P_PACKET_PATH_SET_SHA256 = (
    "39534A6720B99C39263A261CC71E5DD262AD3F71ED40B875AB28B52BE0D1B674"
)
HISTORICAL_FULL_TESTS_CORRECTION_SHA256 = (
    "FD35FC88D44230585B200FFEA021C5C53C56A004D03E8DC284F2F5B0EE6803EF"
)
# Historical source only: this exact terminal-v2 document is retained to make
# the P provenance boundary reviewable, but is no longer accepted as live
# authority by validate_bounded_authorization_document().
HISTORICAL_TERMINAL_V2_AUTHORIZATION = json.loads(r'''
{
  "activation_conditions": [
    "the control parent, control tree, remote main, active phase pointer, phase, authorized-path manifest, workflow, checker, packet, postimage, supported-API, and artifact identities remain exact",
    "every dirty P, A, T, I, or V precommit is on the exact symbolic codex/reorg-closeout-2026-08-m13-i01 branch; every clean symbolic lifecycle checkout is on that branch; only a clean detached checkout used for validation is permitted",
    "P is the exact 42-path direct child of 8960f2a980be22166f321c4ba452eb547529b1fd, the bounded remote ref is absent immediately before its exact absence-lease push and equals P afterward, and exact-head P Lean CI succeeds before the activation review is solicited",
    "the first exact live repository-owner comment is created after P CI and remains live and unedited; A is the contract-only direct child of P; the bounded remote ref equals P immediately before its P-to-A exact-lease push and equals A afterward; and exact-head A Lean CI succeeds before T",
    "T is the contract-only direct child of A; the bounded remote ref equals A immediately before its A-to-T exact-lease push and equals T afterward; and T has an authenticated successful exact-head workflow_dispatch observation before any R0014 or R0015 implementation postimage is applied or staged",
    "R0014 and R0015 replay from exact C0007 code 4e26820d1f4989ec4ec77b7113085f593570e11b, reproduce every hash-pinned postimage, and I is their exact indivisible 14-path direct child of T; the bounded remote ref equals T immediately before its T-to-I exact-lease push and equals I afterward",
    "exact-head I Lean CI succeeds and the second distinct live repository-owner comment is created afterward and remains live and unedited before V",
    "V is the contract-only direct child of I; the bounded remote ref equals I immediately before its I-to-V exact-lease push and equals V afterward; exact-head V post-assurance CI is then dispatched and authenticated read-only and its canonical evidence is recorded only in the untracked local ledger, which terminates this grant; that evidence may be hash-pinned only by a separately authorized C8-PROPOSE epoch"
  ],
  "authorization_id": "C0007-M13-I01-CODE03-terminal-v2",
  "authority_id": "primary-human",
  "authorized_actions": [
    "prepare and validate P using exactly the 42 planned_control rows of the authorized path manifest; commit P and exact-absence-lease create the bounded remote ref at P; after P CI and the activation owner comment, commit contract-only A and exact-lease push the bounded ref from P to A; after A CI, commit contract-only T and exact-lease push the bounded ref from A to T",
    "generate, reproducibly verify, and freeze docs/architecture/supported-api.json and the pending-only C0008-supported-api.json machine-evidence record without assigning any human decision or checkpoint authority",
    "dispatch and monitor exact-head Lean CI for P, A, T, I, and post-assurance V; create the ordinary review issue; and solicit the two exact live GitHub repository-owner comments",
    "after P CI, the activation owner comment, A, A CI, T, and the authenticated live T remote-tip observation, apply R0014 and R0015 only as their complete indivisible 14-path union, commit I, and exact-lease push the bounded ref from T to I",
    "after I CI and the distinct implementation owner comment, commit V and exact-lease push the bounded ref from I to V, dispatch and authenticate exact-head V CI read-only, and record its canonical evidence only in the untracked local ledger"
  ],
  "base": {
    "active_phase_pointer_sha256": "C99061ACCE56AF121B1ACF0FBE2C757B53602A5A8599DC93193871095D3AB360",
    "control_head_sha": "8960f2a980be22166f321c4ba452eb547529b1fd",
    "control_tree_sha": "70cee1e77e1311129b00aeb0945770483d1aa5db",
    "current_checkpoint_id": "C0007",
    "current_checkpoint_sha": "4e26820d1f4989ec4ec77b7113085f593570e11b",
    "phase_sha256": "7DCF4E6B47F3EDEC92D1F6945426F0AB13215A5AC3C362D9356A58C413288AAC",
    "remote_main_sha": "8960f2a980be22166f321c4ba452eb547529b1fd"
  },
  "decision": "approved",
  "expiry": {
    "events": [
      "after the verified V commit is exact-lease pushed from I to refs/heads/codex/reorg-closeout-2026-08-m13-i01 at V, its exact-head workflow_dispatch post-assurance run succeeds, is authenticated with stable remote-main and bounded-ref observations, and its canonical evidence is recorded only in the untracked local ledger",
      "explicit cancellation or supersession",
      "base, authorized-path-manifest, workflow, checker, request-patch, postimage, supported-API, or artifact drift",
      "an exact-lease mismatch, bounded-ref drift, or remote-main drift",
      "primary-human revocation"
    ],
    "terminal_control_state": "verified",
    "valid_only_while_current_checkpoint_id": "C0007"
  },
  "operator_id": "codex-local",
  "phase_id": "repository-reorganization-completion-2026-08",
  "preserved_exclusions": [
    "tracking, committing, or pushing REMOTE_MAIN_REORGANIZATION_CLOSEOUT_PLAN.md",
    "any public declaration name, namespace, normalized type, visibility, or supported-entrypoint reachability change",
    "any tracked path absent from the authorized path manifest or any authorized manifest stage or operation drift",
    "partial application or partial rollback of R0014, R0015, or their complete 14-path union",
    "semantic review by codex-local, any exact artifact generator or action performer, CI, or any service principal",
    "any R0014 or R0015 request resolution, I01 selector finalization, or M13, I01, R0014, R0015, or C0008 status mutation",
    "any C8-PROPOSE or C8-ACCEPT commit, or any C0008 proposal, checkpoint or status acceptance, or finalization action",
    "any non-null decision, reviewer, or reviewed_at_utc in reviews/C0008-supported-api.json, or any interpretation of that record as human review, checkpoint acceptance, request resolution, or authority",
    "any push, merge, force-update, deletion, or other mutation of origin refs/heads/main",
    "repository-wide completion or final release acceptance",
    "bounded-branch retirement, bounded remote-ref deletion, any force push, or any history rewrite"
  ],
  "record_kind": "primary_human_bounded_epoch_authorization",
  "recorded_at": "2026-08-26T01:15:53Z",
  "schema_version": 2,
  "scope": {
    "authorized_path_manifest": {
      "path": "docs/architecture/phases/2026-08-repository-reorganization-completion/reviews/C0007-bounded-epoch-authorized-paths.tsv",
      "row_count": 56,
      "sha256": "121D11A73AF2CD23885FB7A6B38D14B0D8A5440940D913A83F3A5D6941511ECE"
    },
    "checkpoint_acceptance_authorized": false,
    "milestone_id": "M13",
    "remote_main_mutation_authorized": false,
    "request_ids": [
      "R0014",
      "R0015"
    ],
    "request_resolution_authorized": false,
    "supported_api_record": {
      "authority_effect": "none",
      "path": "docs/architecture/phases/2026-08-repository-reorganization-completion/reviews/C0008-supported-api.json",
      "required_null_fields": [
        "decision",
        "reviewer",
        "reviewed_at_utc"
      ],
      "status": "pending_machine_evidence"
    },
    "task_ids": [
      "API-01",
      "CODE-01",
      "CODE-02",
      "CODE-03",
      "EPOCH-01",
      "GOV-01",
      "GOV-02",
      "GOV-03",
      "GOV-04",
      "I01-01",
      "I01-02",
      "VERIFY-01",
      "VERIFY-02",
      "VERIFY-03"
    ],
    "terminal_control_state": "verified",
    "wave_id": "I01"
  },
  "source": {
    "channel": "current Codex desktop task",
    "instruction": "I authorize you to do whatever you need.",
    "received_at": "2026-08-25T15:14:31Z",
    "received_at_source": "task user-message timestamp",
    "user_principal_id": "primary-human"
  },
  "supersedes_draft": {
    "authorization_id": "C0007-M13-I01-CODE03-bounded-v1",
    "sha256": "7AD0DD3ACD880CDDB1D89C1DD28824F8EF6116415462A9466C95E4F593D02439"
  }
}
''')
TIER_MANIFEST = ROOT / "docs" / "architecture" / "tiers.json"
TEST_ROOT = "NumStabilityTest"
PROJECT_PREFIX = "NumStability"
SCHEMA_VERSION = 1
TYPE_NORMALIZATION = "lean-expr-repr-exact-percent-escaped-v1"
MAX_JSON_BYTES = 64 * 1024 * 1024
MAX_JSON_DEPTH = 64
TSV_CHUNK_BYTES = 1024 * 1024
TSV_SMALL_ROW_BYTES = 1024 * 1024
TSV_PREFIX_BYTES = 64 * 1024
C0007_ASSERTION_COUNT = 30_280
C0007_SELECTED_DECLARATION_COUNT = 19_209
C0007_ISOLATED_TEST_MODULE_COUNT = 2_717
C0007_DOCUMENTED_ENTRYPOINT_COUNT = 39
C0007_TEST_CONTRACT_SHA256 = (
    "35FE92995DD229D06B8219D943B527BBE0F7450C8AAB727AC69319AF88F37829"
)
PENDING_REVIEW_RATIONALE = (
    "Machine-derived candidate facts for freezing C0007 and, only after independent "
    "primary-human approval, authorizing the atomic R0014/I01 addition: five "
    "one-import modules, nine #check occurrences, and one newly selected existing "
    "declaration."
)
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
HISTORICAL_P_WORKFLOW_SHA256 = (
    "AF4D9C4471F5D9AA140D8741D2B15AF453168C7B6BBD9970ADE1A479B1CE174C"
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
        "CDF9CD8B9E5D8A06F60CB769801A5AC891F4468E1435207060F77B50BE1C67CE"
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
CANDIDATE_IMPLEMENTATION_PATCH_SHA256 = {
    "docs/architecture/phases/2026-08-repository-reorganization-completion/requests/R0014.patch": (
        "3AC31AFC44B697FF830E0CF393FF1725F18B49022ABCF81D83742220FCCB3A88"
    ),
    "docs/architecture/phases/2026-08-repository-reorganization-completion/requests/R0015.patch": (
        "A6EAA922363136C5B15351849260632094C1A707D7134E7084CBA6556415E820"
    ),
}
CANDIDATE_IMPLEMENTATION_INPUT_SHA256 = {
    "docs/architecture/phases/2026-08-repository-reorganization-completion/requests/R0014.json": (
        "CDF9CD8B9E5D8A06F60CB769801A5AC891F4468E1435207060F77B50BE1C67CE"
    ),
    **CANDIDATE_IMPLEMENTATION_PATCH_SHA256,
    "docs/architecture/phases/2026-08-repository-reorganization-completion/requests/R0014-postimages.tsv": (
        "42F4ED7EFE7C611DE214A0E6FE4ABADA11034632A9086952EADCD1A8AA33A1C9"
    ),
    "docs/architecture/phases/2026-08-repository-reorganization-completion/requests/R0015.json": (
        "A021AD7AC5303C0CEE3546030B4633E3FD78C38C1B03CC978FCBEBC4BB8B1391"
    ),
    "docs/architecture/phases/2026-08-repository-reorganization-completion/requests/R0015-postimages.tsv": (
        "F92A484CAFBB2F8885A14CE5A7A0A9DB4A774888757797BB836254D4600BED8D"
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
APPROVED_I01_C0007_OWNER_MODULES = {
    "NumStability.FloatingPointFormat.binary64MantissaExtendedLocalFormat": (
        "NumStability.Source.Higham.Chapter02.Problem09.DoubleRounding.Counterexample"
    ),
    "NumStability.FloatingPointFormat.problem2_9Source": (
        "NumStability.Source.Higham.Chapter02.Problem09.DoubleRounding.Counterexample"
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
class FileIdentity:
    device: int
    inode: int
    size: int
    mtime_ns: int
    sha256: str


@dataclass(frozen=True)
class CapturedFile:
    path: Path
    raw: bytes
    identity: FileIdentity


@dataclass(frozen=True)
class JsonDocument:
    capture: CapturedFile
    value: Mapping[str, Any]


@dataclass(frozen=True)
class CapturedSource:
    path: Path
    relative: str
    raw: bytes
    text: str
    identity: FileIdentity


@dataclass(frozen=True)
class VirtualSource:
    path: Path
    relative: str
    raw: bytes
    text: str


@dataclass(frozen=True)
class GenerationInputs:
    checker: CapturedFile
    tier_manifest: JsonDocument
    toolchain_inputs: tuple[CapturedFile, ...]
    review_artifacts: tuple[CapturedFile, ...]
    sources: tuple[CapturedSource, ...]


@dataclass(frozen=True)
class Module:
    name: str
    path: Path
    imports: tuple[str, ...]
    exported_imports: tuple[str, ...]
    text: str = ""
    code_mask: str = ""


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
    raw_tsv_bytes: int = 0
    raw_tsv_sha256: str = ""
    physical_record_count: int = 0
    max_physical_record_bytes: int = 0


@dataclass(frozen=True)
class CandidatePostimage:
    rows: tuple[Mapping[str, str], ...]
    bytes_by_path: Mapping[str, bytes]


def sha256_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest().upper()


def canonical_json_bytes(value: Any) -> bytes:
    try:
        rendered = json.dumps(
            value,
            ensure_ascii=False,
            indent=2,
            sort_keys=True,
            allow_nan=False,
        ) + "\n"
        return rendered.encode("utf-8")
    except (TypeError, ValueError, UnicodeEncodeError) as error:
        raise ContractError(f"value is not canonical strict JSON: {error}") from error


def canonical_json_sha256(value: Any) -> str:
    try:
        payload = json.dumps(
            value,
            ensure_ascii=False,
            sort_keys=True,
            separators=(",", ":"),
            allow_nan=False,
        ).encode("utf-8")
    except (TypeError, ValueError, UnicodeEncodeError) as error:
        raise ContractError(f"value is not strict JSON: {error}") from error
    return sha256_bytes(payload)


def json_exact_equal(left: Any, right: Any) -> bool:
    """JSON equality that never aliases bool, int, and float scalars."""

    if type(left) is not type(right):
        return False
    if isinstance(left, dict):
        return set(left) == set(right) and all(
            json_exact_equal(left[key], right[key]) for key in left
        )
    if isinstance(left, list):
        return len(left) == len(right) and all(
            json_exact_equal(a, b) for a, b in zip(left, right)
        )
    return left == right


def json_exact_difference(actual: Any, expected: Any, *, path: str = "$") -> str | None:
    """Return the first type/order/value mismatch in two strict JSON trees."""

    if type(actual) is not type(expected):
        return (
            f"{path}: expected exact JSON type {type(expected).__name__}, "
            f"got {type(actual).__name__}"
        )
    if isinstance(expected, dict):
        actual_keys = set(actual)
        expected_keys = set(expected)
        missing = sorted(expected_keys - actual_keys)
        extra = sorted(actual_keys - expected_keys)
        if missing or extra:
            return f"{path}: missing keys {missing!r}; extra keys {extra!r}"
        for key in expected:
            difference = json_exact_difference(
                actual[key], expected[key], path=f"{path}.{key}"
            )
            if difference is not None:
                return difference
        return None
    if isinstance(expected, list):
        if len(actual) != len(expected):
            return f"{path}: expected {len(expected)} ordered items, got {len(actual)}"
        for index, (actual_item, expected_item) in enumerate(zip(actual, expected)):
            difference = json_exact_difference(
                actual_item, expected_item, path=f"{path}[{index}]"
            )
            if difference is not None:
                return difference
        return None
    if actual != expected:
        return f"{path}: expected {expected!r}, got {actual!r}"
    return None


def _stat_signature(info: os.stat_result) -> tuple[int, int, int, int]:
    return (int(info.st_dev), int(info.st_ino), int(info.st_size), int(info.st_mtime_ns))


def capture_file(path: Path, *, max_bytes: int | None = None) -> CapturedFile:
    """Read one stable regular file once and bind its bytes to its identity."""

    try:
        with path.open("rb") as handle:
            opened = os.fstat(handle.fileno())
            if not stat.S_ISREG(opened.st_mode):
                raise ContractError(f"{path}: expected a regular file")
            if max_bytes is not None and opened.st_size > max_bytes:
                raise ContractError(
                    f"{path}: {opened.st_size} bytes exceeds {max_bytes}-byte limit"
                )
            chunks: list[bytes] = []
            total = 0
            while True:
                chunk = handle.read(1024 * 1024)
                if not chunk:
                    break
                total += len(chunk)
                if max_bytes is not None and total > max_bytes:
                    raise ContractError(f"{path}: exceeds {max_bytes}-byte limit")
                chunks.append(chunk)
            closed = os.fstat(handle.fileno())
        current = path.stat()
    except ContractError:
        raise
    except OSError as error:
        raise ContractError(f"cannot capture {path}: {error}") from error
    if _stat_signature(opened) != _stat_signature(closed) or _stat_signature(
        opened
    ) != _stat_signature(current):
        raise ContractError(f"{path}: file identity changed while it was read")
    raw = b"".join(chunks)
    if len(raw) != opened.st_size:
        raise ContractError(
            f"{path}: captured {len(raw)} bytes but stable size is {opened.st_size}"
        )
    return CapturedFile(
        path=path,
        raw=raw,
        identity=FileIdentity(
            device=int(opened.st_dev),
            inode=int(opened.st_ino),
            size=int(opened.st_size),
            mtime_ns=int(opened.st_mtime_ns),
            sha256=sha256_bytes(raw),
        ),
    )


class _DuplicateJsonKey(ValueError):
    pass


def _strict_object_pairs(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
    result: dict[str, Any] = {}
    for key, value in pairs:
        if key in result:
            raise _DuplicateJsonKey(f"duplicate object key: {key!r}")
        result[key] = value
    return result


def _strict_json_float(text: str) -> float:
    value = float(text)
    if not math.isfinite(value):
        raise ValueError(f"non-finite JSON number: {text}")
    return value


def _reject_json_constant(text: str) -> Any:
    raise ValueError(f"non-standard JSON constant: {text}")


def _has_lone_surrogate(text: str) -> bool:
    return any(0xD800 <= ord(char) <= 0xDFFF for char in text)


def validate_strict_json_tree(value: Any, *, max_depth: int = MAX_JSON_DEPTH) -> None:
    stack: list[tuple[Any, int]] = [(value, 1)]
    while stack:
        item, depth = stack.pop()
        if isinstance(item, dict):
            if depth > max_depth:
                raise ContractError(f"JSON nesting exceeds depth {max_depth}")
            for key, child in item.items():
                if type(key) is not str or _has_lone_surrogate(key):
                    raise ContractError("JSON object key contains a lone surrogate")
                stack.append((child, depth + 1))
        elif isinstance(item, list):
            if depth > max_depth:
                raise ContractError(f"JSON nesting exceeds depth {max_depth}")
            stack.extend((child, depth + 1) for child in item)
        elif type(item) is str:
            if _has_lone_surrogate(item):
                raise ContractError("JSON string contains a lone surrogate")
        elif type(item) is float:
            if not math.isfinite(item):
                raise ContractError("JSON contains a non-finite number")
        elif type(item) not in {type(None), bool, int}:
            raise ContractError(f"unsupported parsed JSON scalar: {type(item).__name__}")


def parse_strict_json_bytes(
    raw: bytes,
    *,
    label: str,
    require_object: bool = True,
) -> Mapping[str, Any]:
    try:
        text = raw.decode("utf-8", errors="strict")
    except UnicodeDecodeError as error:
        raise ContractError(f"{label}: invalid UTF-8: {error}") from error
    try:
        value = json.loads(
            text,
            object_pairs_hook=_strict_object_pairs,
            parse_constant=_reject_json_constant,
            parse_float=_strict_json_float,
        )
    except (_DuplicateJsonKey, json.JSONDecodeError, ValueError, RecursionError) as error:
        raise ContractError(f"{label}: invalid strict JSON: {error}") from error
    validate_strict_json_tree(value)
    if require_object and type(value) is not dict:
        raise ContractError(f"{label}: expected a JSON object")
    return value


def capture_json_document(
    path: Path, *, require_canonical: bool = False
) -> JsonDocument:
    capture = capture_file(path, max_bytes=MAX_JSON_BYTES)
    value = parse_strict_json_bytes(capture.raw, label=str(path))
    if require_canonical and capture.raw != canonical_json_bytes(value):
        raise ContractError(
            f"{path}: bytes are not exact sorted-key/two-space/LF canonical JSON"
        )
    return JsonDocument(capture=capture, value=value)


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


def implementation_postimage_rows(
    inputs: GenerationInputs | None = None,
) -> list[dict[str, str]]:
    rows: list[dict[str, str]] = []
    captured = (
        {
            item.path.relative_to(ROOT).as_posix(): item
            for item in inputs.review_artifacts
        }
        if inputs is not None
        else {}
    )
    for relative, expected_digest in sorted(IMPLEMENTATION_POSTIMAGE_LEDGERS.items()):
        path = ROOT / relative
        artifact = captured.get(relative) or capture_file(path)
        actual_digest = artifact.identity.sha256
        if actual_digest != expected_digest:
            raise ContractError(
                f"atomic implementation ledger drift: {relative}: expected "
                f"{expected_digest}, got {actual_digest}"
            )
        try:
            text = artifact.raw.decode("utf-8-sig", errors="strict")
        except UnicodeDecodeError as error:
            raise ContractError(f"invalid UTF-8 postimage ledger: {relative}: {error}") from error
        lines = text.splitlines()
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
            path_text, preimage_blob_oid, preimage, postimage = fields
            if not path_text or not re.fullmatch(r"[0-9A-F]{64}", postimage):
                raise ContractError(f"{relative}:{line_number}: invalid path/postimage")
            if preimage != "-" and not re.fullmatch(r"[0-9A-F]{64}", preimage):
                raise ContractError(f"{relative}:{line_number}: invalid preimage")
            if (preimage == "-") != (preimage_blob_oid == "-") or (
                preimage_blob_oid != "-"
                and not re.fullmatch(r"[0-9a-f]{40}", preimage_blob_oid)
            ):
                raise ContractError(
                    f"{relative}:{line_number}: invalid preimage blob binding"
                )
            rows.append(
                {
                    "packet_id": "R0014" if "R0014" in relative else "R0015",
                    "path": path_text,
                    "preimage_blob_oid": preimage_blob_oid,
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


def _capture_regular_or_absent(path: Path, *, label: str) -> CapturedFile | None:
    try:
        info = path.lstat()
    except FileNotFoundError:
        return None
    except OSError as error:
        raise ContractError(f"cannot inspect {label}: {path}: {error}") from error
    if stat.S_ISLNK(info.st_mode) or not stat.S_ISREG(info.st_mode):
        raise ContractError(f"{label} is not an exact regular file or absence: {path}")
    return capture_file(path)


def classify_implementation_state() -> str:
    rows = implementation_postimage_rows()
    pre_matches: list[bool] = []
    post_matches: list[bool] = []
    diagnostics: list[str] = []
    for row in rows:
        path = ROOT / row["path"]
        captured = _capture_regular_or_absent(
            path, label="atomic implementation path"
        )
        current = captured.identity.sha256 if captured is not None else "-"
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
            env=_ambient_git_environment(),
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
            env=_ambient_git_environment(),
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


def _validated_candidate_paths(
    rows: Sequence[Mapping[str, str]],
) -> tuple[str, ...]:
    expected_fields = {
        "packet_id",
        "path",
        "preimage_blob_oid",
        "preimage_sha256",
        "postimage_sha256",
    }
    paths: list[str] = []
    packet_counts = {"R0014": 0, "R0015": 0}
    for index, row in enumerate(rows):
        if set(row) != expected_fields:
            raise ContractError(
                f"candidate postimage row {index}: unexpected or missing fields"
            )
        packet_id = row.get("packet_id")
        if packet_id not in packet_counts:
            raise ContractError(f"candidate postimage row {index}: invalid packet")
        packet_counts[packet_id] += 1
        relative = row.get("path", "")
        posix = PurePosixPath(relative)
        if (
            not relative
            or "\\" in relative
            or ":" in relative
            or posix.is_absolute()
            or ".." in posix.parts
            or posix.as_posix() != relative
        ):
            raise ContractError(
                f"candidate postimage row {index}: unsafe/noncanonical path {relative!r}"
            )
        paths.append(relative)
    if len(paths) != 14 or len(set(paths)) != 14:
        raise ContractError(
            "candidate postimage requires exactly 14 unique implementation paths"
        )
    if packet_counts != {"R0014": 12, "R0015": 2}:
        raise ContractError(
            f"candidate postimage packet census mismatch: {packet_counts!r}"
        )
    return tuple(sorted(paths))


def validate_candidate_postimage_bytes(
    rows: Sequence[Mapping[str, str]],
    bytes_by_path: Mapping[str, bytes],
) -> None:
    paths = _validated_candidate_paths(rows)
    if set(bytes_by_path) != set(paths):
        missing = sorted(set(paths) - set(bytes_by_path))
        extra = sorted(set(bytes_by_path) - set(paths))
        raise ContractError(
            f"candidate postimage byte inventory mismatch: missing={missing!r}, "
            f"extra={extra!r}"
        )
    indexed = {row["path"]: row for row in rows}
    for relative in paths:
        payload = bytes_by_path[relative]
        if type(payload) is not bytes:
            raise ContractError(
                f"candidate postimage {relative}: expected captured bytes"
            )
        actual = sha256_bytes(payload)
        expected = indexed[relative]["postimage_sha256"]
        if actual != expected:
            raise ContractError(
                f"candidate postimage hash mismatch: {relative}: "
                f"expected {expected}, got {actual}"
            )


def _validate_candidate_packet_request(
    request: Mapping[str, Any],
    packet_id: str,
    rows: Sequence[Mapping[str, str]],
) -> None:
    packet_rows = sorted(
        (row for row in rows if row["packet_id"] == packet_id),
        key=lambda row: row["path"],
    )
    expected_paths = [row["path"] for row in packet_rows]
    if request.get("request_id") != packet_id:
        raise ContractError(f"candidate {packet_id} request identity mismatch")
    if request.get("target_base_sha") != C0007_CODE_SHA or request.get(
        "target_checkpoint_id"
    ) != "C0007":
        raise ContractError(f"candidate {packet_id} request base mismatch")
    if not json_exact_equal(request.get("paths"), expected_paths):
        raise ContractError(f"candidate {packet_id} request path inventory mismatch")
    expected_preimages = [
        {
            "blob_oid": (
                None
                if row["preimage_blob_oid"] == "-"
                else row["preimage_blob_oid"]
            ),
            "path": row["path"],
        }
        for row in packet_rows
    ]
    if not json_exact_equal(request.get("preimage_blobs"), expected_preimages):
        raise ContractError(f"candidate {packet_id} request preimage map mismatch")
    patch_relative = next(
        relative
        for relative in CANDIDATE_IMPLEMENTATION_PATCH_SHA256
        if f"/{packet_id}.patch" in relative
    )
    expected_patch = {
        "path": patch_relative,
        "sha256": CANDIDATE_IMPLEMENTATION_PATCH_SHA256[patch_relative],
    }
    if not json_exact_equal(request.get("patch"), expected_patch):
        raise ContractError(f"candidate {packet_id} request patch binding mismatch")


def _capture_implementation_worktree(
    rows: Sequence[Mapping[str, str]],
) -> dict[str, CapturedFile | None]:
    paths = _validated_candidate_paths(rows)
    return {
        relative: _capture_regular_or_absent(
            ROOT / relative, label="candidate implementation path"
        )
        for relative in paths
    }


def _require_exact_candidate_base(
    rows: Sequence[Mapping[str, str]],
    snapshot: Mapping[str, CapturedFile | None],
) -> None:
    paths = _validated_candidate_paths(rows)
    if set(snapshot) != set(paths):
        raise ContractError("candidate base worktree snapshot has wrong path inventory")
    for row in rows:
        captured = snapshot[row["path"]]
        actual = captured.identity.sha256 if captured is not None else "-"
        if actual != row["preimage_sha256"]:
            raise ContractError(
                f"candidate reconstruction requires exact C0007 preimage: "
                f"{row['path']}: expected {row['preimage_sha256']}, got {actual}"
            )


def _verify_implementation_worktree_unchanged(
    snapshot: Mapping[str, CapturedFile | None],
) -> None:
    for relative, captured in snapshot.items():
        path = ROOT / relative
        current = _capture_regular_or_absent(
            path, label="candidate implementation path"
        )
        if captured is None:
            if current is not None:
                raise ContractError(
                    f"real worktree changed during candidate reconstruction: {relative}"
                )
        else:
            if (
                current is None
                or current.identity != captured.identity
                or current.raw != captured.raw
            ):
                raise ContractError(
                    f"real worktree changed during candidate reconstruction: {relative}"
                )


def _ambient_git_environment() -> dict[str, str]:
    environment = {
        key: value
        for key, value in os.environ.items()
        if not key.upper().startswith("GIT_")
    }
    environment.update(
        {
            "GIT_CONFIG_GLOBAL": os.devnull,
            "GIT_CONFIG_NOSYSTEM": "1",
            "GIT_NO_REPLACE_OBJECTS": "1",
            "GIT_OPTIONAL_LOCKS": "0",
        }
    )
    return environment


def _run_git_bytes(
    arguments: Sequence[str],
    *,
    environment: Mapping[str, str],
    label: str,
) -> bytes:
    command = (
        "git",
        "-c",
        "core.autocrlf=false",
        "-c",
        "core.eol=lf",
        "-c",
        "core.safecrlf=false",
        *arguments,
    )
    try:
        result = subprocess.run(
            command,
            cwd=ROOT,
            env=dict(environment),
            check=False,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
        )
    except FileNotFoundError as error:
        raise ContractError("required executable not found: git") from error
    if result.returncode:
        details = b"\n".join(
            part.strip() for part in (result.stdout, result.stderr) if part.strip()
        ).decode("utf-8", errors="replace")
        raise ContractError(
            f"candidate Git {label} failed ({result.returncode})"
            + (f":\n{details}" if details else "")
        )
    return result.stdout


def _real_git_metadata_path(name: str) -> Path:
    raw = _run_git_bytes(
        ("rev-parse", "--git-path", name),
        environment=_ambient_git_environment(),
        label=f"resolve {name}",
    )
    try:
        rendered = raw.decode("utf-8", errors="strict").strip()
    except UnicodeDecodeError as error:
        raise ContractError(f"Git {name} path is not UTF-8") from error
    if not rendered or "\n" in rendered or "\r" in rendered:
        raise ContractError(f"Git returned an invalid {name} path")
    path = Path(rendered)
    return (path if path.is_absolute() else ROOT / path).resolve()


def _capture_real_git_observation() -> Mapping[str, bytes]:
    environment = _ambient_git_environment()
    return {
        "head": _run_git_bytes(
            ("rev-parse", "--verify", "HEAD"),
            environment=environment,
            label="observe real HEAD",
        ),
        "objects": _run_git_bytes(
            ("count-objects", "-v"),
            environment=environment,
            label="observe real objects",
        ),
        "refs": _run_git_bytes(
            ("show-ref", "--head"),
            environment=environment,
            label="observe real refs",
        ),
        "status": _run_git_bytes(
            ("status", "--porcelain=v1", "--untracked-files=all"),
            environment=environment,
            label="observe real status",
        ),
    }


def _candidate_index_entry(
    relative: str, *, environment: Mapping[str, str]
) -> tuple[str, str] | None:
    raw = _run_git_bytes(
        ("ls-files", "--stage", "--", relative),
        environment=environment,
        label=f"read index entry {relative}",
    )
    return _parse_candidate_index_entry(raw, relative)


def _parse_candidate_index_entry(
    raw: bytes, relative: str
) -> tuple[str, str] | None:
    if not raw:
        return None
    try:
        line = raw.decode("utf-8", errors="strict").rstrip("\n")
    except UnicodeDecodeError as error:
        raise ContractError(f"candidate index entry is not UTF-8: {relative}") from error
    if "\n" in line or "\t" not in line:
        raise ContractError(f"candidate index entry is ambiguous: {relative}")
    metadata, actual_path = line.split("\t", 1)
    fields = metadata.split(" ")
    if actual_path != relative or len(fields) != 3 or fields[2] != "0":
        raise ContractError(f"candidate index entry is malformed: {relative}")
    mode, object_id, _ = fields
    if mode != "100644" or not re.fullmatch(r"[0-9a-f]{40}", object_id):
        raise ContractError(f"candidate index entry has unsupported mode/OID: {relative}")
    return mode, object_id


def _candidate_diff_status(
    *, environment: Mapping[str, str]
) -> dict[str, str]:
    raw = _run_git_bytes(
        (
            "diff",
            "--cached",
            "--name-status",
            "--no-renames",
            C0007_CODE_SHA,
            "--",
        ),
        environment=environment,
        label="enumerate candidate diff",
    )
    try:
        text = raw.decode("utf-8", errors="strict")
    except UnicodeDecodeError as error:
        raise ContractError("candidate diff path output is not UTF-8") from error
    result: dict[str, str] = {}
    for line in text.splitlines():
        fields = line.split("\t")
        if len(fields) != 2 or fields[0] not in {"A", "M"}:
            raise ContractError(f"candidate diff has unsupported row: {line!r}")
        status, relative = fields
        if relative in result:
            raise ContractError(f"candidate diff repeats path: {relative}")
        result[relative] = status
    return result


def _require_candidate_diff_status(
    rows: Sequence[Mapping[str, str]],
    included_packets: Sequence[str],
    actual_status: Mapping[str, str],
) -> None:
    included = set(included_packets)
    if included - {"R0014", "R0015"}:
        raise ContractError("candidate diff requested an unknown packet")
    expected = {
        row["path"]: ("A" if row["preimage_blob_oid"] == "-" else "M")
        for row in rows
        if row["packet_id"] in included
    }
    if not json_exact_equal(dict(actual_status), expected):
        raise ContractError(
            f"candidate diff path/status mismatch: expected {expected!r}, "
            f"got {dict(actual_status)!r}"
        )


def reconstruct_candidate_postimage(
    inputs: GenerationInputs,
    *,
    temp_path_observer: Callable[[Path], None] | None = None,
) -> CandidatePostimage:
    """Apply pinned packets to an external index/object store and retain only bytes."""

    rows = implementation_postimage_rows(inputs)
    _validated_candidate_paths(rows)
    worktree_before = _capture_implementation_worktree(rows)
    _require_exact_candidate_base(rows, worktree_before)
    real_index_path = _real_git_metadata_path("index")
    real_objects_path = _real_git_metadata_path("objects")
    real_index_before = capture_file(real_index_path)
    real_git_before = _capture_real_git_observation()
    if not real_objects_path.is_dir():
        raise ContractError(f"real Git object directory is absent: {real_objects_path}")
    captured_artifacts = {
        item.path.relative_to(ROOT).as_posix(): item
        for item in inputs.review_artifacts
    }
    candidate_input_captures: dict[str, CapturedFile] = {}
    for relative, expected in CANDIDATE_IMPLEMENTATION_INPUT_SHA256.items():
        captured = captured_artifacts.get(relative)
        if captured is None or captured.identity.sha256 != expected:
            raise ContractError(
                f"candidate packet input capture mismatch: {relative}: expected {expected}"
            )
        candidate_input_captures[relative] = captured
    patch_captures = {
        relative: candidate_input_captures[relative]
        for relative in CANDIDATE_IMPLEMENTATION_PATCH_SHA256
    }
    for packet_id in ("R0014", "R0015"):
        request_relative = next(
            relative
            for relative in CANDIDATE_IMPLEMENTATION_INPUT_SHA256
            if f"/{packet_id}.json" in relative
        )
        request_capture = candidate_input_captures[request_relative]
        request = parse_strict_json_bytes(
            request_capture.raw,
            label=f"captured candidate {packet_id} request",
        )
        if request_capture.raw != canonical_json_bytes(request):
            raise ContractError(
                f"captured candidate {packet_id} request is not canonical JSON"
            )
        _validate_candidate_packet_request(request, packet_id, rows)

    bytes_by_path: dict[str, bytes] = {}
    try:
        with tempfile.TemporaryDirectory(
            prefix="numstability-supported-api-candidate-"
        ) as temp_name:
            temp = Path(temp_name).resolve()
            if temp == ROOT.resolve() or ROOT.resolve() in temp.parents:
                raise ContractError("candidate Git directory must be external to the repository")
            if temp_path_observer is not None:
                temp_path_observer(temp)
            index_path = temp / "candidate.index"
            object_path = temp / "objects"
            object_path.mkdir()
            git_environment = _ambient_git_environment()
            git_environment.update(
                {
                    "GIT_ALTERNATE_OBJECT_DIRECTORIES": str(real_objects_path),
                    "GIT_CONFIG_GLOBAL": os.devnull,
                    "GIT_CONFIG_NOSYSTEM": "1",
                    "GIT_INDEX_FILE": str(index_path),
                    "GIT_NO_REPLACE_OBJECTS": "1",
                    "GIT_OBJECT_DIRECTORY": str(object_path),
                    "GIT_OPTIONAL_LOCKS": "0",
                }
            )
            _run_git_bytes(
                ("read-tree", C0007_CODE_SHA),
                environment=git_environment,
                label="materialize exact C0007 index",
            )
            for row in rows:
                entry = _candidate_index_entry(
                    row["path"], environment=git_environment
                )
                if row["preimage_blob_oid"] == "-":
                    if entry is not None:
                        raise ContractError(
                            f"candidate base unexpectedly contains new path: {row['path']}"
                        )
                    continue
                if entry is None or entry[1] != row["preimage_blob_oid"]:
                    raise ContractError(
                        f"candidate base blob mismatch: {row['path']}"
                    )
                preimage = _run_git_bytes(
                    ("cat-file", "blob", entry[1]),
                    environment=git_environment,
                    label=f"read base blob {row['path']}",
                )
                if sha256_bytes(preimage) != row["preimage_sha256"]:
                    raise ContractError(
                        f"candidate base content mismatch: {row['path']}"
                    )

            included_packets: list[str] = []
            for packet_id in ("R0014", "R0015"):
                relative = next(
                    path
                    for path in CANDIDATE_IMPLEMENTATION_PATCH_SHA256
                    if f"/{packet_id}.patch" in path
                )
                patch_path = temp / f"{packet_id}.patch"
                patch_path.write_bytes(patch_captures[relative].raw)
                _run_git_bytes(
                    (
                        "apply",
                        "--cached",
                        "--check",
                        "--unidiff-zero",
                        "--whitespace=nowarn",
                        str(patch_path),
                    ),
                    environment=git_environment,
                    label=f"check {packet_id} patch",
                )
                _run_git_bytes(
                    (
                        "apply",
                        "--cached",
                        "--unidiff-zero",
                        "--whitespace=nowarn",
                        str(patch_path),
                    ),
                    environment=git_environment,
                    label=f"apply {packet_id} patch",
                )
                included_packets.append(packet_id)
                actual_status = _candidate_diff_status(environment=git_environment)
                _require_candidate_diff_status(
                    rows, included_packets, actual_status
                )

            for row in rows:
                entry = _candidate_index_entry(
                    row["path"], environment=git_environment
                )
                if entry is None:
                    raise ContractError(
                        f"candidate postimage index entry is absent: {row['path']}"
                    )
                payload = _run_git_bytes(
                    ("cat-file", "blob", entry[1]),
                    environment=git_environment,
                    label=f"read candidate blob {row['path']}",
                )
                bytes_by_path[row["path"]] = payload
            validate_candidate_postimage_bytes(rows, bytes_by_path)
    finally:
        verify_captured_files(
            (real_index_before, *candidate_input_captures.values())
        )
        _verify_implementation_worktree_unchanged(worktree_before)
        real_git_after = _capture_real_git_observation()
        if not json_exact_equal(real_git_after, real_git_before):
            changed = sorted(
                key
                for key in real_git_before
                if real_git_before[key] != real_git_after.get(key)
            )
            raise ContractError(
                "real Git HEAD/status/object/ref state changed during candidate "
                f"reconstruction: {changed!r}"
            )
    return CandidatePostimage(
        rows=tuple(dict(row) for row in rows),
        bytes_by_path=dict(bytes_by_path),
    )


def require_exact_candidate_staging_state(inputs: GenerationInputs) -> None:
    rows = implementation_postimage_rows(inputs)
    snapshot = _capture_implementation_worktree(rows)
    _require_exact_candidate_base(rows, snapshot)
    if classify_implementation_state() != "staging":
        raise ContractError(
            "candidate review generation requires the exact C0007 staging state"
        )


def _mask_span(mask: list[str], start: int, end: int, *, sentinel: bool) -> None:
    for index in range(start, end):
        if mask[index] not in "\r\n":
            mask[index] = " "
    if sentinel and start < end and mask[start] not in "\r\n":
        mask[start] = "~"


def _char_literal_end(text: str, start: int) -> int | None:
    if start and (
        is_lean_identifier_char(text[start - 1], initial=False)
        or text[start - 1] in "'Â»"
    ):
        return None
    index = start + 1
    escaped = False
    while index < len(text) and index - start <= 64:
        char = text[index]
        if char in "\r\n":
            return None
        if escaped:
            escaped = False
        elif char == "\\":
            escaped = True
        elif char == "'":
            return index + 1
        index += 1
    return None


def _mask_syntax_quotations(text: str, mask: list[str]) -> None:
    """Mask Lean `` `( ... )`` syntax data and reject assertion-like payloads."""

    index = 0
    while index + 1 < len(mask):
        if mask[index] == "«":
            closing = mask.index("»", index + 1)
            index = closing + 1
            continue
        if mask[index] != "`" or mask[index + 1] != "(":
            index += 1
            continue
        depth = 0
        end = index + 1
        while end < len(mask):
            char = mask[end]
            if char == "(":
                depth += 1
            elif char == ")":
                depth -= 1
                if depth == 0:
                    end += 1
                    break
            end += 1
        if depth:
            raise ContractError("unterminated Lean command/syntax quotation")
        payload = "".join(mask[index:end])
        if ("\n" in payload or "\r" in payload) and any(
            API_COMMAND_LINE_RE.fullmatch(line) is not None
            for line in payload.splitlines()
        ):
            raise ContractError(
                "assertion-looking line inside spanning Lean syntax quotation is unsupported"
            )
        _mask_span(mask, index, end, sentinel=True)
        index = end


def lean_code_mask(text: str) -> str:
    """Return a length/newline-preserving mask of executable Lean source.

    Comments and literal payloads cannot manufacture imports or API assertions.
    Literal openers retain one sentinel code token so a literal before an import
    closes the leading module header rather than becoming invisible whitespace.
    """

    mask = list(text)
    index = 0
    while index < len(text):
        pair = text[index : index + 2]
        if pair == "/-":
            start = index
            depth = 1
            index += 2
            while index < len(text) and depth:
                pair = text[index : index + 2]
                if pair == "/-":
                    depth += 1
                    index += 2
                elif pair == "-/":
                    depth -= 1
                    index += 2
                else:
                    index += 1
            if depth:
                raise ContractError("unterminated Lean block comment")
            _mask_span(mask, start, index, sentinel=False)
            continue
        if pair == "--":
            newline = text.find("\n", index + 2)
            end = len(text) if newline == -1 else newline
            _mask_span(mask, index, end, sentinel=False)
            index = end
            continue
        if text[index] == "«":
            end_marker = text.find("»", index + 1)
            if end_marker == -1:
                raise ContractError("unterminated Lean guillemet identifier")
            if end_marker == index + 1:
                raise ContractError("empty Lean guillemet identifier")
            end = end_marker + 1
            if "\n" in text[index:end] or "\r" in text[index:end]:
                _mask_span(mask, index, end, sentinel=True)
            index = end
            continue
        if text[index] == "»":
            raise ContractError("misplaced Lean closing guillemet")
        if text[index] == "r":
            marker = index + 1
            while marker < len(text) and text[marker] == "#":
                marker += 1
            if marker < len(text) and text[marker] == '"':
                hashes = text[index + 1 : marker]
                delimiter = '"' + hashes
                end_marker = text.find(delimiter, marker + 1)
                if end_marker == -1:
                    raise ContractError("unterminated Lean raw string")
                end = end_marker + len(delimiter)
                _mask_span(mask, index, end, sentinel=True)
                index = end
                continue
        if text[index] == '"':
            start = index
            index += 1
            escaped = False
            while index < len(text):
                char = text[index]
                if escaped:
                    escaped = False
                elif char == "\\":
                    escaped = True
                elif char == '"':
                    index += 1
                    break
                index += 1
            else:
                raise ContractError("unterminated Lean string")
            _mask_span(mask, start, index, sentinel=True)
            continue
        if text[index] == "'":
            end = _char_literal_end(text, index)
            if end is not None:
                _mask_span(mask, index, end, sentinel=True)
                index = end
                continue
        index += 1
    _mask_syntax_quotations(text, mask)
    return "".join(mask)


def remove_lean_comments(text: str) -> str:
    """Compatibility name for the strict executable-code mask."""

    return lean_code_mask(text)


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


def capture_sources() -> tuple[CapturedSource, ...]:
    before = tuple(path.relative_to(ROOT).as_posix() for path in lean_source_paths())
    captured: list[CapturedSource] = []
    for relative in before:
        path = ROOT / relative
        file_capture = capture_file(path)
        try:
            text = file_capture.raw.decode("utf-8-sig", errors="strict")
        except UnicodeDecodeError as error:
            raise ContractError(f"{path}: invalid UTF-8 Lean source: {error}") from error
        if _has_lone_surrogate(text):
            raise ContractError(f"{path}: Lean source contains a lone surrogate")
        captured.append(
            CapturedSource(
                path=path,
                relative=relative,
                raw=file_capture.raw,
                text=text,
                identity=file_capture.identity,
            )
        )
    after = tuple(path.relative_to(ROOT).as_posix() for path in lean_source_paths())
    if before != after:
        raise ContractError("Lean source inventory changed while it was captured")
    return tuple(captured)


def capture_generation_inputs() -> GenerationInputs:
    checker = capture_file(Path(__file__).resolve())
    tier_manifest = capture_json_document(TIER_MANIFEST)
    toolchain = tuple(
        capture_file(ROOT / name)
        for name in ("lake-manifest.json", "lakefile.toml", "lean-toolchain")
    )
    review_artifact_paths = sorted(
        set(R0014_ARTIFACT_SHA256)
        | set(IMPLEMENTATION_POSTIMAGE_LEDGERS)
        | set(CANDIDATE_IMPLEMENTATION_INPUT_SHA256)
    )
    review_artifacts = tuple(
        capture_file(ROOT / relative) for relative in review_artifact_paths
    )
    return GenerationInputs(
        checker=checker,
        tier_manifest=tier_manifest,
        toolchain_inputs=toolchain,
        review_artifacts=review_artifacts,
        sources=capture_sources(),
    )


def verify_generation_inputs(inputs: GenerationInputs) -> None:
    """Require exact path/content/metadata identity after build and extraction."""

    expected_paths = tuple(source.relative for source in inputs.sources)
    current_paths = tuple(path.relative_to(ROOT).as_posix() for path in lean_source_paths())
    if current_paths != expected_paths:
        raise ContractError("Lean source inventory changed during generation")
    expected_files = (
        (inputs.checker.path, inputs.checker.identity),
        (inputs.tier_manifest.capture.path, inputs.tier_manifest.capture.identity),
        *((item.path, item.identity) for item in inputs.toolchain_inputs),
        *((item.path, item.identity) for item in inputs.review_artifacts),
        *((item.path, item.identity) for item in inputs.sources),
    )
    for path, expected in expected_files:
        current = capture_file(path).identity
        if current != expected:
            raise ContractError(f"generation input changed during build/extraction: {path}")


def verify_captured_files(captures: Iterable[CapturedFile]) -> None:
    """Recheck exact input identities after all validation that consumed them."""

    seen: set[Path] = set()
    for capture in captures:
        if capture.path in seen:
            continue
        seen.add(capture.path)
        current = capture_file(capture.path).identity
        if current != capture.identity:
            raise ContractError(f"captured lifecycle input changed during validation: {capture.path}")


def _parse_import_target(target: str, *, line_number: int) -> str:
    try:
        parsed = parse_lean_qualified_name(target, 0)
    except ContractError as error:
        raise ContractError(f"line {line_number}: malformed import target: {error}") from error
    if parsed is None:
        raise ContractError(f"line {line_number}: import target is missing")
    components, end = parsed
    trailing = target[end:].strip()
    if trailing:
        raise ContractError(
            f"line {line_number}: trailing or second import target: {trailing!r}"
        )
    return render_lean_name(components)


def _parse_header_import_line(
    stripped: str, *, module_mode: bool, line_number: int
) -> tuple[str, bool]:
    """Parse the deliberately fail-closed one-line subset of Module.import."""

    parsed = re.fullmatch(
        r"(?:(?P<public>public)[ \t]+)?"
        r"(?:(?P<meta>meta)[ \t]+)?"
        r"import[ \t]+"
        r"(?:(?P<all>all)[ \t]+)?"
        r"(?P<target>.+)",
        stripped,
    )
    if parsed is None:
        raise ContractError(f"line {line_number}: unsupported import modifier/order")
    public = parsed.group("public") is not None
    meta = parsed.group("meta") is not None
    import_all = parsed.group("all") is not None
    if public and not module_mode:
        raise ContractError(
            f"line {line_number}: public import requires leading module header"
        )
    if meta and not module_mode:
        raise ContractError(
            f"line {line_number}: meta import requires leading module header"
        )
    if import_all and not module_mode:
        raise ContractError(
            f"line {line_number}: import all requires leading module header"
        )
    if public and import_all:
        raise ContractError(f"line {line_number}: public import all is unsupported")
    target = _parse_import_target(parsed.group("target"), line_number=line_number)
    exported = public or (not module_mode and not meta and not import_all)
    return target, exported


def parse_import_edges(code_mask: str) -> tuple[tuple[str, ...], tuple[str, ...]]:
    """Parse only the exact leading Lean ``Module.header`` import sequence."""

    imports: list[str] = []
    exported: list[str] = []
    module_mode = False
    module_seen = False
    prelude_seen = False
    import_seen = False
    for line_number, line in enumerate(code_mask.splitlines(), 1):
        stripped = line.strip()
        if not stripped:
            continue
        if stripped == "module":
            if module_seen or prelude_seen or import_seen:
                raise ContractError(f"line {line_number}: misplaced/duplicate module header")
            module_mode = True
            module_seen = True
            continue
        if stripped == "prelude":
            if prelude_seen or import_seen:
                raise ContractError(f"line {line_number}: misplaced/duplicate prelude")
            prelude_seen = True
            continue
        header_like = bool(
            re.match(r"^(?:import|module|prelude)\b", stripped)
            or re.match(r"^(?:public|private|meta)\b.*\bimport\b", stripped)
        )
        if header_like:
            target, is_exported = _parse_header_import_line(
                stripped, module_mode=module_mode, line_number=line_number
            )
            imports.append(target)
            if is_exported:
                exported.append(target)
            import_seen = True
            continue
        # The Module.header is closed by the first non-header code token.  Never
        # scan a later macro, quotation, structure field, or command for imports.
        break
    return tuple(imports), tuple(exported)


def scan_source_images(
    sources: Sequence[CapturedSource | VirtualSource],
) -> dict[str, Module]:
    modules: dict[str, Module] = {}
    for source in sources:
        relative = Path(source.relative)
        name = module_name(relative)
        code_mask = lean_code_mask(source.text)
        imports, exported_imports = parse_import_edges(code_mask)
        if name in modules:
            raise ContractError(f"duplicate Lean module: {name}")
        modules[name] = Module(
            name=name,
            path=source.path,
            imports=imports,
            exported_imports=exported_imports,
            text=source.text,
            code_mask=code_mask,
        )
    return modules


def scan_modules(inputs: GenerationInputs | None = None) -> dict[str, Module]:
    sources = inputs.sources if inputs is not None else capture_sources()
    return scan_source_images(sources)


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
        assertions = explicit_api_names(module.code_mask)
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


def selection_contract_rows(
    selections: Mapping[str, TestSelection],
) -> list[dict[str, Any]]:
    return sorted_contract_rows(
        {
            "assertion_occurrences": occurrences,
            "declaration": fqn,
            "surface": surface,
            "surface_kind": surface_kind,
            "test_module": test_module,
        }
        for fqn, selection in selections.items()
        for test_module, surface, surface_kind, occurrences in selection.test_evidence
    )


def candidate_modules_and_tiers(
    inputs: GenerationInputs,
    candidate: CandidatePostimage,
) -> tuple[dict[str, Module], Mapping[str, Any]]:
    """Build a virtual postimage graph; never consult candidate Lean artifacts."""

    validate_candidate_postimage_bytes(candidate.rows, candidate.bytes_by_path)
    row_index = {row["path"]: row for row in candidate.rows}
    source_index = {source.relative: source for source in inputs.sources}
    virtual_sources: dict[str, CapturedSource | VirtualSource] = dict(source_index)
    for relative, payload in candidate.bytes_by_path.items():
        if not (
            relative == "NumStability.lean"
            or relative == "NumStabilityTest.lean"
            or relative.startswith("NumStability/")
            or relative.startswith("NumStabilityTest/")
        ) or not relative.endswith(".lean"):
            continue
        row = row_index[relative]
        base_source = source_index.get(relative)
        if row["preimage_sha256"] == "-":
            if base_source is not None:
                raise ContractError(
                    f"candidate new Lean source already exists at C0007: {relative}"
                )
        elif (
            base_source is None
            or base_source.identity.sha256 != row["preimage_sha256"]
        ):
            raise ContractError(
                f"candidate Lean source preimage mismatch: {relative}"
            )
        try:
            text = payload.decode("utf-8-sig", errors="strict")
        except UnicodeDecodeError as error:
            raise ContractError(
                f"candidate Lean source is not strict UTF-8: {relative}"
            ) from error
        if _has_lone_surrogate(text):
            raise ContractError(
                f"candidate Lean source contains a lone surrogate: {relative}"
            )
        virtual_sources[relative] = VirtualSource(
            path=ROOT / relative,
            relative=relative,
            raw=payload,
            text=text,
        )

    tier_relative = TIER_MANIFEST.relative_to(ROOT).as_posix()
    tier_payload = candidate.bytes_by_path.get(tier_relative)
    tier_row = row_index.get(tier_relative)
    if tier_payload is None or tier_row is None:
        raise ContractError("candidate postimage does not contain tiers.json")
    if inputs.tier_manifest.capture.identity.sha256 != tier_row["preimage_sha256"]:
        raise ContractError("candidate tier manifest does not start at exact C0007")
    candidate_tiers = parse_strict_json_bytes(
        tier_payload, label="candidate in-memory tiers.json"
    )
    if sha256_bytes(tier_payload) != R0014_TIER_MANIFEST_SHA256:
        raise ContractError("candidate tier manifest hash does not match R0014")

    return (
        scan_source_images(
            tuple(virtual_sources[key] for key in sorted(virtual_sources))
        ),
        candidate_tiers,
    )


def validate_candidate_review_delta(
    *,
    baseline: Mapping[str, Any],
    base_modules: Mapping[str, Module],
    candidate_modules: Mapping[str, Module],
    base_tiers: Mapping[str, Any],
    candidate_tiers: Mapping[str, Any],
) -> None:
    """Prove the exact I01 source-graph delta without importing candidate modules."""

    base_selections, base_derivation = derive_test_selections(
        base_modules, base_tiers
    )
    candidate_selections, candidate_derivation = derive_test_selections(
        candidate_modules, candidate_tiers
    )
    entrypoints = tuple(baseline["derivation"]["documented_entrypoints"])
    require_c0007_ratchets(base_derivation, len(entrypoints))

    def occurrence_map(
        selections: Mapping[str, TestSelection],
    ) -> dict[tuple[str, str, str, str], int]:
        return {
            (
                str(row["declaration"]),
                str(row["test_module"]),
                str(row["surface"]),
                str(row["surface_kind"]),
            ): int(row["assertion_occurrences"])
            for row in selection_contract_rows(selections)
        }

    base_occurrences = occurrence_map(base_selections)
    candidate_occurrences = occurrence_map(candidate_selections)
    removed = {
        key: count - candidate_occurrences.get(key, 0)
        for key, count in base_occurrences.items()
        if candidate_occurrences.get(key, 0) < count
    }
    if removed:
        raise ContractError(
            f"candidate implementation removes/weakens C0007 test evidence: {removed!r}"
        )
    additive_rows = sorted_contract_rows(
        {
            "assertion_occurrences": count - base_occurrences.get(key, 0),
            "declaration": key[0],
            "test_module": key[1],
            "surface": key[2],
            "surface_kind": key[3],
        }
        for key, count in candidate_occurrences.items()
        if count > base_occurrences.get(key, 0)
    )
    expected_rows = approved_i01_evidence_json()
    if not json_exact_equal(additive_rows, expected_rows):
        raise ContractError(
            "candidate test evidence delta is not the exact reviewed 5-module/9-assertion set"
        )
    expected_modules = {row["test_module"] for row in expected_rows}
    base_test_modules = {key[1] for key in base_occurrences}
    candidate_test_modules = {key[1] for key in candidate_occurrences}
    if candidate_test_modules - base_test_modules != expected_modules:
        raise ContractError(
            "candidate one-import test-module delta is not the exact reviewed five modules"
        )
    if set(candidate_selections) - set(base_selections) != APPROVED_I01_NEW_FQNS:
        raise ContractError(
            "candidate selected-declaration delta is not exactly problem2_9Source"
        )
    exact_count_deltas = {
        "assertion_count": 9,
        "isolated_test_module_count": 5,
        "selected_declaration_count": 1,
    }
    for field, expected_delta in exact_count_deltas.items():
        actual_delta = candidate_derivation[field] - base_derivation[field]
        if type(actual_delta) is not int or actual_delta != expected_delta:
            raise ContractError(
                f"candidate {field} delta: expected {expected_delta}, got {actual_delta}"
            )

    baseline_rows = index_rows(baseline.get("declarations"), "fqn")
    base_entrypoint_closures = entrypoint_closures(base_modules, entrypoints)
    candidate_entrypoint_closures = entrypoint_closures(
        candidate_modules, entrypoints
    )
    for fqn, destination in APPROVED_I01_OWNER_DESTINATIONS.items():
        baseline_row = baseline_rows.get(fqn)
        if baseline_row is not None:
            frozen_reachability = baseline_row.get(
                "expected_entrypoint_reachability"
            )
        else:
            frozen_reachability = reachable_entrypoints_for_owner(
                APPROVED_I01_C0007_OWNER_MODULES[fqn],
                base_entrypoint_closures,
            )
        candidate_reachability = reachable_entrypoints_for_owner(
            destination, candidate_entrypoint_closures
        )
        if not json_exact_equal(candidate_reachability, frozen_reachability):
            raise ContractError(
                f"{fqn}: candidate destination entrypoint reachability differs "
                f"from exact C0007: expected {frozen_reachability!r}, "
                f"got {candidate_reachability!r}"
            )
    candidate_owners: dict[str, str] = {}
    for fqn in sorted({row["declaration"] for row in expected_rows}):
        if fqn in APPROVED_I01_OWNER_DESTINATIONS:
            candidate_owners[fqn] = APPROVED_I01_OWNER_DESTINATIONS[fqn]
            continue
        baseline_row = baseline_rows.get(fqn)
        owner = baseline_row.get("owner_module") if baseline_row else None
        if type(owner) is not str or not owner:
            raise ContractError(
                f"candidate evidence declaration has no exact C0007 owner: {fqn}"
            )
        candidate_owners[fqn] = owner
    surface_closures: dict[str, set[str]] = {}
    for row in expected_rows:
        surface = row["surface"]
        if surface not in candidate_modules:
            raise ContractError(
                f"reviewed additive evidence surface is not a candidate module: {surface}"
            )
        surface_closures.setdefault(
            surface, exported_api_closure(candidate_modules, (surface,))
        )
        owner = candidate_owners[row["declaration"]]
        if owner not in surface_closures[surface]:
            raise ContractError(
                f"{row['declaration']}: approved destination owner {owner} is not "
                f"reachable from candidate evidence surface {surface}"
            )


def c0007_ratchet_failures(
    derivation: Mapping[str, Any], documented_entrypoint_count: Any
) -> list[str]:
    expected = {
        "assertion_count": C0007_ASSERTION_COUNT,
        "selected_declaration_count": C0007_SELECTED_DECLARATION_COUNT,
        "isolated_test_module_count": C0007_ISOLATED_TEST_MODULE_COUNT,
        "contract_sha256": C0007_TEST_CONTRACT_SHA256,
    }
    failures: list[str] = []
    for field, value in expected.items():
        actual = derivation.get(field)
        if not json_exact_equal(actual, value):
            failures.append(
                f"C0007 ratchet {field}: expected {value!r}, got {actual!r}"
            )
    if not json_exact_equal(
        documented_entrypoint_count, C0007_DOCUMENTED_ENTRYPOINT_COUNT
    ):
        failures.append(
            "C0007 ratchet documented_entrypoint_count: expected "
            f"{C0007_DOCUMENTED_ENTRYPOINT_COUNT}, got {documented_entrypoint_count!r}"
        )
    return failures


def require_c0007_ratchets(
    derivation: Mapping[str, Any], documented_entrypoint_count: Any
) -> None:
    failures = c0007_ratchet_failures(derivation, documented_entrypoint_count)
    if failures:
        raise ContractError("C0007 parser/selection ratchet failure:\n" + "\n".join(failures))


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
        normalized = module.text.replace("\r\n", "\n").replace("\r", "\n")
        digest.update(relative.encode("utf-8"))
        digest.update(b"\0")
        digest.update(normalized.encode("utf-8"))
        digest.update(b"\0")
    return digest.hexdigest().upper()


_ENVIRONMENT_BUILD_CACHE_KEY: tuple[Any, ...] | None = None
_ALLOWED_DIRTY_GOVERNED_PATHS: set[str] = set()


def allow_exact_implementation_dirty_paths(enabled: bool) -> None:
    global _ALLOWED_DIRTY_GOVERNED_PATHS
    _ALLOWED_DIRTY_GOVERNED_PATHS = (
        {row["path"] for row in implementation_postimage_rows()} if enabled else set()
    )


def environment_build_key(inputs: GenerationInputs) -> tuple[Any, ...]:
    """Bind a cached Lake build to exact source inventory and file identities."""

    return (
        tuple(
            (source.relative, source.identity)
            for source in inputs.sources
        ),
        tuple(
            (item.path.relative_to(ROOT).as_posix(), item.identity)
            for item in inputs.toolchain_inputs
        ),
    )


def current_environment_build_key(inputs: GenerationInputs) -> tuple[Any, ...]:
    expected_paths = tuple(source.relative for source in inputs.sources)
    current_paths = tuple(path.relative_to(ROOT).as_posix() for path in lean_source_paths())
    if current_paths != expected_paths:
        raise ContractError("Lean source inventory changed before/during cached build")
    current_sources = tuple(
        (relative, capture_file(ROOT / relative).identity)
        for relative in current_paths
    )
    current_toolchain = tuple(
        (
            item.path.relative_to(ROOT).as_posix(),
            capture_file(item.path).identity,
        )
        for item in inputs.toolchain_inputs
    )
    return current_sources, current_toolchain


def _ensure_build_for_exact_key(
    captured_key: tuple[Any, ...],
    current_key: Callable[[], tuple[Any, ...]],
    build: Callable[[], None],
) -> bool:
    """Run once per exact key, never trusting a stale/reverted global cache."""

    global _ENVIRONMENT_BUILD_CACHE_KEY
    before = current_key()
    if before != captured_key:
        raise ContractError("captured environment build identity is already stale")
    if _ENVIRONMENT_BUILD_CACHE_KEY == captured_key:
        return False
    # A different-key build may partially rewrite shared Lake outputs before it
    # fails.  Invalidate the prior identity before starting so a later source
    # revert cannot revive a stale successful-build claim.
    _ENVIRONMENT_BUILD_CACHE_KEY = None
    build()
    after = current_key()
    if after != captured_key:
        raise ContractError("environment build inputs changed while Lake was running")
    _ENVIRONMENT_BUILD_CACHE_KEY = captured_key
    return True


def ensure_environment_built(inputs: GenerationInputs) -> None:
    """Build the clean exact-identity test root before consulting environment data."""

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
            env=_ambient_git_environment(),
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
    def build() -> None:
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
                "required exact-identity NumStabilityTest build failed "
                f"({result.returncode}):\n{details}"
            )

    captured_key = environment_build_key(inputs)
    _ensure_build_for_exact_key(
        captured_key,
        lambda: current_environment_build_key(inputs),
        build,
    )


def _decode_environment_payload_block(
    data: bytes, *, final: bool, tail: bytes, digest: Any
) -> bytes:
    combined = tail + data
    next_tail = b""
    if not final:
        last_percent = combined.rfind(b"%")
        if last_percent >= max(0, len(combined) - 2):
            next_tail = combined[last_percent:]
            combined = combined[:last_percent]
    residual = combined
    for escape in (b"%25", b"%09", b"%0D", b"%0A"):
        residual = residual.replace(escape, b"")
    if b"%" in residual:
        offset = combined.find(b"%")
        raise ContractError(
            f"invalid exact type-evidence percent escape near payload offset {offset}"
        )
    # Decode %25 last: an original literal "%09" is encoded as "%2509" and
    # must not be decoded a second time into a tab.
    decoded = (
        combined.replace(b"%09", b"\t")
        .replace(b"%0D", b"\r")
        .replace(b"%0A", b"\n")
        .replace(b"%25", b"%")
    )
    digest.update(decoded)
    if final and next_tail:
        raise ContractError("truncated exact type-evidence percent escape")
    return next_tail


def parse_environment_tsv(
    path: Path,
    selected_names: Sequence[str],
    *,
    chunk_bytes: int = TSV_CHUNK_BYTES,
) -> EnvironmentSnapshot:
    """Parse extractor output with bounded buffers and streaming type hashes."""

    if chunk_bytes <= 0 or chunk_bytes > TSV_CHUNK_BYTES:
        raise ContractError(
            f"environment TSV chunk size must be in 1..{TSV_CHUNK_BYTES}"
        )
    selected: dict[str, EnvironmentDeclaration] = {}
    visible_by_owner: dict[str, list[str]] = {}
    visible_names: set[str] = set()
    raw_digest = hashlib.sha256()
    raw_bytes = 0
    record_count = 0
    max_record_bytes = 0
    format_seen = False

    prefix = bytearray()
    record_bytes = 0
    pending_meta: tuple[str, str, str, bool, str] | None = None
    payload_digest: Any | None = None
    payload_utf8: Any | None = None
    payload_escape_tail = b""
    payload_raw_bytes = 0

    def feed_payload(data: bytes, *, final: bool) -> None:
        nonlocal payload_escape_tail, payload_raw_bytes
        assert payload_digest is not None and payload_utf8 is not None
        if any(marker in data for marker in (b"\t", b"\r", b"\n", b"\0")):
            raise ContractError("environment selected payload contains raw control bytes")
        try:
            payload_utf8.decode(data, final=final)
        except UnicodeDecodeError as error:
            raise ContractError(
                f"environment selected payload contains invalid UTF-8: {error}"
            ) from error
        payload_raw_bytes += len(data)
        payload_escape_tail = _decode_environment_payload_block(
            data,
            final=final,
            tail=payload_escape_tail,
            digest=payload_digest,
        )
        if final and payload_escape_tail:
            raise ContractError("truncated exact type-evidence percent escape")

    def maybe_start_selected_payload() -> None:
        nonlocal prefix, pending_meta, payload_digest, payload_utf8
        if not prefix.startswith(b"selected\t"):
            return
        position = -1
        for _ in range(6):
            position = prefix.find(b"\t", position + 1)
            if position == -1:
                if len(prefix) > TSV_PREFIX_BYTES:
                    raise ContractError("environment selected-row prefix exceeds cap")
                return
        metadata_raw = bytes(prefix[:position])
        remainder = bytes(prefix[position + 1 :])
        try:
            fields = metadata_raw.decode("utf-8", errors="strict").split("\t")
        except UnicodeDecodeError as error:
            raise ContractError(
                f"environment selected-row prefix contains invalid UTF-8: {error}"
            ) from error
        if len(fields) != 6 or fields[0] != "selected":
            raise ContractError("environment selected row has malformed prefix fields")
        _, fqn, owner, kind, protected_text, visibility = fields
        if not fqn or not owner or not kind:
            raise ContractError("environment selected row has an empty metadata field")
        if fqn in selected:
            raise ContractError(f"duplicate selected environment row: {fqn}")
        if protected_text not in {"true", "false"}:
            raise ContractError(f"invalid protected flag for {fqn}: {protected_text!r}")
        if visibility not in {"public", "private", "internal"}:
            raise ContractError(f"invalid declaration visibility for {fqn}: {visibility!r}")
        pending_meta = (fqn, owner, kind, protected_text == "true", visibility)
        payload_digest = hashlib.sha256()
        payload_utf8 = codecs.getincrementaldecoder("utf-8")(errors="strict")
        prefix = bytearray()
        if remainder:
            feed_payload(remainder, final=False)

    def feed_record(data: bytes) -> None:
        nonlocal record_bytes, prefix
        record_bytes += len(data)
        if pending_meta is not None:
            feed_payload(data, final=False)
            return
        prefix.extend(data)
        maybe_start_selected_payload()
        if pending_meta is None and len(prefix) > TSV_SMALL_ROW_BYTES:
            raise ContractError("environment format/visibility row exceeds cap")

    def finish_record() -> None:
        nonlocal prefix, record_bytes, record_count, max_record_bytes, format_seen
        nonlocal pending_meta, payload_digest, payload_utf8, payload_escape_tail
        nonlocal payload_raw_bytes
        record_count += 1
        max_record_bytes = max(max_record_bytes, record_bytes + 1)
        if pending_meta is not None:
            feed_payload(b"", final=True)
            if payload_raw_bytes == 0:
                raise ContractError("environment selected row has an empty type payload")
            fqn, owner, kind, protected, visibility = pending_meta
            assert payload_digest is not None
            selected[fqn] = EnvironmentDeclaration(
                fqn=fqn,
                owner_module=owner,
                kind=kind,
                protected=protected,
                visibility=visibility,
                normalized_type_sha256=payload_digest.hexdigest().upper(),
            )
        else:
            try:
                fields = bytes(prefix).decode("utf-8", errors="strict").split("\t")
            except UnicodeDecodeError as error:
                raise ContractError(
                    f"environment row {record_count} contains invalid UTF-8: {error}"
                ) from error
            if fields == ["format", "1"]:
                if format_seen or record_count != 1:
                    raise ContractError("duplicate or misplaced environment format row")
                format_seen = True
            elif len(fields) == 3 and fields[0] == "visible":
                _, fqn, owner = fields
                if not format_seen:
                    raise ContractError("environment visibility row precedes format row")
                if not fqn or not owner:
                    raise ContractError("environment visibility row has an empty field")
                if fqn in visible_names:
                    raise ContractError(f"duplicate visible environment row: {fqn}")
                visible_names.add(fqn)
                visible_by_owner.setdefault(owner, []).append(fqn)
            else:
                raise ContractError(
                    f"invalid environment row {record_count}: {fields[:3]!r}"
                )
        prefix = bytearray()
        record_bytes = 0
        pending_meta = None
        payload_digest = None
        payload_utf8 = None
        payload_escape_tail = b""
        payload_raw_bytes = 0

    try:
        with path.open("rb") as handle:
            opened = os.fstat(handle.fileno())
            if not stat.S_ISREG(opened.st_mode):
                raise ContractError("environment extractor output is not a regular file")
            while True:
                chunk = handle.read(chunk_bytes)
                if not chunk:
                    break
                raw_digest.update(chunk)
                raw_bytes += len(chunk)
                if b"\r" in chunk or b"\0" in chunk:
                    raise ContractError("environment TSV contains CR or NUL bytes")
                start = 0
                while True:
                    newline = chunk.find(b"\n", start)
                    if newline == -1:
                        feed_record(chunk[start:])
                        break
                    feed_record(chunk[start:newline])
                    finish_record()
                    start = newline + 1
            closed = os.fstat(handle.fileno())
        current = path.stat()
    except ContractError:
        raise
    except OSError as error:
        raise ContractError(f"cannot parse environment TSV {path}: {error}") from error
    if _stat_signature(opened) != _stat_signature(closed) or _stat_signature(
        opened
    ) != _stat_signature(current):
        raise ContractError("environment TSV changed while it was consumed")
    if raw_bytes != opened.st_size:
        raise ContractError("environment TSV byte accounting mismatch")
    if record_bytes or prefix or pending_meta is not None:
        raise ContractError("environment TSV is missing its final LF")
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
    unexpected = sorted(set(selected) - set(selected_names))
    if unexpected:
        raise ContractError(
            "environment returned unrequested selected declarations: "
            + ", ".join(unexpected[:10])
        )
    return EnvironmentSnapshot(
        selected=selected,
        public_names_by_owner={
            owner: tuple(sorted(names))
            for owner, names in sorted(visible_by_owner.items())
        },
        raw_tsv_bytes=raw_bytes,
        raw_tsv_sha256=raw_digest.hexdigest().upper(),
        physical_record_count=record_count,
        max_physical_record_bytes=max_record_bytes,
    )


def run_environment_extractor(
    selected_names: Sequence[str],
    entrypoints: Sequence[str],
    *,
    inputs: GenerationInputs,
) -> EnvironmentSnapshot:
    ensure_environment_built(inputs)
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
        snapshot = parse_environment_tsv(output, selected_names)
        print(
            "supported-API environment TSV: "
            f"raw_bytes={snapshot.raw_tsv_bytes}, "
            f"sha256={snapshot.raw_tsv_sha256}, "
            f"records={snapshot.physical_record_count}, "
            f"max_record_bytes={snapshot.max_physical_record_bytes}"
        )
        return snapshot


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
                env=_ambient_git_environment(),
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
    inputs: GenerationInputs | None = None,
) -> dict[str, Any]:
    if inputs is None:
        inputs = capture_generation_inputs()
    tiers = inputs.tier_manifest.value
    modules = scan_modules(inputs)
    require_exact_c0007_generation_state(modules, checkpoint_code_sha)
    selections, test_derivation = derive_test_selections(modules, tiers)
    entrypoints = documented_entrypoints(tiers)
    require_c0007_ratchets(test_derivation, len(entrypoints))
    env = run_environment_extractor(tuple(selections), entrypoints, inputs=inputs)
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

    result = {
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
            "checker_sha256": inputs.checker.identity.sha256,
            "environment_extractor_sha256": sha256_bytes(
                LEAN_EXTRACTOR_SOURCE.encode("utf-8")
            ),
            "protected_selected_declaration_count": sum(
                1 for row in declarations if row["protected"]
            ),
            "tier_manifest_sha256": inputs.tier_manifest.capture.identity.sha256,
            "toolchain_inputs": {
                item.path.name: item.identity.sha256
                for item in inputs.toolchain_inputs
            },
            "type_normalization": TYPE_NORMALIZATION,
            "visibility_exclusion_policy": VISIBILITY_EXCLUSION_POLICY,
            "visibility_guard_policy": VISIBILITY_GUARD_POLICY,
        },
        "record_kind": "supported_api_baseline",
        "schema_version": SCHEMA_VERSION,
        "visibility_guard": visibility_guard(closures, env.public_names_by_owner),
    }
    verify_generation_inputs(inputs)
    return result


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


def validate_baseline_schema(
    baseline: Mapping[str, Any], *, inputs: GenerationInputs | None = None
) -> list[str]:
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
    if not json_exact_equal(baseline.get("schema_version"), SCHEMA_VERSION):
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
            if not json_exact_equal(baseline_facts.get(field), expected):
                failures.append(
                    f"baseline.{field}: expected exact C0007 {expected}, "
                    f"got {baseline_facts.get(field)!r}"
                )
    entrypoints = require_sorted_unique_strings(
        derivation.get("documented_entrypoints"),
        "derivation.documented_entrypoints",
        failures,
    )
    failures.extend(c0007_ratchet_failures(derivation, len(entrypoints)))
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
    checker_sha256 = (
        inputs.checker.identity.sha256
        if inputs is not None
        else capture_file(Path(__file__).resolve()).identity.sha256
    )
    expected_input_hashes = {
        "checker_sha256": checker_sha256,
        "environment_extractor_sha256": sha256_bytes(
            LEAN_EXTRACTOR_SOURCE.encode("utf-8")
        ),
        "tier_manifest_sha256": C0007_TIER_MANIFEST_SHA256,
    }
    for field, expected in expected_input_hashes.items():
        if not json_exact_equal(derivation.get(field), expected):
            failures.append(
                f"derivation.{field}: pinned input drift: expected {expected}, "
                f"got {derivation.get(field)!r}"
            )
    toolchain_captures = (
        inputs.toolchain_inputs
        if inputs is not None
        else tuple(
            capture_file(ROOT / name)
            for name in ("lake-manifest.json", "lakefile.toml", "lean-toolchain")
        )
    )
    expected_toolchain_inputs = {
        item.path.name: item.identity.sha256 for item in toolchain_captures
    }
    if not json_exact_equal(derivation.get("toolchain_inputs"), expected_toolchain_inputs):
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
        if not json_exact_equal(derivation.get(field), expected):
            failures.append(
                f"derivation.{field}: expected reconstructed value {expected!r}, "
                f"got {derivation.get(field)!r}"
            )
    expected_protected_count = sum(
        1 for row in declarations if isinstance(row, dict) and row.get("protected") is True
    )
    if not json_exact_equal(
        derivation.get("protected_selected_declaration_count"), expected_protected_count
    ):
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


def pinned_artifact_rows(
    mapping: Mapping[str, str], *, inputs: GenerationInputs | None = None
) -> list[dict[str, str]]:
    rows: list[dict[str, str]] = []
    captured = (
        {
            item.path.relative_to(ROOT).as_posix(): item
            for item in inputs.review_artifacts
        }
        if inputs is not None
        else {}
    )
    for relative, expected in sorted(mapping.items()):
        artifact = captured.get(relative) or capture_file(ROOT / relative)
        actual = artifact.identity.sha256
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


def require_exact_c0007_owner_environment(
    environment: EnvironmentSnapshot,
    expected_owners: Mapping[str, str],
) -> None:
    if set(environment.selected) != set(expected_owners):
        raise ContractError(
            "exact C0007 owner extraction returned the wrong declaration inventory"
        )
    for fqn, expected_owner in expected_owners.items():
        declaration = environment.selected[fqn]
        if declaration.owner_module != expected_owner:
            raise ContractError(
                f"{fqn}: exact C0007 owner must be {expected_owner}, got "
                f"{declaration.owner_module}; candidate/stale artifacts are forbidden"
            )


def derive_exact_c0007_review_environment_facts(
    baseline: Mapping[str, Any],
    modules: Mapping[str, Module] | None = None,
    inputs: GenerationInputs | None = None,
) -> tuple[list[dict[str, Any]], list[dict[str, Any]]]:
    """Freshly derive the R0014 declaration and owner facts at exact C0007.

    ``problem2_9Source`` exists at C0007 but is not selected by that test contract.
    Import only its exact present C0007 owner source to bind elaborated metadata;
    never import a candidate destination through the shared Lake search path.
    Separately replay the pinned implementation in an external Git object/index
    store and derive all candidate test/surface facts from its in-memory sources.
    """

    if modules is None:
        if inputs is None:
            inputs = capture_generation_inputs()
        modules = scan_modules(inputs)
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
    if inputs is None:
        raise ContractError("C0007 review extraction requires captured generation inputs")

    candidate = reconstruct_candidate_postimage(inputs)
    candidate_modules, candidate_tiers = candidate_modules_and_tiers(
        inputs, candidate
    )
    validate_candidate_review_delta(
        baseline=baseline,
        base_modules=modules,
        candidate_modules=candidate_modules,
        base_tiers=inputs.tier_manifest.value,
        candidate_tiers=candidate_tiers,
    )

    exact_owner_imports = tuple(
        sorted(
            {
                APPROVED_I01_C0007_OWNER_MODULES[fqn]
                for fqn in APPROVED_I01_NEW_FQNS
            }
        )
    )
    missing_owner_modules = [
        owner for owner in exact_owner_imports if owner not in modules
    ]
    if missing_owner_modules:
        raise ContractError(
            "exact C0007 declaration owner source is absent: "
            + ", ".join(missing_owner_modules)
        )
    env = run_environment_extractor(
        sorted(APPROVED_I01_NEW_FQNS), exact_owner_imports, inputs=inputs
    )
    require_exact_c0007_owner_environment(
        env,
        {
            fqn: APPROVED_I01_C0007_OWNER_MODULES[fqn]
            for fqn in APPROVED_I01_NEW_FQNS
        },
    )
    approved_rows = approved_i01_evidence_json()
    declaration_rows = []
    for fqn in sorted(APPROVED_I01_NEW_FQNS):
        declaration = env.selected[fqn]
        if declaration.visibility != "public":
            raise ContractError(f"reviewed additive declaration is not public: {fqn}")
        evidence_rows = [
            row for row in approved_rows if row["declaration"] == fqn
        ]
        declaration_rows.append(
            declaration_row_from_evidence(
                declaration,
                evidence_rows,
                closures,
            )
        )
    baseline_rows = index_rows(baseline.get("declarations"), "fqn")
    pre_move_owners: dict[str, str] = {}
    for fqn in APPROVED_I01_OWNER_DESTINATIONS:
        if fqn in APPROVED_I01_NEW_FQNS:
            owner = env.selected[fqn].owner_module
        else:
            baseline_row = baseline_rows.get(fqn)
            owner = baseline_row.get("owner_module") if baseline_row else None
        expected_owner = APPROVED_I01_C0007_OWNER_MODULES[fqn]
        if owner != expected_owner:
            raise ContractError(
                f"{fqn}: exact C0007 pre-move owner mismatch: expected "
                f"{expected_owner}, got {owner!r}"
            )
        pre_move_owners[fqn] = expected_owner
    approved_owner_moves = [
        {
            "fqn": fqn,
            "from_owner_module": pre_move_owners[fqn],
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
    if not json_exact_equal(
        review.get("approved_additive_declarations"), list(expected_declarations)
    ):
        failures.append(
            "review.approved_additive_declarations: metadata does not exact-match "
            "the freshly extracted C0007 environment"
        )
    if not json_exact_equal(
        review.get("approved_owner_moves"), list(expected_owner_moves)
    ):
        failures.append(
            "review.approved_owner_moves: from-owner facts do not exact-match the "
            "freshly extracted C0007 environment"
        )
    return failures


def validate_review_against_exact_c0007_environment(
    review: Mapping[str, Any],
    baseline: Mapping[str, Any],
    *,
    inputs: GenerationInputs | None = None,
) -> list[str]:
    """Fail closed on forged pending machine facts before I01 activation."""

    expected_declarations, expected_owner_moves = (
        derive_exact_c0007_review_environment_facts(baseline, inputs=inputs)
    )
    return validate_review_environment_facts(
        review, expected_declarations, expected_owner_moves
    )


def validate_exact_pending_review(
    review: Mapping[str, Any], expected: Mapping[str, Any]
) -> list[str]:
    """Require type-exact equality with the complete freshly generated record."""

    if json_exact_equal(review, expected):
        return []
    failures = [
        "pending supported-API review does not exact-match the freshly rendered "
        "canonical C0007 record"
    ]
    if not json_exact_equal(review.get("rationale"), expected.get("rationale")):
        failures.append("pending supported-API review rationale drift")
    return failures


def build_additive_review(
    baseline: Mapping[str, Any], *, inputs: GenerationInputs | None = None
) -> dict[str, Any]:
    if inputs is None:
        inputs = capture_generation_inputs()
    require_exact_candidate_staging_state(inputs)
    failures = validate_baseline_schema(baseline, inputs=inputs)
    if failures:
        raise ContractError("cannot review an invalid baseline:\n" + "\n".join(failures))
    declaration_rows, approved_owner_moves = (
        derive_exact_c0007_review_environment_facts(baseline, inputs=inputs)
    )
    approved_rows = approved_i01_evidence_json()
    request_artifacts = pinned_artifact_rows(R0014_ARTIFACT_SHA256, inputs=inputs)
    implementation_ledgers = pinned_artifact_rows(
        IMPLEMENTATION_POSTIMAGE_LEDGERS, inputs=inputs
    )
    result = {
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
        "rationale": PENDING_REVIEW_RATIONALE,
        "record_kind": "supported_api_freeze_review",
        "reviewed_at_utc": None,
        "reviewer": None,
        "requested_reviewer_role": "primary-human",
        "schema_version": SCHEMA_VERSION,
    }
    verify_generation_inputs(inputs)
    require_exact_candidate_staging_state(inputs)
    return result


def validate_review_schema(
    review: Mapping[str, Any],
    baseline: Mapping[str, Any],
    *,
    inputs: GenerationInputs | None = None,
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
        if not json_exact_equal(review.get(field), expected):
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
    if not json_exact_equal(review.get("baseline_inputs"), expected_baseline_inputs):
        failures.append("review.baseline_inputs: does not exact-bind C0007 inputs")
    if not json_exact_equal(review.get("rationale"), PENDING_REVIEW_RATIONALE):
        failures.append("review.rationale: expected exact pending machine rationale")
    decision = review.get("decision")
    if decision is not None:
        failures.append("review.decision: machine fact record must remain null/pending")
    if review.get("reviewer") is not None or review.get("reviewed_at_utc") is not None:
        failures.append("review: machine fact record must not claim a reviewer or review time")

    approved_evidence = review.get("approved_additive_test_evidence")
    if not json_exact_equal(approved_evidence, approved_i01_evidence_json()):
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
        if not json_exact_equal(row, {
            "fqn": fqn,
            "from_owner_module": source_row.get("owner_module"),
            "to_owner_module": destination,
        }):
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
            IMPLEMENTATION_POSTIMAGE_LEDGERS, inputs=inputs
        ),
        "implementation_id": "I01",
        "request_id": "R0014",
        "request_artifacts": pinned_artifact_rows(
            R0014_ARTIFACT_SHA256, inputs=inputs
        ),
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
        if not json_exact_equal(activation_scope.get(field), expected):
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
        if not json_exact_equal(evidence, expected_evidence):
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


def require_exact_ci_recovery_completion_checker_sha(actual_sha256: str) -> None:
    """Reject placeholders and drift while accepting the frozen checker itself."""

    if not re.fullmatch(r"[0-9A-F]{64}", CI_RECOVERY_COMPLETION_CHECKER_SHA256):
        raise ContractError(
            "completion checker final SHA-256 placeholder has not been replaced"
        )
    if actual_sha256 != CI_RECOVERY_COMPLETION_CHECKER_SHA256:
        raise ContractError(
            "current completion checker drift: expected exact "
            f"{CI_RECOVERY_COMPLETION_CHECKER_SHA256}, got {actual_sha256}"
        )


def capture_lifecycle_file_hashes(
    *,
    baseline: JsonDocument,
    review: JsonDocument,
    authorization: JsonDocument,
    inputs: GenerationInputs,
) -> tuple[
    dict[str, str], dict[str, CapturedFile], tuple[CapturedFile, ...]
]:
    """Capture the seven current recovery artifacts and separate P history."""

    completion = capture_file(ROOT / COMPLETION_CHECKER_RELATIVE)
    manifest = capture_file(ROOT / BOUNDED_MANIFEST_RELATIVE)
    correction = capture_file(ROOT / FULL_TESTS_CORRECTION_RELATIVE)
    workflow = capture_file(ROOT / WORKFLOW_RELATIVE)
    historical_packet_artifacts = tuple(
        capture_file(ROOT / relative)
        for relative in HISTORICAL_P_PACKET_ARTIFACTS
    )
    manifest_failures = validate_ci_only_recovery_manifest(manifest)
    if manifest_failures:
        raise ContractError("invalid CI-only recovery manifest:\n" + "\n".join(manifest_failures))
    require_exact_ci_recovery_completion_checker_sha(completion.identity.sha256)
    if workflow.identity.sha256 != CI_ONLY_RECOVERY_WORKFLOW_SHA256:
        raise ContractError(
            "current CI-only recovery workflow drift: expected exact "
            f"{CI_ONLY_RECOVERY_WORKFLOW_SHA256}, got {workflow.identity.sha256}"
        )
    if authorization.capture.identity.sha256 != CI_ONLY_RECOVERY_AUTHORIZATION_SHA256:
        raise ContractError(
            "current CI-only recovery authorization drift: expected exact "
            f"{CI_ONLY_RECOVERY_AUTHORIZATION_SHA256}, got "
            f"{authorization.capture.identity.sha256}"
        )
    for capture in historical_packet_artifacts:
        relative = capture.path.relative_to(ROOT).as_posix()
        expected = HISTORICAL_P_PACKET_ARTIFACTS[relative]
        if (
            capture.identity.sha256 != expected["sha256"]
            or capture.identity.size != expected["byte_count"]
        ):
            raise ContractError(
                f"historical P packet artifact drift: {relative}: expected "
                f"{expected['byte_count']}/{expected['sha256']}, got "
                f"{capture.identity.size}/{capture.identity.sha256}"
            )
    if correction.identity.sha256 != HISTORICAL_FULL_TESTS_CORRECTION_SHA256:
        raise ContractError(
            "historical P full-tests correction drift: expected exact "
            f"{HISTORICAL_FULL_TESTS_CORRECTION_SHA256}, got "
            f"{correction.identity.sha256}"
        )
    captures = (
        baseline.capture,
        review.capture,
        authorization.capture,
        manifest,
        inputs.checker,
        completion,
        correction,
        workflow,
        *historical_packet_artifacts,
    )
    hashes = {
        COMPLETION_CHECKER_RELATIVE: completion.identity.sha256,
        SUPPORTED_API_CHECKER_RELATIVE: inputs.checker.identity.sha256,
        SUPPORTED_API_BASELINE_RELATIVE: baseline.capture.identity.sha256,
        SUPPORTED_API_REVIEW_RELATIVE: review.capture.identity.sha256,
        BOUNDED_MANIFEST_RELATIVE: manifest.identity.sha256,
        BOUNDED_AUTHORIZATION_RELATIVE: authorization.capture.identity.sha256,
        WORKFLOW_RELATIVE: workflow.identity.sha256,
    }
    current_captures = {
        COMPLETION_CHECKER_RELATIVE: completion,
        SUPPORTED_API_CHECKER_RELATIVE: inputs.checker,
        SUPPORTED_API_BASELINE_RELATIVE: baseline.capture,
        SUPPORTED_API_REVIEW_RELATIVE: review.capture,
        BOUNDED_MANIFEST_RELATIVE: manifest,
        BOUNDED_AUTHORIZATION_RELATIVE: authorization.capture,
        WORKFLOW_RELATIVE: workflow,
    }
    return hashes, current_captures, captures


def git_blob_oid(data: bytes) -> str:
    header = f"blob {len(data)}\0".encode("ascii")
    return hashlib.sha1(header + data).hexdigest()


def ci_only_recovery_constraints(
    authorization: Mapping[str, Any],
) -> dict[str, Any]:
    return {
        field: json.loads(json.dumps(authorization.get(field)))
        for field in (
            "scope",
            "authorized_actions",
            "activation_conditions",
            "preserved_exclusions",
            "expiry",
            "run_policy",
        )
    }


def ci_only_recovery_pending_ci() -> dict[str, Any]:
    fields = {
        "branch",
        "candidate_sha",
        "candidate_tree",
        "check_suite_id",
        "completed_at",
        "conclusion",
        "event",
        "full_build",
        "full_tests",
        "job_completed_at",
        "job_id",
        "job_log_byte_count",
        "job_log_sha256",
        "job_name",
        "job_started_at",
        "repository",
        "run_attempt",
        "run_id",
        "runner_name",
        "started_at",
        "status",
        "workflow_path",
    }
    result = {field: None for field in fields}
    result.update(
        {
            "branch": "codex/reorg-closeout-2026-08-m13-i01",
            "repository": "AlexGeorgantzas/lean-numerical-stability",
            "status": "pending",
            "workflow_path": WORKFLOW_RELATIVE,
        }
    )
    return result


def failed_p_control_record() -> dict[str, Any]:
    return {
        "authorization_blob_oid": FAILED_P_AUTHORIZATION_BLOB_OID,
        "authorization_path": BOUNDED_AUTHORIZATION_RELATIVE,
        "authorization_sha256": HISTORICAL_TERMINAL_V2_AUTHORIZATION_SHA256,
        "ci": {
            "branch": "codex/reorg-closeout-2026-08-m13-i01",
            "check_suite_conclusion": "failure",
            "check_suite_id": FAILED_P_CHECK_SUITE_ID,
            "completed_at": "2026-08-26T12:03:44Z",
            "conclusion": "failure",
            "event": "workflow_dispatch",
            "failed_step": "Check architecture source graph and Python tooling",
            "head_sha": FAILED_P_COMMIT_SHA,
            "job_completed_at": "2026-08-26T12:03:43Z",
            "job_conclusion": "failure",
            "job_id": FAILED_P_JOB_ID,
            "job_log_byte_count": FAILED_P_JOB_LOG_BYTE_COUNT,
            "job_log_sha256": FAILED_P_JOB_LOG_SHA256,
            "job_name": "build",
            "job_started_at": "2026-08-26T12:02:32Z",
            "run_attempt": 1,
            "run_id": FAILED_P_RUN_ID,
            "run_number": FAILED_P_RUN_NUMBER,
            "runner_name": "GitHub Actions 1000008996",
            "skipped_steps": [
                "Build library and smoke tests",
                "Verify supported API from the built environment",
                "Run Lake test driver",
            ],
            "started_at": "2026-08-26T12:02:27Z",
            "status": "failure",
            "workflow_path": WORKFLOW_RELATIVE,
        },
        "commit_sha": FAILED_P_COMMIT_SHA,
        "completion_checker_blob_oid": FAILED_P_COMPLETION_CHECKER_BLOB_OID,
        "completion_checker_path": COMPLETION_CHECKER_RELATIVE,
        "completion_checker_sha256": FAILED_P_COMPLETION_CHECKER_SHA256,
        "contract_blob_oid": FAILED_P_CONTRACT_BLOB_OID,
        "contract_path": DEFAULT_ACTIVATION_REVIEW.relative_to(ROOT).as_posix(),
        "contract_sha256": FAILED_P_CONTRACT_SHA256,
        "failure_reason": FAILED_P_FAILURE_REASON,
        "manifest_blob_oid": FAILED_P_MANIFEST_BLOB_OID,
        "manifest_path": BOUNDED_MANIFEST_RELATIVE,
        "manifest_sha256": "121D11A73AF2CD23885FB7A6B38D14B0D8A5440940D913A83F3A5D6941511ECE",
        "parent_sha": CI_ONLY_RECOVERY_CONTROL_HEAD_SHA,
        "subject": "chore(reorganization): plan M13 I01 and CODE03",
        "tree_sha": FAILED_P_TREE_SHA,
        "workflow_blob_oid": FAILED_P_WORKFLOW_BLOB_OID,
        "workflow_path": WORKFLOW_RELATIVE,
        "workflow_sha256": HISTORICAL_P_WORKFLOW_SHA256,
    }


def expected_ci_only_recovery_contract(
    artifacts: Sequence[Mapping[str, Any]],
    authorization: Mapping[str, Any],
) -> dict[str, Any]:
    clone = lambda value: json.loads(json.dumps(value))
    constraints = ci_only_recovery_constraints(authorization)
    historical = [
        {
            "blob_oid": facts["blob_oid"],
            "byte_count": facts["byte_count"],
            "mode": "100644",
            "path": path,
            "sha256": facts["sha256"],
            "source_commit_sha": FAILED_P_COMMIT_SHA,
        }
        for path, facts in sorted(HISTORICAL_P_PACKET_ARTIFACTS.items())
    ]
    return {
        "activation_conditions": clone(authorization.get("activation_conditions")),
        "application_mode": "ci_recovery_control_only",
        "artifacts": [clone(item) for item in artifacts],
        "authority": {
            "authority_id": "primary-human",
            "authorization_id": CI_ONLY_RECOVERY_AUTHORIZATION_ID,
            "authorization_path": BOUNDED_AUTHORIZATION_RELATIVE,
            "authorization_sha256": CI_ONLY_RECOVERY_AUTHORIZATION_SHA256,
            "authorized_manifest_path": BOUNDED_MANIFEST_RELATIVE,
            "authorized_manifest_rows": CI_ONLY_RECOVERY_MANIFEST_ROW_COUNT,
            "authorized_manifest_sha256": CI_ONLY_RECOVERY_MANIFEST_SHA256,
            "authorized_path_list_sha256": CI_ONLY_RECOVERY_PATH_SET_SHA256,
            "operator_id": "codex-local",
        },
        "authorized_actions": clone(authorization.get("authorized_actions")),
        "base": {
            "control_head_sha": CI_ONLY_RECOVERY_CONTROL_HEAD_SHA,
            "control_tree_sha": CI_ONLY_RECOVERY_CONTROL_TREE_SHA,
            "failed_planned_control_commit_sha": FAILED_P_COMMIT_SHA,
            "failed_planned_control_tree_sha": FAILED_P_TREE_SHA,
            "recovery_parent_sha": FAILED_P_COMMIT_SHA,
            "remote_main_sha_at_authorization": CI_ONLY_RECOVERY_CONTROL_HEAD_SHA,
            "request_replay_checkpoint_id": "C0007",
            "request_replay_code_sha": C0007_CODE_SHA,
        },
        "branch": {
            "base_sha": FAILED_P_COMMIT_SHA,
            "local_branch": "codex/reorg-closeout-2026-08-m13-i01",
            "operator_id": "codex-local",
            "push_policy": "fast_forward_only_with_exact_observed_lease",
            "remote": "origin",
            "remote_main_ref": "refs/heads/main",
            "remote_ref": "refs/heads/codex/reorg-closeout-2026-08-m13-i01",
            "remote_url": (
                "https://github.com/AlexGeorgantzas/"
                "lean-numerical-stability.git"
            ),
            "repository": "AlexGeorgantzas/lean-numerical-stability",
            "repository_id": "R_kgDORdQhag",
            "retirement_authorized": False,
        },
        "ci": {"planned_recovery": ci_only_recovery_pending_ci()},
        "constraints_sha256": canonical_json_sha256(constraints),
        "control_id": CI_ONLY_RECOVERY_CONTROL_ID,
        "expiry": clone(authorization.get("expiry")),
        "failed_planned_control": failed_p_control_record(),
        "graph": ["B->P_failed", "P_failed->PR"],
        "historical_packet_artifacts": historical,
        "lifecycle": {
            "continuation_authorized": False,
            "failed_planned_control_commit_sha": FAILED_P_COMMIT_SHA,
            "failed_planned_control_contract_blob_oid": FAILED_P_CONTRACT_BLOB_OID,
            "failed_planned_control_tree_sha": FAILED_P_TREE_SHA,
            "planned_recovery_commit_sha": None,
            "planned_recovery_contract_blob_oid": None,
            "planned_recovery_tree_sha": None,
            "state": CI_ONLY_RECOVERY_STATE,
        },
        "path_census": {
            "artifact_snapshot": {
                "path_count": 7,
                "path_set_sha256": CI_ONLY_RECOVERY_ARTIFACT_PATH_SET_SHA256,
            },
            "ci_recovery_control": {
                "modify_count": 8,
                "path_count": 8,
                "path_set_sha256": CI_ONLY_RECOVERY_PATH_SET_SHA256,
            },
            "contract_path": DEFAULT_ACTIVATION_REVIEW.relative_to(ROOT).as_posix(),
            "historical_packet_artifacts": {
                "path_count": 5,
                "path_set_sha256": (
                    CI_ONLY_RECOVERY_HISTORICAL_PACKET_PATH_SET_SHA256
                ),
            },
            "local_ledger_exclusion": "REMOTE_MAIN_REORGANIZATION_CLOSEOUT_PLAN.md",
            "self_hash_policy": (
                "excluded_from_artifacts_but_bound_by_direct_child_commit"
            ),
        },
        "permissions": {
            "activation_authorized": False,
            "implementation_authorized": False,
            "owner_solicitation_authorized": False,
            "post_assurance_transition_authorized": False,
            "remote_main_mutation_authorized": False,
            "request_resolution_authorized": False,
            "rerun_authorized": False,
        },
        "phase_id": "repository-reorganization-completion-2026-08",
        "preserved_exclusions": clone(authorization.get("preserved_exclusions")),
        "record_kind": CI_ONLY_RECOVERY_CONTRACT_KIND,
        "run_policy": clone(authorization.get("run_policy")),
        "schema_version": CI_ONLY_RECOVERY_CONTRACT_SCHEMA_VERSION,
        "scope": clone(authorization.get("scope")),
        "workflow": {
            "build_step_name": "Build library and smoke tests",
            "checkout_action": (
                "actions/checkout@fbc6f3992d24b796d5a048ff273f7fcc4a7b6c09"
            ),
            "checkout_ref_expression": "$" "{{ github.sha }}",
            "full_build_command": "lake build NumStability NumStabilityTest",
            "github_actions_read_permission": True,
            "github_issues_read_permission": True,
            "job_name": "build",
            "job_timeout_minutes": 360,
            "lean_action": (
                "leanprover/lean-action@50fcf42d2e460296f1a34b402e990d1b24f8b596"
            ),
            "lean_action_use_github_cache": True,
            "origin_normalization_command": (
                "git remote set-url origin "
                "https://github.com/AlexGeorgantzas/"
                "lean-numerical-stability.git"
            ),
            "path": WORKFLOW_RELATIVE,
            "sha256": CI_ONLY_RECOVERY_WORKFLOW_SHA256,
            "supported_api_commands": [
                "python tools/architecture/check_supported_api.py --self-test",
                (
                    "python tools/architecture/check_supported_api.py "
                    "--baseline docs/architecture/supported-api.json "
                    "--mode lifecycle"
                ),
            ],
            "supported_api_step_name": (
                "Verify supported API from the built environment"
            ),
            "test_command": "lake test",
            "test_step_name": "Run Lake test driver",
            "toolchain": "leanprover/lean4:v4.29.0-rc3",
            "workflow_id": 240911818,
            "workflow_name": "Lean CI",
        },
    }


def validate_ci_only_recovery_contract(
    contract: Mapping[str, Any],
    authorization: Mapping[str, Any],
    *,
    current_file_hashes: Mapping[str, str],
    current_file_captures: Mapping[str, CapturedFile],
    mode: str,
) -> list[str]:
    failures: list[str] = []
    try:
        validate_strict_json_tree(contract)
    except ContractError as error:
        return [f"CI-only recovery contract is not strict type-exact JSON: {error}"]
    if mode != "staging":
        failures.append(
            "CI-only recovery authority permits only the pre-implementation staging state"
        )
    expected_paths = set(CI_ONLY_RECOVERY_ARTIFACT_PATHS)
    if set(current_file_hashes) != expected_paths:
        failures.append("CI-only recovery current-file hash set must be exactly seven paths")
    if set(current_file_captures) != expected_paths:
        failures.append("CI-only recovery capture set must be exactly seven paths")

    artifacts_value = contract.get("artifacts")
    artifacts = artifacts_value if isinstance(artifacts_value, list) else []
    if not isinstance(artifacts_value, list):
        failures.append("CI-only recovery contract artifacts must be an array")
    artifact_paths = [
        row.get("path") if isinstance(row, dict) else None for row in artifacts
    ]
    if artifact_paths != list(CI_ONLY_RECOVERY_ARTIFACT_PATHS):
        failures.append(
            "CI-only recovery artifacts must be the seven sorted non-contract paths"
        )
    artifact_keys = {
        "base_blob_oid",
        "base_mode",
        "operation",
        "packet_id",
        "path",
        "post_blob_oid",
        "post_mode",
        "sha256",
    }
    for index, row in enumerate(artifacts):
        label = f"CI-only recovery artifacts[{index}]"
        if not isinstance(row, dict):
            failures.append(f"{label}: expected object")
            continue
        path = row.get("path")
        capture = current_file_captures.get(path) if isinstance(path, str) else None
        if set(row) != artifact_keys:
            failures.append(f"{label}: unexpected or missing keys")
        if path not in CI_ONLY_RECOVERY_ARTIFACT_BASE_BLOB_OIDS:
            failures.append(f"{label}: path is outside the recovery artifact boundary")
            continue
        exact_fields = {
            "base_blob_oid": CI_ONLY_RECOVERY_ARTIFACT_BASE_BLOB_OIDS[path],
            "base_mode": "100644",
            "operation": "modify",
            "packet_id": "CI01R1",
            "post_mode": "100644",
        }
        for field, expected in exact_fields.items():
            if not json_exact_equal(row.get(field), expected):
                failures.append(f"{label}.{field}: exact recovery binding drift")
        if capture is None:
            failures.append(f"{label}: missing independently captured current bytes")
            continue
        if row.get("sha256") != current_file_hashes.get(path):
            failures.append(f"{label}.sha256: does not bind current captured bytes")
        if row.get("post_blob_oid") != git_blob_oid(capture.raw):
            failures.append(f"{label}.post_blob_oid: does not bind current captured bytes")
        if row.get("post_blob_oid") == row.get("base_blob_oid"):
            failures.append(f"{label}.post_blob_oid: recovery postimage equals P preimage")

    expected = expected_ci_only_recovery_contract(artifacts, authorization)
    if not json_exact_equal(contract, expected):
        failures.append(
            "CI-only recovery contract identity, authority snapshot, failed-P "
            "evidence, historical packet boundary, or pending PR fields drifted"
        )
    return failures


def validate_bounded_authorization_document(
    authorization: Mapping[str, Any],
    *,
    authorization_sha256: str,
) -> list[str]:
    """Require the exact CI-only recovery grant and its narrow trust boundary."""

    failures: list[str] = []
    try:
        validate_strict_json_tree(authorization)
    except ContractError as error:
        return [f"bounded authorization is not strict type-exact JSON: {error}"]
    if authorization_sha256 != CI_ONLY_RECOVERY_AUTHORIZATION_SHA256:
        failures.append(
            "CI-only recovery authorization raw SHA-256 mismatch: expected "
            f"{CI_ONLY_RECOVERY_AUTHORIZATION_SHA256}, got {authorization_sha256}"
        )
    canonical_sha256 = sha256_bytes(canonical_json_bytes(authorization))
    if canonical_sha256 != CI_ONLY_RECOVERY_AUTHORIZATION_SHA256:
        failures.append(
            "CI-only recovery authorization canonical bytes do not match the exact grant"
        )
    expected_top_keys = {
        "activation_conditions",
        "authority_id",
        "authorization_id",
        "authorized_actions",
        "base",
        "decision",
        "expiry",
        "operator_id",
        "phase_id",
        "preserved_exclusions",
        "record_kind",
        "recorded_at",
        "run_policy",
        "schema_version",
        "scope",
        "source",
        "supersedes",
    }
    if set(authorization) != expected_top_keys:
        failures.append("CI-only recovery authorization has unexpected or missing keys")
    exact_scalars = {
        "authority_id": "primary-human",
        "authorization_id": CI_ONLY_RECOVERY_AUTHORIZATION_ID,
        "decision": "approved_for_ci_recovery_only",
        "operator_id": "codex-local",
        "phase_id": "repository-reorganization-completion-2026-08",
        "record_kind": "primary_human_ci_only_recovery_authorization",
        "schema_version": 3,
    }
    for field, expected in exact_scalars.items():
        if not json_exact_equal(authorization.get(field), expected):
            failures.append(
                f"CI-only recovery authorization {field}: expected {expected!r}, "
                f"got {authorization.get(field)!r}"
            )

    scope = authorization.get("scope")
    expected_scope_keys = {
        "activation_authorized",
        "authorized_path_manifest",
        "bounded_ref",
        "checkpoint_acceptance_authorized",
        "implementation_authorized",
        "owner_solicitation_authorized",
        "post_assurance_transition_authorized",
        "recovery_parent_sha",
        "recovery_subject",
        "remote_main_mutation_authorized",
        "request_resolution_authorized",
        "supported_api_record",
        "target_state",
        "task_ids",
    }
    if not isinstance(scope, dict) or set(scope) != expected_scope_keys:
        failures.append("CI-only recovery authorization scope has wrong shape")
        scope = {}
    for field in (
        "activation_authorized",
        "checkpoint_acceptance_authorized",
        "implementation_authorized",
        "owner_solicitation_authorized",
        "post_assurance_transition_authorized",
        "remote_main_mutation_authorized",
        "request_resolution_authorized",
    ):
        if scope.get(field) is not False:
            failures.append(f"CI-only recovery authorization scope.{field} must be false")
    exact_scope_values = {
        "bounded_ref": "refs/heads/codex/reorg-closeout-2026-08-m13-i01",
        "recovery_parent_sha": "1d454ecb8dc80dc4ece21ebc26eec29b8f9a6ae9",
        "recovery_subject": "fix(reorganization): recover M13 planned-control CI",
        "target_state": CI_ONLY_RECOVERY_STATE,
        "task_ids": ["CI-01", "EPOCH-01", "VERIFY-01", "VERIFY-02", "VERIFY-03"],
    }
    for field, expected in exact_scope_values.items():
        if not json_exact_equal(scope.get(field), expected):
            failures.append(f"CI-only recovery authorization scope.{field} drift")
    expected_manifest = {
        "path": BOUNDED_MANIFEST_RELATIVE,
        "path_list_sha256": CI_ONLY_RECOVERY_PATH_SET_SHA256,
        "preimage_freeze_sha256": CI_ONLY_RECOVERY_PREIMAGE_FREEZE_SHA256,
        "row_count": CI_ONLY_RECOVERY_MANIFEST_ROW_COUNT,
        "sha256": CI_ONLY_RECOVERY_MANIFEST_SHA256,
    }
    if not json_exact_equal(scope.get("authorized_path_manifest"), expected_manifest):
        failures.append("CI-only recovery authorization manifest binding drift")
    expected_supported_api_record = {
        "authority_effect": "none",
        "path": SUPPORTED_API_REVIEW_RELATIVE,
        "required_null_fields": ["decision", "reviewer", "reviewed_at_utc"],
        "status": "pending_machine_evidence",
    }
    if not json_exact_equal(
        scope.get("supported_api_record"), expected_supported_api_record
    ):
        failures.append("CI-only recovery authorization supported-API boundary drift")

    run_policy = authorization.get("run_policy")
    expected_run_policy = {
        "attempt": 1,
        "event": "workflow_dispatch",
        "matching_run_ids": 1,
        "rerun_authorized": False,
        "terminal_evidence_location": "untracked local ledger only",
    }
    if not json_exact_equal(run_policy, expected_run_policy):
        failures.append("CI-only recovery authorization run policy drift")
    supersedes = authorization.get("supersedes")
    expected_supersedes = {
        "authorization_id": HISTORICAL_TERMINAL_V2_AUTHORIZATION_ID,
        "effect": "historical P evidence only; no action remains authorized",
        "sha256": HISTORICAL_TERMINAL_V2_AUTHORIZATION_SHA256,
    }
    if not json_exact_equal(supersedes, expected_supersedes):
        failures.append("CI-only recovery authorization terminal-v2 boundary drift")
    actions = authorization.get("authorized_actions")
    if not isinstance(actions, list) or not all(isinstance(item, str) for item in actions):
        failures.append("CI-only recovery authorization actions must be strings")
    elif any(
        marker in item.lower()
        for item in actions
        for marker in ("activate m13", "apply r0014", "apply r0015", "commit i", "commit v")
    ):
        failures.append("CI-only recovery authorization contains an implementation action")
    return failures


def validate_ci_only_recovery_manifest(capture: CapturedFile) -> list[str]:
    failures: list[str] = []
    if capture.path.relative_to(ROOT).as_posix() != BOUNDED_MANIFEST_RELATIVE:
        failures.append("CI-only recovery manifest path mismatch")
    if capture.identity.sha256 != CI_ONLY_RECOVERY_MANIFEST_SHA256:
        failures.append(
            "CI-only recovery manifest SHA-256 mismatch: expected "
            f"{CI_ONLY_RECOVERY_MANIFEST_SHA256}, got {capture.identity.sha256}"
        )
    if capture.raw != CI_ONLY_RECOVERY_MANIFEST_BYTES:
        failures.append("CI-only recovery manifest is not the exact eight-row contract")
    expected_path_payload = ("\n".join(CI_ONLY_RECOVERY_PATHS) + "\n").encode("utf-8")
    if sha256_bytes(expected_path_payload) != CI_ONLY_RECOVERY_PATH_SET_SHA256:
        failures.append("CI-only recovery checker path-set constant is internally inconsistent")
    return failures


def ci_only_recovery_contract_state(
    contract: Mapping[str, Any] | None,
    *,
    authorization: Mapping[str, Any],
    current_file_hashes: Mapping[str, str],
    current_file_captures: Mapping[str, CapturedFile],
    mode: str,
    contract_path: Path,
) -> tuple[list[str], bool]:
    """Validate the pending recovery record; it never activates implementation."""
    if contract is None:
        return ([f"missing CI-only recovery contract: {contract_path}"], False)
    failures = validate_ci_only_recovery_contract(
        contract,
        authorization,
        current_file_hashes=current_file_hashes,
        current_file_captures=current_file_captures,
        mode=mode,
    )
    return failures, False


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
            if not json_exact_equal(actual.get(field), expected.get(field)):
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
    if not json_exact_equal(
        current_derivation.get("tier_manifest_sha256"), expected_tier_sha
    ):
        failures.append(
            "tier manifest drift: expected exact "
            f"{expected_tier_sha}, got {current_derivation.get('tier_manifest_sha256')!r}"
        )
    expected_entrypoints = baseline.get("derivation", {}).get(
        "documented_entrypoints"
    )
    if not json_exact_equal(
        current_derivation.get("documented_entrypoints"), expected_entrypoints
    ):
        failures.append(
            "documented entrypoint set drift: expected "
            f"{expected_entrypoints!r}, got "
            f"{current_derivation.get('documented_entrypoints')!r}"
        )
    for field, expected in expected_derivation.items():
        if not json_exact_equal(current_derivation.get(field), expected):
            failures.append(
                f"test derivation {field} drift: expected {expected!r}, "
                f"got {current_derivation.get(field)!r}"
            )
    expected_protected_count = sum(
        1 for row in expected_declarations if row.get("protected") is True
    )
    if not json_exact_equal(
        current_derivation.get("protected_selected_declaration_count"),
        expected_protected_count,
    ):
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
            if not json_exact_equal(actual.get(field), expected.get(field)):
                failures.append(
                    f"{entrypoint}: unreviewed public visibility drift in {field}: "
                    f"expected {expected.get(field)!r}, got {actual.get(field)!r}"
                )
    return failures


def current_contract_from_baseline(
    baseline: Mapping[str, Any],
    review: Mapping[str, Any],
    *,
    inputs: GenerationInputs | None = None,
) -> dict[str, Any]:
    if inputs is None:
        inputs = capture_generation_inputs()
    schema_failures = validate_baseline_schema(baseline, inputs=inputs)
    if schema_failures:
        raise ContractError("invalid baseline:\n" + "\n".join(schema_failures))
    tiers = inputs.tier_manifest.value
    modules = scan_modules(inputs)
    selections, derivation = derive_test_selections(modules, tiers)
    current_entrypoints = documented_entrypoints(tiers)
    derivation["documented_entrypoints"] = list(current_entrypoints)
    derivation["tier_manifest_sha256"] = inputs.tier_manifest.capture.identity.sha256
    reachable_tests = all_import_closure(modules, (TEST_ROOT,))
    approved_modules = {
        row["test_module"] for row in review["approved_additive_test_evidence"]
    }
    baseline_rows = index_rows(baseline["declarations"], "fqn")
    selected_names = sorted(set(baseline_rows) | set(selections))
    env = run_environment_extractor(
        selected_names, current_entrypoints, inputs=inputs
    )
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
    result = {
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
    verify_generation_inputs(inputs)
    return result


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


def _expect_contract_error(
    action: Callable[[], Any], *, contains: str | None = None
) -> None:
    try:
        action()
    except ContractError as error:
        if contains is not None and contains not in str(error):
            raise AssertionError(
                f"expected ContractError containing {contains!r}, got {error!r}"
            ) from error
    else:
        raise AssertionError("expected ContractError")


def self_test_strict_json() -> None:
    valid = parse_strict_json_bytes(
        b'{"array":[true,1,1.0,null],"text":"ok"}', label="valid fixture"
    )
    assert type(valid["array"][0]) is bool
    assert type(valid["array"][1]) is int
    assert type(valid["array"][2]) is float
    assert not json_exact_equal(True, 1)
    assert not json_exact_equal(1, 1.0)
    assert not json_exact_equal(False, 0)

    invalid_documents = (
        b'{"outer":{"duplicate":1,"duplicate":2}}',
        b'{"value":NaN}',
        b'{"value":Infinity}',
        b'{"value":-Infinity}',
        b'{"value":1e999}',
        b'{"value":"\xff"}',
        b'{"value":"\\ud800"}',
        b'{"\\udfff":"value"}',
        b'{"value":1} trailing',
        b'\xef\xbb\xbf{"value":1}',
        b'[1,2,3]',
    )
    for index, raw in enumerate(invalid_documents):
        _expect_contract_error(
            lambda raw=raw, index=index: parse_strict_json_bytes(
                raw, label=f"invalid fixture {index}"
            )
        )

    depth_64 = b'{"value":' + b"[" * 63 + b"0" + b"]" * 63 + b"}"
    parse_strict_json_bytes(depth_64, label="depth-64 fixture")
    depth_65 = b'{"value":' + b"[" * 64 + b"0" + b"]" * 64 + b"}"
    _expect_contract_error(
        lambda: parse_strict_json_bytes(depth_65, label="depth-65 fixture"),
        contains="depth 64",
    )

    canonical_value = {"a": [1, False], "b": "λ"}
    canonical = canonical_json_bytes(canonical_value)
    noncanonical = (
        canonical.replace(b"\n", b"\r\n"),
        json.dumps(
            {"b": "λ", "a": [1, False]},
            ensure_ascii=False,
            indent=2,
            sort_keys=False,
            allow_nan=False,
        ).encode("utf-8")
        + b"\n",
        json.dumps(
            canonical_value,
            ensure_ascii=False,
            indent=4,
            sort_keys=True,
            allow_nan=False,
        ).encode("utf-8")
        + b"\n",
        canonical[:-1],
        canonical + b"\n",
    )
    with tempfile.TemporaryDirectory(prefix="supported-api-json-test-") as temp_name:
        temp = Path(temp_name)
        path = temp / "canonical.json"
        path.write_bytes(canonical)
        document = capture_json_document(path, require_canonical=True)
        assert document.capture.raw == canonical
        assert document.capture.identity.sha256 == sha256_bytes(canonical)
        assert json_exact_equal(document.value, canonical_value)
        for index, raw in enumerate(noncanonical):
            candidate = temp / f"noncanonical-{index}.json"
            candidate.write_bytes(raw)
            _expect_contract_error(
                lambda candidate=candidate: capture_json_document(
                    candidate, require_canonical=True
                ),
                contains="canonical JSON",
            )

        too_large = temp / "too-large.json"
        with too_large.open("wb") as handle:
            handle.truncate(MAX_JSON_BYTES + 1)
        _expect_contract_error(
            lambda: capture_json_document(too_large), contains="byte limit"
        )

        mutable = temp / "mutable.txt"
        mutable.write_bytes(b"first")
        captured = capture_file(mutable)
        mutable.write_bytes(b"second version")
        _expect_contract_error(
            lambda: verify_captured_files((captured,)), contains="changed"
        )


def self_test_module_header_parser() -> None:
    source = '''/- import NumStability.CommentDecoy -/
module
prelude
public import NumStability.Visible
meta import NumStability.MetaPrivate
import all NumStability.AllPrivate

def ordinary := "first line
import NumStability.StringDecoy
#check NumStability.StringAssertionDecoy"
def raw := r##"raw line
import NumStability.RawDecoy
#synth NumStability.RawAssertionDecoy"##
def character := 'x'
def quoted := `(#check NumStability.OneLineSyntaxData)
import NumStability.LateImport
#check NumStability.Executed
'''
    mask = lean_code_mask(source)
    imports, exports = parse_import_edges(mask)
    assert imports == (
        "NumStability.Visible",
        "NumStability.MetaPrivate",
        "NumStability.AllPrivate",
    )
    assert exports == ("NumStability.Visible",)
    assert explicit_api_names(mask) == ("NumStability.Executed",)

    guillemet_source = '''namespace NumStability
def Executed : Nat := 0
end NumStability
def «embedded
#check NumStability.GuillemetDecoy
identifier» : Nat := 0
#check NumStability.Executed
'''
    guillemet_mask = lean_code_mask(guillemet_source)
    assert len(guillemet_mask) == len(guillemet_source)
    assert tuple(
        index for index, char in enumerate(guillemet_mask) if char in "\r\n"
    ) == tuple(
        index for index, char in enumerate(guillemet_source) if char in "\r\n"
    )
    assert explicit_api_names(guillemet_mask) == ("NumStability.Executed",)
    assert "GuillemetDecoy" not in guillemet_mask
    with tempfile.TemporaryDirectory(
        prefix="supported-api-guillemet-test-"
    ) as temp_name:
        fixture = Path(temp_name) / "GuillemetFixture.lean"
        fixture.write_text(guillemet_source, encoding="utf-8", newline="\n")
        try:
            compiled = subprocess.run(
                ("lake", "env", "lean", str(fixture)),
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
        assert compiled.returncode == 0, compiled.stdout + compiled.stderr

    guillemet_crlf = "def «left\r\n#check NumStability.Decoy\r\nright» := 0\r\n"
    crlf_mask = lean_code_mask(guillemet_crlf)
    assert len(crlf_mask) == len(guillemet_crlf)
    assert [
        (index, char)
        for index, char in enumerate(crlf_mask)
        if char in "\r\n"
    ] == [
        (index, char)
        for index, char in enumerate(guillemet_crlf)
        if char in "\r\n"
    ]
    assert not explicit_api_names(crlf_mask)
    assert explicit_api_names(
        lean_code_mask("#check NumStability.«single line component»\n")
    ) == ("NumStability.«single line component»",)
    assert lean_code_mask("def «`(#check NumStability.SyntaxDecoy)» := 0\n")
    assert lean_code_mask(
        'def s := "«unterminated in string"\n'
        'def r := r#"» misplaced in raw string"#\n'
        '-- «unterminated in comment\n'
    )
    _expect_contract_error(
        lambda: lean_code_mask("def «unterminated\n"),
        contains="unterminated Lean guillemet",
    )
    _expect_contract_error(
        lambda: lean_code_mask("def «» := 0\n"),
        contains="empty Lean guillemet",
    )
    _expect_contract_error(
        lambda: lean_code_mask("def misplaced» := 0\n"),
        contains="misplaced Lean closing guillemet",
    )

    spanning_syntax = '''module
public import NumStability.Visible
def quoted := `(
#check NumStability.SyntaxData
)
'''
    _expect_contract_error(
        lambda: lean_code_mask(spanning_syntax),
        contains="syntax quotation",
    )
    _expect_contract_error(
        lambda: lean_code_mask("def q := `(unterminated\n"),
        contains="unterminated",
    )

    assert parse_import_edges("important := true\nimport NumStability.Late\n") == (
        (),
        (),
    )
    assert parse_import_edges(
        "import NumStability.First\ndef x := 1\nimport NumStability.Late\n"
    ) == (("NumStability.First",), ("NumStability.First",))
    assert parse_import_edges("import NumStability.«quoted module»\n") == (
        ("NumStability.«quoted module»",),
        ("NumStability.«quoted module»",),
    )
    assert parse_import_edges(
        "module\npublic meta import NumStability.MetaExported\n"
    ) == (
        ("NumStability.MetaExported",),
        ("NumStability.MetaExported",),
    )
    assert parse_import_edges(
        "module\npublic\timport\tNumStability.TabPublic\n"
        "meta\timport\tNumStability.TabMeta\n"
        "import\tall\tNumStability.TabAll\n"
    ) == (
        (
            "NumStability.TabPublic",
            "NumStability.TabMeta",
            "NumStability.TabAll",
        ),
        ("NumStability.TabPublic",),
    )
    assert parse_import_edges(
        "module\npublic\tmeta\timport\tNumStability.TabPublicMeta\n"
    ) == (
        ("NumStability.TabPublicMeta",),
        ("NumStability.TabPublicMeta",),
    )
    assert parse_import_edges("import\tNumStability.TabLegacy\n") == (
        ("NumStability.TabLegacy",),
        ("NumStability.TabLegacy",),
    )
    unsupported_imports = (
        "public import NumStability.BadLegacy\n",
        "meta import NumStability.BadLegacy\n",
        "import all NumStability.BadLegacy\n",
        "module\nprivate import NumStability.Bad\n",
        "module\nmeta public import NumStability.Bad\n",
        "module\npublic import all NumStability.Bad\n",
        "module\nmeta\tpublic\timport\tNumStability.Bad\n",
        "import NumStability.First NumStability.Second\n",
        "import NumStability.First as Alias\n",
        "import NumStability.First.\n",
        "import NumStability.«unterminated\n",
        "module extra\n",
        "prelude extra\n",
    )
    for text in unsupported_imports:
        _expect_contract_error(lambda text=text: parse_import_edges(text))

    higham_path = (
        ROOT
        / "NumStability"
        / "Source"
        / "Higham"
        / "Chapter16"
        / "Problem02"
        / "Results"
        / "Core.lean"
    )
    higham = capture_file(higham_path).raw.decode("utf-8", errors="strict")
    higham_imports, higham_exports = parse_import_edges(lean_code_mask(higham))
    lyapunov = (
        "NumStability.Source.Higham.Chapter16.Problem02."
        "LyapunovIntegral.Results"
    )
    assert lyapunov in higham_imports
    assert lyapunov in higham_exports
    assert higham_imports == higham_exports


def _encoded_type_payload(text: str) -> bytes:
    return (
        text.replace("%", "%25")
        .replace("\t", "%09")
        .replace("\r", "%0D")
        .replace("\n", "%0A")
        .encode("utf-8")
    )


def self_test_environment_tsv() -> None:
    selected_name = "NumStability.StreamingFixture"
    owner = "NumStability.Streaming"
    type_text = "∀ (λ : String), λ = %09 literal\tline\r\nend"
    encoded = _encoded_type_payload(type_text)
    rows = (
        b"format\t1\n"
        + f"visible\t{selected_name}\t{owner}\n".encode("utf-8")
        + f"selected\t{selected_name}\t{owner}\tdefinition\tfalse\tpublic\t".encode(
            "utf-8"
        )
        + encoded
        + b"\n"
    )
    with tempfile.TemporaryDirectory(prefix="supported-api-tsv-test-") as temp_name:
        temp = Path(temp_name)
        path = temp / "environment.tsv"
        path.write_bytes(rows)
        expected_type_sha = sha256_bytes(type_text.encode("utf-8"))
        assert sha256_bytes(
            decode_type_payload(encoded.decode("utf-8")).encode("utf-8")
        ) == expected_type_sha
        for chunk_bytes in (1, 2, 3, 7, 31, 1024):
            snapshot = parse_environment_tsv(
                path, (selected_name,), chunk_bytes=chunk_bytes
            )
            assert snapshot.selected[selected_name].normalized_type_sha256 == expected_type_sha
            assert snapshot.raw_tsv_bytes == len(rows)
            assert snapshot.raw_tsv_sha256 == sha256_bytes(rows)
            assert snapshot.physical_record_count == 3
            assert snapshot.max_physical_record_bytes == max(
                len(row) + 1 for row in rows[:-1].split(b"\n")
            )

        giant_size = 5 * 1024 * 1024
        giant_payload = b"x" * giant_size
        giant = (
            b"format\t1\n"
            + f"selected\t{selected_name}\t{owner}\tdefinition\tfalse\tpublic\t".encode(
                "utf-8"
            )
            + giant_payload
            + b"\n"
        )
        path.write_bytes(giant)
        giant_snapshot = parse_environment_tsv(
            path, (selected_name,), chunk_bytes=17
        )
        assert giant_snapshot.selected[selected_name].normalized_type_sha256 == sha256_bytes(
            giant_payload
        )
        assert giant_snapshot.max_physical_record_bytes == len(giant.split(b"\n")[1]) + 1

        malformed_rows: list[tuple[bytes, Sequence[str]]] = [
            (rows[:-1], (selected_name,)),
            (rows.replace(b"\n", b"\r\n", 1), (selected_name,)),
            (rows.replace(b"visible", b"vis\0ible", 1), (selected_name,)),
            (
                rows.replace(encoded, b"bad%ZZ", 1),
                (selected_name,),
            ),
            (
                rows.replace(encoded, b"bad%", 1),
                (selected_name,),
            ),
            (
                rows.replace(encoded, b"bad\xff", 1),
                (selected_name,),
            ),
            (b"format\t1\nformat\t1\n", ()),
            (b"visible\tName\tOwner\nformat\t1\n", ()),
            (
                b"format\t1\nvisible\tName\tOwner\nvisible\tName\tOwner\n",
                (),
            ),
            (
                b"format\t1\n"
                + f"selected\t{selected_name}\t{owner}\tdefinition\tfalse\tpublic\tx\n".encode()
                + f"selected\t{selected_name}\t{owner}\tdefinition\tfalse\tpublic\ty\n".encode(),
                (selected_name,),
            ),
            (b"format\t1\n", (selected_name,)),
            (rows, ()),
            (
                b"format\t1\n"
                + f"selected\t{selected_name}\t{owner}\tdefinition\tfalse\tpublic\t\n".encode(),
                (selected_name,),
            ),
            (
                b"format\t1\nvisible\t" + b"x" * (TSV_SMALL_ROW_BYTES + 1) + b"\tOwner\n",
                (),
            ),
            (
                b"format\t1\nselected\t" + b"x" * (TSV_PREFIX_BYTES + 1) + b"\n",
                (),
            ),
        ]
        for index, (raw, selected_names) in enumerate(malformed_rows):
            candidate = temp / f"malformed-{index}.tsv"
            candidate.write_bytes(raw)
            _expect_contract_error(
                lambda candidate=candidate, selected_names=selected_names: parse_environment_tsv(
                    candidate, selected_names, chunk_bytes=13
                )
            )


def self_test_ratchets_and_pending_review() -> None:
    exact_derivation: dict[str, Any] = {
        "assertion_count": C0007_ASSERTION_COUNT,
        "selected_declaration_count": C0007_SELECTED_DECLARATION_COUNT,
        "isolated_test_module_count": C0007_ISOLATED_TEST_MODULE_COUNT,
        "contract_sha256": C0007_TEST_CONTRACT_SHA256,
    }
    assert not c0007_ratchet_failures(
        exact_derivation, C0007_DOCUMENTED_ENTRYPOINT_COUNT
    )
    mutations = (
        ("assertion_count", C0007_ASSERTION_COUNT + 1),
        ("selected_declaration_count", C0007_SELECTED_DECLARATION_COUNT - 1),
        ("isolated_test_module_count", C0007_ISOLATED_TEST_MODULE_COUNT + 1),
        ("contract_sha256", "0" * 64),
    )
    for field, value in mutations:
        changed = dict(exact_derivation)
        changed[field] = value
        failures = c0007_ratchet_failures(
            changed, C0007_DOCUMENTED_ENTRYPOINT_COUNT
        )
        assert len(failures) == 1 and field in failures[0]
    entrypoint_failures = c0007_ratchet_failures(
        exact_derivation, C0007_DOCUMENTED_ENTRYPOINT_COUNT - 1
    )
    assert len(entrypoint_failures) == 1 and "documented_entrypoint_count" in entrypoint_failures[0]
    boolean_alias = dict(exact_derivation)
    boolean_alias["assertion_count"] = True
    assert c0007_ratchet_failures(
        boolean_alias, C0007_DOCUMENTED_ENTRYPOINT_COUNT
    )

    pending = {
        "count": 9,
        "rationale": PENDING_REVIEW_RATIONALE,
        "reviewer": None,
    }
    assert not validate_exact_pending_review(pending, pending)
    rationale_tamper = dict(pending)
    rationale_tamper["rationale"] += " altered"
    rationale_failures = validate_exact_pending_review(rationale_tamper, pending)
    assert any("rationale drift" in failure for failure in rationale_failures)
    scalar_alias = dict(pending)
    scalar_alias["count"] = 9.0
    assert validate_exact_pending_review(scalar_alias, pending)


def self_test_environment_build_cache() -> None:
    global _ENVIRONMENT_BUILD_CACHE_KEY

    saved_cache = _ENVIRONMENT_BUILD_CACHE_KEY
    key_a: tuple[Any, ...] = (("source", "A"), ("toolchain", "A"))
    key_b: tuple[Any, ...] = (("source", "B"), ("toolchain", "A"))
    key_c: tuple[Any, ...] = (("source", "C"), ("toolchain", "A"))
    current = [key_a]
    builds: list[tuple[Any, ...]] = []

    def current_key() -> tuple[Any, ...]:
        return current[0]

    def build() -> None:
        builds.append(current[0])

    try:
        _ENVIRONMENT_BUILD_CACHE_KEY = None
        assert _ensure_build_for_exact_key(key_a, current_key, build)
        assert builds == [key_a]
        assert not _ensure_build_for_exact_key(key_a, current_key, build)
        assert builds == [key_a]

        current[0] = key_b
        assert _ensure_build_for_exact_key(key_b, current_key, build)
        assert builds == [key_a, key_b]

        current[0] = key_a
        assert _ensure_build_for_exact_key(key_a, current_key, build)
        assert builds == [key_a, key_b, key_a]

        # A failed B build can have polluted shared outputs.  Reverting the
        # sources to A must rebuild rather than trust the older A cache entry.
        current[0] = key_b

        def fail_different_key_build() -> None:
            builds.append(current[0])
            raise ContractError("synthetic B build failure")

        _expect_contract_error(
            lambda: _ensure_build_for_exact_key(
                key_b, current_key, fail_different_key_build
            ),
            contains="synthetic B build failure",
        )
        assert _ENVIRONMENT_BUILD_CACHE_KEY is None
        current[0] = key_a
        assert _ensure_build_for_exact_key(key_a, current_key, build)
        assert builds[-2:] == [key_b, key_a]

        # A nominally successful different-key build whose captured inputs
        # mutate before the post-build check also invalidates the old A claim.
        current[0] = key_b

        def mutate_after_different_key_build() -> None:
            builds.append(current[0])
            current[0] = key_c

        _expect_contract_error(
            lambda: _ensure_build_for_exact_key(
                key_b, current_key, mutate_after_different_key_build
            ),
            contains="changed while Lake was running",
        )
        assert _ENVIRONMENT_BUILD_CACHE_KEY is None
        current[0] = key_a
        assert _ensure_build_for_exact_key(key_a, current_key, build)
        assert builds[-2:] == [key_b, key_a]

        _ENVIRONMENT_BUILD_CACHE_KEY = key_a
        current[0] = key_b
        builds_before_stale_check = list(builds)
        _expect_contract_error(
            lambda: _ensure_build_for_exact_key(key_a, current_key, build),
            contains="already stale",
        )
        assert builds == builds_before_stale_check

        _ENVIRONMENT_BUILD_CACHE_KEY = None
        current[0] = key_a

        def mutate_during_build() -> None:
            builds.append(current[0])
            current[0] = key_b

        _expect_contract_error(
            lambda: _ensure_build_for_exact_key(
                key_a, current_key, mutate_during_build
            ),
            contains="changed while Lake was running",
        )
        assert _ENVIRONMENT_BUILD_CACHE_KEY is None
    finally:
        _ENVIRONMENT_BUILD_CACHE_KEY = saved_cache


def self_test_candidate_reconstruction() -> None:
    with tempfile.TemporaryDirectory(
        prefix="supported-api-path-kind-test-"
    ) as temp_name:
        temp = Path(temp_name)
        assert _capture_regular_or_absent(
            temp / "absent", label="self-test path"
        ) is None
        regular = temp / "regular"
        regular.write_bytes(b"regular")
        assert _capture_regular_or_absent(
            regular, label="self-test path"
        ) is not None
        directory = temp / "directory"
        directory.mkdir()
        _expect_contract_error(
            lambda: _capture_regular_or_absent(
                directory, label="self-test path"
            ),
            contains="not an exact regular file or absence",
        )
        broken_link = temp / "broken-link"
        try:
            broken_link.symlink_to(temp / "missing-target")
        except OSError:
            pass
        else:
            _expect_contract_error(
                lambda: _capture_regular_or_absent(
                    broken_link, label="self-test path"
                ),
                contains="not an exact regular file or absence",
            )

    inputs = capture_generation_inputs()
    state = classify_implementation_state()
    with tempfile.TemporaryDirectory(
        prefix="supported-api-git-poison-test-"
    ) as poison_name:
        poisoned = {
            "GIT_DIR": str(Path(poison_name) / "foreign.git"),
            "GIT_INDEX_FILE": str(Path(poison_name) / "foreign.index"),
            "GIT_OPTIONAL_LOCKS": "1",
            "GIT_WORK_TREE": str(Path(poison_name) / "foreign-worktree"),
        }
        saved_environment = {key: os.environ.get(key) for key in poisoned}
        os.environ.update(poisoned)
        try:
            assert classify_implementation_state() == state
            if state == "staging":
                require_exact_candidate_staging_state(inputs)
        finally:
            for key, value in saved_environment.items():
                if value is None:
                    os.environ.pop(key, None)
                else:
                    os.environ[key] = value
    observed_temp: list[tuple[Path, bool]] = []
    if state == "staging":
        require_exact_candidate_staging_state(inputs)
        candidate = reconstruct_candidate_postimage(
            inputs,
            temp_path_observer=lambda path: observed_temp.append(
                (path, path.exists())
            ),
        )
    else:
        completion_rows = implementation_postimage_rows(inputs)
        candidate = CandidatePostimage(
            rows=tuple(dict(row) for row in completion_rows),
            bytes_by_path={
                row["path"]: capture_file(ROOT / row["path"]).raw
                for row in completion_rows
            },
        )
        validate_candidate_postimage_bytes(
            candidate.rows, candidate.bytes_by_path
        )
    assert len(candidate.rows) == 14
    assert len(candidate.bytes_by_path) == 14
    if state == "staging":
        assert observed_temp and observed_temp[0][1]
        assert not observed_temp[0][0].exists()
    inputs_relative = (
        "NumStability/Source/Higham/Chapter02/Problem09/DoubleRounding/"
        "Counterexample/Inputs.lean"
    )
    assert (ROOT / inputs_relative).exists() == (state == "completion")
    assert inputs_relative in candidate.bytes_by_path
    if state == "staging":
        candidate_modules, candidate_tiers = candidate_modules_and_tiers(
            inputs, candidate
        )
        assert (
            "NumStability.Source.Higham.Chapter02.Problem09.DoubleRounding."
            "Counterexample.Inputs"
        ) in candidate_modules
        assert isinstance(candidate_tiers, dict)

    base_snapshot = _capture_implementation_worktree(candidate.rows)
    if state == "staging":
        _require_exact_candidate_base(candidate.rows, base_snapshot)
        partial_snapshot = dict(base_snapshot)
        modified_row = next(
            row for row in candidate.rows if row["preimage_sha256"] != "-"
        )
        partial_snapshot[modified_row["path"]] = None
        _expect_contract_error(
            lambda: _require_exact_candidate_base(
                candidate.rows, partial_snapshot
            ),
            contains="exact C0007 preimage",
        )
        unexpected_new = dict(base_snapshot)
        new_row = next(
            row for row in candidate.rows if row["preimage_sha256"] == "-"
        )
        unexpected_new[new_row["path"]] = inputs.checker
        _expect_contract_error(
            lambda: _require_exact_candidate_base(candidate.rows, unexpected_new),
            contains="exact C0007 preimage",
        )

    exact_bytes = dict(candidate.bytes_by_path)
    missing_bytes = dict(exact_bytes)
    missing_bytes.pop(next(iter(missing_bytes)))
    _expect_contract_error(
        lambda: validate_candidate_postimage_bytes(candidate.rows, missing_bytes),
        contains="byte inventory mismatch",
    )
    tampered_bytes = dict(exact_bytes)
    tampered_path = next(iter(tampered_bytes))
    tampered_bytes[tampered_path] += b"tamper"
    _expect_contract_error(
        lambda: validate_candidate_postimage_bytes(candidate.rows, tampered_bytes),
        contains="hash mismatch",
    )
    _expect_contract_error(
        lambda: validate_candidate_postimage_bytes(candidate.rows[:-1], exact_bytes),
        contains="exactly 14",
    )
    unsafe_rows = [dict(row) for row in candidate.rows]
    unsafe_rows[0]["path"] = "../escape"
    _expect_contract_error(
        lambda: validate_candidate_postimage_bytes(unsafe_rows, exact_bytes),
        contains="unsafe/noncanonical path",
    )
    wrong_packet_rows = [dict(row) for row in candidate.rows]
    wrong_packet_rows[0]["packet_id"] = "R0015"
    _expect_contract_error(
        lambda: validate_candidate_postimage_bytes(wrong_packet_rows, exact_bytes),
        contains="packet census",
    )
    captured_by_relative = {
        item.path.relative_to(ROOT).as_posix(): item
        for item in inputs.review_artifacts
    }
    r0014_request_relative = next(
        relative
        for relative in CANDIDATE_IMPLEMENTATION_INPUT_SHA256
        if "/R0014.json" in relative
    )
    r0014_request = dict(
        parse_strict_json_bytes(
            captured_by_relative[r0014_request_relative].raw,
            label="self-test R0014 request",
        )
    )
    _validate_candidate_packet_request(r0014_request, "R0014", candidate.rows)
    tampered_request = json.loads(json.dumps(r0014_request))
    tampered_request["paths"].pop()
    _expect_contract_error(
        lambda: _validate_candidate_packet_request(
            tampered_request, "R0014", candidate.rows
        ),
        contains="path inventory mismatch",
    )
    tampered_request = json.loads(json.dumps(r0014_request))
    tampered_request["patch"]["sha256"] = "0" * 64
    _expect_contract_error(
        lambda: _validate_candidate_packet_request(
            tampered_request, "R0014", candidate.rows
        ),
        contains="patch binding mismatch",
    )

    r0014_status = {
        row["path"]: ("A" if row["preimage_blob_oid"] == "-" else "M")
        for row in candidate.rows
        if row["packet_id"] == "R0014"
    }
    _require_candidate_diff_status(candidate.rows, ("R0014",), r0014_status)
    wrong_status = dict(r0014_status)
    status_path = next(iter(wrong_status))
    wrong_status[status_path] = "M" if wrong_status[status_path] == "A" else "A"
    _expect_contract_error(
        lambda: _require_candidate_diff_status(
            candidate.rows, ("R0014",), wrong_status
        ),
        contains="path/status mismatch",
    )
    object_id = "a" * 40
    assert _parse_candidate_index_entry(
        f"100644 {object_id} 0\tpath.lean\n".encode("ascii"), "path.lean"
    ) == ("100644", object_id)
    _expect_contract_error(
        lambda: _parse_candidate_index_entry(
            f"100755 {object_id} 0\tpath.lean\n".encode("ascii"), "path.lean"
        ),
        contains="unsupported mode/OID",
    )

    saved_git_index = os.environ.get("GIT_INDEX_FILE")
    try:
        os.environ["GIT_INDEX_FILE"] = "poisoned-real-index"
        sanitized = _ambient_git_environment()
        assert sanitized.get("GIT_INDEX_FILE") is None
        assert sanitized["GIT_NO_REPLACE_OBJECTS"] == "1"
        assert sanitized["GIT_OPTIONAL_LOCKS"] == "0"
    finally:
        if saved_git_index is None:
            os.environ.pop("GIT_INDEX_FILE", None)
        else:
            os.environ["GIT_INDEX_FILE"] = saved_git_index

    stale_owner = EnvironmentSnapshot(
        selected={
            "NumStability.FloatingPointFormat.problem2_9Source": (
                EnvironmentDeclaration(
                    fqn="NumStability.FloatingPointFormat.problem2_9Source",
                    owner_module=APPROVED_I01_OWNER_DESTINATIONS[
                        "NumStability.FloatingPointFormat.problem2_9Source"
                    ],
                    kind="definition",
                    protected=False,
                    visibility="public",
                    normalized_type_sha256="0" * 64,
                )
            )
        },
        public_names_by_owner={},
    )
    _expect_contract_error(
        lambda: require_exact_c0007_owner_environment(
            stale_owner,
            {
                "NumStability.FloatingPointFormat.problem2_9Source": (
                    APPROVED_I01_C0007_OWNER_MODULES[
                        "NumStability.FloatingPointFormat.problem2_9Source"
                    ]
                )
            },
        ),
        contains="candidate/stale artifacts are forbidden",
    )
    assert "run_environment_extractor" not in validate_candidate_review_delta.__code__.co_names


def self_test_candidate_review_delta() -> None:
    global C0007_ASSERTION_COUNT
    global C0007_DOCUMENTED_ENTRYPOINT_COUNT
    global C0007_ISOLATED_TEST_MODULE_COUNT
    global C0007_SELECTED_DECLARATION_COUNT
    global C0007_TEST_CONTRACT_SHA256

    counterexample = (
        "NumStability.Source.Higham.Chapter02.Problem09.DoubleRounding."
        "Counterexample"
    )
    inputs_owner = counterexample + ".Inputs"
    pnorm = "NumStability.Algorithms.NormEstimation.PNorm.All"
    series = "NumStability.Source.Higham.Chapter17.Results.Series"
    historical = "NumStability.Analysis.DoubleRounding"
    entrypoint = "NumStability.Entry"
    base_existing = sorted(
        {row["declaration"] for row in approved_i01_evidence_json()}
        - APPROVED_I01_NEW_FQNS
    )
    owners = {
        "NumStability.RectPNormPair.oneColumnValueRect": pnorm,
        "NumStability.FloatingPointFormat.binary64MantissaExtendedLocalFormat": counterexample,
        "NumStability.FloatingPointFormat.problem2_9_direct_double_ne_double_rounded_extended64": counterexample,
        "NumStability.summable_infNorm_matPow": series,
    }

    def fixture_module(
        name: str,
        *,
        imports: Sequence[str] = (),
        exported: Sequence[str] | None = None,
        assertions: Sequence[str] = (),
    ) -> Module:
        code = "".join(f"#check {fqn}\n" for fqn in assertions)
        return Module(
            name=name,
            path=ROOT / (name.replace(".", "/") + ".lean"),
            imports=tuple(imports),
            exported_imports=tuple(imports if exported is None else exported),
            text=code,
            code_mask=code,
        )

    base_modules: dict[str, Module] = {
        counterexample: fixture_module(counterexample),
        pnorm: fixture_module(pnorm),
        series: fixture_module(series),
        historical: fixture_module(historical, imports=(counterexample,)),
        entrypoint: fixture_module(entrypoint, imports=(counterexample,)),
    }
    base_tests: list[str] = []
    for index, fqn in enumerate(base_existing):
        test_name = f"NumStabilityTest.Base.Existing{index}"
        base_tests.append(test_name)
        owner = owners[fqn]
        base_modules[test_name] = fixture_module(
            test_name, imports=(owner,), assertions=(fqn,)
        )
    base_modules[TEST_ROOT] = fixture_module(TEST_ROOT, imports=base_tests)

    candidate_modules = dict(base_modules)
    candidate_modules[inputs_owner] = fixture_module(inputs_owner)
    candidate_modules[counterexample] = fixture_module(
        counterexample, imports=(inputs_owner,)
    )
    candidate_modules[historical] = fixture_module(
        historical, imports=(inputs_owner,)
    )
    approved_by_test: dict[str, list[Mapping[str, Any]]] = {}
    for row in approved_i01_evidence_json():
        approved_by_test.setdefault(row["test_module"], []).append(row)
    for test_module, rows in approved_by_test.items():
        surfaces = {row["surface"] for row in rows}
        assert len(surfaces) == 1
        candidate_modules[test_module] = fixture_module(
            test_module,
            imports=(next(iter(surfaces)),),
            assertions=tuple(
                row["declaration"]
                for row in rows
                for _ in range(row["assertion_occurrences"])
            ),
        )
    i01_all = "NumStabilityTest.Reorganization.I01.All"
    candidate_modules[i01_all] = fixture_module(
        i01_all, imports=tuple(sorted(approved_by_test))
    )
    candidate_modules[TEST_ROOT] = fixture_module(
        TEST_ROOT, imports=(*base_tests, i01_all)
    )

    tiers = {
        "exact": {historical: "compatibility"},
        "prefixes": [],
    }
    baseline_declarations = [
        {
            "fqn": fqn,
            "owner_module": owners[fqn],
            "expected_entrypoint_reachability": (
                [entrypoint]
                if fqn
                == "NumStability.FloatingPointFormat.binary64MantissaExtendedLocalFormat"
                else []
            ),
        }
        for fqn in base_existing
    ]
    baseline = {
        "declarations": baseline_declarations,
        "derivation": {"documented_entrypoints": [entrypoint]},
    }
    _, base_derivation = derive_test_selections(base_modules, tiers)
    saved_ratchets = (
        C0007_ASSERTION_COUNT,
        C0007_DOCUMENTED_ENTRYPOINT_COUNT,
        C0007_ISOLATED_TEST_MODULE_COUNT,
        C0007_SELECTED_DECLARATION_COUNT,
        C0007_TEST_CONTRACT_SHA256,
    )
    C0007_ASSERTION_COUNT = base_derivation["assertion_count"]
    C0007_DOCUMENTED_ENTRYPOINT_COUNT = 1
    C0007_ISOLATED_TEST_MODULE_COUNT = base_derivation[
        "isolated_test_module_count"
    ]
    C0007_SELECTED_DECLARATION_COUNT = base_derivation[
        "selected_declaration_count"
    ]
    C0007_TEST_CONTRACT_SHA256 = base_derivation["contract_sha256"]
    try:
        validate_candidate_review_delta(
            baseline=baseline,
            base_modules=base_modules,
            candidate_modules=candidate_modules,
            base_tiers=tiers,
            candidate_tiers=tiers,
        )

        missing_surface = dict(candidate_modules)
        missing_surface.pop(inputs_owner)
        _expect_contract_error(
            lambda: validate_candidate_review_delta(
                baseline=baseline,
                base_modules=base_modules,
                candidate_modules=missing_surface,
                base_tiers=tiers,
                candidate_tiers=tiers,
            )
        )

        assertion_drift = dict(candidate_modules)
        assertion_module = next(iter(approved_by_test))
        original = assertion_drift[assertion_module]
        assertion_drift[assertion_module] = fixture_module(
            assertion_module,
            imports=original.imports,
            assertions=("NumStability.Unreviewed",),
        )
        _expect_contract_error(
            lambda: validate_candidate_review_delta(
                baseline=baseline,
                base_modules=base_modules,
                candidate_modules=assertion_drift,
                base_tiers=tiers,
                candidate_tiers=tiers,
            ),
            contains="exact reviewed",
        )

        wrong_tiers = {"exact": {}, "prefixes": []}
        _expect_contract_error(
            lambda: validate_candidate_review_delta(
                baseline=baseline,
                base_modules=base_modules,
                candidate_modules=candidate_modules,
                base_tiers=tiers,
                candidate_tiers=wrong_tiers,
            ),
            contains="exact reviewed",
        )

        import_drift = dict(candidate_modules)
        original = import_drift[assertion_module]
        import_drift[assertion_module] = fixture_module(
            assertion_module,
            imports=(*original.imports, entrypoint),
            assertions=tuple(
                row["declaration"] for row in approved_by_test[assertion_module]
            ),
        )
        _expect_contract_error(
            lambda: validate_candidate_review_delta(
                baseline=baseline,
                base_modules=base_modules,
                candidate_modules=import_drift,
                base_tiers=tiers,
                candidate_tiers=tiers,
            ),
            contains="exact reviewed",
        )

        unreachable_root = dict(candidate_modules)
        unreachable_root[TEST_ROOT] = fixture_module(
            TEST_ROOT, imports=base_tests
        )
        _expect_contract_error(
            lambda: validate_candidate_review_delta(
                baseline=baseline,
                base_modules=base_modules,
                candidate_modules=unreachable_root,
                base_tiers=tiers,
                candidate_tiers=tiers,
            ),
            contains="exact reviewed",
        )

        wrong_destination_export = dict(candidate_modules)
        wrong_destination_export[counterexample] = fixture_module(counterexample)
        _expect_contract_error(
            lambda: validate_candidate_review_delta(
                baseline=baseline,
                base_modules=base_modules,
                candidate_modules=wrong_destination_export,
                base_tiers=tiers,
                candidate_tiers=tiers,
            ),
            contains="entrypoint reachability",
        )

        wrong_entrypoint = dict(candidate_modules)
        wrong_entrypoint[entrypoint] = fixture_module(entrypoint)
        _expect_contract_error(
            lambda: validate_candidate_review_delta(
                baseline=baseline,
                base_modules=base_modules,
                candidate_modules=wrong_entrypoint,
                base_tiers=tiers,
                candidate_tiers=tiers,
            ),
            contains="entrypoint reachability",
        )
    finally:
        (
            C0007_ASSERTION_COUNT,
            C0007_DOCUMENTED_ENTRYPOINT_COUNT,
            C0007_ISOLATED_TEST_MODULE_COUNT,
            C0007_SELECTED_DECLARATION_COUNT,
            C0007_TEST_CONTRACT_SHA256,
        ) = saved_ratchets


def self_test_atomic_json_writer() -> None:
    with tempfile.TemporaryDirectory(prefix="supported-api-writer-test-") as temp_name:
        temp = Path(temp_name)
        destination = temp / "contract.json"
        old_value = {"accepted": "old"}
        old_payload = canonical_json_bytes(old_value)
        destination.write_bytes(old_payload)

        calls: list[str] = []
        new_value = {"accepted": "new", "ordered": [False, 1, 1.0]}
        write_json(
            destination,
            new_value,
            pre_replace_check=lambda: calls.append("checked"),
        )
        assert calls == ["checked"]
        assert destination.read_bytes() == canonical_json_bytes(new_value)
        assert json_exact_equal(
            capture_json_document(destination, require_canonical=True).value,
            new_value,
        )
        assert not tuple(temp.glob(f".{destination.name}.*.tmp"))

        destination.write_bytes(old_payload)

        def reject_freshness() -> None:
            raise ContractError("synthetic freshness rejection")

        _expect_contract_error(
            lambda: write_json(
                destination,
                new_value,
                pre_replace_check=reject_freshness,
            ),
            contains="synthetic freshness rejection",
        )
        assert destination.read_bytes() == old_payload
        assert not tuple(temp.glob(f".{destination.name}.*.tmp"))

        absent = temp / "absent.json"
        _expect_contract_error(
            lambda: write_json(
                absent,
                new_value,
                pre_replace_check=reject_freshness,
            ),
            contains="synthetic freshness rejection",
        )
        assert not absent.exists()
        assert not tuple(temp.glob(f".{absent.name}.*.tmp"))

        directory_destination = temp / "directory.json"
        directory_destination.mkdir()
        try:
            write_json(directory_destination, new_value)
        except OSError:
            pass
        else:
            raise AssertionError("atomic replacement of a directory unexpectedly succeeded")
        assert directory_destination.is_dir()
        assert not tuple(temp.glob(f".{directory_destination.name}.*.tmp"))

        _expect_contract_error(
            lambda: write_json(temp / "nonfinite.json", {"value": float("nan")}),
            contains="canonical strict JSON",
        )


def self_test_bounded_authorization() -> None:
    authorization_document = capture_json_document(
        ROOT / BOUNDED_AUTHORIZATION_RELATIVE,
        require_canonical=True,
    )
    exact = authorization_document.value
    exact_sha256 = authorization_document.capture.identity.sha256
    assert exact_sha256 == CI_ONLY_RECOVERY_AUTHORIZATION_SHA256
    failures = validate_bounded_authorization_document(
        exact, authorization_sha256=exact_sha256
    )
    assert not failures, failures

    mutations: list[Callable[[dict[str, Any]], None]] = [
        lambda value: value["base"].__setitem__("control_head_sha", "0" * 40),
        lambda value: value.__setitem__("phase_id", "another-phase"),
        lambda value: value["source"].__setitem__("instruction", "broader grant"),
        lambda value: value.__setitem__("recorded_at", "2026-08-26T12:56:22Z"),
        lambda value: value["supersedes"].__setitem__("sha256", "0" * 64),
        lambda value: value.__setitem__("authorized_actions", []),
        lambda value: value["authorized_actions"].append("activate M13 implementation"),
        lambda value: value.__setitem__("activation_conditions", []),
        lambda value: value["preserved_exclusions"].reverse(),
        lambda value: value["expiry"].__setitem__("terminal_control_state", "verified"),
        lambda value: value["run_policy"].__setitem__("rerun_authorized", True),
        lambda value: value["scope"].__setitem__("implementation_authorized", True),
        lambda value: value["scope"].__setitem__("remote_main_mutation_authorized", 0),
        lambda value: value["scope"]["authorized_path_manifest"].__setitem__(
            "row_count", 9
        ),
        lambda value: value["scope"]["supported_api_record"].__setitem__(
            "required_null_fields", ["decision"]
        ),
        lambda value: value.__setitem__("decision", "approved"),
        lambda value: value.__setitem__("authorization_id", "terminal-v3"),
        lambda value: value.__setitem__("schema_version", 3.0),
        lambda value: value.__setitem__("extra_grant", True),
    ]
    for mutate in mutations:
        changed = json.loads(json.dumps(exact))
        mutate(changed)
        assert validate_bounded_authorization_document(
            changed, authorization_sha256=CI_ONLY_RECOVERY_AUTHORIZATION_SHA256
        )

    historical = json.loads(json.dumps(HISTORICAL_TERMINAL_V2_AUTHORIZATION))
    assert validate_bounded_authorization_document(
        historical,
        authorization_sha256=HISTORICAL_TERMINAL_V2_AUTHORIZATION_SHA256,
    )

    manifest = capture_file(ROOT / BOUNDED_MANIFEST_RELATIVE)
    assert not validate_ci_only_recovery_manifest(manifest)
    assert manifest.raw == CI_ONLY_RECOVERY_MANIFEST_BYTES
    assert (
        sha256_bytes(("\n".join(CI_ONLY_RECOVERY_PATHS) + "\n").encode("utf-8"))
        == CI_ONLY_RECOVERY_PATH_SET_SHA256
    )
    assert (
        sha256_bytes(
            ("\n".join(CI_ONLY_RECOVERY_ARTIFACT_PATHS) + "\n").encode("utf-8")
        )
        == CI_ONLY_RECOVERY_ARTIFACT_PATH_SET_SHA256
    )
    assert (
        capture_file(ROOT / WORKFLOW_RELATIVE).identity.sha256
        == CI_ONLY_RECOVERY_WORKFLOW_SHA256
    )
    for relative, expected in HISTORICAL_P_PACKET_ARTIFACTS.items():
        capture = capture_file(ROOT / relative)
        assert capture.identity.sha256 == expected["sha256"]
        assert capture.identity.size == expected["byte_count"]
    assert (
        sha256_bytes(
            (
                "\n".join(sorted(HISTORICAL_P_PACKET_ARTIFACTS)) + "\n"
            ).encode("utf-8")
        )
        == HISTORICAL_P_PACKET_PATH_SET_SHA256
        == CI_ONLY_RECOVERY_HISTORICAL_PACKET_PATH_SET_SHA256
    )
    assert (
        capture_file(ROOT / FULL_TESTS_CORRECTION_RELATIVE).identity.sha256
        == HISTORICAL_FULL_TESTS_CORRECTION_SHA256
    )
    assert re.fullmatch(
        r"[0-9A-F]{64}", CI_RECOVERY_COMPLETION_CHECKER_SHA256
    )
    completion_sha256 = capture_file(ROOT / COMPLETION_CHECKER_RELATIVE).identity.sha256
    require_exact_ci_recovery_completion_checker_sha(completion_sha256)
    _expect_contract_error(
        lambda: require_exact_ci_recovery_completion_checker_sha("0" * 64),
        contains="current completion checker drift",
    )


def self_test() -> None:
    self_test_strict_json()
    self_test_module_header_parser()
    self_test_environment_tsv()
    self_test_ratchets_and_pending_review()
    self_test_environment_build_cache()
    self_test_candidate_reconstruction()
    self_test_candidate_review_delta()
    self_test_atomic_json_writer()
    self_test_bounded_authorization()
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

    # Recovery is a terminal, CI-only successor to immutable failed P.  Its
    # contract has no activation/review/implementation state and always returns
    # a false implementation-approval bit even when every recovery binding is exact.
    with tempfile.TemporaryDirectory(prefix="supported-api-recovery-test-") as temp_name:
        temp = Path(temp_name)
        authorization = capture_json_document(
            ROOT / BOUNDED_AUTHORIZATION_RELATIVE,
            require_canonical=True,
        ).value
        current_captures: dict[str, CapturedFile] = {}
        for index, relative in enumerate(CI_ONLY_RECOVERY_ARTIFACT_PATHS):
            fixture = temp / f"artifact-{index}.bin"
            fixture.write_bytes(f"recovery artifact {index}\n".encode("ascii"))
            current_captures[relative] = capture_file(fixture)
        current_hashes = {
            relative: capture.identity.sha256
            for relative, capture in current_captures.items()
        }
        artifacts = [
            {
                "base_blob_oid": CI_ONLY_RECOVERY_ARTIFACT_BASE_BLOB_OIDS[relative],
                "base_mode": "100644",
                "operation": "modify",
                "packet_id": "CI01R1",
                "path": relative,
                "post_blob_oid": git_blob_oid(current_captures[relative].raw),
                "post_mode": "100644",
                "sha256": current_hashes[relative],
            }
            for relative in CI_ONLY_RECOVERY_ARTIFACT_PATHS
        ]
        contract = expected_ci_only_recovery_contract(artifacts, authorization)
        contract_path = temp / "contract.json"
        exact_failures, implementation_approved = ci_only_recovery_contract_state(
            contract,
            authorization=authorization,
            current_file_hashes=current_hashes,
            current_file_captures=current_captures,
            mode="staging",
            contract_path=contract_path,
        )
        assert not exact_failures and not implementation_approved

        completion_failures, completion_approved = ci_only_recovery_contract_state(
            contract,
            authorization=authorization,
            current_file_hashes=current_hashes,
            current_file_captures=current_captures,
            mode="completion",
            contract_path=contract_path,
        )
        assert completion_failures and not completion_approved

        mutations: list[Callable[[dict[str, Any]], None]] = [
            lambda value: value.__setitem__("schema_version", 4.0),
            lambda value: value.__setitem__("record_kind", "c0007_bounded_planned_control"),
            lambda value: value.__setitem__("graph", ["B->P", "P->A"]),
            lambda value: value["permissions"].__setitem__(
                "implementation_authorized", True
            ),
            lambda value: value["lifecycle"].__setitem__(
                "continuation_authorized", True
            ),
            lambda value: value["lifecycle"].__setitem__("state", "active"),
            lambda value: value["failed_planned_control"]["ci"].__setitem__(
                "conclusion", "success"
            ),
            lambda value: value["historical_packet_artifacts"].pop(),
            lambda value: value["artifacts"][0].__setitem__(
                "packet_id", "R0014"
            ),
            lambda value: value["artifacts"][0].__setitem__(
                "post_blob_oid", "0" * 40
            ),
            lambda value: value["artifacts"][0].__setitem__("sha256", "0" * 64),
            lambda value: value["workflow"].__setitem__(
                "sha256", HISTORICAL_P_WORKFLOW_SHA256
            ),
            lambda value: value["workflow"].__setitem__(
                "checkout_ref_expression",
                "refs/heads/codex/reorg-closeout-2026-08-m13-i01",
            ),
            lambda value: value.__setitem__("constraints_sha256", "0" * 64),
            lambda value: value.__setitem__("reviews", {"activation": "forbidden"}),
        ]
        for mutate in mutations:
            changed = json.loads(json.dumps(contract))
            mutate(changed)
            mutation_failures, mutation_approved = ci_only_recovery_contract_state(
                changed,
                authorization=authorization,
                current_file_hashes=current_hashes,
                current_file_captures=current_captures,
                mode="staging",
                contract_path=contract_path,
            )
            assert mutation_failures and not mutation_approved

        missing_failures, missing_approved = ci_only_recovery_contract_state(
            None,
            authorization=authorization,
            current_file_hashes=current_hashes,
            current_file_captures=current_captures,
            mode="staging",
            contract_path=contract_path,
        )
        assert missing_failures and not missing_approved

        incomplete_hashes = dict(current_hashes)
        incomplete_hashes.pop(SUPPORTED_API_REVIEW_RELATIVE)
        incomplete_failures, incomplete_approved = ci_only_recovery_contract_state(
            contract,
            authorization=authorization,
            current_file_hashes=incomplete_hashes,
            current_file_captures=current_captures,
            mode="staging",
            contract_path=contract_path,
        )
        assert incomplete_failures and not incomplete_approved

    nonnull_review = json.loads(json.dumps(review))
    nonnull_review["decision"] = "approved"
    nonnull_review["reviewer"] = "primary-human"
    nonnull_review["reviewed_at_utc"] = "2026-08-26T12:56:21Z"
    nonnull_failures = validate_review_schema(nonnull_review, baseline)
    assert any("must remain null/pending" in item for item in nonnull_failures)
    assert any("must not claim a reviewer" in item for item in nonnull_failures)

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


def load_json(path: Path, *, require_canonical: bool = False) -> dict[str, Any]:
    """Compatibility wrapper; lifecycle code retains the full JsonDocument."""

    return dict(
        capture_json_document(path, require_canonical=require_canonical).value
    )


def _fsync_directory(directory: Path) -> None:
    """Persist a directory entry where the host exposes directory fsync."""

    flags = os.O_RDONLY | getattr(os, "O_DIRECTORY", 0)
    try:
        descriptor = os.open(directory, flags)
    except OSError as error:
        if os.name == "nt":
            return
        raise ContractError(f"cannot open output directory for fsync: {directory}: {error}") from error
    try:
        os.fsync(descriptor)
    except OSError as error:
        if os.name != "nt":
            raise ContractError(f"cannot fsync output directory: {directory}: {error}") from error
    finally:
        os.close(descriptor)


def write_json(
    path: Path,
    value: Mapping[str, Any],
    *,
    pre_replace_check: Callable[[], None] | None = None,
) -> None:
    """Atomically install one verified canonical JSON object in its destination."""

    payload = canonical_json_bytes(value)
    if len(payload) > MAX_JSON_BYTES:
        raise ContractError(
            f"generated {path} is {len(payload)} bytes, exceeding {MAX_JSON_BYTES}"
        )
    parsed_payload = parse_strict_json_bytes(payload, label=f"generated {path}")
    if not json_exact_equal(parsed_payload, value):
        raise ContractError(f"generated canonical JSON does not type-exactly round-trip: {path}")
    path.parent.mkdir(parents=True, exist_ok=True)
    descriptor: int | None = None
    temporary: Path | None = None
    try:
        descriptor, temporary_name = tempfile.mkstemp(
            prefix=f".{path.name}.", suffix=".tmp", dir=path.parent
        )
        temporary = Path(temporary_name)
        with os.fdopen(descriptor, "wb") as handle:
            descriptor = None
            handle.write(payload)
            handle.flush()
            os.fsync(handle.fileno())
        temporary_document = capture_json_document(
            temporary, require_canonical=True
        )
        if (
            temporary_document.capture.raw != payload
            or not json_exact_equal(temporary_document.value, value)
        ):
            raise ContractError(
                f"temporary canonical JSON write verification failed: {temporary}"
            )
        if pre_replace_check is not None:
            pre_replace_check()
        verify_captured_files((temporary_document.capture,))
        os.replace(temporary, path)
        temporary = None
        _fsync_directory(path.parent)
        written = capture_json_document(path, require_canonical=True)
        if written.capture.raw != payload or not json_exact_equal(written.value, value):
            raise ContractError(f"generated JSON write verification failed: {path}")
    finally:
        if descriptor is not None:
            os.close(descriptor)
        if temporary is not None:
            try:
                temporary.unlink()
            except FileNotFoundError:
                pass


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
                "supported-API checker self-test passed: strict/canonical captured JSON, "
                "exact leading Module.header and literal/quotation masking, Lean module-mode "
                "export semantics, bounded streaming TSV/type hashing, five independent C0007 "
                "ratchets, exact pending review, CI-only recovery authority/lifecycle, "
                "and supported declaration/visibility drift rejection"
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

        authorization_document = capture_json_document(
            ROOT / BOUNDED_AUTHORIZATION_RELATIVE,
            require_canonical=True,
        )
        authorization_failures = validate_bounded_authorization_document(
            authorization_document.value,
            authorization_sha256=authorization_document.capture.identity.sha256,
        )
        if authorization_failures:
            raise ContractError(
                "invalid bounded authorization:\n" + "\n".join(authorization_failures)
            )
        manifest_capture = capture_file(ROOT / BOUNDED_MANIFEST_RELATIVE)
        manifest_failures = validate_ci_only_recovery_manifest(manifest_capture)
        if manifest_failures:
            raise ContractError(
                "invalid CI-only recovery manifest:\n" + "\n".join(manifest_failures)
            )

        if args.write_baseline:
            inputs = capture_generation_inputs()
            value = build_contract(
                checkpoint_id=args.checkpoint_id,
                checkpoint_code_sha=args.checkpoint_code_sha,
                inputs=inputs,
            )
            failures = validate_baseline_schema(value, inputs=inputs)
            if failures:
                raise ContractError("generated invalid baseline:\n" + "\n".join(failures))
            verify_generation_inputs(inputs)

            def verify_baseline_write_epoch() -> None:
                verify_generation_inputs(inputs)
                verify_captured_files(
                    (authorization_document.capture, manifest_capture)
                )

            write_json(
                baseline_path,
                value,
                pre_replace_check=verify_baseline_write_epoch,
            )
            verify_generation_inputs(inputs)
            verify_captured_files((authorization_document.capture, manifest_capture))
            print(
                f"wrote supported-API baseline: {len(value['declarations'])} declarations, "
                f"{len(value['visibility_guard'])} entrypoints, {baseline_path}"
            )
            return 0

        baseline_document = capture_json_document(
            baseline_path, require_canonical=True
        )
        baseline = baseline_document.value
        inputs = capture_generation_inputs()
        schema_failures = validate_baseline_schema(baseline, inputs=inputs)
        if schema_failures:
            for failure in schema_failures:
                print(f"error: {failure}", file=sys.stderr)
            return 1
        if args.write_review:
            if classify_implementation_state() != "staging":
                raise ContractError("pending review generation requires exact pre-I01 state")
            allow_exact_implementation_dirty_paths(False)
            value = build_additive_review(baseline, inputs=inputs)
            failures = validate_review_schema(value, baseline, inputs=inputs)
            if failures:
                raise ContractError("generated invalid review:\n" + "\n".join(failures))
            verify_generation_inputs(inputs)

            def verify_review_write_epoch() -> None:
                verify_generation_inputs(inputs)
                verify_captured_files(
                    (
                        baseline_document.capture,
                        authorization_document.capture,
                        manifest_capture,
                    )
                )
                require_exact_candidate_staging_state(inputs)

            write_json(
                review_path,
                value,
                pre_replace_check=verify_review_write_epoch,
            )
            verify_generation_inputs(inputs)
            verify_captured_files(
                (
                    baseline_document.capture,
                    authorization_document.capture,
                    manifest_capture,
                )
            )
            print(
                "wrote pending supported-API review facts: 5 modules, 9 assertions, "
                f"1 additive declaration, 2 owner moves, {review_path}"
            )
            return 0

        review_document = capture_json_document(review_path, require_canonical=True)
        review = review_document.value
        review_failures = validate_review_schema(review, baseline, inputs=inputs)
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

        # At P/A/T the complete pending record, not merely selected metadata rows,
        # must equal a fresh exact-C0007 rendering.  At I the already-gated record
        # is immutable machine evidence whose captured raw bytes are independently
        # hash-bound by the authenticated lifecycle contract.
        c0007_review_failures: list[str] = []
        if effective_mode == "staging":
            fresh_review = build_additive_review(baseline, inputs=inputs)
            c0007_review_failures.extend(
                validate_exact_pending_review(review, fresh_review)
            )

        activation_document = (
            capture_json_document(activation_path, require_canonical=True)
            if activation_path.is_file()
            else None
        )
        activation_contract = (
            activation_document.value if activation_document is not None else None
        )
        (
            current_file_hashes,
            current_file_captures,
            lifecycle_captures,
        ) = capture_lifecycle_file_hashes(
            baseline=baseline_document,
            review=review_document,
            authorization=authorization_document,
            inputs=inputs,
        )
        activation_failures, activation_approved = ci_only_recovery_contract_state(
            activation_contract,
            authorization=authorization_document.value,
            current_file_hashes=current_file_hashes,
            current_file_captures=current_file_captures,
            mode=effective_mode,
            contract_path=activation_path,
        )

        current = current_contract_from_baseline(
            baseline, review, inputs=inputs
        )
        verify_generation_inputs(inputs)
        verify_captured_files(
            (*lifecycle_captures,)
            + (
                (activation_document.capture,)
                if activation_document is not None
                else ()
            )
        )
        failures = (
            state_failures
            + c0007_review_failures
            + activation_failures
            + compare_contracts(
                baseline,
                current,
                review,
                mode=effective_mode,
                activation_approved=activation_approved,
            )
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
    except (
        ContractError,
        KeyError,
        OSError,
        subprocess.SubprocessError,
        TypeError,
        ValueError,
    ) as error:
        print(f"error: {error}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
