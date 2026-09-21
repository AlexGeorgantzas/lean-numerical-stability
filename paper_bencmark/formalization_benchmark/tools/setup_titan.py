from __future__ import annotations

import argparse
import json
import os
import shlex
import shutil
import stat
import subprocess
import sys
import tempfile
from pathlib import Path
from typing import Any, Mapping

from codex_driver import CodexDriver
from common import (
    BenchmarkError,
    canonical_json_bytes,
    file_tree_fingerprint,
    load_json,
    minimal_system_mount_args,
    sha256_bytes,
    sha256_file,
    stable_regular_bytes,
    treatment_free_runtime_manifest,
    tree_manifest,
    utc_now,
    visible_system_runtime_manifest,
    write_bytes_atomic,
    write_json_atomic,
)
from deployment import GLOBAL_REGISTRY_ROOT, Deployment
from formalization_validator import run_bounded_command
from hardware import (
    frozen_hardware_identity,
    host_cpu_selection,
    snapshot_hardware,
    systemd_service_envelope_prefix,
)
from manifest_control import EXPECTED_BASE_COMMIT, task_record, verify_manifest
from measure_library_build import validate_build_record
from runtime_canary import run_runtime_canaries


ROOT = Path(__file__).resolve().parents[1]
REPOSITORY_ROOT = ROOT.parents[1]
FROZEN_LIBRARY_COMMIT = "45813a95dacf577461bae13f033af0dbc985a225"
FROZEN_TOOLCHAIN = "leanprover/lean4:v4.29.0-rc3"
PILOT10_PILOT_ID = "formalization-benchmark-pilot-10"
PILOT10_RELEASE_COMMIT = "c75840169037df96af3e4b946c8a6372e33f7377"
PILOT10_MANIFEST_PAYLOAD_SHA256 = (
    "753396d3d41ee5fae0ac488afb76b0ecf67a2c9c677a7ee91bffd7caf7e9b60a"
)
PILOT10_MANIFEST_FILE_SHA256 = (
    "36398dcefc3a24f68e0f647f4e19ea6ddc384eb70a1ce0994974e09d5955be72"
)
PILOT10_DEPLOYMENT_SHA256 = (
    "18c67fd64df4ee5ef1c3802ab6399869fda273064be37de917243757eb8b876a"
)
PILOT10_BUILD_RECORD_SHA256 = (
    "3d9a00ac37216feaab03010538b992b9738d19b6ec3de53db35b32b62a0e6794"
)
PILOT10_QUALIFICATION_SHA256 = (
    "ba26624b9e4dba410c1d133667656967afe7508302a02168e8b3ca87709ed711"
)
PILOT10_QUALIFICATION_ROLES_TREE_SHA256 = (
    "a54d41a8bad20547b3092966c91c3e58f3eadb6ba624190efaab8834c7129b4e"
)
PILOT10_FAILED_WARM_ROOT_SHA256 = (
    "1f532db6810812309a8f36f6963fadd038851d95daa8a80cfa6540ede4399e08"
)
PILOT10_SCOUT_TURN_SHA256 = (
    "b3e2663e125edd1cd661b70dec20591b66b1e0a30e3d924a76ab2c4056a776e6"
)
PILOT10_CHECKPOINT_TREE_SHA256 = (
    "4d835bc3ac9c7643619ab9bd88e42ee0182197a3d81cdde96c80c168f60774ee"
)
PILOT10_SCOUT_ARTIFACTS_TREE_SHA256 = (
    "7571bf6c4b8aa957efe8e2225ff63d923d87867632b9d0475580dfc62a90da8e"
)
PILOT9_PILOT_ID = "formalization-benchmark-pilot-9"
PILOT9_RELEASE_COMMIT = "16172f249084b517b8069859760517297e4fb4cf"
PILOT9_MANIFEST_PAYLOAD_SHA256 = (
    "7de3b3ad11a96f7b0e5afa1f0f33c1d05a59e095cc4710656b0db638d7785d49"
)
PILOT9_MANIFEST_FILE_SHA256 = (
    "4514b3f21733343a65793417160d0a6f74eee62befa61ce95f890a8e8e9adc36"
)
PILOT9_DEPLOYMENT_SHA256 = (
    "cf84e8cfeb47447be38055cb8cd2758c50ccb7ff98d6afe8bdf531e9ab480863"
)
PILOT9_BUILD_RECORD_SHA256 = (
    "7f12698294c2e10f68431d86a959bccf34698bda1dbf3fd236a7993349ae80fa"
)
PILOT9_QUALIFICATION_SHA256 = (
    "54efe6d01d9ef0a50235c905298779876a338e1f12806432a0f4f6b16ea2ca2a"
)
PILOT9_QUALIFICATION_ROLES_TREE_SHA256 = (
    "44abda6f8a174740bc65ace23dc21f92aa5c71c6385e37e855954d4c0ba8072c"
)
PILOT9_INCIDENT_RUN_ID = "H22-11-20260920T220652Z-bd624406"
PILOT9_INDEX_SHA256 = (
    "f7ff7d6e7d96b4ab26015351228f0ce7582f43cb66401fe9cac7b150bb877172"
)
PILOT9_PAIR_STATE_SHA256 = (
    "57d8d733988f0879783f6b6a0c2b14b989c6ae6815465dfbd1a7efa58eb60f26"
)
PILOT9_PAIR_REPORT_SHA256 = (
    "14df6656ebbaeb861447bb4eeebf162660d72e8cbb438edfc87c900440698de7"
)
PILOT9_L_CONDITION_STATE_SHA256 = (
    "cc63766f62353d366fa089ff93dccd52f5a9c43a2b127861e5046527a0f0e03b"
)
PILOT9_N_CONDITION_STATE_SHA256 = (
    "80f23cb955671174b100aed6c49384b055ef3812ea825d27e2df9bbf59aaaf07"
)
PILOT9_AUDIT_INCIDENT_SHA256 = (
    "151c577b0f3684afae163f24f570cc19691ba32344e27c468625a368efa80c75"
)
PILOT8_PILOT_ID = "formalization-benchmark-pilot-8"
PILOT8_RELEASE_COMMIT = "c3c07630bc961675ed22c0e39b247242ed8539ff"
PILOT8_MANIFEST_PAYLOAD_SHA256 = (
    "9b958df6de4c2724e1b91cd4e3e56df60d0cc4dc8630f841919e505b92169b7f"
)
PILOT8_MANIFEST_FILE_SHA256 = (
    "3ce1b1ce8a0952bbfc7756365f4c4b66f23613f12add8283e6b3d9ecf3daade4"
)
PILOT8_DEPLOYMENT_SHA256 = (
    "3c680b39563e3e7c66e2892a16d7cb72f541ed04631d4b134cee101acda04588"
)
PILOT8_BUILD_RECORD_SHA256 = (
    "94a3cec672a8c67ef1f5ffeb842320b56b68f49df2d5bfc7daaa96e545b31584"
)
PILOT8_QUALIFICATION_SHA256 = (
    "e8e90208a08dfcf60ca336fab3e82edc1b240701df4ab0ff6e1ec31ce6165a2e"
)
PILOT8_QUALIFICATION_ROLES_TREE_SHA256 = (
    "8f091bde20bfd3411358cf942a1618aa8556a2e86bd26dca24d4670091ac5748"
)
PILOT8_INCIDENT_RUN_ID = "H22-11-20260920T204005Z-9c01c2fb"
PILOT8_INDEX_SHA256 = (
    "b5465f575d6d6db020b9ecf4d38b0efeef0e90e1c8768130afcb93f70b8179ee"
)
PILOT8_PAIR_STATE_SHA256 = (
    "26894a79e4cbbf0cf5fffac3dcab4846cc506a4db4c6dd6dbe1d77e998dd36ec"
)
PILOT8_PAIR_REPORT_SHA256 = (
    "3107c59a3fb32137297796a1b8d85df0e7b8319533d8f7955a247be93433628f"
)
PILOT8_CONDITION_STATE_SHA256 = (
    "aac5f7748d864bbb5934f4d388adcf9102a85612d4fe1e3bf28f287eec10484c"
)
PILOT8_AUDIT_INCIDENT_SHA256 = (
    "4363f8fde6b0121ab33372364bb0806967e43ff814b010b5fcc89f1e16195469"
)
PILOT7_PILOT_ID = "formalization-benchmark-pilot-7"
PILOT7_RELEASE_COMMIT = "44cfb84693ccc8686e00f831aa9fbdf6d20af0a2"
PILOT7_MANIFEST_PAYLOAD_SHA256 = (
    "077163f27773f0a918846e18c9f04ea11fd0c20c8088bdc66c46871052554d69"
)
PILOT7_MANIFEST_FILE_SHA256 = (
    "53432f3946acb4782a04deab3eb182748ce4709980599cb9ffdbfd66f919da04"
)
PILOT7_DEPLOYMENT_SHA256 = (
    "8258440ac97ec55a4775839fa2e5cd25e1e90d62005c4e9de2b29a037be9ec8e"
)
PILOT7_BUILD_RECORD_SHA256 = (
    "af3ad72d084743adecabcc9b5a1ebca09b89dd1ff28ee440a317dd2eab0e073a"
)
PILOT7_FAILED_QUALIFICATION_SHA256 = (
    "93e26b4e45f0eea423967a77083c95b0a708caaa361bd2f573e57ba598f9c8fd"
)
PILOT7_FAILED_QUALIFICATION_ROLES_TREE_SHA256 = (
    "f899abfa7e14e5615cc95130e584751337ccbd4f7dd3d1c867aa59e6c1383a52"
)
PILOT5_PILOT_ID = "formalization-benchmark-t2-pilot-5"
PILOT5_RELEASE_COMMIT = "131baed049dc97e114fbd420ee14b3239633a13d"
PILOT5_MANIFEST_PAYLOAD_SHA256 = (
    "78d056271ab96d96ab2282d40f7bbabeaa64daf0e3bcf5a620138f95d02d4ab6"
)
PILOT5_MANIFEST_FILE_SHA256 = (
    "12794fd4c622adcfde82972ce0eb94644dcec6bfaf92a5bcde175326d97d5d90"
)
PILOT5_DEPLOYMENT_SHA256 = (
    "41632d90da27b5d5edda4bcaad6648264bfb2d042d551858c0d62f89a363404f"
)
PILOT5_BUILD_RECORD_SHA256 = (
    "d9abf28dfa5444a78fc88ce6818fc4c0e4ed166296d922f5b53b46476f4316db"
)
PILOT5_QUALIFICATION_SHA256 = (
    "0c0c4ccb252b432e41025fa1f4e17dfa1df78c1f6f8c9a54801a32bd5ee97e16"
)
PILOT5_QUALIFICATION_ROLES_TREE_SHA256 = (
    "ec615f4b8b7914829942283b689441343e22e744a57ac17006bb46316b04dedf"
)
PILOT5_SEALED_PAIRS = {
    "P01-T2": {
        "run_id": "P01-T2-20260916T170046Z-91f2e89d",
        "index_sha256": "d2db1271f9710f5d3ff94284256492e822e9ea60b382882d0eb8f447dd913302",
        "state_sha256": "7641f60e23fdde4d1ff84c4bdf925a8883cbc875e382bb34de70b10e32cc7f3b",
        "report_sha256": "ff4666528a69b39d5522463073c0282164c0df3c6e1881ae5477695d7e4cc56d",
    },
    "P02-T2": {
        "run_id": "P02-T2-20260916T184927Z-3172f243",
        "index_sha256": "058cf470fc2d8397d0713b4bc3beb64447307bf906dfc6e9f434dad8805d7faa",
        "state_sha256": "fa6fbcefa301a26c2e94d9a2491b62c22f95edaed3c0f8e5afb5b57d0403d3b0",
        "report_sha256": "0ff7368b428dab9c0862f40e090fff8a618ebd70a78287036951764443ed619c",
    },
}
PILOT4_PILOT_ID = "formalization-benchmark-t2-pilot-4"
PILOT4_RELEASE_COMMIT = "09bb21292eba57d2390efe2e00e7e2063dfc7669"
PILOT4_MANIFEST_PAYLOAD_SHA256 = (
    "3a5db5447b120fbdd4793114f1469e273fb810c3223f00bce96bab52e8063d97"
)
PILOT4_MANIFEST_FILE_SHA256 = (
    "2773bc7265ec90ce37595abf57aaa7b2ba5b4a67b13bbf28c823513c109447bc"
)
PILOT4_DEPLOYMENT_SHA256 = (
    "bd9dbc1c1f7576399c767d9dc7cae19732965e5e21989d195720bb884b31a749"
)
PILOT4_BUILD_RECORD_SHA256 = (
    "42d1a09980a908d4b4757b174dff0239d20f9cc35e0e67dd7499a0bec60580ec"
)
PILOT4_FAILED_QUALIFICATION_SHA256 = (
    "930a69c9a059f8e00590a6689ea9d15177e27b435e901e724e57861a1db79c9a"
)
PILOT4_QUALIFICATION_ROLES_MANIFEST_SHA256 = (
    "7a2042cf41d11ebe83ff1a81739fcba54e9bf808790ac3bc187173af5431f7b9"
)
PILOT3_PILOT_ID = "formalization-benchmark-t2-pilot-3"
PILOT3_RELEASE_COMMIT = "2df140d15c207703e0a5f5a222eb34f223525f6d"
PILOT3_MANIFEST_PAYLOAD_SHA256 = (
    "46402dd9f63f5ee85d387762c07ff22ca7c25a7ef787552d6eb8b26c7007e183"
)
PILOT3_MANIFEST_FILE_SHA256 = (
    "bee6fc6e278364a6e215f25ec4e567daac16a50e88abf3d04831b527c0950581"
)
PILOT3_DEPLOYMENT_SHA256 = (
    "ee699c530894511fce8e96c7a39c6b76e9295cbde5ea4f96560a83751d8fb9a0"
)
PILOT3_INCIDENT_RUN_ID = "P01-T2-20260916T150151Z-40b3a1dd"
PILOT3_INDEX_SHA256 = (
    "578a3ff3d263ce7d9caa1a274787190e88dac88290ebd54e92fc2673a29d876e"
)
PILOT3_STATE_SHA256 = (
    "935e085b452af737fa7b43658024e1cd0431e834d0a400ebab2b00ec90e56860"
)
PILOT3_INCIDENT_REPORT_SHA256 = (
    "04e44175c8192d719a943b6d56f565b0e013ee737471ccd03fc8b4db896254c7"
)
PILOT3_QUALIFICATION_SHA256 = (
    "6d8155f5e3f626c572b8f950eb9dc3df8c3be853f6850cc2d6726f6261e29eea"
)
PREDECESSOR_PILOT_ID = "formalization-benchmark-t2-pilot-2"
PREDECESSOR_RELEASE_COMMIT = "a26d275b47e0d786a9b3aecdaa3584149f6aa3c3"
PREDECESSOR_MANIFEST_PAYLOAD_SHA256 = (
    "ebff35ac93a1bdbd1afb02c63e90339f974d377eb46474a171de149bc314fbd1"
)
PREDECESSOR_INCIDENT_RUN_ID = "P01-T2-20260916T084145Z-6dad064a"
PREDECESSOR_INCIDENT_REPORT_SHA256 = (
    "793d39f9578a52edf46f3549dace7279daac657a89548bce0178027a41362101"
)
PREDECESSOR_DEPLOYMENT_SHA256 = (
    "8b63df321fc16b52a91c514606315854c13096032b2c41aea07c29bd918399d2"
)
PREDECESSOR_MANIFEST_FILE_SHA256 = (
    "41497ccf66d2a6a195d2ad42d16168ac87b540406ca2bce00f9ed7439c0cab9a"
)
PREDECESSOR_INDEX_SHA256 = (
    "7bfd86ed0961721ab3636f40286ac1b3558171f68336d65c023645a8ba9bbde2"
)
PREDECESSOR_STATE_SHA256 = (
    "9d542c41975bd6e29dda95f52ab268295e795303a326364cbacecd2f49b0fbb8"
)
LEGACY_PILOT_ID = "formalization-benchmark-t2-pilot-1"
LEGACY_RELEASE_COMMIT = "98a707bca8d32b9af29771acd13ed6cdbfb7c806"
LEGACY_MANIFEST_PAYLOAD_SHA256 = (
    "8178fa0f4e8caa1964c36f8d4eaafcb713ed7c243e1516782cb79e617afb76a5"
)
LEGACY_INCIDENT_RUN_ID = "P01-T2-20260915T231647Z-f94727b2"
LEGACY_INCIDENT_REPORT_SHA256 = (
    "8f389436cab2a9a81ab72bf9127b846f6d435e3ec8ea9c12c3495380ae7864ca"
)
LEGACY_DEPLOYMENT_SHA256 = (
    "f7c84bd38cc0d1b69726b36c23fc5ac80a1fe7313c96debac089a671c3e0ac02"
)
LEGACY_MANIFEST_FILE_SHA256 = (
    "4bae3fd0288800d41bcf33e75cf616fc2547f335afba9ff7b6ee1328974dc83a"
)
LEGACY_INDEX_SHA256 = (
    "1b8cecb796b705990a48304b6a36afb3b2f44f8e6c0e2e656ddb77568963bc2c"
)
LEGACY_STATE_SHA256 = (
    "02652d839d919ecd6e25cb97eab94d9d31b7be301031dc5a87c03214eab7fa3e"
)


def legacy_predecessor_lineage(
    legacy_run_root: Path, pilot2_record: Mapping[str, Any]
) -> dict[str, str]:
    """Recheck the pilot-1 release and incident pinned by pilot-2's record."""

    root = legacy_run_root.parent
    record_path = root / "deployment.json"
    manifest_path = (
        root / "release" / "paper_bencmark" / "formalization_benchmark" / "manifest.json"
    )
    index_path = legacy_run_root / "index" / "P01-T2.json"
    for path, expected in (
        (record_path, LEGACY_DEPLOYMENT_SHA256),
        (manifest_path, LEGACY_MANIFEST_FILE_SHA256),
        (index_path, LEGACY_INDEX_SHA256),
    ):
        if not path.is_file() or path.is_symlink() or sha256_file(path) != expected:
            raise BenchmarkError(f"sealed pilot-1 evidence is missing or changed: {path}")
    if (
        pilot2_record.get("predecessor_pilot_id") != LEGACY_PILOT_ID
        or pilot2_record.get("predecessor_deployment_record") != str(record_path)
        or pilot2_record.get("predecessor_deployment_record_sha256")
        != LEGACY_DEPLOYMENT_SHA256
        or pilot2_record.get("predecessor_run_root") != str(legacy_run_root)
    ):
        raise BenchmarkError("pilot-2 record does not bind the sealed pilot-1 release")
    legacy_record = load_json(record_path)
    legacy_manifest = load_json(manifest_path)
    if (
        legacy_record.get("schema_version") != "formalization-deployment-1"
        or legacy_record.get("release_commit") != LEGACY_RELEASE_COMMIT
        or legacy_record.get("release_manifest_sha256")
        != LEGACY_MANIFEST_FILE_SHA256
        or legacy_manifest.get("pilot_id") != LEGACY_PILOT_ID
        or legacy_manifest.get("manifest_payload_sha256")
        != LEGACY_MANIFEST_PAYLOAD_SHA256
        or legacy_record.get("run_root") != str(legacy_run_root)
    ):
        raise BenchmarkError("sealed pilot-1 release identity changed")
    index = load_json(index_path)
    raw_pair_root = index.get("pair_root")
    if (
        index.get("task_id") != "P01-T2"
        or index.get("run_id") != LEGACY_INCIDENT_RUN_ID
        or not isinstance(raw_pair_root, str)
    ):
        raise BenchmarkError("sealed pilot-1 P01 index changed")
    pair_root_path = Path(raw_pair_root)
    pair_root = pair_root_path.resolve()
    if pair_root_path.is_symlink() or pair_root.parent != legacy_run_root / "pairs":
        raise BenchmarkError("sealed pilot-1 P01 pair path is unsafe")
    report_path = pair_root / "pair_report.json"
    state_path = pair_root / "pair_state.json"
    for path, expected in (
        (report_path, LEGACY_INCIDENT_REPORT_SHA256),
        (state_path, LEGACY_STATE_SHA256),
    ):
        if not path.is_file() or path.is_symlink() or sha256_file(path) != expected:
            raise BenchmarkError(f"sealed pilot-1 incident evidence changed: {path}")
    if (
        pilot2_record.get("predecessor_pair_report") != str(report_path)
        or pilot2_record.get("predecessor_pair_report_sha256")
        != LEGACY_INCIDENT_REPORT_SHA256
    ):
        raise BenchmarkError("pilot-2 record does not bind the sealed pilot-1 incident")
    report = load_json(report_path)
    state = load_json(state_path)
    if (
        state.get("status") != "PAIR_INCIDENT"
        or state.get("run_id") != LEGACY_INCIDENT_RUN_ID
        or state.get("pair_root") != str(pair_root)
        or state.get("pair_state_path") != str(state_path)
        or state.get("pair_report_sha256") != LEGACY_INCIDENT_REPORT_SHA256
        or index.get("pair_state_path") != str(state_path)
        or report.get("pilot_id") != LEGACY_PILOT_ID
        or report.get("task_id") != "P01-T2"
        or report.get("status") != "PAIR_INCIDENT"
        or report.get("run_id") != LEGACY_INCIDENT_RUN_ID
        or report.get("manifest_sha256") != LEGACY_MANIFEST_FILE_SHA256
        or report.get("pair_root") != str(pair_root)
        or report.get("pair_state_path") != str(state_path)
    ):
        raise BenchmarkError("sealed pilot-1 incident hash chain changed")
    return {
        "legacy_predecessor_deployment_record": str(record_path),
        "legacy_predecessor_deployment_record_sha256": LEGACY_DEPLOYMENT_SHA256,
        "legacy_predecessor_release_manifest": str(manifest_path),
        "legacy_predecessor_release_manifest_sha256": LEGACY_MANIFEST_FILE_SHA256,
        "legacy_predecessor_run_root": str(legacy_run_root),
        "legacy_predecessor_task_index": str(index_path),
        "legacy_predecessor_task_index_sha256": LEGACY_INDEX_SHA256,
        "legacy_predecessor_pair_report": str(report_path),
        "legacy_predecessor_pair_report_sha256": LEGACY_INCIDENT_REPORT_SHA256,
        "legacy_predecessor_pair_state": str(state_path),
        "legacy_predecessor_pair_state_sha256": LEGACY_STATE_SHA256,
    }


def pilot2_lineage(root_argument: str) -> dict[str, str]:
    """Authenticate the sealed pilot-2 incident without modifying its deployment."""

    root = Path(root_argument).expanduser()
    if not root.is_absolute() or root.is_symlink() or not root.is_dir():
        raise BenchmarkError("predecessor deployment root is missing or unsafe")
    root = root.resolve()
    record_path = root / "deployment.json"
    manifest_path = (
        root / "release" / "paper_bencmark" / "formalization_benchmark" / "manifest.json"
    )
    for path in (record_path, manifest_path):
        if not path.is_file() or path.is_symlink():
            raise BenchmarkError(f"predecessor release evidence is missing or unsafe: {path}")
    if (
        sha256_file(record_path) != PREDECESSOR_DEPLOYMENT_SHA256
        or sha256_file(manifest_path) != PREDECESSOR_MANIFEST_FILE_SHA256
    ):
        raise BenchmarkError("predecessor pilot-2 release bytes changed")
    previous = load_json(record_path)
    previous_manifest = load_json(manifest_path)
    if (
        previous.get("schema_version") != "formalization-deployment-1"
        or previous.get("pilot_id") != PREDECESSOR_PILOT_ID
        or previous.get("release_commit") != PREDECESSOR_RELEASE_COMMIT
        or previous_manifest.get("pilot_id") != PREDECESSOR_PILOT_ID
        or previous_manifest.get("manifest_payload_sha256")
        != PREDECESSOR_MANIFEST_PAYLOAD_SHA256
        or previous.get("release_manifest_sha256") != sha256_file(manifest_path)
    ):
        raise BenchmarkError("predecessor deployment is not the sealed pilot-2 release")
    run_root = root / "runs"
    recorded_run_root = previous.get("run_root")
    if (
        not run_root.is_dir()
        or run_root.is_symlink()
        or not isinstance(recorded_run_root, str)
        or Path(recorded_run_root).resolve() != run_root
    ):
        raise BenchmarkError("predecessor run root does not match its deployment record")
    legacy_run_root_raw = previous.get("predecessor_run_root")
    if not isinstance(legacy_run_root_raw, str):
        raise BenchmarkError("pilot-2 deployment is missing its pilot-1 run root")
    legacy_run_root = Path(legacy_run_root_raw)
    if (
        previous.get("predecessor_pilot_id") != "formalization-benchmark-t2-pilot-1"
        or not legacy_run_root.is_absolute()
        or legacy_run_root.is_symlink()
        or not legacy_run_root.is_dir()
        or legacy_run_root.resolve() == run_root
    ):
        raise BenchmarkError("pilot-2 legacy predecessor run root is unsafe")
    legacy_run_root = legacy_run_root.resolve()
    index_path = run_root / "index" / "P01-T2.json"
    if not index_path.is_file() or index_path.is_symlink():
        raise BenchmarkError("predecessor P01 task index is missing or unsafe")
    if sha256_file(index_path) != PREDECESSOR_INDEX_SHA256:
        raise BenchmarkError("predecessor P01 index bytes changed")
    index = load_json(index_path)
    pair_root_raw = index.get("pair_root")
    if (
        index.get("task_id") != "P01-T2"
        or index.get("run_id") != PREDECESSOR_INCIDENT_RUN_ID
        or not isinstance(pair_root_raw, str)
    ):
        raise BenchmarkError("predecessor P01 task index is malformed")
    raw_pair_root = Path(pair_root_raw)
    pair_root = raw_pair_root.resolve()
    if raw_pair_root.is_symlink() or pair_root.parent != run_root / "pairs":
        raise BenchmarkError("predecessor P01 pair path is outside its run root")
    report_path = pair_root / "pair_report.json"
    state_path = pair_root / "pair_state.json"
    if (
        not report_path.is_file()
        or report_path.is_symlink()
        or not state_path.is_file()
        or state_path.is_symlink()
    ):
        raise BenchmarkError("predecessor P01 incident report is missing or unsafe")
    if sha256_file(state_path) != PREDECESSOR_STATE_SHA256:
        raise BenchmarkError("predecessor P01 state bytes changed")
    report_sha256 = sha256_file(report_path)
    state = load_json(state_path)
    if (
        report_sha256 != PREDECESSOR_INCIDENT_REPORT_SHA256
        or state.get("pair_report_sha256") != report_sha256
        or state.get("status") != "PAIR_INCIDENT"
        or state.get("run_id") != PREDECESSOR_INCIDENT_RUN_ID
        or state.get("pair_root") != str(pair_root)
        or state.get("pair_state_path") != str(state_path)
        or index.get("pair_state_path") != str(state_path)
    ):
        raise BenchmarkError("predecessor P01 incident hash chain changed")
    report = load_json(report_path)
    if (
        report.get("pilot_id") != PREDECESSOR_PILOT_ID
        or report.get("task_id") != "P01-T2"
        or report.get("status") != "PAIR_INCIDENT"
        or report.get("run_id") != index.get("run_id")
        or report.get("manifest_sha256") != sha256_file(manifest_path)
        or report.get("pair_root") != str(pair_root)
        or report.get("pair_state_path") != str(state_path)
    ):
        raise BenchmarkError("predecessor P01 report is not the sealed incident")
    return {
        "predecessor_pilot_id": PREDECESSOR_PILOT_ID,
        "predecessor_deployment_record": str(record_path),
        "predecessor_deployment_record_sha256": sha256_file(record_path),
        "predecessor_release_manifest": str(manifest_path),
        "predecessor_release_manifest_sha256": sha256_file(manifest_path),
        "predecessor_run_root": str(run_root),
        "predecessor_task_index": str(index_path),
        "predecessor_task_index_sha256": sha256_file(index_path),
        "predecessor_pair_report": str(report_path),
        "predecessor_pair_report_sha256": report_sha256,
        "predecessor_pair_state": str(state_path),
        "predecessor_pair_state_sha256": sha256_file(state_path),
        **legacy_predecessor_lineage(legacy_run_root, previous),
    }


def pilot3_lineage(root_argument: str) -> dict[str, str]:
    """Authenticate pilot-3's sealed incident and its pilot-2/pilot-1 lineage."""

    root = Path(root_argument).expanduser()
    if not root.is_absolute() or root.is_symlink() or not root.is_dir():
        raise BenchmarkError("pilot-3 predecessor deployment root is missing or unsafe")
    root = root.resolve()
    record_path = root / "deployment.json"
    manifest_path = (
        root / "release" / "paper_bencmark" / "formalization_benchmark" / "manifest.json"
    )
    for path, expected in (
        (record_path, PILOT3_DEPLOYMENT_SHA256),
        (manifest_path, PILOT3_MANIFEST_FILE_SHA256),
    ):
        if not path.is_file() or path.is_symlink() or sha256_file(path) != expected:
            raise BenchmarkError(f"sealed pilot-3 release evidence is missing or changed: {path}")
    previous = load_json(record_path)
    previous_manifest = load_json(manifest_path)
    if (
        previous.get("schema_version") != "formalization-deployment-1"
        or previous.get("pilot_id") != PILOT3_PILOT_ID
        or previous.get("release_commit") != PILOT3_RELEASE_COMMIT
        or previous.get("release_manifest_sha256") != PILOT3_MANIFEST_FILE_SHA256
        or previous.get("manifest_payload_sha256")
        != PILOT3_MANIFEST_PAYLOAD_SHA256
        or previous_manifest.get("pilot_id") != PILOT3_PILOT_ID
        or previous_manifest.get("manifest_payload_sha256")
        != PILOT3_MANIFEST_PAYLOAD_SHA256
    ):
        raise BenchmarkError("sealed pilot-3 release identity changed")
    run_root = root / "runs"
    if (
        not run_root.is_dir()
        or run_root.is_symlink()
        or previous.get("run_root") != str(run_root)
    ):
        raise BenchmarkError("pilot-3 run root does not match its deployment record")
    pilot2_run_root_raw = previous.get("predecessor_run_root")
    if not isinstance(pilot2_run_root_raw, str):
        raise BenchmarkError("pilot-3 deployment is missing its pilot-2 run root")
    pilot2_run_root = Path(pilot2_run_root_raw)
    if (
        not pilot2_run_root.is_absolute()
        or pilot2_run_root.is_symlink()
        or not pilot2_run_root.is_dir()
        or pilot2_run_root.resolve() == run_root
    ):
        raise BenchmarkError("pilot-3 pilot-2 predecessor run root is unsafe")
    old_lineage = pilot2_lineage(str(pilot2_run_root.parent))
    if any(previous.get(key) != value for key, value in old_lineage.items()):
        raise BenchmarkError("pilot-3 record does not bind the sealed pilot-2/pilot-1 lineage")
    index_path = run_root / "index" / "P01-T2.json"
    if (
        not index_path.is_file()
        or index_path.is_symlink()
        or sha256_file(index_path) != PILOT3_INDEX_SHA256
    ):
        raise BenchmarkError("sealed pilot-3 P01 index is missing or changed")
    index = load_json(index_path)
    pair_root_raw = index.get("pair_root")
    if (
        index.get("task_id") != "P01-T2"
        or index.get("run_id") != PILOT3_INCIDENT_RUN_ID
        or not isinstance(pair_root_raw, str)
    ):
        raise BenchmarkError("sealed pilot-3 P01 index is malformed")
    raw_pair_root = Path(pair_root_raw)
    pair_root = raw_pair_root.resolve()
    if raw_pair_root.is_symlink() or pair_root.parent != run_root / "pairs":
        raise BenchmarkError("sealed pilot-3 P01 pair path is unsafe")
    report_path = pair_root / "pair_report.json"
    state_path = pair_root / "pair_state.json"
    for path, expected in (
        (report_path, PILOT3_INCIDENT_REPORT_SHA256),
        (state_path, PILOT3_STATE_SHA256),
    ):
        if not path.is_file() or path.is_symlink() or sha256_file(path) != expected:
            raise BenchmarkError(f"sealed pilot-3 incident evidence is missing or changed: {path}")
    report = load_json(report_path)
    state = load_json(state_path)
    if (
        state.get("status") != "PAIR_INCIDENT"
        or state.get("run_id") != PILOT3_INCIDENT_RUN_ID
        or state.get("pair_root") != str(pair_root)
        or state.get("pair_state_path") != str(state_path)
        or state.get("pair_report_sha256") != PILOT3_INCIDENT_REPORT_SHA256
        or index.get("pair_state_path") != str(state_path)
        or report.get("pilot_id") != PILOT3_PILOT_ID
        or report.get("task_id") != "P01-T2"
        or report.get("status") != "PAIR_INCIDENT"
        or report.get("run_id") != PILOT3_INCIDENT_RUN_ID
        or report.get("manifest_sha256") != PILOT3_MANIFEST_FILE_SHA256
        or report.get("pair_root") != str(pair_root)
        or report.get("pair_state_path") != str(state_path)
    ):
        raise BenchmarkError("sealed pilot-3 P01 incident hash chain changed")
    qualification_path = (
        run_root / "qualifications" / PILOT3_MANIFEST_FILE_SHA256 / "qualification.json"
    )
    if (
        not qualification_path.is_file()
        or qualification_path.is_symlink()
        or sha256_file(qualification_path) != PILOT3_QUALIFICATION_SHA256
    ):
        raise BenchmarkError("sealed pilot-3 qualification evidence is missing or changed")
    qualification = load_json(qualification_path)
    qualification_identity = qualification.get("identity")
    qualification_roles = qualification_path.parent / "roles"
    if (
        qualification.get("schema_version") != "formalization-provider-qualification-2"
        or qualification.get("status") != "PASSED"
        or not isinstance(qualification_identity, Mapping)
        or qualification_identity.get("pilot_id") != PILOT3_PILOT_ID
        or qualification_identity.get("manifest_sha256")
        != PILOT3_MANIFEST_FILE_SHA256
        or qualification_identity.get("manifest_payload_sha256")
        != PILOT3_MANIFEST_PAYLOAD_SHA256
        or qualification_identity.get("deployment_path") != str(record_path)
        or qualification_identity.get("deployment_sha256") != PILOT3_DEPLOYMENT_SHA256
        or qualification.get("roles_manifest") != tree_manifest(qualification_roles)
    ):
        raise BenchmarkError("sealed pilot-3 qualification is not passed")
    return {
        "predecessor_pilot_id": PILOT3_PILOT_ID,
        "predecessor_deployment_record": str(record_path),
        "predecessor_deployment_record_sha256": PILOT3_DEPLOYMENT_SHA256,
        "predecessor_release_manifest": str(manifest_path),
        "predecessor_release_manifest_sha256": PILOT3_MANIFEST_FILE_SHA256,
        "predecessor_run_root": str(run_root),
        "predecessor_task_index": str(index_path),
        "predecessor_task_index_sha256": PILOT3_INDEX_SHA256,
        "predecessor_pair_report": str(report_path),
        "predecessor_pair_report_sha256": PILOT3_INCIDENT_REPORT_SHA256,
        "predecessor_pair_state": str(state_path),
        "predecessor_pair_state_sha256": PILOT3_STATE_SHA256,
        "predecessor_qualification": str(qualification_path),
        "predecessor_qualification_sha256": PILOT3_QUALIFICATION_SHA256,
        **{
            (
                "legacy_predecessor_" + key.removeprefix("predecessor_")
                if key.startswith("predecessor_")
                else "ancestral_predecessor_" + key.removeprefix("legacy_predecessor_")
            ): value
            for key, value in old_lineage.items()
        },
    }


def predecessor_lineage(root_argument: str) -> dict[str, str]:
    """Authenticate pilot-4's failed qualification and all earlier releases.

    Pilot-4 never entered the official pair namespace.  Its failed one-shot
    qualification, measured library build, and three older pilot incidents are
    still immutable predecessor evidence for a new pilot-5 deployment.
    """

    root = Path(root_argument).expanduser()
    if not root.is_absolute() or root.is_symlink() or not root.is_dir():
        raise BenchmarkError("pilot-4 predecessor deployment root is missing or unsafe")
    root = root.resolve()
    record_path = root / "deployment.json"
    manifest_path = (
        root / "release" / "paper_bencmark" / "formalization_benchmark" / "manifest.json"
    )
    build_path = root / "runtime" / "library" / "build" / "build-record.json"
    run_root = root / "runs"
    qualification_path = (
        run_root / "qualifications" / PILOT4_MANIFEST_FILE_SHA256 / "qualification.json"
    )
    for path, expected in (
        (record_path, PILOT4_DEPLOYMENT_SHA256),
        (manifest_path, PILOT4_MANIFEST_FILE_SHA256),
        (build_path, PILOT4_BUILD_RECORD_SHA256),
        (qualification_path, PILOT4_FAILED_QUALIFICATION_SHA256),
    ):
        if not path.is_file() or path.is_symlink() or sha256_file(path) != expected:
            raise BenchmarkError(f"sealed pilot-4 evidence is missing or changed: {path}")
    previous = load_json(record_path)
    previous_manifest = load_json(manifest_path)
    if (
        previous.get("schema_version") != "formalization-deployment-1"
        or previous.get("pilot_id") != PILOT4_PILOT_ID
        or previous.get("release_commit") != PILOT4_RELEASE_COMMIT
        or previous.get("release_manifest_sha256") != PILOT4_MANIFEST_FILE_SHA256
        or previous.get("manifest_payload_sha256") != PILOT4_MANIFEST_PAYLOAD_SHA256
        or previous.get("library_build_record") != str(build_path)
        or previous.get("library_build_record_sha256") != PILOT4_BUILD_RECORD_SHA256
        or previous.get("run_root") != str(run_root)
        or previous_manifest.get("pilot_id") != PILOT4_PILOT_ID
        or previous_manifest.get("manifest_payload_sha256")
        != PILOT4_MANIFEST_PAYLOAD_SHA256
    ):
        raise BenchmarkError("sealed pilot-4 release identity changed")
    if not run_root.is_dir() or run_root.is_symlink():
        raise BenchmarkError("sealed pilot-4 run root is missing or unsafe")
    for name in ("index", "pairs"):
        official_root = run_root / name
        if official_root.is_symlink() or (
            official_root.exists()
            and (not official_root.is_dir() or any(official_root.iterdir()))
        ):
            raise BenchmarkError("pilot-4 unexpectedly contains official pair evidence")
    registry_index = GLOBAL_REGISTRY_ROOT / "index" / PILOT4_PILOT_ID
    if registry_index.is_symlink() or (
        registry_index.exists()
        and (not registry_index.is_dir() or any(registry_index.iterdir()))
    ):
        raise BenchmarkError("pilot-4 unexpectedly has an account-global task reservation")
    pilot3_run_root_raw = previous.get("predecessor_run_root")
    if not isinstance(pilot3_run_root_raw, str):
        raise BenchmarkError("pilot-4 deployment is missing its pilot-3 run root")
    pilot3_run_root = Path(pilot3_run_root_raw)
    if (
        not pilot3_run_root.is_absolute()
        or pilot3_run_root.is_symlink()
        or not pilot3_run_root.is_dir()
        or pilot3_run_root.resolve() == run_root
    ):
        raise BenchmarkError("pilot-4 pilot-3 predecessor run root is unsafe")
    old_lineage = pilot3_lineage(str(pilot3_run_root.parent))
    if any(previous.get(key) != value for key, value in old_lineage.items()):
        raise BenchmarkError("pilot-4 record does not bind the sealed pilot-3/2/1 lineage")
    qualification = load_json(qualification_path)
    qualification_identity = qualification.get("identity")
    roles_root = qualification_path.parent / "roles"
    roles_manifest = tree_manifest(roles_root)
    if (
        set(qualification_path.parent.iterdir()) != {qualification_path, roles_root}
        or qualification.get("schema_version") != "formalization-provider-qualification-3"
        or qualification.get("status") != "FAILED"
        or qualification.get("classification") != "off_benchmark_provider_qualification"
        or qualification.get("charged_to_contestant") is not False
        or not isinstance(qualification_identity, Mapping)
        or qualification_identity.get("pilot_id") != PILOT4_PILOT_ID
        or qualification_identity.get("manifest_sha256")
        != PILOT4_MANIFEST_FILE_SHA256
        or qualification_identity.get("manifest_payload_sha256")
        != PILOT4_MANIFEST_PAYLOAD_SHA256
        or qualification_identity.get("deployment_path") != str(record_path)
        or qualification_identity.get("deployment_sha256")
        != PILOT4_DEPLOYMENT_SHA256
        or sha256_bytes(canonical_json_bytes(roles_manifest))
        != PILOT4_QUALIFICATION_ROLES_MANIFEST_SHA256
        or len(roles_manifest.get("entries", [])) != 21
    ):
        raise BenchmarkError("sealed pilot-4 failed qualification identity changed")
    return {
        "predecessor_pilot_id": PILOT4_PILOT_ID,
        "predecessor_deployment_record": str(record_path),
        "predecessor_deployment_record_sha256": PILOT4_DEPLOYMENT_SHA256,
        "predecessor_release_manifest": str(manifest_path),
        "predecessor_release_manifest_sha256": PILOT4_MANIFEST_FILE_SHA256,
        "predecessor_library_build_record": str(build_path),
        "predecessor_library_build_record_sha256": PILOT4_BUILD_RECORD_SHA256,
        "predecessor_run_root": str(run_root),
        "predecessor_qualification": str(qualification_path),
        "predecessor_qualification_sha256": PILOT4_FAILED_QUALIFICATION_SHA256,
        "predecessor_qualification_roles_manifest_sha256": (
            PILOT4_QUALIFICATION_ROLES_MANIFEST_SHA256
        ),
        **{
            (
                "legacy_predecessor_" + key.removeprefix("predecessor_")
                if key.startswith("predecessor_")
                else "ancestral_predecessor_" + key.removeprefix("legacy_predecessor_")
                if key.startswith("legacy_predecessor_")
                else "great_ancestral_predecessor_"
                + key.removeprefix("ancestral_predecessor_")
            ): value
            for key, value in old_lineage.items()
        },
    }


def _pilot5_release_closure(root: Path, manifest: Mapping[str, Any]) -> None:
    """Authenticate old executable bytes before invoking their read-only status."""

    release_root = root / "release"
    benchmark_root = release_root / "paper_bencmark" / "formalization_benchmark"

    def checked_file(base: Path, relative: str, expected: str) -> Path:
        candidate = Path(relative)
        if (
            not relative
            or candidate.is_absolute()
            or ".." in candidate.parts
            or len(expected) != 64
        ):
            raise BenchmarkError("pilot-5 release closure has an unsafe file reference")
        path = base / candidate
        if not path.resolve().is_relative_to(base.resolve()):
            raise BenchmarkError("pilot-5 release closure escapes its root")
        ancestors = (
            base,
            *(base / Path(*candidate.parts[:index]) for index in range(1, len(candidate.parts) + 1)),
        )
        for ancestor in ancestors:
            if ancestor.is_symlink():
                raise BenchmarkError("pilot-5 release closure contains a symlink")
        if not path.is_file() or sha256_file(path) != expected:
            raise BenchmarkError(f"pilot-5 release closure changed: {path}")
        return path

    release_files = manifest.get("release_files")
    repository_files = manifest.get("repository_files")
    if not isinstance(release_files, list) or not isinstance(repository_files, list):
        raise BenchmarkError("pilot-5 release closure is missing")
    recorded_paths: set[str] = set()
    for record in release_files:
        if not isinstance(record, Mapping):
            raise BenchmarkError("pilot-5 release closure is malformed")
        relative, expected = record.get("relative_path"), record.get("sha256")
        if not isinstance(relative, str) or not isinstance(expected, str):
            raise BenchmarkError("pilot-5 release closure is malformed")
        checked_file(benchmark_root, relative, expected)
        recorded_paths.add(relative)
    actual_paths = {
        path.relative_to(benchmark_root).as_posix()
        for path in benchmark_root.rglob("*")
        if path.is_file() and path != benchmark_root / "manifest.json"
    }
    if recorded_paths != actual_paths:
        raise BenchmarkError("pilot-5 release closure gained or lost a file")
    for record in repository_files:
        if not isinstance(record, Mapping):
            raise BenchmarkError("pilot-5 repository closure is malformed")
        relative, expected = record.get("repository_relative_path"), record.get("sha256")
        if not isinstance(relative, str) or not isinstance(expected, str):
            raise BenchmarkError("pilot-5 repository closure is malformed")
        checked_file(release_root, relative, expected)


def _pilot5_status(root: Path, deployment_record: Path, task_id: str) -> Mapping[str, Any]:
    """Use the pinned pilot-5 verifier without provider calls or state changes."""

    runner = (
        root / "release" / "paper_bencmark" / "formalization_benchmark"
        / "tools" / "run_benchmark.py"
    )
    environment = os.environ.copy()
    environment.pop("HIGHAMBENCH_COMMAND_CGROUP_PROCS", None)
    environment["HIGHAMBENCH_FORMALIZATION_DEPLOYMENT"] = str(deployment_record)
    environment["HIGHAMBENCH_FORMALIZATION_DEPLOYMENT_SHA256"] = PILOT5_DEPLOYMENT_SHA256
    completed = run_bounded_command(
        isolated_runner_command(
            runner, "--deployment", str(deployment_record), "status", "--task-id", task_id
        ),
        cwd=root,
        environment=environment,
        timeout_seconds=600,
        maximum_output_bytes=16 * 1024 * 1024,
    )
    if (
        completed["timed_out"]
        or completed["output_limit_exceeded"]
        or completed["returncode"] != 0
    ):
        raise BenchmarkError(f"frozen pilot-5 status authentication failed for {task_id}")
    try:
        result = json.loads(completed["output"])
    except json.JSONDecodeError as error:
        raise BenchmarkError("frozen pilot-5 status output is malformed") from error
    if not isinstance(result, Mapping):
        raise BenchmarkError("frozen pilot-5 status output is malformed")
    return result


def pilot5_lineage(root_argument: str, *, verify_status: bool = True) -> dict[str, str]:
    """Pin pilot-5; optionally verify full attempt closure outside campaign locks.

    Setup invokes the frozen pilot-5 status verifier before publication. A
    successor doctor already holds the shared campaign lock, so it must use the pinned
    byte/identity checks only; invoking pilot-5 status there would reacquire the
    same lock from a second process.
    """

    root = Path(root_argument).expanduser()
    if not root.is_absolute() or root.is_symlink() or not root.is_dir():
        raise BenchmarkError("pilot-5 predecessor deployment root is missing or unsafe")
    root = root.resolve()
    record_path = root / "deployment.json"
    manifest_path = (
        root / "release" / "paper_bencmark" / "formalization_benchmark" / "manifest.json"
    )
    build_path = root / "runtime" / "library" / "build" / "build-record.json"
    run_root = root / "runs"
    qualification_path = (
        run_root / "qualifications" / PILOT5_MANIFEST_FILE_SHA256 / "qualification.json"
    )
    for path, expected in (
        (record_path, PILOT5_DEPLOYMENT_SHA256),
        (manifest_path, PILOT5_MANIFEST_FILE_SHA256),
        (build_path, PILOT5_BUILD_RECORD_SHA256),
        (qualification_path, PILOT5_QUALIFICATION_SHA256),
    ):
        if not path.is_file() or path.is_symlink() or sha256_file(path) != expected:
            raise BenchmarkError(f"sealed pilot-5 evidence is missing or changed: {path}")
    previous = load_json(record_path)
    previous_manifest = load_json(manifest_path)
    if (
        previous.get("schema_version") != "formalization-deployment-1"
        or previous.get("pilot_id") != PILOT5_PILOT_ID
        or previous.get("release_commit") != PILOT5_RELEASE_COMMIT
        or previous.get("release_manifest_sha256") != PILOT5_MANIFEST_FILE_SHA256
        or previous.get("manifest_payload_sha256") != PILOT5_MANIFEST_PAYLOAD_SHA256
        or previous.get("library_build_record") != str(build_path)
        or previous.get("library_build_record_sha256") != PILOT5_BUILD_RECORD_SHA256
        or previous.get("run_root") != str(run_root)
        or previous_manifest.get("pilot_id") != PILOT5_PILOT_ID
        or previous_manifest.get("manifest_payload_sha256")
        != PILOT5_MANIFEST_PAYLOAD_SHA256
    ):
        raise BenchmarkError("sealed pilot-5 release identity changed")
    _pilot5_release_closure(root, previous_manifest)
    pilot4_run_root_raw = previous.get("predecessor_run_root")
    if not isinstance(pilot4_run_root_raw, str):
        raise BenchmarkError("pilot-5 deployment is missing its pilot-4 run root")
    pilot4_run_root = Path(pilot4_run_root_raw)
    if (
        not pilot4_run_root.is_absolute()
        or pilot4_run_root.is_symlink()
        or not pilot4_run_root.is_dir()
        or pilot4_run_root.resolve() == run_root
    ):
        raise BenchmarkError("pilot-5 pilot-4 predecessor run root is unsafe")
    old_lineage = predecessor_lineage(str(pilot4_run_root.parent))
    if any(previous.get(key) != value for key, value in old_lineage.items()):
        raise BenchmarkError("pilot-5 record does not bind the sealed pilot-4/3/2/1 lineage")
    qualification = load_json(qualification_path)
    roles_root = qualification_path.parent / "roles"
    roles_manifest = tree_manifest(roles_root)
    identity = qualification.get("identity")
    if (
        set(qualification_path.parent.iterdir()) != {qualification_path, roles_root}
        or qualification.get("schema_version") != "formalization-provider-qualification-4"
        or qualification.get("status") != "PASSED"
        or qualification.get("classification") != "off_benchmark_provider_qualification"
        or qualification.get("charged_to_contestant") is not False
        or qualification.get("roles_manifest") != roles_manifest
        or roles_manifest.get("tree_sha256") != PILOT5_QUALIFICATION_ROLES_TREE_SHA256
        or not isinstance(identity, Mapping)
        or identity.get("pilot_id") != PILOT5_PILOT_ID
        or identity.get("manifest_sha256") != PILOT5_MANIFEST_FILE_SHA256
        or identity.get("manifest_payload_sha256") != PILOT5_MANIFEST_PAYLOAD_SHA256
        or identity.get("deployment_path") != str(record_path)
        or identity.get("deployment_sha256") != PILOT5_DEPLOYMENT_SHA256
    ):
        raise BenchmarkError("sealed pilot-5 qualification identity changed")

    index_root = run_root / "index"
    pairs_root = run_root / "pairs"
    registry_index_root = GLOBAL_REGISTRY_ROOT / "index" / PILOT5_PILOT_ID
    expected_tasks = set(PILOT5_SEALED_PAIRS)
    expected_runs = {record["run_id"] for record in PILOT5_SEALED_PAIRS.values()}
    for directory, expected_names in (
        (index_root, {f"{task}.json" for task in expected_tasks}),
        (pairs_root, expected_runs),
        (registry_index_root, {f"{task}.json" for task in expected_tasks}),
    ):
        if (
            not directory.is_dir()
            or directory.is_symlink()
            or {entry.name for entry in directory.iterdir()} != expected_names
        ):
            raise BenchmarkError("pilot-5 official pair namespace changed")

    if verify_status:
        # The frozen status verifier acquires these existing locks with O_CREAT,
        # so fail before invoking it if any path would otherwise be created.
        lock_paths = [
            run_root / "locks" / "formalization-pilot.lock",
            GLOBAL_REGISTRY_ROOT / "locks" / "campaign.lock",
            *(
                old_roots / "locks" / "formalization-pilot.lock"
                for old_roots in (
                    pilot4_run_root,
                    Path(old_lineage["legacy_predecessor_run_root"]),
                    Path(old_lineage["ancestral_predecessor_run_root"]),
                    Path(old_lineage["great_ancestral_predecessor_run_root"]),
                )
            ),
        ]
        if any(not path.is_file() or path.is_symlink() for path in lock_paths):
            raise BenchmarkError("pilot-5 status would create a predecessor lock")

    pair_lineage: dict[str, str] = {}
    for task_id, seal in PILOT5_SEALED_PAIRS.items():
        run_id = seal["run_id"]
        pair_root = pairs_root / run_id
        index_path = index_root / f"{task_id}.json"
        registry_path = registry_index_root / f"{task_id}.json"
        state_path = pair_root / "pair_state.json"
        report_path = pair_root / "pair_report.json"
        for path, expected in (
            (index_path, seal["index_sha256"]),
            (registry_path, seal["index_sha256"]),
            (state_path, seal["state_sha256"]),
            (report_path, seal["report_sha256"]),
        ):
            if not path.is_file() or path.is_symlink() or sha256_file(path) != expected:
                raise BenchmarkError(f"sealed pilot-5 pair evidence changed: {path}")
        index = load_json(index_path)
        state = load_json(state_path)
        report = load_json(report_path)
        if (
            load_json(registry_path) != index
            or index.get("schema_version") != "formalization-task-index-2"
            or index.get("pilot_id") != PILOT5_PILOT_ID
            or index.get("release_commit") != PILOT5_RELEASE_COMMIT
            or index.get("manifest_sha256") != PILOT5_MANIFEST_FILE_SHA256
            or index.get("manifest_payload_sha256") != PILOT5_MANIFEST_PAYLOAD_SHA256
            or index.get("deployment_sha256") != PILOT5_DEPLOYMENT_SHA256
            or index.get("task_id") != task_id
            or index.get("run_id") != run_id
            or index.get("pair_root") != str(pair_root)
            or index.get("pair_state_path") != str(state_path)
            or state.get("status") != "PAIR_INCIDENT"
            or report.get("status") != "PAIR_INCIDENT"
            or state.get("pair_report_sha256") != seal["report_sha256"]
            or any(
                candidate.get(key) != value
                for candidate in (state, report)
                for key, value in (
                    ("pilot_id", PILOT5_PILOT_ID),
                    ("task_id", task_id),
                    ("run_id", run_id),
                    ("manifest_sha256", PILOT5_MANIFEST_FILE_SHA256),
                    ("pair_root", str(pair_root)),
                    ("pair_state_path", str(state_path)),
                )
            )
        ):
            raise BenchmarkError(f"sealed pilot-5 {task_id} hash chain changed")
        if verify_status:
            status = _pilot5_status(root, record_path, task_id)
            if (
                status.get("task_id") != task_id
                or status.get("run_id") != run_id
                or status.get("status") != "PAIR_INCIDENT"
                or status.get("pair_report_sha256") != seal["report_sha256"]
            ):
                raise BenchmarkError(f"frozen pilot-5 {task_id} status changed")
        suffix = task_id.lower().replace("-", "_")
        pair_lineage.update({
            f"predecessor_{suffix}_task_index": str(index_path),
            f"predecessor_{suffix}_task_index_sha256": seal["index_sha256"],
            f"predecessor_{suffix}_pair_state": str(state_path),
            f"predecessor_{suffix}_pair_state_sha256": seal["state_sha256"],
            f"predecessor_{suffix}_pair_report": str(report_path),
            f"predecessor_{suffix}_pair_report_sha256": seal["report_sha256"],
        })
    return {
        "predecessor_pilot_id": PILOT5_PILOT_ID,
        "predecessor_deployment_record": str(record_path),
        "predecessor_deployment_record_sha256": PILOT5_DEPLOYMENT_SHA256,
        "predecessor_release_manifest": str(manifest_path),
        "predecessor_release_manifest_sha256": PILOT5_MANIFEST_FILE_SHA256,
        "predecessor_library_build_record": str(build_path),
        "predecessor_library_build_record_sha256": PILOT5_BUILD_RECORD_SHA256,
        "predecessor_run_root": str(run_root),
        "predecessor_qualification": str(qualification_path),
        "predecessor_qualification_sha256": PILOT5_QUALIFICATION_SHA256,
        "predecessor_qualification_roles_tree_sha256": (
            PILOT5_QUALIFICATION_ROLES_TREE_SHA256
        ),
        **pair_lineage,
        **{
            (
                "legacy_predecessor_" + key.removeprefix("predecessor_")
                if key.startswith("predecessor_")
                else "ancestral_predecessor_" + key.removeprefix("legacy_predecessor_")
                if key.startswith("legacy_predecessor_")
                else "great_ancestral_predecessor_"
                + key.removeprefix("ancestral_predecessor_")
                if key.startswith("ancestral_predecessor_")
                else "fifth_ancestral_predecessor_"
                + key.removeprefix("great_ancestral_predecessor_")
            ): value
            for key, value in old_lineage.items()
        },
    }


def pilot7_lineage(root_argument: str, *, verify_status: bool = True) -> dict[str, str]:
    """Authenticate the sealed zero-token Pilot-7 qualification failure.

    Pilot-8 is an authentication-repaired successor, not a retry of Pilot-7.
    This check binds the failed qualification and shifts Pilot-7's complete
    Pilot-5/4/3/2/1 lineage forward by one generation.
    """

    root = Path(root_argument).expanduser()
    if not root.is_absolute() or root.is_symlink() or not root.is_dir():
        raise BenchmarkError("pilot-7 predecessor deployment root is missing or unsafe")
    root = root.resolve()
    record_path = root / "deployment.json"
    manifest_path = (
        root / "release" / "paper_bencmark" / "formalization_benchmark" / "manifest.json"
    )
    build_path = root / "runtime" / "library" / "build" / "build-record.json"
    run_root = root / "runs"
    qualification_path = (
        run_root / "qualifications" / PILOT7_MANIFEST_FILE_SHA256 / "qualification.json"
    )
    for path, expected in (
        (record_path, PILOT7_DEPLOYMENT_SHA256),
        (manifest_path, PILOT7_MANIFEST_FILE_SHA256),
        (build_path, PILOT7_BUILD_RECORD_SHA256),
        (qualification_path, PILOT7_FAILED_QUALIFICATION_SHA256),
    ):
        if not path.is_file() or path.is_symlink() or sha256_file(path) != expected:
            raise BenchmarkError(f"sealed pilot-7 evidence is missing or changed: {path}")

    previous = load_json(record_path)
    previous_manifest = load_json(manifest_path)
    if (
        previous.get("schema_version") != "formalization-deployment-1"
        or previous.get("pilot_id") != PILOT7_PILOT_ID
        or previous.get("release_commit") != PILOT7_RELEASE_COMMIT
        or previous.get("release_manifest_sha256") != PILOT7_MANIFEST_FILE_SHA256
        or previous.get("manifest_payload_sha256") != PILOT7_MANIFEST_PAYLOAD_SHA256
        or previous.get("library_build_record") != str(build_path)
        or previous.get("library_build_record_sha256") != PILOT7_BUILD_RECORD_SHA256
        or previous.get("run_root") != str(run_root)
        or previous_manifest.get("pilot_id") != PILOT7_PILOT_ID
        or previous_manifest.get("manifest_payload_sha256")
        != PILOT7_MANIFEST_PAYLOAD_SHA256
    ):
        raise BenchmarkError("sealed pilot-7 release identity changed")
    _pilot5_release_closure(root, previous_manifest)
    if not run_root.is_dir() or run_root.is_symlink():
        raise BenchmarkError("sealed pilot-7 run root is missing or unsafe")

    pilot5_run_root_raw = previous.get("predecessor_run_root")
    if not isinstance(pilot5_run_root_raw, str):
        raise BenchmarkError("pilot-7 deployment is missing its pilot-5 run root")
    pilot5_run_root = Path(pilot5_run_root_raw)
    if (
        not pilot5_run_root.is_absolute()
        or pilot5_run_root.is_symlink()
        or not pilot5_run_root.is_dir()
        or pilot5_run_root.resolve() == run_root
    ):
        raise BenchmarkError("pilot-7 pilot-5 predecessor run root is unsafe")
    old_lineage = pilot5_lineage(
        str(pilot5_run_root.parent), verify_status=verify_status
    )
    if any(previous.get(key) != value for key, value in old_lineage.items()):
        raise BenchmarkError("pilot-7 record does not bind the sealed pilot-5/4/3/2/1 lineage")

    qualification = load_json(qualification_path)
    identity = qualification.get("identity")
    roles_root = qualification_path.parent / "roles"
    roles_manifest = tree_manifest(roles_root)
    if (
        set(qualification_path.parent.iterdir()) != {qualification_path, roles_root}
        or qualification.get("schema_version") != "formalization-provider-qualification-5"
        or qualification.get("status") != "FAILED"
        or qualification.get("classification") != "off_benchmark_provider_qualification"
        or qualification.get("charged_to_contestant") is not False
        or qualification.get("completed_roles") != []
        or roles_manifest.get("tree_sha256")
        != PILOT7_FAILED_QUALIFICATION_ROLES_TREE_SHA256
        or not isinstance(identity, Mapping)
        or identity.get("pilot_id") != PILOT7_PILOT_ID
        or identity.get("manifest_sha256") != PILOT7_MANIFEST_FILE_SHA256
        or identity.get("manifest_payload_sha256")
        != PILOT7_MANIFEST_PAYLOAD_SHA256
        or identity.get("deployment_path") != str(record_path)
        or identity.get("deployment_sha256") != PILOT7_DEPLOYMENT_SHA256
    ):
        raise BenchmarkError("sealed pilot-7 failed qualification identity changed")

    for name in ("index", "pairs"):
        official_root = run_root / name
        if official_root.is_symlink() or (
            official_root.exists()
            and (not official_root.is_dir() or any(official_root.iterdir()))
        ):
            raise BenchmarkError("pilot-7 unexpectedly contains official pair evidence")
    registry_index = GLOBAL_REGISTRY_ROOT / "index" / PILOT7_PILOT_ID
    if registry_index.is_symlink() or (
        registry_index.exists()
        and (not registry_index.is_dir() or any(registry_index.iterdir()))
    ):
        raise BenchmarkError("pilot-7 unexpectedly has an account-global task reservation")

    shifted_lineage = {
        (
            "legacy_predecessor_" + key.removeprefix("predecessor_")
            if key.startswith("predecessor_")
            else "ancestral_predecessor_" + key.removeprefix("legacy_predecessor_")
            if key.startswith("legacy_predecessor_")
            else "great_ancestral_predecessor_"
            + key.removeprefix("ancestral_predecessor_")
            if key.startswith("ancestral_predecessor_")
            else "fifth_ancestral_predecessor_"
            + key.removeprefix("great_ancestral_predecessor_")
            if key.startswith("great_ancestral_predecessor_")
            else "sixth_ancestral_predecessor_"
            + key.removeprefix("fifth_ancestral_predecessor_")
        ): value
        for key, value in old_lineage.items()
    }
    return {
        "predecessor_pilot_id": PILOT7_PILOT_ID,
        "predecessor_deployment_record": str(record_path),
        "predecessor_deployment_record_sha256": PILOT7_DEPLOYMENT_SHA256,
        "predecessor_release_manifest": str(manifest_path),
        "predecessor_release_manifest_sha256": PILOT7_MANIFEST_FILE_SHA256,
        "predecessor_library_build_record": str(build_path),
        "predecessor_library_build_record_sha256": PILOT7_BUILD_RECORD_SHA256,
        "predecessor_run_root": str(run_root),
        "predecessor_qualification": str(qualification_path),
        "predecessor_qualification_sha256": PILOT7_FAILED_QUALIFICATION_SHA256,
        "predecessor_qualification_roles_tree_sha256": (
            PILOT7_FAILED_QUALIFICATION_ROLES_TREE_SHA256
        ),
        **shifted_lineage,
    }


def _pilot8_status(root: Path, deployment_record: Path) -> Mapping[str, Any]:
    """Use the frozen Pilot-8 verifier without provider calls or state changes."""

    runner = (
        root / "release" / "paper_bencmark" / "formalization_benchmark"
        / "tools" / "run_benchmark.py"
    )
    environment = os.environ.copy()
    environment.pop("HIGHAMBENCH_COMMAND_CGROUP_PROCS", None)
    environment["HIGHAMBENCH_FORMALIZATION_DEPLOYMENT"] = str(deployment_record)
    environment["HIGHAMBENCH_FORMALIZATION_DEPLOYMENT_SHA256"] = PILOT8_DEPLOYMENT_SHA256
    completed = run_bounded_command(
        isolated_runner_command(
            runner,
            "--deployment",
            str(deployment_record),
            "status",
            "--task-id",
            "H22-11",
        ),
        cwd=root,
        environment=environment,
        timeout_seconds=600,
        maximum_output_bytes=16 * 1024 * 1024,
    )
    if (
        completed["timed_out"]
        or completed["output_limit_exceeded"]
        or completed["returncode"] != 0
    ):
        raise BenchmarkError("frozen pilot-8 status authentication failed for H22-11")
    try:
        result = json.loads(completed["output"])
    except json.JSONDecodeError as error:
        raise BenchmarkError("frozen pilot-8 status output is malformed") from error
    if not isinstance(result, Mapping):
        raise BenchmarkError("frozen pilot-8 status output is malformed")
    return result


def pilot8_lineage(root_argument: str, *, verify_status: bool = True) -> dict[str, str]:
    """Authenticate Pilot-8's sealed H22-11 audit-interface incident."""

    root = Path(root_argument).expanduser()
    if not root.is_absolute() or root.is_symlink() or not root.is_dir():
        raise BenchmarkError("pilot-8 predecessor deployment root is missing or unsafe")
    root = root.resolve()
    record_path = root / "deployment.json"
    manifest_path = (
        root / "release" / "paper_bencmark" / "formalization_benchmark" / "manifest.json"
    )
    build_path = root / "runtime" / "library" / "build" / "build-record.json"
    run_root = root / "runs"
    qualification_path = (
        run_root / "qualifications" / PILOT8_MANIFEST_FILE_SHA256 / "qualification.json"
    )
    index_path = run_root / "index" / "H22-11.json"
    pair_root = run_root / "pairs" / PILOT8_INCIDENT_RUN_ID
    state_path = pair_root / "pair_state.json"
    report_path = pair_root / "pair_report.json"
    condition_state_path = pair_root / "conditions" / "L" / "condition_state.json"
    audit_incident_path = (
        pair_root
        / "audits"
        / "bd33a3bdd1ee7d42c66b32d86f781d352f9cebd44a28b58604b5cc934bd985a2"
        / "incident.json"
    )
    for path, expected in (
        (record_path, PILOT8_DEPLOYMENT_SHA256),
        (manifest_path, PILOT8_MANIFEST_FILE_SHA256),
        (build_path, PILOT8_BUILD_RECORD_SHA256),
        (qualification_path, PILOT8_QUALIFICATION_SHA256),
        (index_path, PILOT8_INDEX_SHA256),
        (state_path, PILOT8_PAIR_STATE_SHA256),
        (report_path, PILOT8_PAIR_REPORT_SHA256),
        (condition_state_path, PILOT8_CONDITION_STATE_SHA256),
        (audit_incident_path, PILOT8_AUDIT_INCIDENT_SHA256),
    ):
        if not path.is_file() or path.is_symlink() or sha256_file(path) != expected:
            raise BenchmarkError(f"sealed pilot-8 evidence is missing or changed: {path}")

    previous = load_json(record_path)
    previous_manifest = load_json(manifest_path)
    if (
        previous.get("schema_version") != "formalization-deployment-1"
        or previous.get("pilot_id") != PILOT8_PILOT_ID
        or previous.get("release_commit") != PILOT8_RELEASE_COMMIT
        or previous.get("release_manifest_sha256") != PILOT8_MANIFEST_FILE_SHA256
        or previous.get("manifest_payload_sha256") != PILOT8_MANIFEST_PAYLOAD_SHA256
        or previous.get("library_build_record") != str(build_path)
        or previous.get("library_build_record_sha256") != PILOT8_BUILD_RECORD_SHA256
        or previous.get("run_root") != str(run_root)
        or previous_manifest.get("pilot_id") != PILOT8_PILOT_ID
        or previous_manifest.get("manifest_payload_sha256")
        != PILOT8_MANIFEST_PAYLOAD_SHA256
    ):
        raise BenchmarkError("sealed pilot-8 release identity changed")
    _pilot5_release_closure(root, previous_manifest)
    if not run_root.is_dir() or run_root.is_symlink():
        raise BenchmarkError("sealed pilot-8 run root is missing or unsafe")

    pilot7_run_root_raw = previous.get("predecessor_run_root")
    if not isinstance(pilot7_run_root_raw, str):
        raise BenchmarkError("pilot-8 deployment is missing its pilot-7 run root")
    pilot7_run_root = Path(pilot7_run_root_raw)
    if (
        not pilot7_run_root.is_absolute()
        or pilot7_run_root.is_symlink()
        or not pilot7_run_root.is_dir()
        or pilot7_run_root.resolve() == run_root
    ):
        raise BenchmarkError("pilot-8 pilot-7 predecessor run root is unsafe")
    old_lineage = pilot7_lineage(
        str(pilot7_run_root.parent), verify_status=verify_status
    )
    if any(previous.get(key) != value for key, value in old_lineage.items()):
        raise BenchmarkError(
            "pilot-8 record does not bind the sealed pilot-7/5/4/3/2/1 lineage"
        )

    qualification = load_json(qualification_path)
    identity = qualification.get("identity")
    roles_root = qualification_path.parent / "roles"
    roles_manifest = tree_manifest(roles_root)
    if (
        set(qualification_path.parent.iterdir()) != {qualification_path, roles_root}
        or qualification.get("schema_version") != "formalization-provider-qualification-5"
        or qualification.get("status") != "PASSED"
        or qualification.get("classification") != "off_benchmark_provider_qualification"
        or qualification.get("charged_to_contestant") is not False
        or qualification.get("roles_manifest") != roles_manifest
        or roles_manifest.get("tree_sha256") != PILOT8_QUALIFICATION_ROLES_TREE_SHA256
        or not isinstance(identity, Mapping)
        or identity.get("pilot_id") != PILOT8_PILOT_ID
        or identity.get("manifest_sha256") != PILOT8_MANIFEST_FILE_SHA256
        or identity.get("manifest_payload_sha256") != PILOT8_MANIFEST_PAYLOAD_SHA256
        or identity.get("deployment_path") != str(record_path)
        or identity.get("deployment_sha256") != PILOT8_DEPLOYMENT_SHA256
    ):
        raise BenchmarkError("sealed pilot-8 qualification identity changed")

    index_root = run_root / "index"
    pairs_root = run_root / "pairs"
    registry_index_root = GLOBAL_REGISTRY_ROOT / "index" / PILOT8_PILOT_ID
    for directory, expected_names in (
        (index_root, {"H22-11.json"}),
        (pairs_root, {PILOT8_INCIDENT_RUN_ID}),
        (registry_index_root, {"H22-11.json"}),
    ):
        if (
            not directory.is_dir()
            or directory.is_symlink()
            or {entry.name for entry in directory.iterdir()} != expected_names
        ):
            raise BenchmarkError("pilot-8 official pair namespace changed")
    registry_path = registry_index_root / "H22-11.json"
    if (
        not registry_path.is_file()
        or registry_path.is_symlink()
        or sha256_file(registry_path) != PILOT8_INDEX_SHA256
        or load_json(registry_path) != load_json(index_path)
    ):
        raise BenchmarkError("sealed pilot-8 account-global task index changed")

    index = load_json(index_path)
    state = load_json(state_path)
    report = load_json(report_path)
    condition_state = load_json(condition_state_path)
    audit_incident = load_json(audit_incident_path)
    if (
        index.get("schema_version") != "formalization-task-index-2"
        or index.get("pilot_id") != PILOT8_PILOT_ID
        or index.get("release_commit") != PILOT8_RELEASE_COMMIT
        or index.get("manifest_sha256") != PILOT8_MANIFEST_FILE_SHA256
        or index.get("manifest_payload_sha256") != PILOT8_MANIFEST_PAYLOAD_SHA256
        or index.get("deployment_sha256") != PILOT8_DEPLOYMENT_SHA256
        or index.get("task_id") != "H22-11"
        or index.get("run_id") != PILOT8_INCIDENT_RUN_ID
        or index.get("pair_root") != str(pair_root)
        or index.get("pair_state_path") != str(state_path)
        or state.get("status") != "PAIR_INCIDENT"
        or report.get("status") != "PAIR_INCIDENT"
        or state.get("pair_report_sha256") != PILOT8_PAIR_REPORT_SHA256
        or condition_state.get("status") != "AUDIT_SYSTEM_INCIDENT"
        or audit_incident.get("status") != "AUDIT_SYSTEM_INCIDENT"
        or audit_incident.get("classification") != "audit_system_infrastructure"
        or "auditor dependency record does not match D001"
        not in str(audit_incident.get("error", ""))
        or any(
            candidate.get(key) != value
            for candidate in (state, report)
            for key, value in (
                ("pilot_id", PILOT8_PILOT_ID),
                ("task_id", "H22-11"),
                ("run_id", PILOT8_INCIDENT_RUN_ID),
                ("manifest_sha256", PILOT8_MANIFEST_FILE_SHA256),
                ("pair_root", str(pair_root)),
                ("pair_state_path", str(state_path)),
            )
        )
    ):
        raise BenchmarkError("sealed pilot-8 H22-11 incident hash chain changed")

    if verify_status:
        lock_paths = [
            run_root / "locks" / "formalization-pilot.lock",
            GLOBAL_REGISTRY_ROOT / "locks" / "campaign.lock",
            *(
                Path(old_lineage[key]) / "locks" / "formalization-pilot.lock"
                for key in (
                    "predecessor_run_root",
                    "legacy_predecessor_run_root",
                    "ancestral_predecessor_run_root",
                    "great_ancestral_predecessor_run_root",
                    "fifth_ancestral_predecessor_run_root",
                    "sixth_ancestral_predecessor_run_root",
                )
            ),
        ]
        if any(not path.is_file() or path.is_symlink() for path in lock_paths):
            raise BenchmarkError("pilot-8 status would create a predecessor lock")
        status = _pilot8_status(root, record_path)
        if (
            status.get("task_id") != "H22-11"
            or status.get("run_id") != PILOT8_INCIDENT_RUN_ID
            or status.get("status") != "PAIR_INCIDENT"
            or status.get("pair_report_sha256") != PILOT8_PAIR_REPORT_SHA256
        ):
            raise BenchmarkError("frozen pilot-8 H22-11 status changed")

    shifted_lineage = {
        (
            "legacy_predecessor_" + key.removeprefix("predecessor_")
            if key.startswith("predecessor_")
            else "ancestral_predecessor_" + key.removeprefix("legacy_predecessor_")
            if key.startswith("legacy_predecessor_")
            else "great_ancestral_predecessor_"
            + key.removeprefix("ancestral_predecessor_")
            if key.startswith("ancestral_predecessor_")
            else "fifth_ancestral_predecessor_"
            + key.removeprefix("great_ancestral_predecessor_")
            if key.startswith("great_ancestral_predecessor_")
            else "sixth_ancestral_predecessor_"
            + key.removeprefix("fifth_ancestral_predecessor_")
            if key.startswith("fifth_ancestral_predecessor_")
            else "seventh_ancestral_predecessor_"
            + key.removeprefix("sixth_ancestral_predecessor_")
        ): value
        for key, value in old_lineage.items()
    }
    return {
        "predecessor_pilot_id": PILOT8_PILOT_ID,
        "predecessor_deployment_record": str(record_path),
        "predecessor_deployment_record_sha256": PILOT8_DEPLOYMENT_SHA256,
        "predecessor_release_manifest": str(manifest_path),
        "predecessor_release_manifest_sha256": PILOT8_MANIFEST_FILE_SHA256,
        "predecessor_library_build_record": str(build_path),
        "predecessor_library_build_record_sha256": PILOT8_BUILD_RECORD_SHA256,
        "predecessor_run_root": str(run_root),
        "predecessor_qualification": str(qualification_path),
        "predecessor_qualification_sha256": PILOT8_QUALIFICATION_SHA256,
        "predecessor_qualification_roles_tree_sha256": (
            PILOT8_QUALIFICATION_ROLES_TREE_SHA256
        ),
        "predecessor_h22_11_task_index": str(index_path),
        "predecessor_h22_11_task_index_sha256": PILOT8_INDEX_SHA256,
        "predecessor_h22_11_pair_state": str(state_path),
        "predecessor_h22_11_pair_state_sha256": PILOT8_PAIR_STATE_SHA256,
        "predecessor_h22_11_pair_report": str(report_path),
        "predecessor_h22_11_pair_report_sha256": PILOT8_PAIR_REPORT_SHA256,
        "predecessor_h22_11_condition_state": str(condition_state_path),
        "predecessor_h22_11_condition_state_sha256": PILOT8_CONDITION_STATE_SHA256,
        "predecessor_h22_11_audit_incident": str(audit_incident_path),
        "predecessor_h22_11_audit_incident_sha256": PILOT8_AUDIT_INCIDENT_SHA256,
        **shifted_lineage,
    }


def _pilot9_status(root: Path, deployment_record: Path) -> Mapping[str, Any]:
    """Use the frozen Pilot-9 verifier without provider calls or state changes."""

    runner = (
        root / "release" / "paper_bencmark" / "formalization_benchmark"
        / "tools" / "run_benchmark.py"
    )
    environment = os.environ.copy()
    environment.pop("HIGHAMBENCH_COMMAND_CGROUP_PROCS", None)
    environment["HIGHAMBENCH_FORMALIZATION_DEPLOYMENT"] = str(deployment_record)
    environment["HIGHAMBENCH_FORMALIZATION_DEPLOYMENT_SHA256"] = PILOT9_DEPLOYMENT_SHA256
    completed = run_bounded_command(
        isolated_runner_command(
            runner,
            "--deployment",
            str(deployment_record),
            "status",
            "--task-id",
            "H22-11",
        ),
        cwd=root,
        environment=environment,
        timeout_seconds=600,
        maximum_output_bytes=16 * 1024 * 1024,
    )
    if (
        completed["timed_out"]
        or completed["output_limit_exceeded"]
        or completed["returncode"] != 0
    ):
        raise BenchmarkError("frozen pilot-9 status authentication failed for H22-11")
    try:
        result = json.loads(completed["output"])
    except json.JSONDecodeError as error:
        raise BenchmarkError("frozen pilot-9 status output is malformed") from error
    if not isinstance(result, Mapping):
        raise BenchmarkError("frozen pilot-9 status output is malformed")
    return result


def pilot9_lineage(root_argument: str, *, verify_status: bool = True) -> dict[str, str]:
    """Authenticate Pilot-9's sealed cold-start H22-11 pair incident."""

    root = Path(root_argument).expanduser()
    if not root.is_absolute() or root.is_symlink() or not root.is_dir():
        raise BenchmarkError("pilot-9 predecessor deployment root is missing or unsafe")
    root = root.resolve()
    record_path = root / "deployment.json"
    manifest_path = (
        root / "release" / "paper_bencmark" / "formalization_benchmark" / "manifest.json"
    )
    build_path = root / "runtime" / "library" / "build" / "build-record.json"
    run_root = root / "runs"
    qualification_path = (
        run_root / "qualifications" / PILOT9_MANIFEST_FILE_SHA256 / "qualification.json"
    )
    index_path = run_root / "index" / "H22-11.json"
    pair_root = run_root / "pairs" / PILOT9_INCIDENT_RUN_ID
    state_path = pair_root / "pair_state.json"
    report_path = pair_root / "pair_report.json"
    l_condition_path = pair_root / "conditions" / "L" / "condition_state.json"
    n_condition_path = pair_root / "conditions" / "N" / "condition_state.json"
    audit_incident_path = (
        pair_root / "audits"
        / "eac7fcb6672367757eba8b5ad322311edb52d7cae0186eb13dd84cfc5f99a666"
        / "incident.json"
    )
    for path, expected in (
        (record_path, PILOT9_DEPLOYMENT_SHA256),
        (manifest_path, PILOT9_MANIFEST_FILE_SHA256),
        (build_path, PILOT9_BUILD_RECORD_SHA256),
        (qualification_path, PILOT9_QUALIFICATION_SHA256),
        (index_path, PILOT9_INDEX_SHA256),
        (state_path, PILOT9_PAIR_STATE_SHA256),
        (report_path, PILOT9_PAIR_REPORT_SHA256),
        (l_condition_path, PILOT9_L_CONDITION_STATE_SHA256),
        (n_condition_path, PILOT9_N_CONDITION_STATE_SHA256),
        (audit_incident_path, PILOT9_AUDIT_INCIDENT_SHA256),
    ):
        if not path.is_file() or path.is_symlink() or sha256_file(path) != expected:
            raise BenchmarkError(f"sealed pilot-9 evidence is missing or changed: {path}")

    previous = load_json(record_path)
    previous_manifest = load_json(manifest_path)
    if (
        previous.get("schema_version") != "formalization-deployment-1"
        or previous.get("pilot_id") != PILOT9_PILOT_ID
        or previous.get("release_commit") != PILOT9_RELEASE_COMMIT
        or previous.get("release_manifest_sha256") != PILOT9_MANIFEST_FILE_SHA256
        or previous.get("manifest_payload_sha256") != PILOT9_MANIFEST_PAYLOAD_SHA256
        or previous.get("library_build_record") != str(build_path)
        or previous.get("library_build_record_sha256") != PILOT9_BUILD_RECORD_SHA256
        or previous.get("run_root") != str(run_root)
        or previous_manifest.get("pilot_id") != PILOT9_PILOT_ID
        or previous_manifest.get("manifest_payload_sha256")
        != PILOT9_MANIFEST_PAYLOAD_SHA256
    ):
        raise BenchmarkError("sealed pilot-9 release identity changed")
    _pilot5_release_closure(root, previous_manifest)
    old_lineage = pilot8_lineage(
        str(Path(str(previous["predecessor_run_root"])).parent),
        verify_status=verify_status,
    )
    if any(previous.get(key) != value for key, value in old_lineage.items()):
        raise BenchmarkError("pilot-9 record does not bind the sealed prior lineage")

    qualification = load_json(qualification_path)
    roles_root = qualification_path.parent / "roles"
    roles_manifest = tree_manifest(roles_root)
    identity = qualification.get("identity")
    if (
        qualification.get("schema_version") != "formalization-provider-qualification-5"
        or qualification.get("status") != "PASSED"
        or qualification.get("charged_to_contestant") is not False
        or qualification.get("roles_manifest") != roles_manifest
        or roles_manifest.get("tree_sha256") != PILOT9_QUALIFICATION_ROLES_TREE_SHA256
        or not isinstance(identity, Mapping)
        or identity.get("pilot_id") != PILOT9_PILOT_ID
        or identity.get("manifest_sha256") != PILOT9_MANIFEST_FILE_SHA256
        or identity.get("manifest_payload_sha256") != PILOT9_MANIFEST_PAYLOAD_SHA256
        or identity.get("deployment_sha256") != PILOT9_DEPLOYMENT_SHA256
    ):
        raise BenchmarkError("sealed pilot-9 qualification identity changed")

    index = load_json(index_path)
    state = load_json(state_path)
    report = load_json(report_path)
    l_condition = load_json(l_condition_path)
    n_condition = load_json(n_condition_path)
    incident = load_json(audit_incident_path)
    registry_path = GLOBAL_REGISTRY_ROOT / "index" / PILOT9_PILOT_ID / "H22-11.json"
    if (
        not registry_path.is_file()
        or registry_path.is_symlink()
        or sha256_file(registry_path) != PILOT9_INDEX_SHA256
        or load_json(registry_path) != index
        or index.get("schema_version") != "formalization-task-index-2"
        or index.get("pilot_id") != PILOT9_PILOT_ID
        or index.get("release_commit") != PILOT9_RELEASE_COMMIT
        or index.get("manifest_sha256") != PILOT9_MANIFEST_FILE_SHA256
        or index.get("manifest_payload_sha256") != PILOT9_MANIFEST_PAYLOAD_SHA256
        or index.get("deployment_sha256") != PILOT9_DEPLOYMENT_SHA256
        or index.get("run_id") != PILOT9_INCIDENT_RUN_ID
        or state.get("status") != "PAIR_INCIDENT"
        or report.get("status") != "PAIR_INCIDENT"
        or state.get("pair_report_sha256") != PILOT9_PAIR_REPORT_SHA256
        or l_condition.get("status") != "ACCEPTED_FAITHFUL"
        or n_condition.get("status") != "AUDIT_SYSTEM_INCIDENT"
        or incident.get("status") != "AUDIT_SYSTEM_INCIDENT"
    ):
        raise BenchmarkError("sealed pilot-9 H22-11 incident hash chain changed")
    if verify_status:
        status = _pilot9_status(root, record_path)
        if (
            status.get("task_id") != "H22-11"
            or status.get("run_id") != PILOT9_INCIDENT_RUN_ID
            or status.get("status") != "PAIR_INCIDENT"
            or status.get("pair_report_sha256") != PILOT9_PAIR_REPORT_SHA256
        ):
            raise BenchmarkError("frozen pilot-9 H22-11 status changed")

    def shift(key: str) -> str:
        for source, destination in (
            ("seventh_ancestral_predecessor_", "eighth_ancestral_predecessor_"),
            ("sixth_ancestral_predecessor_", "seventh_ancestral_predecessor_"),
            ("fifth_ancestral_predecessor_", "sixth_ancestral_predecessor_"),
            ("great_ancestral_predecessor_", "fifth_ancestral_predecessor_"),
            ("ancestral_predecessor_", "great_ancestral_predecessor_"),
            ("legacy_predecessor_", "ancestral_predecessor_"),
            ("predecessor_", "legacy_predecessor_"),
        ):
            if key.startswith(source):
                return destination + key.removeprefix(source)
        raise BenchmarkError(f"unknown predecessor lineage field: {key}")

    shifted_lineage = {shift(key): value for key, value in old_lineage.items()}
    return {
        "predecessor_pilot_id": PILOT9_PILOT_ID,
        "predecessor_deployment_record": str(record_path),
        "predecessor_deployment_record_sha256": PILOT9_DEPLOYMENT_SHA256,
        "predecessor_release_manifest": str(manifest_path),
        "predecessor_release_manifest_sha256": PILOT9_MANIFEST_FILE_SHA256,
        "predecessor_library_build_record": str(build_path),
        "predecessor_library_build_record_sha256": PILOT9_BUILD_RECORD_SHA256,
        "predecessor_run_root": str(run_root),
        "predecessor_qualification": str(qualification_path),
        "predecessor_qualification_sha256": PILOT9_QUALIFICATION_SHA256,
        "predecessor_qualification_roles_tree_sha256": PILOT9_QUALIFICATION_ROLES_TREE_SHA256,
        "predecessor_h22_11_task_index": str(index_path),
        "predecessor_h22_11_task_index_sha256": PILOT9_INDEX_SHA256,
        "predecessor_h22_11_pair_state": str(state_path),
        "predecessor_h22_11_pair_state_sha256": PILOT9_PAIR_STATE_SHA256,
        "predecessor_h22_11_pair_report": str(report_path),
        "predecessor_h22_11_pair_report_sha256": PILOT9_PAIR_REPORT_SHA256,
        "predecessor_h22_11_l_condition_state": str(l_condition_path),
        "predecessor_h22_11_l_condition_state_sha256": PILOT9_L_CONDITION_STATE_SHA256,
        "predecessor_h22_11_n_condition_state": str(n_condition_path),
        "predecessor_h22_11_n_condition_state_sha256": PILOT9_N_CONDITION_STATE_SHA256,
        "predecessor_h22_11_audit_incident": str(audit_incident_path),
        "predecessor_h22_11_audit_incident_sha256": PILOT9_AUDIT_INCIDENT_SHA256,
        **shifted_lineage,
    }


def _pilot10_status(root: Path, deployment_record: Path) -> Mapping[str, Any]:
    """Use the frozen Pilot-10 verifier without provider calls or state changes."""

    runner = (
        root / "release" / "paper_bencmark" / "formalization_benchmark"
        / "tools" / "run_benchmark.py"
    )
    environment = os.environ.copy()
    environment.pop("HIGHAMBENCH_COMMAND_CGROUP_PROCS", None)
    environment["HIGHAMBENCH_FORMALIZATION_DEPLOYMENT"] = str(deployment_record)
    environment["HIGHAMBENCH_FORMALIZATION_DEPLOYMENT_SHA256"] = (
        PILOT10_DEPLOYMENT_SHA256
    )
    completed = run_bounded_command(
        isolated_runner_command(
            runner,
            "--deployment",
            str(deployment_record),
            "status",
            "--task-id",
            "H22-11",
        ),
        cwd=root,
        environment=environment,
        timeout_seconds=600,
        maximum_output_bytes=16 * 1024 * 1024,
    )
    if (
        completed["timed_out"]
        or completed["output_limit_exceeded"]
        or completed["returncode"] != 0
    ):
        raise BenchmarkError("frozen pilot-10 status authentication failed for H22-11")
    try:
        result = json.loads(completed["output"])
    except json.JSONDecodeError as error:
        raise BenchmarkError("frozen pilot-10 status output is malformed") from error
    if not isinstance(result, Mapping):
        raise BenchmarkError("frozen pilot-10 status output is malformed")
    return result


def pilot10_lineage(root_argument: str, *, verify_status: bool = True) -> dict[str, str]:
    """Authenticate Pilot-10's sealed, failed one-shot warm-root attempt."""

    root = Path(root_argument).expanduser()
    if not root.is_absolute() or root.is_symlink() or not root.is_dir():
        raise BenchmarkError("pilot-10 predecessor deployment root is missing or unsafe")
    root = root.resolve()
    record_path = root / "deployment.json"
    manifest_path = (
        root / "release" / "paper_bencmark" / "formalization_benchmark" / "manifest.json"
    )
    build_path = root / "runtime" / "library" / "build" / "build-record.json"
    run_root = root / "runs"
    qualification_path = (
        run_root / "qualifications" / PILOT10_MANIFEST_FILE_SHA256 / "qualification.json"
    )
    warm_root = run_root / "warm-roots" / PILOT10_MANIFEST_PAYLOAD_SHA256
    warm_record_path = warm_root / "warm-root.json"
    scout_turn_path = warm_root / "scout-artifacts" / "turn.json"
    checkpoint_root = warm_root / "checkpoint"
    scout_artifacts_root = warm_root / "scout-artifacts"
    for path, expected in (
        (record_path, PILOT10_DEPLOYMENT_SHA256),
        (manifest_path, PILOT10_MANIFEST_FILE_SHA256),
        (build_path, PILOT10_BUILD_RECORD_SHA256),
        (qualification_path, PILOT10_QUALIFICATION_SHA256),
        (warm_record_path, PILOT10_FAILED_WARM_ROOT_SHA256),
        (scout_turn_path, PILOT10_SCOUT_TURN_SHA256),
    ):
        if not path.is_file() or path.is_symlink() or sha256_file(path) != expected:
            raise BenchmarkError(f"sealed pilot-10 evidence is missing or changed: {path}")
    if (
        tree_manifest(checkpoint_root).get("tree_sha256")
        != PILOT10_CHECKPOINT_TREE_SHA256
        or tree_manifest(scout_artifacts_root).get("tree_sha256")
        != PILOT10_SCOUT_ARTIFACTS_TREE_SHA256
    ):
        raise BenchmarkError("sealed pilot-10 failed warm-root tree changed")

    previous = load_json(record_path)
    previous_manifest = load_json(manifest_path)
    if (
        previous.get("schema_version") != "formalization-deployment-1"
        or previous.get("pilot_id") != PILOT10_PILOT_ID
        or previous.get("release_commit") != PILOT10_RELEASE_COMMIT
        or previous.get("release_manifest_sha256") != PILOT10_MANIFEST_FILE_SHA256
        or previous.get("manifest_payload_sha256") != PILOT10_MANIFEST_PAYLOAD_SHA256
        or previous.get("library_build_record") != str(build_path)
        or previous.get("library_build_record_sha256") != PILOT10_BUILD_RECORD_SHA256
        or previous.get("run_root") != str(run_root)
        or previous_manifest.get("pilot_id") != PILOT10_PILOT_ID
        or previous_manifest.get("manifest_payload_sha256")
        != PILOT10_MANIFEST_PAYLOAD_SHA256
    ):
        raise BenchmarkError("sealed pilot-10 release identity changed")
    _pilot5_release_closure(root, previous_manifest)
    old_lineage = pilot9_lineage(
        str(Path(str(previous["predecessor_run_root"])).parent),
        verify_status=verify_status,
    )
    if any(previous.get(key) != value for key, value in old_lineage.items()):
        raise BenchmarkError("pilot-10 record does not bind the sealed prior lineage")

    qualification = load_json(qualification_path)
    roles_root = qualification_path.parent / "roles"
    roles_manifest = tree_manifest(roles_root)
    identity = qualification.get("identity")
    if (
        qualification.get("schema_version") != "formalization-provider-qualification-5"
        or qualification.get("status") != "PASSED"
        or qualification.get("charged_to_contestant") is not False
        or qualification.get("roles_manifest") != roles_manifest
        or roles_manifest.get("tree_sha256") != PILOT10_QUALIFICATION_ROLES_TREE_SHA256
        or not isinstance(identity, Mapping)
        or identity.get("pilot_id") != PILOT10_PILOT_ID
        or identity.get("manifest_sha256") != PILOT10_MANIFEST_FILE_SHA256
        or identity.get("manifest_payload_sha256") != PILOT10_MANIFEST_PAYLOAD_SHA256
        or identity.get("deployment_sha256") != PILOT10_DEPLOYMENT_SHA256
    ):
        raise BenchmarkError("sealed pilot-10 qualification identity changed")

    warm_record = load_json(warm_record_path)
    scout_turn = load_json(scout_turn_path)
    expected_raw_usage = {
        "cache_write_input_tokens": 0,
        "cached_input_tokens": 2_939_136,
        "input_tokens": 3_240_551,
        "output_tokens": 19_132,
        "reasoning_output_tokens": 3_938,
        "total_tokens": 3_259_683,
    }
    expected_cumulative_usage = {
        "cache_write_input_tokens": 0,
        "cached_input_tokens": 2_704_256,
        "input_tokens": 2_991_596,
        "output_tokens": 14_632,
        "reasoning_output_tokens": 3_938,
        "total_tokens": 3_006_228,
    }
    if (
        warm_record.get("schema_version") != "formalization-warm-root-1"
        or warm_record.get("pilot_id") != PILOT10_PILOT_ID
        or warm_record.get("manifest_payload_sha256")
        != PILOT10_MANIFEST_PAYLOAD_SHA256
        or warm_record.get("status") != "FAILED"
        or warm_record.get("failure_kind") != "telemetry_invalid"
        or warm_record.get("formalizer_exit_code") != 70
        or warm_record.get("task_material_available") is not False
        or warm_record.get("benchmark_charged") is not False
        or warm_record.get("scout_runs_per_release") != 1
        or scout_turn.get("terminal_status") != "completed"
        or scout_turn.get("exit_code") != 70
        or scout_turn.get("failure_kind") != "telemetry_invalid"
        or scout_turn.get("usage_complete") is not False
        or scout_turn.get("protocol_error")
        != "Codex raw response usage disagrees with the cumulative usage delta"
        or scout_turn.get("usage") != expected_raw_usage
        or scout_turn.get("cumulative_usage_delta_cross_check")
        != expected_cumulative_usage
        or scout_turn.get("thread_id") != "01a0c34a-0076-7f52-bc73-b936ab93c15b"
        or scout_turn.get("turn_id") != "01a0c34a-0082-7693-98a2-060f4d3157e9"
    ):
        raise BenchmarkError("sealed pilot-10 failed warm-root record changed")

    local_index_root = run_root / "index"
    registry_root = GLOBAL_REGISTRY_ROOT / "index" / PILOT10_PILOT_ID
    if (
        (local_index_root.exists() and any(local_index_root.iterdir()))
        or (registry_root.exists() and any(registry_root.iterdir()))
    ):
        raise BenchmarkError("pilot-10 unexpectedly contains an official task observation")
    if verify_status:
        status = _pilot10_status(root, record_path)
        if status != {"status": "NOT_STARTED", "task_id": "H22-11"}:
            raise BenchmarkError("frozen pilot-10 H22-11 status changed")

    def shift(key: str) -> str:
        for source, destination in (
            ("eighth_ancestral_predecessor_", "ninth_ancestral_predecessor_"),
            ("seventh_ancestral_predecessor_", "eighth_ancestral_predecessor_"),
            ("sixth_ancestral_predecessor_", "seventh_ancestral_predecessor_"),
            ("fifth_ancestral_predecessor_", "sixth_ancestral_predecessor_"),
            ("great_ancestral_predecessor_", "fifth_ancestral_predecessor_"),
            ("ancestral_predecessor_", "great_ancestral_predecessor_"),
            ("legacy_predecessor_", "ancestral_predecessor_"),
            ("predecessor_", "legacy_predecessor_"),
        ):
            if key.startswith(source):
                return destination + key.removeprefix(source)
        raise BenchmarkError(f"unknown predecessor lineage field: {key}")

    shifted_lineage = {shift(key): value for key, value in old_lineage.items()}
    return {
        "predecessor_pilot_id": PILOT10_PILOT_ID,
        "predecessor_deployment_record": str(record_path),
        "predecessor_deployment_record_sha256": PILOT10_DEPLOYMENT_SHA256,
        "predecessor_release_manifest": str(manifest_path),
        "predecessor_release_manifest_sha256": PILOT10_MANIFEST_FILE_SHA256,
        "predecessor_library_build_record": str(build_path),
        "predecessor_library_build_record_sha256": PILOT10_BUILD_RECORD_SHA256,
        "predecessor_run_root": str(run_root),
        "predecessor_qualification": str(qualification_path),
        "predecessor_qualification_sha256": PILOT10_QUALIFICATION_SHA256,
        "predecessor_qualification_roles_tree_sha256": (
            PILOT10_QUALIFICATION_ROLES_TREE_SHA256
        ),
        "predecessor_failed_warm_root_record": str(warm_record_path),
        "predecessor_failed_warm_root_record_sha256": PILOT10_FAILED_WARM_ROOT_SHA256,
        "predecessor_failed_warm_root_checkpoint_tree_sha256": (
            PILOT10_CHECKPOINT_TREE_SHA256
        ),
        "predecessor_failed_warm_root_scout_artifacts_tree_sha256": (
            PILOT10_SCOUT_ARTIFACTS_TREE_SHA256
        ),
        "predecessor_failed_warm_root_scout_turn": str(scout_turn_path),
        "predecessor_failed_warm_root_scout_turn_sha256": PILOT10_SCOUT_TURN_SHA256,
        **shifted_lineage,
    }


def verify_predecessor_lineage(root_argument: str, deployment_record: Mapping[str, Any]) -> None:
    observed = pilot10_lineage(root_argument)
    if any(deployment_record.get(field) != value for field, value in observed.items()):
        raise BenchmarkError("predecessor evidence changed during pilot-11 setup")


def fsync_directory(path: Path) -> None:
    descriptor = os.open(path, os.O_RDONLY | os.O_DIRECTORY)
    try:
        os.fsync(descriptor)
    finally:
        os.close(descriptor)


def run(
    command: list[str], *, cwd: Path | None = None, env: Mapping[str, str] | None = None
) -> str:
    completed = subprocess.run(
        command,
        cwd=cwd,
        env=env,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        check=False,
    )
    if completed.returncode != 0:
        raise BenchmarkError(
            f"command failed ({completed.returncode}): {' '.join(command)}\n{completed.stdout}"
        )
    return completed.stdout.strip()


def command_path(name: str) -> Path:
    raw = shutil.which(name)
    if raw is None:
        raise BenchmarkError(f"required Titan command is missing: {name}")
    return Path(raw).resolve()


def measured_build_service_environment(deployment_root: Path) -> dict[str, str]:
    """Prepare stable, private paths passed into the measured build service."""

    tooling_root = deployment_root.parent / "tooling"
    paths = {
        "TMPDIR": tooling_root / "tmp",
        "XDG_CACHE_HOME": tooling_root / "cache",
        "ELAN_HOME": tooling_root / "elan",
    }
    for path in (tooling_root, *paths.values()):
        path.mkdir(parents=True, exist_ok=True, mode=0o700)
        metadata = path.lstat()
        if (
            path.is_symlink()
            or not path.is_dir()
            or metadata.st_uid != os.getuid()
            or metadata.st_mode & 0o077
        ):
            raise BenchmarkError(f"measured-build tooling path is unsafe: {path.name}")
    return {key: str(path.resolve()) for key, path in sorted(paths.items())}


def private_provisioning_environment(deployment_root: Path) -> dict[str, str]:
    """Keep Lake cache downloads and temporary clones off the home filesystem."""

    environment = dict(os.environ)
    environment.update(measured_build_service_environment(deployment_root))
    environment["PATH"] = environment.get("PATH", "/usr/bin:/bin")
    private_tooling_bin = deployment_root.parent / "tooling" / "elan" / "bin"
    if private_tooling_bin.is_dir() and not private_tooling_bin.is_symlink():
        environment["PATH"] = f"{private_tooling_bin}:{environment['PATH']}"
    return environment


def measured_build_command(
    *,
    systemd_run: Path,
    build_runner: Path,
    checkout: Path,
    artifact_root: Path,
    toolchain_root: Path,
    expected_commit: str,
    mathlib_commit: str,
    lean_toolchain: str,
    service_environment: Mapping[str, str],
) -> list[str]:
    environment_arguments = [
        argument
        for key, value in sorted(service_environment.items())
        for argument in ("--setenv", f"{key}={value}")
    ]
    return [
        *systemd_service_envelope_prefix(str(systemd_run)),
        *environment_arguments,
        *isolated_runner_command(
            build_runner,
            "--checkout",
            str(checkout),
            "--artifact-root",
            str(artifact_root),
            "--toolchain-root",
            str(toolchain_root),
            "--expected-commit",
            expected_commit,
            "--mathlib-commit",
            mathlib_commit,
            "--lean-toolchain",
            lean_toolchain,
        ),
    ]


def copy_tree_read_only(source: Path, destination: Path) -> None:
    if destination.exists():
        shutil.rmtree(destination)
    shutil.copytree(source, destination, symlinks=False)
    for path in [destination, *destination.rglob("*")]:
        mode = path.stat().st_mode
        if path.is_dir():
            path.chmod((mode & 0o555) or 0o500)
        else:
            path.chmod((mode & 0o555) or 0o400)


def find_toolchain_root(
    *, cwd: Path, env: Mapping[str, str] | None = None
) -> Path:
    lean = Path(run(["elan", "which", "lean"], cwd=cwd, env=env)).resolve()
    if lean.name != "lean" or lean.parent.name != "bin":
        raise BenchmarkError(f"could not derive Lean toolchain root from {lean}")
    return lean.parent.parent


def isolated_runner_command(runner: Path, *arguments: str) -> list[str]:
    """Invoke a frozen sibling-import script without weakening Python isolation."""

    runner = runner.resolve()
    bootstrap = (
        "import runpy,sys;"
        f"sys.path.insert(0,{json.dumps(str(runner.parent))});"
        f"sys.argv[0]={json.dumps(str(runner))};"
        f"runpy.run_path({json.dumps(str(runner))},run_name='__main__')"
    )
    return [sys.executable, "-I", "-B", "-c", bootstrap, *arguments]


def launcher_bytes(
    deployment_record: Path, deployment_sha256: str, runner: Path
) -> bytes:
    command = " ".join(shlex.quote(item) for item in isolated_runner_command(runner))
    source = f"""#!/bin/sh
set -eu
export HIGHAMBENCH_FORMALIZATION_DEPLOYMENT={shlex.quote(str(deployment_record))}
export HIGHAMBENCH_FORMALIZATION_DEPLOYMENT_SHA256={shlex.quote(deployment_sha256)}
exec {command} "$@"
    """
    return source.encode("utf-8")


def write_launcher(
    path: Path, deployment_record: Path, deployment_sha256: str, runner: Path
) -> None:
    payload = launcher_bytes(deployment_record, deployment_sha256, runner)
    path.parent.mkdir(parents=True, exist_ok=True)
    flags = os.O_WRONLY | os.O_CREAT | os.O_EXCL | os.O_CLOEXEC
    if hasattr(os, "O_NOFOLLOW"):
        flags |= os.O_NOFOLLOW
    descriptor = os.open(path, flags, 0o500)
    try:
        offset = 0
        while offset < len(payload):
            offset += os.write(descriptor, payload[offset:])
        os.fsync(descriptor)
        os.fchmod(descriptor, 0o500)
    finally:
        os.close(descriptor)
    fsync_directory(path.parent)


def _directory_state(path: Path) -> tuple[tuple[int, int], int]:
    """Return one no-follow directory identity and mode from the same open."""

    flags = os.O_RDONLY | os.O_CLOEXEC
    if hasattr(os, "O_DIRECTORY"):
        flags |= os.O_DIRECTORY
    if hasattr(os, "O_NOFOLLOW"):
        flags |= os.O_NOFOLLOW
    descriptor = os.open(path, flags)
    try:
        opened = os.fstat(descriptor)
        named = os.stat(path, follow_symlinks=False)
    finally:
        os.close(descriptor)
    if not stat.S_ISDIR(opened.st_mode) or not stat.S_ISDIR(named.st_mode):
        raise BenchmarkError(f"expected a directory: {path}")
    identity = (opened.st_dev, opened.st_ino)
    if identity != (named.st_dev, named.st_ino):
        raise BenchmarkError(f"directory changed while it was opened: {path}")
    return identity, stat.S_IMODE(opened.st_mode)


def _directory_has_identity(path: Path, expected: tuple[int, int]) -> bool:
    try:
        metadata = os.stat(path, follow_symlinks=False)
    except OSError:
        return False
    return stat.S_ISDIR(metadata.st_mode) and (
        metadata.st_dev,
        metadata.st_ino,
    ) == expected


def _replace_skill_directory(
    source: Path,
    destination: Path,
    *,
    expected_identity: tuple[int, int],
    preserved_mode: int,
) -> None:
    """Move one skill directory while preserving its exact root mode.

    Some Linux filesystems reject a cross-parent directory rename when the
    directory being moved is owner-read/execute-only.  Frozen skill roots are
    intentionally mode 0500, so add only owner-write for the duration of the
    rename.  Restoring through an open descriptor follows the directory across
    the rename and also handles an exception raised after the rename committed.
    """

    flags = os.O_RDONLY | os.O_CLOEXEC
    if hasattr(os, "O_DIRECTORY"):
        flags |= os.O_DIRECTORY
    if hasattr(os, "O_NOFOLLOW"):
        flags |= os.O_NOFOLLOW
    descriptor = os.open(source, flags)
    move_error: BaseException | None = None
    try:
        opened = os.fstat(descriptor)
        named = os.stat(source, follow_symlinks=False)
        if not stat.S_ISDIR(opened.st_mode) or not stat.S_ISDIR(named.st_mode):
            raise BenchmarkError(f"skill move source is not a directory: {source}")
        opened_identity = (opened.st_dev, opened.st_ino)
        if opened_identity != expected_identity:
            raise BenchmarkError(f"unexpected skill move source: {source}")
        if opened_identity != (named.st_dev, named.st_ino):
            raise BenchmarkError(f"skill move source changed before rename: {source}")
        current_mode = stat.S_IMODE(opened.st_mode)
        relaxed_mode = current_mode | stat.S_IWUSR
        cross_parent = source.parent != destination.parent
        if cross_parent and relaxed_mode != current_mode:
            os.fchmod(descriptor, relaxed_mode)
        try:
            os.replace(source, destination)
            installed = os.stat(destination, follow_symlinks=False)
            if not stat.S_ISDIR(installed.st_mode) or (
                installed.st_dev,
                installed.st_ino,
            ) != opened_identity:
                raise BenchmarkError(
                    "skill rename destination does not identify the moved directory: "
                    f"{destination}"
                )
        except BaseException as error:
            move_error = error
            raise
        finally:
            if stat.S_IMODE(os.fstat(descriptor).st_mode) != preserved_mode:
                try:
                    os.fchmod(descriptor, preserved_mode)
                except BaseException as first_restore_error:
                    try:
                        os.fchmod(descriptor, preserved_mode)
                    except BaseException as retry_restore_error:
                        message = (
                            "skill directory mode could not be restored after rename; "
                            "the transaction was retained for exact recovery: "
                            f"{retry_restore_error}"
                        )
                        if move_error is not None:
                            raise BenchmarkError(message) from move_error
                        raise BenchmarkError(message) from first_restore_error
                    if stat.S_IMODE(os.fstat(descriptor).st_mode) != preserved_mode:
                        raise BenchmarkError(
                            "skill directory mode recovery did not restore the exact "
                            f"mode {preserved_mode:#o}"
                        ) from first_restore_error
                    message = (
                        "skill directory mode restoration initially failed; exact "
                        "mode was recovered and the installation was rolled back"
                    )
                    if move_error is None:
                        raise BenchmarkError(message) from first_restore_error
            if stat.S_IMODE(os.fstat(descriptor).st_mode) != preserved_mode:
                raise BenchmarkError(
                    "skill directory mode differs from its preserved mode after rename"
                )
            if move_error is None:
                installed = os.stat(destination, follow_symlinks=False)
                if not stat.S_ISDIR(installed.st_mode) or (
                    installed.st_dev,
                    installed.st_ino,
                ) != opened_identity:
                    raise BenchmarkError(
                        "skill rename destination changed before move completion: "
                        f"{destination}"
                    )
    finally:
        os.close(descriptor)


def _remove_directory_contents_by_descriptor(descriptor: int) -> None:
    """Delete one owned directory tree without following path substitutions."""

    metadata = os.fstat(descriptor)
    if not stat.S_ISDIR(metadata.st_mode):
        raise BenchmarkError("skill transaction cleanup descriptor is not a directory")
    required_mode = stat.S_IMODE(metadata.st_mode) | stat.S_IWUSR
    if required_mode != stat.S_IMODE(metadata.st_mode):
        os.fchmod(descriptor, required_mode)
    for name in os.listdir(descriptor):
        named = os.stat(name, dir_fd=descriptor, follow_symlinks=False)
        if stat.S_ISDIR(named.st_mode):
            flags = os.O_RDONLY | os.O_CLOEXEC
            if hasattr(os, "O_DIRECTORY"):
                flags |= os.O_DIRECTORY
            if hasattr(os, "O_NOFOLLOW"):
                flags |= os.O_NOFOLLOW
            child = os.open(name, flags, dir_fd=descriptor)
            try:
                opened = os.fstat(child)
                expected = (named.st_dev, named.st_ino)
                if not stat.S_ISDIR(opened.st_mode) or (
                    opened.st_dev,
                    opened.st_ino,
                ) != expected:
                    raise BenchmarkError(
                        f"skill transaction child changed before traversal: {name}"
                    )
                _remove_directory_contents_by_descriptor(child)
                current = os.stat(name, dir_fd=descriptor, follow_symlinks=False)
                if not stat.S_ISDIR(current.st_mode) or (
                    current.st_dev,
                    current.st_ino,
                ) != expected:
                    raise BenchmarkError(
                        f"skill transaction child changed before removal: {name}"
                    )
            finally:
                os.close(child)
            os.rmdir(name, dir_fd=descriptor)
        elif stat.S_ISREG(named.st_mode) or stat.S_ISLNK(named.st_mode):
            os.unlink(name, dir_fd=descriptor)
        else:
            raise BenchmarkError(
                f"unsafe special file in skill transaction: {name}"
            )


def _remove_skill_transaction_tree(transaction_root: Path) -> None:
    """Quarantine then remove exactly one authenticated transaction tree."""

    flags = os.O_RDONLY | os.O_CLOEXEC
    if hasattr(os, "O_DIRECTORY"):
        flags |= os.O_DIRECTORY
    if hasattr(os, "O_NOFOLLOW"):
        flags |= os.O_NOFOLLOW
    descriptor = os.open(transaction_root, flags)
    quarantine = transaction_root.parent / (
        f".{transaction_root.name}.cleanup-{os.getpid()}-{os.urandom(8).hex()}"
    )
    try:
        opened = os.fstat(descriptor)
        named = os.stat(transaction_root, follow_symlinks=False)
        expected = (opened.st_dev, opened.st_ino)
        if not stat.S_ISDIR(opened.st_mode) or not stat.S_ISDIR(named.st_mode):
            raise BenchmarkError("skill transaction root is not a directory")
        if expected != (named.st_dev, named.st_ino):
            raise BenchmarkError("skill transaction root changed before quarantine")
        os.rename(transaction_root, quarantine)
        fsync_directory(transaction_root.parent)
        quarantined = os.stat(quarantine, follow_symlinks=False)
        if not stat.S_ISDIR(quarantined.st_mode) or (
            quarantined.st_dev,
            quarantined.st_ino,
        ) != expected:
            raise BenchmarkError("skill transaction root changed during quarantine")
        _remove_directory_contents_by_descriptor(descriptor)
        quarantined = os.stat(quarantine, follow_symlinks=False)
        if not stat.S_ISDIR(quarantined.st_mode) or (
            quarantined.st_dev,
            quarantined.st_ino,
        ) != expected:
            raise BenchmarkError("skill transaction root changed before removal")
        os.rmdir(quarantine)
        fsync_directory(transaction_root.parent)
    finally:
        os.close(descriptor)


def _quarantine_unverified_skill_destination(destination: Path) -> Path:
    """Move an untrusted destination entry aside without traversing it."""

    quarantine = destination.parent / (
        f".{destination.name}.untrusted-{os.getpid()}-{os.urandom(8).hex()}"
    )
    os.replace(destination, quarantine)
    fsync_directory(destination.parent)
    return quarantine


def install_skill_atomically(source: Path, destination: Path) -> None:
    """Replace an installed skill without deleting the prior copy first.

    Staging and backup names are unique so concurrent installer invocations do
    not delete one another's files.  The old directory is restored if the
    final rename fails.  A backup that cannot be cleaned after a successful
    install is deliberately retained in its uniquely named transaction
    directory rather than turning a usable installation into a failed setup.
    """

    if not source.is_dir() or source.is_symlink():
        raise BenchmarkError(f"skill source is missing or unsafe: {source}")
    destination.parent.mkdir(parents=True, exist_ok=True)
    for abandoned in destination.parent.glob(f".{destination.name}.install-*"):
        if not abandoned.is_dir() or abandoned.is_symlink():
            raise BenchmarkError(f"unsafe abandoned skill transaction: {abandoned}")
        state_record = abandoned / "skill-install-state.json"
        if os.path.lexists(state_record):
            raise BenchmarkError(
                "a journaled skill transaction requires exact recovery before a "
                f"new install may start: {abandoned}"
            )
        previous = abandoned / "previous"
        staged_abandoned = abandoned / "staged"
        if (
            not os.path.lexists(destination)
            and previous.is_dir()
            and not previous.is_symlink()
        ):
            previous_identity, previous_mode = _directory_state(previous)
            _replace_skill_directory(
                previous,
                destination,
                expected_identity=previous_identity,
                preserved_mode=previous_mode,
            )
            fsync_directory(destination.parent)
        if os.path.lexists(destination):
            try:
                _remove_skill_transaction_tree(abandoned)
            except (BenchmarkError, OSError):
                pass
        elif staged_abandoned.is_dir() and not staged_abandoned.is_symlink():
            try:
                _remove_skill_transaction_tree(abandoned)
            except (BenchmarkError, OSError):
                pass
    if destination.exists() or destination.is_symlink():
        if not destination.is_dir() or destination.is_symlink():
            raise BenchmarkError(
                f"installed skill destination is unsafe: {destination}"
            )

    transaction_root = Path(
        tempfile.mkdtemp(
            prefix=f".{destination.name}.install-", dir=str(destination.parent)
        )
    )
    staged = transaction_root / "staged"
    backup = transaction_root / "previous"
    destination_existed = destination.exists()
    staged_identity: tuple[int, int] | None = None
    staged_mode: int | None = None
    previous_identity: tuple[int, int] | None = None
    previous_mode: int | None = None
    try:
        if destination_existed:
            previous_identity, previous_mode = _directory_state(destination)
        shutil.copytree(source, staged)
        staged_identity, staged_mode = _directory_state(staged)
        write_json_atomic(
            transaction_root / "skill-install-state.json",
            {
                "schema_version": 1,
                "destination": str(destination),
                "destination_existed": destination_existed,
                "staged_identity": list(staged_identity),
                "staged_mode": staged_mode,
                "previous_identity": (
                    list(previous_identity) if previous_identity is not None else None
                ),
                "previous_mode": previous_mode,
            },
            mode=0o600,
        )
        if destination_existed:
            assert previous_identity is not None and previous_mode is not None
            _replace_skill_directory(
                destination,
                backup,
                expected_identity=previous_identity,
                preserved_mode=previous_mode,
            )
            fsync_directory(destination.parent)
        _replace_skill_directory(
            staged,
            destination,
            expected_identity=staged_identity,
            preserved_mode=staged_mode,
        )
        fsync_directory(destination.parent)
    except BaseException as install_error:
        try:
            backup_is_previous = (
                previous_identity is not None
                and _directory_has_identity(backup, previous_identity)
            )
            if backup_is_previous:
                assert previous_identity is not None and previous_mode is not None
                if os.path.lexists(destination):
                    if staged_identity is not None and _directory_has_identity(
                        destination, staged_identity
                    ):
                        assert staged_mode is not None
                        _replace_skill_directory(
                            destination,
                            staged,
                            expected_identity=staged_identity,
                            preserved_mode=staged_mode,
                        )
                        fsync_directory(destination.parent)
                    else:
                        _quarantine_unverified_skill_destination(destination)
                _replace_skill_directory(
                    backup,
                    destination,
                    expected_identity=previous_identity,
                    preserved_mode=previous_mode,
                )
                fsync_directory(destination.parent)
            elif destination_existed:
                if previous_identity is None or not _directory_has_identity(
                    destination, previous_identity
                ):
                    raise BenchmarkError(
                        "previous skill is not at its destination or backup; "
                        f"recover the retained transaction at {transaction_root}"
                    )
                assert previous_mode is not None
                if stat.S_IMODE(
                    os.stat(destination, follow_symlinks=False).st_mode
                ) != previous_mode:
                    raise BenchmarkError(
                        "previous skill mode is not exact; recover the retained "
                        f"transaction at {transaction_root}"
                    )
            elif os.path.lexists(destination):
                if staged_identity is not None and _directory_has_identity(
                    destination, staged_identity
                ):
                    assert staged_mode is not None
                    _replace_skill_directory(
                        destination,
                        staged,
                        expected_identity=staged_identity,
                        preserved_mode=staged_mode,
                    )
                    fsync_directory(destination.parent)
                else:
                    _quarantine_unverified_skill_destination(destination)
        except BaseException as restore_error:
            raise BenchmarkError(
                "skill install failed and its previous installation could not be "
                f"restored; recover it from {transaction_root}: {restore_error}"
            ) from install_error
        try:
            _remove_skill_transaction_tree(transaction_root)
        except (BenchmarkError, OSError):
            pass
        raise
    # The destination is now durably committed. Cleanup is best-effort and
    # must not turn a usable deployment into a rollback after the skill swap.
    try:
        _remove_skill_transaction_tree(transaction_root)
    except BaseException:
        pass


def make_tree_read_only(root: Path) -> None:
    for path in sorted(root.rglob("*"), key=lambda item: len(item.parts), reverse=True):
        if path.is_symlink():
            raise BenchmarkError(f"frozen release contains a symlink: {path}")
        mode = path.stat().st_mode
        path.chmod((mode & 0o555) or (0o500 if path.is_dir() else 0o400))
    root.chmod(0o500)


def directory_identity(path: Path) -> tuple[int, int]:
    """Read a directory identity without following its final path component."""

    flags = os.O_RDONLY | os.O_CLOEXEC
    if hasattr(os, "O_DIRECTORY"):
        flags |= os.O_DIRECTORY
    if hasattr(os, "O_NOFOLLOW"):
        flags |= os.O_NOFOLLOW
    descriptor = os.open(path, flags)
    try:
        opened = os.fstat(descriptor)
        named = os.stat(path, follow_symlinks=False)
    finally:
        os.close(descriptor)
    if not stat.S_ISDIR(opened.st_mode) or not stat.S_ISDIR(named.st_mode):
        raise BenchmarkError(f"deployment root is no longer a directory: {path}")
    opened_identity = (opened.st_dev, opened.st_ino)
    if opened_identity != (named.st_dev, named.st_ino):
        raise BenchmarkError("deployment root changed while its identity was checked")
    return opened_identity


def assert_directory_identity(
    path: Path, expected: tuple[int, int], *, phase: str
) -> None:
    try:
        actual = directory_identity(path)
    except (OSError, BenchmarkError) as error:
        raise BenchmarkError(
            f"installer-owned deployment root became unsafe during {phase}: {error}"
        ) from error
    if actual != expected:
        raise BenchmarkError(
            f"installer-owned deployment root identity changed during {phase}"
        )


def remove_owned_deployment_root(
    path: Path, expected_identity: tuple[int, int]
) -> None:
    """Remove only a failed root created by the current installer invocation."""

    assert_directory_identity(path, expected_identity, phase="failure cleanup entry")
    quarantine = path.parent / f".{path.name}.failed-{os.getpid()}-{os.urandom(8).hex()}"
    os.rename(path, quarantine)
    fsync_directory(path.parent)
    # Reauthenticate after the atomic rename. A last-moment substitution is
    # preserved at the quarantine name and is never recursively deleted.
    assert_directory_identity(
        quarantine, expected_identity, phase="failure cleanup quarantine"
    )
    for current, directories, files in os.walk(quarantine, topdown=True):
        assert_directory_identity(
            quarantine, expected_identity, phase="failure cleanup traversal"
        )
        os.chmod(current, 0o700)
        for name in directories:
            candidate = Path(current) / name
            if not candidate.is_symlink():
                candidate.chmod(0o700)
        for name in files:
            candidate = Path(current) / name
            if not candidate.is_symlink():
                candidate.chmod(0o600)
    assert_directory_identity(
        quarantine, expected_identity, phase="failure cleanup removal"
    )
    shutil.rmtree(quarantine)
    fsync_directory(path.parent)


def _regular_file_equals(path: Path, expected: bytes) -> bool:
    """Return false, rather than masking a canary failure, for a missing artifact."""

    try:
        metadata = path.lstat()
        if stat.S_ISLNK(metadata.st_mode) or not stat.S_ISREG(metadata.st_mode):
            return False
        return stable_regular_bytes(path, maximum_bytes=len(expected)) == expected
    except (BenchmarkError, OSError):
        return False


def _regular_file_present(path: Path) -> bool:
    """Check for a non-symlink regular artifact without raising on absence."""

    try:
        metadata = path.lstat()
    except OSError:
        return False
    return stat.S_ISREG(metadata.st_mode) and not stat.S_ISLNK(metadata.st_mode)


def _regular_file_nonempty(path: Path) -> bool:
    """Check a canary marker without replacing the originating sandbox error."""

    try:
        metadata = path.lstat()
    except OSError:
        return False
    return (
        stat.S_ISREG(metadata.st_mode)
        and not stat.S_ISLNK(metadata.st_mode)
        and metadata.st_size > 0
    )


def run_command_sandbox_canary(deployment: Deployment, condition: str) -> dict:
    """Exercise Landlock, seccomp, control isolation, and Lean through Bash."""

    if condition not in {"N", "L"}:
        raise BenchmarkError(f"invalid command-canary condition: {condition}")
    with tempfile.TemporaryDirectory(
        prefix=f"formalization-command-{condition}-", dir=deployment.path.parent
    ) as temporary:
        root = Path(temporary)
        workspace = root / "workspace"
        control = root / "control"
        workspace.mkdir()
        control.mkdir()
        marker = root / "network-violations.bin"
        write_bytes_atomic(marker, b"", mode=0o600)
        fake_auth = control / "auth.json"
        fake_secret = b"command-canary-secret\n"
        write_bytes_atomic(fake_auth, fake_secret, mode=0o600)
        import_line = "import NumStability" if condition == "L" else "import Mathlib"
        write_bytes_atomic(
            workspace / "Canary.lean",
            f"{import_line}\n#check Nat\n".encode("utf-8"),
            mode=0o600,
        )
        library_assertion = (
            "test -r /library/NumStability.lean"
            if condition == "L"
            else "test ! -e /library/NumStability.lean"
        )
        script = f"""set -eu
test -z "${{CODEX_HOME+x}}"
test "$HOME" = /home/bench
test "$(ulimit -f)" = 262144
test "$(ulimit -c)" = 0
printf 'workspace-ok\\n' > /workspace/write-ok
if cat /control/codex/auth.json >/dev/null 2>&1; then exit 41; fi
if : > /control/codex/auth.json 2>/dev/null; then exit 42; fi
if printf injected > /control/codex/config.toml 2>/dev/null; then exit 43; fi
if mv /control/codex/auth.json /workspace/moved-auth 2>/dev/null; then exit 44; fi
if ln /control/codex/auth.json /workspace/linked-auth 2>/dev/null; then exit 45; fi
if ln -s /control/codex/auth.json /workspace/control-link 2>/dev/null; then exit 46; fi
if mkfifo /workspace/generated-fifo 2>/dev/null; then exit 47; fi
if dd if=/proc/1/mem of=/dev/null bs=1 count=1 >/dev/null 2>&1; then exit 48; fi
if cat /proc/1/environ >/dev/null 2>&1; then exit 49; fi
if ls /proc/1/fd >/dev/null 2>&1; then exit 50; fi
if cat /proc/1/root/control/codex/auth.json >/dev/null 2>&1; then exit 51; fi
{library_assertion}
lean --root /workspace -o /workspace/Canary.olean /workspace/Canary.lean
python3 - <<'PY'
import ctypes
import errno
import fcntl
import os
libc = ctypes.CDLL(None, use_errno=True)
ctypes.set_errno(0)
result = libc.socket(2, 1, 0)
if result != -1 or ctypes.get_errno() != errno.EPERM:
    raise SystemExit(51)
open('/workspace/network-ok', 'w', encoding='utf-8').write('socket-denied\\n')

result = libc.syscall(0x40000000 | 41, 2, 1, 0)
if result != -1 or ctypes.get_errno() != errno.EPERM:
    raise SystemExit(52)
open('/workspace/x32-ok', 'w', encoding='utf-8').write('x32-denied\\n')

def require_denied(number, *arguments):
    ctypes.set_errno(0)
    result = libc.syscall(number, *arguments)
    if result != -1 or ctypes.get_errno() != errno.EPERM:
        raise SystemExit(53)

# x86-64 syscall numbers. The launcher itself rejects every other ABI.
require_denied(62, 2147483647, 0)  # kill(guessed-positive-pid, 0)
require_denied(109, 0, os.getsid(0))  # setpgid cannot rejoin supervisor group
require_denied(234, os.getpid(), os.getpid(), 0)  # tgkill
require_denied(434, os.getpid(), 0)  # pidfd_open
require_denied(424, -1, 0, 0, 0)  # pidfd_send_signal
read_fd, write_fd = os.pipe()
require_denied(72, read_fd, fcntl.F_SETOWN, os.getppid())
owner = ctypes.c_int(os.getppid())
require_denied(16, read_fd, 0x8901, ctypes.byref(owner))  # ioctl FIOSETOWN
require_denied(16, read_fd, 0x4008667C, ctypes.byref(owner))  # FIOSETOWN_EX
os.close(read_fd)
os.close(write_fd)
require_denied(302, 1, 7, 0, 0)  # prlimit64(PID 1, RLIMIT_NOFILE, ...)
require_denied(141, 0, 1, 0)  # setpriority(PRIO_PROCESS, PID 1, ...)
require_denied(203, 1, 0, 0)  # sched_setaffinity(PID 1, ...)
require_denied(142, 1, 0)  # sched_setparam(PID 1, ...)
require_denied(144, 1, 0, 0)  # sched_setscheduler(PID 1, ...)
require_denied(314, 1, 0, 0)  # sched_setattr(PID 1, ...)
require_denied(251, 1, 1, 0)  # ioprio_set(IOPRIO_WHO_PROCESS, PID 1, ...)
require_denied(256, 1, 0, 0, 0)  # migrate_pages(PID 1, ...)
require_denied(279, 1, 0, 0, 0, 0, 0)  # move_pages(PID 1, ...)
require_denied(90, b'/workspace/write-ok', 0o600)  # chmod
require_denied(188, b'/workspace/write-ok', b'user.highambench', b'x', 1, 0)
require_denied(280, -100, b'/workspace/write-ok', 0, 0)  # utimensat

ctypes.set_errno(0)
if libc.syscall(62, 0, 0) != 0:  # kill(0, 0) stays local to this process group.
    raise SystemExit(54)
open('/workspace/isolation-ok', 'w', encoding='utf-8').write(
    'signals-resources-scheduling-and-metadata-denied\\n'
)
PY
if exec 9<>/dev/tcp/127.0.0.1/9; then exit 47; fi
"""
        command = [
            str(deployment.bwrap_binary),
            "--unshare-all",
            "--share-net",
            "--die-with-parent",
            "--new-session",
            "--clearenv",
        ]
        command.extend(minimal_system_mount_args())
        command.extend(
            [
                "--proc",
                "/proc",
                "--dev",
                "/dev",
                "--tmpfs",
                "/tmp",
                "--dir",
                "/home",
                "--dir",
                "/home/bench",
                "--dir",
                "/control",
                "--bind",
                str(control),
                "/control/codex",
                "--bind",
                str(workspace),
                "/workspace",
                "--ro-bind",
                str(deployment.offline_shell),
                "/offline-bash",
                "--ro-bind",
                str(deployment.toolchain_root),
                "/lean",
                "--ro-bind",
                str(deployment.packages_root),
                "/packages",
            ]
        )
        lean_paths: list[str] = []
        if condition == "L":
            command.extend(
                [
                    "--dir",
                    "/library",
                    "--ro-bind",
                    str(deployment.library_source),
                    "/library/NumStability",
                    "--ro-bind",
                    str(deployment.library_source.parent / "NumStability.lean"),
                    "/library/NumStability.lean",
                    "--ro-bind",
                    str(deployment.library_olean),
                    "/library-olean",
                ]
            )
            lean_paths.append("/library-olean")
        for package in sorted(deployment.packages_root.iterdir(), key=lambda item: item.name):
            compiled = package / ".lake" / "build" / "lib" / "lean"
            if compiled.is_dir():
                lean_paths.append(f"/packages/{package.name}/.lake/build/lib/lean")
        lean_paths.extend(["/lean/lib/lean", "/workspace"])
        command.extend(
            [
                "--dir",
                "/run",
                "--dir",
                "/run/highambench",
                "--bind",
                str(marker),
                "/run/highambench/network-violations",
                "--setenv",
                "CODEX_HOME",
                "/control/codex",
                "--setenv",
                "HOME",
                "/home/bench",
                "--setenv",
                "PATH",
                "/lean/bin:/usr/bin",
                "--setenv",
                "LEAN_PATH",
                ":".join(lean_paths),
                "--setenv",
                "HIGHAMBENCH_NETWORK_VIOLATION_MARKER",
                "/run/highambench/network-violations",
                "--chdir",
                "/workspace",
                "/offline-bash",
                "-c",
                script,
            ]
        )
        completed = subprocess.run(
            command,
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            timeout=180,
            check=False,
        )
        checks = {
            "command_succeeded": completed.returncode == 0,
            "workspace_write_succeeded": _regular_file_equals(
                workspace / "write-ok", b"workspace-ok\n"
            ),
            "lean_compile_succeeded": _regular_file_present(
                workspace / "Canary.olean"
            ),
            "x32_syscalls_denied": _regular_file_equals(
                workspace / "x32-ok", b"x32-denied\n"
            ),
            "native_socket_syscall_denied": _regular_file_equals(
                workspace / "network-ok", b"socket-denied\n"
            ),
            "signal_and_metadata_syscalls_denied": _regular_file_equals(
                workspace / "isolation-ok",
                b"signals-resources-scheduling-and-metadata-denied\n",
            ),
            "control_auth_unchanged": _regular_file_equals(fake_auth, fake_secret),
            "control_config_absent": not os.path.lexists(control / "config.toml"),
            "special_workspace_nodes_denied": not os.path.lexists(
                workspace / "control-link"
            )
            and not os.path.lexists(workspace / "generated-fifo"),
            "network_attempt_marked": _regular_file_nonempty(marker),
        }
        if not all(checks.values()):
            raise BenchmarkError(
                f"condition {condition} command sandbox canary failed: {checks}; "
                f"returncode={completed.returncode}; output={completed.stdout[-2000:]}"
            )
        return {
            "condition": condition,
            "checks": checks,
            "returncode": completed.returncode,
            "output_sha256": sha256_bytes(completed.stdout.encode("utf-8")),
            "network_marker_sha256": sha256_file(marker),
        }


def _copy_frozen_source_pdfs(
    *,
    manifest: dict[str, Any],
    task_ids: list[str],
    source_pdf_root: Path,
    pdf_root: Path,
) -> None:
    """Copy each distinct frozen PDF once and reject basename/hash conflicts."""
    for task_id in task_ids:
        paper = task_record(manifest, task_id)["source_pdf"]
        source = source_pdf_root / paper["path_basename"]
        if (
            not source.is_file()
            or source.is_symlink()
            or sha256_file(source) != paper["sha256"]
        ):
            raise BenchmarkError(f"private PDF failed its frozen hash: {source}")
        destination = pdf_root / source.name
        if os.path.lexists(destination):
            if (
                destination.is_symlink()
                or not destination.is_file()
                or sha256_file(destination) != paper["sha256"]
            ):
                raise BenchmarkError(
                    f"duplicate PDF basename has conflicting content: {destination}"
                )
            continue
        shutil.copyfile(source, destination)
        destination.chmod(0o400)
        if sha256_file(destination) != paper["sha256"]:
            raise BenchmarkError(f"copied PDF failed verification: {destination}")


def _install_once(
    args: argparse.Namespace,
    deployment_root: Path,
    owned_root_identity: tuple[int, int],
    published_root: Path,
) -> Path:
    os.umask(0o077)
    assert_directory_identity(
        deployment_root, owned_root_identity, phase="installer entry"
    )
    manifest, config = verify_manifest()
    if sys.version_info < (3, 11):
        raise BenchmarkError("Titan requires Python 3.11 or newer")
    provisioning_environment = private_provisioning_environment(deployment_root)
    for name in (
        "git",
        "cc",
        "bwrap",
        "pdftotext",
        "elan",
        "lake",
        "systemd-run",
        "loginctl",
        "rg",
        "time",
    ):
        if name in {"elan", "lake"}:
            if shutil.which(name, path=provisioning_environment["PATH"]) is None:
                raise BenchmarkError(f"required Titan command is missing: {name}")
        else:
            command_path(name)
    if command_path("rg") != Path("/usr/bin/rg"):
        raise BenchmarkError("Titan requires ripgrep at /usr/bin/rg for the L sandbox")
    if command_path("time") != Path("/usr/bin/time"):
        raise BenchmarkError("Titan requires GNU time at /usr/bin/time")
    if "GNU Time" not in run(["/usr/bin/time", "--version"]):
        raise BenchmarkError("/usr/bin/time is not GNU time")
    linger = run(
        ["loginctl", "show-user", str(os.getuid()), "--property=Linger", "--value"]
    )
    if linger != "yes":
        raise BenchmarkError("Titan requires user-manager lingering for long benchmark runs")
    codex = Path(args.codex_binary).expanduser().resolve() if args.codex_binary else command_path("codex")
    code_mode_host = codex.with_name("codex-code-mode-host")
    if (
        code_mode_host.is_symlink()
        or not code_mode_host.is_file()
        or not os.access(code_mode_host, os.X_OK)
    ):
        raise BenchmarkError("matching Codex Code Mode host is missing or unsafe")
    code_mode_host_sha256 = sha256_file(code_mode_host)
    auth_file = Path(args.auth_file).expanduser().resolve()
    if not auth_file.is_file():
        raise BenchmarkError(f"Codex auth file is missing: {auth_file}")

    def published(path: Path) -> Path:
        return published_root / path.relative_to(deployment_root)
    release_commit = run(["git", "rev-parse", "HEAD"], cwd=REPOSITORY_ROOT)
    release_branch = run(["git", "branch", "--show-current"], cwd=REPOSITORY_ROOT)
    if release_branch != "formalization_benchmark":
        raise BenchmarkError(
            f"setup must run from formalization_benchmark, not {release_branch or 'detached HEAD'}"
        )
    if run(["git", "status", "--porcelain"], cwd=REPOSITORY_ROOT):
        raise BenchmarkError("setup refuses a dirty release checkout")
    base_commit = manifest.get("base_commit")
    if base_commit != EXPECTED_BASE_COMMIT:
        raise BenchmarkError("release manifest names an unexpected benchmark base")
    ancestry = subprocess.run(
        ["git", "merge-base", "--is-ancestor", base_commit, release_commit],
        cwd=REPOSITORY_ROOT,
        check=False,
    )
    if ancestry.returncode != 0:
        raise BenchmarkError("release branch is not descended from the frozen benchmark base")
    if config.get("pilot_id") != "formalization-benchmark-pilot-11":
        raise BenchmarkError("this installer requires the frozen pilot-11 identity")
    predecessor = pilot10_lineage(args.predecessor_deployment_root)
    pilot6_root = (
        Path.home() / ".local" / "share" / "highambench-formalization-pilot-6-r1"
    ).resolve()
    if published_root == pilot6_root:
        raise BenchmarkError("pilot-11 must not overwrite the pilot-6 deployment")
    if published_root == Path(predecessor["predecessor_run_root"]).parent:
        raise BenchmarkError("pilot-11 must not overwrite the pilot-10 deployment")
    if published_root == Path(predecessor["legacy_predecessor_run_root"]).parent:
        raise BenchmarkError("pilot-11 must not overwrite the pilot-9 deployment")
    if published_root == Path(predecessor["ancestral_predecessor_run_root"]).parent:
        raise BenchmarkError("pilot-11 must not overwrite the pilot-8 deployment")
    if published_root == Path(predecessor["great_ancestral_predecessor_run_root"]).parent:
        raise BenchmarkError("pilot-11 must not overwrite the pilot-7 deployment")
    if published_root == Path(predecessor["fifth_ancestral_predecessor_run_root"]).parent:
        raise BenchmarkError("pilot-11 must not overwrite the pilot-5 deployment")
    if published_root == Path(predecessor["sixth_ancestral_predecessor_run_root"]).parent:
        raise BenchmarkError("pilot-11 must not overwrite the pilot-4 deployment")
    if published_root == Path(predecessor["seventh_ancestral_predecessor_run_root"]).parent:
        raise BenchmarkError("pilot-11 must not overwrite the pilot-3 deployment")
    if published_root == Path(predecessor["eighth_ancestral_predecessor_run_root"]).parent:
        raise BenchmarkError("pilot-11 must not overwrite the pilot-2 deployment")
    if published_root == Path(predecessor["ninth_ancestral_predecessor_run_root"]).parent:
        raise BenchmarkError("pilot-11 must not overwrite the pilot-1 deployment")
    if GLOBAL_REGISTRY_ROOT.is_symlink() or (
        GLOBAL_REGISTRY_ROOT.exists() and not GLOBAL_REGISTRY_ROOT.is_dir()
    ):
        raise BenchmarkError("account-global benchmark registry path is unsafe")

    release_root = deployment_root / "release"
    run(
        [
            "git",
            "clone",
            "--no-hardlinks",
            "--no-checkout",
            str(REPOSITORY_ROOT),
            str(release_root),
        ]
    )
    run(["git", "checkout", "--detach", release_commit], cwd=release_root)
    if run(["git", "rev-parse", "HEAD"], cwd=release_root) != release_commit:
        raise BenchmarkError("frozen release checkout resolved to the wrong commit")
    if run(["git", "status", "--porcelain", "--untracked-files=all"], cwd=release_root):
        raise BenchmarkError("frozen release checkout is not clean")
    assert_directory_identity(
        deployment_root, owned_root_identity, phase="release checkout"
    )
    shutil.rmtree(release_root / ".git")
    if any(release_root.rglob("*.pyc")) or any(
        path.name == "__pycache__" for path in release_root.rglob("*")
    ):
        raise BenchmarkError("frozen release unexpectedly contains Python bytecode")
    frozen_benchmark_root = release_root / "paper_bencmark" / "formalization_benchmark"
    frozen_runner = frozen_benchmark_root / "tools" / "titan_envelope.py"
    if not frozen_runner.is_file():
        raise BenchmarkError("frozen release is missing the benchmark runner")
    pdf_root = deployment_root / "private" / "pdfs"
    pdf_root.mkdir(parents=True, exist_ok=True, mode=0o700)
    private_auth_file = deployment_root / "private" / "codex-auth.json"
    write_bytes_atomic(
        private_auth_file,
        stable_regular_bytes(auth_file, maximum_bytes=4 * 1024 * 1024),
        mode=0o600,
    )
    source_pdf_root = Path(args.pdf_source_dir).expanduser().resolve()
    _copy_frozen_source_pdfs(
        manifest=manifest,
        task_ids=config["task_ids"],
        source_pdf_root=source_pdf_root,
        pdf_root=pdf_root,
    )

    common_project = deployment_root / "runtime" / "common-project"
    common_project.mkdir(parents=True, exist_ok=True)
    for name in ("lakefile.toml", "lake-manifest.json", "lean-toolchain"):
        shutil.copyfile(release_root / name, common_project / name)
    run(["elan", "toolchain", "install", FROZEN_TOOLCHAIN], env=provisioning_environment)
    toolchain_root = find_toolchain_root(
        cwd=common_project, env=provisioning_environment
    )
    run(["lake", "update"], cwd=common_project, env=provisioning_environment)
    run(["lake", "exe", "cache", "get"], cwd=common_project, env=provisioning_environment)
    packages_root = common_project / ".lake" / "packages"
    if not (packages_root / "mathlib" / ".lake" / "build" / "lib" / "lean").is_dir():
        raise BenchmarkError("Mathlib compiled cache was not prepared")

    runtime_record = {
        "schema_version": "formalization-runtime-snapshot-1",
        "created_at_utc": utc_now(),
        "lean_toolchain": FROZEN_TOOLCHAIN,
        "mathlib_commit": config["mathlib_commit"],
        "toolchain": tree_manifest(toolchain_root),
        "packages": tree_manifest(packages_root),
        "condition_n_treatment_absence": treatment_free_runtime_manifest(
            {"packages": packages_root, "toolchain": toolchain_root}
        ),
    }
    runtime_record_path = deployment_root / "runtime" / "snapshot.json"
    write_json_atomic(runtime_record_path, runtime_record, mode=0o400)

    library_root = deployment_root / "runtime" / "library"
    with tempfile.TemporaryDirectory(
        prefix="highambench-library-",
        dir=provisioning_environment["TMPDIR"],
    ) as temporary:
        checkout = Path(temporary) / "checkout"
        run(["git", "clone", "--no-checkout", str(REPOSITORY_ROOT), str(checkout)])
        run(["git", "checkout", "--detach", FROZEN_LIBRARY_COMMIT], cwd=checkout)
        actual_commit = run(["git", "rev-parse", "HEAD"], cwd=checkout)
        if actual_commit != FROZEN_LIBRARY_COMMIT:
            raise BenchmarkError("NumStability checkout resolved to the wrong commit")
        run(["lake", "update"], cwd=checkout, env=provisioning_environment)
        run(["lake", "exe", "cache", "get"], cwd=checkout, env=provisioning_environment)
        build_root = library_root / "build"
        build_runner = frozen_benchmark_root / "tools" / "measure_library_build.py"
        if not build_runner.is_file() or build_runner.is_symlink():
            raise BenchmarkError("frozen release is missing the library build measurer")
        build_service_environment = measured_build_service_environment(deployment_root)
        run(
            measured_build_command(
                systemd_run=command_path("systemd-run"),
                build_runner=build_runner,
                checkout=checkout,
                artifact_root=build_root,
                toolchain_root=toolchain_root,
                expected_commit=FROZEN_LIBRARY_COMMIT,
                mathlib_commit=str(config["mathlib_commit"]),
                lean_toolchain=FROZEN_TOOLCHAIN,
                service_environment=build_service_environment,
            ),
            cwd=checkout,
        )
        build_record_path = build_root / "build-record.json"
        if not build_record_path.is_file() or build_record_path.is_symlink():
            raise BenchmarkError("measured NumStability build record is missing")
        try:
            build_record = json.loads(
                stable_regular_bytes(build_record_path).decode("utf-8")
            )
        except (UnicodeDecodeError, json.JSONDecodeError) as error:
            raise BenchmarkError("measured NumStability build record is malformed") from error
        if not isinstance(build_record, dict):
            raise BenchmarkError("measured NumStability build record is not an object")
        validate_build_record(
            build_record,
            expected_source_commit=FROZEN_LIBRARY_COMMIT,
            expected_mathlib_commit=str(config["mathlib_commit"]),
            expected_toolchain=FROZEN_TOOLCHAIN,
            expected_tool_hashes={
                "lake_sha256": sha256_file(toolchain_root / "bin" / "lake"),
                "lean_sha256": sha256_file(toolchain_root / "bin" / "lean"),
                "gnu_time_sha256": sha256_file(Path("/usr/bin/time")),
            },
        )
        generated_root = checkout / ".lake" / "build" / "lib" / "lean"
        expected_generated_tree = {"present": True, **file_tree_fingerprint(generated_root)}
        if build_record.get("generated_output_tree") != expected_generated_tree:
            raise BenchmarkError("measured NumStability build output digest changed")
        expected_generated_olean = {
            "present": True,
            **file_tree_fingerprint(generated_root, suffix=".olean"),
        }
        if build_record.get("generated_olean") != expected_generated_olean:
            raise BenchmarkError("measured NumStability OLean inventory changed")
        source_root = library_root / "source"
        olean_root = library_root / "olean"
        copy_tree_read_only(checkout / "NumStability", source_root / "NumStability")
        shutil.copyfile(checkout / "NumStability.lean", source_root / "NumStability.lean")
        (source_root / "NumStability.lean").chmod(0o400)
        copy_tree_read_only(checkout / ".lake" / "build" / "lib" / "lean", olean_root)
        published_generated_tree = {"present": True, **file_tree_fingerprint(olean_root)}
        if build_record.get("generated_output_tree") != published_generated_tree:
            raise BenchmarkError("published NumStability build output changed during copy")
        published_generated_olean = {
            "present": True,
            **file_tree_fingerprint(olean_root, suffix=".olean"),
        }
        if build_record.get("generated_olean") != published_generated_olean:
            raise BenchmarkError("published NumStability OLean inventory changed during copy")

    make_tree_read_only(library_root / "build")

    library_record = {
        "schema_version": "numstability-formalization-snapshot-1",
        "commit": FROZEN_LIBRARY_COMMIT,
        "created_at_utc": utc_now(),
        "source": tree_manifest(library_root / "source"),
        "olean": tree_manifest(library_root / "olean"),
        "build": tree_manifest(library_root / "build"),
    }
    library_record_path = library_root / "snapshot.json"
    write_json_atomic(library_record_path, library_record, mode=0o400)

    offline_shell = deployment_root / "bin" / "offline-shell"
    offline_shell.parent.mkdir(parents=True, exist_ok=True)
    run(
        [
            str(command_path("cc")),
            "-std=c11",
            "-O2",
            "-Wall",
            "-Wextra",
            "-Werror",
            "-o",
            str(offline_shell),
            str(
                release_root
                / "paper_bencmark"
                / "highambench"
                / "tools"
                / "offline_shell.c"
            ),
        ]
    )
    offline_shell.chmod(0o500)

    visible_system_runtime_path = deployment_root / "runtime" / "visible-system.json"
    write_json_atomic(
        visible_system_runtime_path,
        visible_system_runtime_manifest(),
        mode=0o400,
    )

    deployment_record = deployment_root / "deployment.json"
    run_root = deployment_root / "runs"
    run_root.mkdir(parents=True, exist_ok=True, mode=0o700)
    record = {
        "schema_version": "formalization-deployment-1",
        "created_at_utc": utc_now(),
        "pilot_id": config["pilot_id"],
        "release_commit": release_commit,
        "release_branch": release_branch,
        "release_root": str(published(release_root)),
        "release_manifest_sha256": sha256_file(frozen_benchmark_root / "manifest.json"),
        "manifest_payload_sha256": manifest["manifest_payload_sha256"],
        "global_registry_root": str(GLOBAL_REGISTRY_ROOT),
        **predecessor,
        "run_root": str(published(run_root)),
        "pdf_root": str(published(pdf_root)),
        "codex_binary": str(codex),
        "codex_binary_sha256": sha256_file(codex),
        "codex_version": run([str(codex), "--version"]),
        "code_mode_host_binary": str(code_mode_host),
        "code_mode_host_sha256": code_mode_host_sha256,
        "auth_file": str(published(private_auth_file)),
        "bwrap_binary": str(command_path("bwrap")),
        "offline_shell": str(published(offline_shell)),
        "toolchain_root": str(toolchain_root),
        "packages_root": str(published(packages_root)),
        "library_source": str(published(library_root / "source" / "NumStability")),
        "library_olean": str(published(library_root / "olean")),
        "library_snapshot_record": str(published(library_record_path)),
        "library_snapshot_record_sha256": sha256_file(library_record_path),
        "library_build_record": str(published(library_root / "build" / "build-record.json")),
        "library_build_record_sha256": sha256_file(
            library_root / "build" / "build-record.json"
        ),
        "runtime_snapshot_record": str(published(runtime_record_path)),
        "runtime_snapshot_record_sha256": sha256_file(runtime_record_path),
        "visible_system_runtime_record": str(published(visible_system_runtime_path)),
        "visible_system_runtime_record_sha256": sha256_file(
            visible_system_runtime_path
        ),
        "bwrap_binary_sha256": sha256_file(command_path("bwrap")),
        "offline_shell_sha256": sha256_file(offline_shell),
        "hardware_identity": frozen_hardware_identity(
            snapshot_hardware(strict=False), affinity_cpus=host_cpu_selection()
        ),
        "strict_hardware": True,
    }
    deployed = Deployment(
        path=deployment_record,
        run_root=run_root,
        pdf_root=pdf_root,
        codex_binary=codex,
        code_mode_host_sha256=code_mode_host_sha256,
        auth_file=private_auth_file,
        bwrap_binary=command_path("bwrap"),
        offline_shell=offline_shell,
        toolchain_root=toolchain_root,
        packages_root=packages_root,
        library_source=library_root / "source" / "NumStability",
        library_olean=library_root / "olean",
        library_snapshot_record=library_record_path,
        runtime_snapshot_record=runtime_record_path,
        strict_hardware=True,
        pilot_id=config["pilot_id"],
        release_commit=release_commit,
        release_manifest_sha256=sha256_file(frozen_benchmark_root / "manifest.json"),
        manifest_payload_sha256=manifest["manifest_payload_sha256"],
        global_registry_root=GLOBAL_REGISTRY_ROOT,
        predecessor_run_root=Path(predecessor["predecessor_run_root"]),
        legacy_predecessor_run_root=Path(predecessor["legacy_predecessor_run_root"]),
        ancestral_predecessor_run_root=Path(predecessor["ancestral_predecessor_run_root"]),
        great_ancestral_predecessor_run_root=Path(
            predecessor["great_ancestral_predecessor_run_root"]
        ),
        fifth_ancestral_predecessor_run_root=Path(
            predecessor["fifth_ancestral_predecessor_run_root"]
        ),
        sixth_ancestral_predecessor_run_root=Path(
            predecessor["sixth_ancestral_predecessor_run_root"]
        ),
        seventh_ancestral_predecessor_run_root=Path(
            predecessor["seventh_ancestral_predecessor_run_root"]
        ),
        eighth_ancestral_predecessor_run_root=Path(
            predecessor["eighth_ancestral_predecessor_run_root"]
        ),
        ninth_ancestral_predecessor_run_root=Path(
            predecessor["ninth_ancestral_predecessor_run_root"]
        ),
    )
    command_canary = {
        "schema_version": "formalization-command-sandbox-canary-1",
        "provider_calls": 0,
        "conditions": [
            run_command_sandbox_canary(deployed, "N"),
            run_command_sandbox_canary(deployed, "L"),
        ],
    }
    command_canary_path = deployment_root / "command-sandbox-canary.json"
    write_json_atomic(command_canary_path, command_canary, mode=0o400)
    canary = run_runtime_canaries(deployed)
    canary_path = deployment_root / "runtime-canary.json"
    write_json_atomic(canary_path, canary, mode=0o400)
    codex_preflight: dict[str, Any] = {
        "schema_version": "formalization-codex-model-preflights-1",
        "provider_calls": 0,
        "roles": {},
    }
    for role, model_key, effort_key, writable in (
        (
            "formalizer",
            "formalizer_model",
            "formalizer_reasoning_effort",
            True,
        ),
        ("auditor", "audit_model", "audit_reasoning_effort", False),
    ):
        with tempfile.TemporaryDirectory(
            prefix=f"formalization-codex-{role}-preflight-", dir=deployment_root
        ) as temporary:
            preflight_root = Path(temporary)
            preflight_workspace = preflight_root / "workspace"
            preflight_workspace.mkdir()
            preflight_driver = CodexDriver(
                codex_binary=codex,
                code_mode_host_sha256=code_mode_host_sha256,
                model=str(config[model_key]),
                reasoning_effort=str(config[effort_key]),
                state_root=None,
                auth_file=private_auth_file,
                bwrap_binary=deployed.bwrap_binary,
                offline_shell=offline_shell,
                toolchain_root=toolchain_root,
                packages_root=packages_root,
                workspace_writable=writable,
            )
            try:
                role_record = preflight_driver.preflight(
                    workspace=preflight_workspace,
                    artifact_dir=preflight_root / "artifacts",
                    timeout_seconds=60,
                )
            finally:
                preflight_driver.close()
            if role_record.get("provider_call_permitted") is not False:
                raise BenchmarkError(f"{role} compatibility preflight was not provider-free")
            codex_preflight["roles"][role] = role_record
    codex_preflight_path = deployment_root / "codex-preflight.json"
    write_json_atomic(codex_preflight_path, codex_preflight, mode=0o400)
    record.update(
        {
            "runtime_canary_record": str(published(canary_path)),
            "runtime_canary_record_sha256": sha256_file(canary_path),
            "command_sandbox_canary_record": str(published(command_canary_path)),
            "command_sandbox_canary_record_sha256": sha256_file(
                command_canary_path
            ),
            "codex_preflight_record": str(published(codex_preflight_path)),
            "codex_preflight_record_sha256": sha256_file(codex_preflight_path),
        }
    )
    verify_predecessor_lineage(args.predecessor_deployment_root, record)
    write_json_atomic(deployment_record, record, mode=0o600)
    assert_directory_identity(
        deployment_root, owned_root_identity, phase="deployment record publication"
    )
    deployment_record.chmod(0o400)
    deployment_record_sha256 = sha256_file(deployment_record)
    make_tree_read_only(release_root)
    assert_directory_identity(
        deployment_root, owned_root_identity, phase="staged deployment completion"
    )
    if deployment_record_sha256 != sha256_file(deployment_record):
        raise BenchmarkError("staged deployment record changed before publication")
    return deployment_record


INSTALL_TRANSACTION = "install-transaction.json"
INSTALL_TRANSACTION_SCHEMA = "formalization-install-transaction-1"


def _transaction_record(
    *,
    status: str,
    deployment_root: Path,
    launcher: Path,
    deployment_record_sha256: str | None = None,
) -> dict[str, Any]:
    record: dict[str, Any] = {
        "schema_version": INSTALL_TRANSACTION_SCHEMA,
        "status": status,
        "deployment_root": str(deployment_root),
        "launcher": str(launcher),
        "release_manifest_sha256": sha256_file(ROOT / "manifest.json"),
        "updated_at_utc": utc_now(),
    }
    if deployment_record_sha256 is not None:
        record["deployment_record_sha256"] = deployment_record_sha256
    return record


def _load_transaction(
    root: Path, *, deployment_root: Path, launcher: Path
) -> dict[str, Any]:
    path = root / INSTALL_TRANSACTION
    if not path.is_file() or path.is_symlink():
        raise BenchmarkError("deployment has no safe installation transaction record")
    try:
        record = json.loads(stable_regular_bytes(path).decode("utf-8"))
    except (UnicodeDecodeError, json.JSONDecodeError) as error:
        raise BenchmarkError("deployment installation transaction is malformed") from error
    if (
        not isinstance(record, dict)
        or record.get("schema_version") != INSTALL_TRANSACTION_SCHEMA
        or Path(str(record.get("deployment_root", ""))).resolve() != deployment_root
        or Path(str(record.get("launcher", ""))).resolve() != launcher
        or record.get("release_manifest_sha256")
        != sha256_file(ROOT / "manifest.json")
        or record.get("status")
        not in {"BUILDING", "READY_TO_PUBLISH", "FINALIZING", "COMPLETE"}
    ):
        raise BenchmarkError("deployment installation transaction is malformed")
    return record


def _finalize_install(
    args: argparse.Namespace, deployment_root: Path, launcher: Path
) -> Path:
    transaction_path = deployment_root / INSTALL_TRANSACTION
    transaction = _load_transaction(
        deployment_root, deployment_root=deployment_root, launcher=launcher
    )
    if transaction["status"] == "COMPLETE":
        raise BenchmarkError("formalization benchmark is already installed")
    if transaction["status"] not in {"READY_TO_PUBLISH", "FINALIZING"}:
        raise BenchmarkError("deployment is not ready for installation finalization")
    deployment_record = deployment_root / "deployment.json"
    expected_deployment_hash = transaction.get("deployment_record_sha256")
    if (
        not isinstance(expected_deployment_hash, str)
        or len(expected_deployment_hash) != 64
        or not deployment_record.is_file()
        or deployment_record.is_symlink()
        or sha256_file(deployment_record) != expected_deployment_hash
    ):
        raise BenchmarkError("published deployment record failed authentication")
    verify_predecessor_lineage(
        args.predecessor_deployment_root, load_json(deployment_record)
    )
    transaction["status"] = "FINALIZING"
    transaction["updated_at_utc"] = utc_now()
    write_json_atomic(transaction_path, transaction, mode=0o600)

    frozen_runner = (
        deployment_root
        / "release"
        / "paper_bencmark"
        / "formalization_benchmark"
        / "tools"
        / "titan_envelope.py"
    )
    if not frozen_runner.is_file() or frozen_runner.is_symlink():
        raise BenchmarkError("published deployment is missing its frozen runner")
    environment = os.environ.copy()
    environment["HIGHAMBENCH_FORMALIZATION_DEPLOYMENT"] = str(deployment_record)
    environment["HIGHAMBENCH_FORMALIZATION_DEPLOYMENT_SHA256"] = (
        expected_deployment_hash
    )
    completed = run_bounded_command(
        isolated_runner_command(
            frozen_runner,
            "doctor",
            "--task-id",
            "P01-T2",
        ),
        cwd=deployment_root,
        environment=environment,
        timeout_seconds=1800,
        maximum_output_bytes=8 * 1024 * 1024,
    )
    doctor_output = completed["output"].encode("utf-8")
    if completed["timed_out"]:
        raise BenchmarkError("post-install doctor exceeded 1800 seconds")
    if completed["output_limit_exceeded"]:
        raise BenchmarkError("post-install doctor output exceeded 8 MiB")
    if completed["returncode"] != 0:
        rendered = doctor_output[-8000:].decode("utf-8", errors="replace")
        raise BenchmarkError(f"post-install doctor failed:\n{rendered}")
    write_bytes_atomic(
        deployment_root / "last-doctor.json", doctor_output, mode=0o400
    )

    expected_launcher = launcher_bytes(
        deployment_record, expected_deployment_hash, frozen_runner
    )
    if launcher.exists() or launcher.is_symlink():
        if (
            launcher.is_symlink()
            or not launcher.is_file()
            or stable_regular_bytes(launcher) != expected_launcher
        ):
            raise BenchmarkError("existing launcher does not match pending deployment")
    else:
        write_launcher(
            launcher, deployment_record, expected_deployment_hash, frozen_runner
        )

    skill_source = (
        deployment_root
        / "release"
        / ".codex"
        / "skills"
        / "run-highambench-experiments"
    )
    skill_destination = (
        Path.home() / ".codex" / "skills" / "run-highambench-experiments"
    )
    install_skill_atomically(skill_source, skill_destination)
    transaction["status"] = "COMPLETE"
    transaction["completed_at_utc"] = utc_now()
    transaction["updated_at_utc"] = transaction["completed_at_utc"]
    write_json_atomic(transaction_path, transaction, mode=0o400)
    return deployment_record


def install(args: argparse.Namespace) -> Path:
    """Build beside the canonical root, atomically publish, and resume safely."""

    requested_root = Path(args.deployment_root).expanduser()
    if requested_root.is_symlink():
        raise BenchmarkError("deployment root may not be a symlink")
    deployment_root = requested_root.resolve()
    launcher = Path(args.launcher).expanduser().resolve()
    deployment_root.parent.mkdir(parents=True, exist_ok=True, mode=0o700)

    if os.path.lexists(deployment_root):
        if deployment_root.is_symlink() or not deployment_root.is_dir():
            raise BenchmarkError("deployment root exists and is unsafe")
        return _finalize_install(args, deployment_root, launcher)

    staging_prefix = f".{deployment_root.name}.install-"
    ready_staging: Path | None = None
    for candidate in sorted(deployment_root.parent.glob(staging_prefix + "*")):
        if candidate.is_symlink() or not candidate.is_dir():
            raise BenchmarkError(f"unsafe abandoned deployment transaction: {candidate}")
        try:
            transaction = _load_transaction(
                candidate, deployment_root=deployment_root, launcher=launcher
            )
        except (BenchmarkError, OSError, json.JSONDecodeError):
            abandoned = deployment_root.parent / (
                f".{deployment_root.name}.abandoned-{os.urandom(8).hex()}"
            )
            os.rename(candidate, abandoned)
            fsync_directory(deployment_root.parent)
            continue
        if transaction["status"] == "READY_TO_PUBLISH":
            if ready_staging is not None:
                raise BenchmarkError("multiple ready deployment transactions exist")
            ready_staging = candidate
        else:
            abandoned = deployment_root.parent / (
                f".{deployment_root.name}.abandoned-{os.urandom(8).hex()}"
            )
            os.rename(candidate, abandoned)
            fsync_directory(deployment_root.parent)
    if ready_staging is not None:
        os.rename(ready_staging, deployment_root)
        fsync_directory(deployment_root.parent)
        return _finalize_install(args, deployment_root, launcher)

    if launcher.exists() or launcher.is_symlink():
        raise BenchmarkError(
            "launcher exists without a resumable deployment; refusing to overwrite it"
        )
    staging_root = Path(
        tempfile.mkdtemp(prefix=staging_prefix, dir=str(deployment_root.parent))
    )
    os.chmod(staging_root, 0o700)
    owned_root_identity = directory_identity(staging_root)
    write_json_atomic(
        staging_root / INSTALL_TRANSACTION,
        _transaction_record(
            status="BUILDING",
            deployment_root=deployment_root,
            launcher=launcher,
        ),
        mode=0o600,
    )
    try:
        staged_record = _install_once(
            args,
            staging_root,
            owned_root_identity,
            deployment_root,
        )
        deployment_hash = sha256_file(staged_record)
        write_json_atomic(
            staging_root / INSTALL_TRANSACTION,
            _transaction_record(
                status="READY_TO_PUBLISH",
                deployment_root=deployment_root,
                launcher=launcher,
                deployment_record_sha256=deployment_hash,
            ),
            mode=0o600,
        )
        assert_directory_identity(
            staging_root, owned_root_identity, phase="atomic publication"
        )
        os.rename(staging_root, deployment_root)
        fsync_directory(deployment_root.parent)
        return _finalize_install(args, deployment_root, launcher)
    except BaseException as install_error:
        # Before publication, remove only the inode created by this invocation.
        # After publication, retain the authenticated FINALIZING transaction so
        # the next invocation can complete it without rebuilding.
        if os.path.lexists(staging_root):
            try:
                remove_owned_deployment_root(staging_root, owned_root_identity)
            except BaseException as cleanup_error:
                raise BenchmarkError(
                    "setup failed and staging cleanup could not be authenticated: "
                    f"{cleanup_error}"
                ) from install_error
        raise


def make_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--pdf-source-dir", required=True)
    parser.add_argument(
        "--deployment-root",
        default=str(Path.home() / ".local" / "share" / "highambench-formalization-pilot-11-r1"),
    )
    parser.add_argument(
        "--predecessor-deployment-root",
        required=True,
        help="read-only path to sealed pilot-10 deployment and its nine-release lineage",
    )
    parser.add_argument("--auth-file", default=str(Path.home() / ".codex" / "auth.json"))
    parser.add_argument("--codex-binary")
    parser.add_argument(
        "--launcher", default=str(Path.home() / ".local" / "bin" / "run-highambench-formalization-pilot-11-r1")
    )
    return parser


if __name__ == "__main__":
    try:
        output = install(make_parser().parse_args())
    except (BenchmarkError, OSError, subprocess.SubprocessError) as error:
        print(f"Titan setup error: {error}", file=sys.stderr)
        raise SystemExit(2)
    print(output)
