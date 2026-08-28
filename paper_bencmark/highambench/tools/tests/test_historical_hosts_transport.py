from __future__ import annotations

import copy
import unittest

from paper_bencmark.highambench.tools import render_p01_report
from paper_bencmark.highambench.tools import render_report
from paper_bencmark.highambench.tools import run_matrix
from paper_bencmark.highambench.tools import runner


class HistoricalHostsTransportTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.current = runner.authenticate_provider_transport_provenance(
            ["/usr/bin/python3.10"]
        )

    def historical(self, marker: str, byte_delta: int) -> dict:
        transport = copy.deepcopy(self.current)
        hosts = transport["resolver"]["hosts_file"]
        hosts["sha256"] = marker * 64
        hosts["bytes"] = int(hosts["bytes"]) + byte_delta
        return transport

    def test_two_historical_nodes_are_accepted_against_their_own_snapshots(self) -> None:
        for marker, delta in (("a", 1), ("b", 2)):
            transport = self.historical(marker, delta)
            snapshot = copy.deepcopy(transport["resolver"]["hosts_file"])
            checked = render_report._gate_transport(
                transport,
                f"job-{marker}",
                authenticated_historical_hosts_file=snapshot,
            )
            self.assertEqual(checked, transport)

    def test_historical_snapshot_is_opt_in(self) -> None:
        transport = self.historical("a", 1)
        with self.assertRaisesRegex(
            render_report.ReportError, "hosts_file.*no longer matches"
        ):
            render_report._gate_transport(transport, "strict-current")

    def test_gate_hosts_must_equal_authenticated_freeze_snapshot(self) -> None:
        transport = self.historical("a", 1)
        other = copy.deepcopy(transport["resolver"]["hosts_file"])
        other["sha256"] = "b" * 64
        with self.assertRaisesRegex(
            render_report.ReportError, "authenticated historical snapshot"
        ):
            render_report._gate_transport(
                transport,
                "tampered-gate",
                authenticated_historical_hosts_file=other,
            )

    def test_historical_exception_is_only_for_fixed_regular_etc_hosts(self) -> None:
        for field, value, message in (
            ("logical_path", "/tmp/hosts", "fixed regular node-local hosts"),
            ("resolved_path", "/tmp/hosts", "fixed regular node-local hosts"),
            ("symlink_target", "hosts.real", "fixed regular node-local hosts"),
        ):
            transport = self.historical("a", 1)
            transport["resolver"]["hosts_file"][field] = value
            snapshot = copy.deepcopy(transport["resolver"]["hosts_file"])
            with self.assertRaisesRegex(render_report.ReportError, message):
                render_report._gate_transport(
                    transport,
                    f"bad-{field}",
                    authenticated_historical_hosts_file=snapshot,
                )

    def test_non_hosts_dependency_still_requires_live_bytes(self) -> None:
        transport = self.historical("a", 1)
        transport["resolver"]["resolv_conf"]["sha256"] = "c" * 64
        with self.assertRaisesRegex(
            render_report.ReportError, "resolv_conf.*no longer matches"
        ):
            render_report._gate_transport(
                transport,
                "non-host-tamper",
                authenticated_historical_hosts_file=transport["resolver"]["hosts_file"],
            )

    def test_p01_helper_requires_exact_pair_policy_and_freeze_transport(self) -> None:
        transport = self.historical("a", 1)
        freeze = {
            "hardware_matching_policy": copy.deepcopy(
                run_matrix.HARDWARE_MATCHING_POLICY
            ),
            "provider_token_gate": {"transport_provenance": transport},
        }
        self.assertEqual(
            render_p01_report._authenticated_historical_hosts_file(
                freeze, "pair freeze"
            ),
            transport["resolver"]["hosts_file"],
        )
        freeze["hardware_matching_policy"]["scope"] = "cross_pair"
        with self.assertRaisesRegex(
            render_p01_report.ReportError, "unknown paired-hardware policy"
        ):
            render_p01_report._authenticated_historical_hosts_file(
                freeze, "tampered pair freeze"
            )


if __name__ == "__main__":
    unittest.main()
