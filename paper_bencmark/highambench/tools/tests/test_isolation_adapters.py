from __future__ import annotations

import argparse
import os
from pathlib import Path
import platform
import shlex
import shutil
import subprocess
import sys
import tempfile
import unittest


TOOLS = Path(__file__).resolve().parents[1]
if str(TOOLS) not in sys.path:
    sys.path.insert(0, str(TOOLS))

from codex_isolated import (  # noqa: E402
    NETWORK_VIOLATION_MARKER_ENV,
    bubblewrap_command,
    build_prompt,
    normalized_usage,
    positive_int,
)
from lean_isolated import namespace_prefix  # noqa: E402


def mounts(command: list[str]) -> list[tuple[str, str, str, int]]:
    result: list[tuple[str, str, str, int]] = []
    for index, item in enumerate(command):
        if item in ("--bind", "--ro-bind"):
            result.append((item, command[index + 1], command[index + 2], index))
    return result


def setenv_value(command: list[str], name: str) -> str:
    for index, item in enumerate(command):
        if item == "--setenv" and command[index + 1] == name:
            return command[index + 2]
    raise AssertionError(f"missing --setenv {name}")


class IsolationAdapterTests(unittest.TestCase):
    def setUp(self) -> None:
        self.temporary = tempfile.TemporaryDirectory()
        self.root = Path(self.temporary.name)
        self.workspace = self.root / "workspace"
        self.workspace.mkdir()
        (self.workspace / "task" / "shared").mkdir(parents=True)
        self.state_home = self.root / "state-home"
        self.state_home.mkdir()
        self.toolchain = self.root / "toolchain"
        self.toolchain.mkdir()
        self.packages = self.root / "packages"
        (self.packages / "mathlib" / ".lake" / "build" / "lib" / "lean").mkdir(
            parents=True
        )
        (self.packages / "batteries" / ".lake" / "build" / "lib" / "lean").mkdir(
            parents=True
        )
        self.shared_olean = self.root / "shared-olean"
        self.shared_olean.mkdir()
        self.library_source = self.root / "library-source"
        self.library_source.mkdir()
        self.library_olean = self.root / "library-olean"
        self.library_olean.mkdir()
        self.library_root = self.root / "NumStability.lean"
        self.library_root.write_text("import NumStability.Basic\n", encoding="utf-8")
        self.resolver = self.root / "resolver"
        self.resolver.mkdir()
        self.codex = self.root / "codex"
        self.codex.write_text("binary", encoding="utf-8")
        self.offline_shell = self.root / "offline-shell"
        self.offline_shell.write_text("binary", encoding="utf-8")
        self.network_marker = self.workspace / ".network-marker"
        self.network_marker.write_bytes(b"")
        self.bwrap = self.root / "bwrap"
        self.bwrap.write_text("binary", encoding="utf-8")

    def tearDown(self) -> None:
        self.temporary.cleanup()

    def codex_args(self, condition: str) -> argparse.Namespace:
        return argparse.Namespace(
            bwrap=self.bwrap,
            resolver_root=self.resolver,
            inside_home="/u501/tester",
            workspace=self.workspace,
            controlled_relative="task",
            codex=self.codex,
            offline_shell=self.offline_shell,
            toolchain_root=self.toolchain,
            packages_root=self.packages,
            shared_olean_root=self.shared_olean,
            shared_root_relative="task/shared",
            condition=condition,
            library_source=self.library_source if condition == "L" else None,
            library_root_file=self.library_root if condition == "L" else None,
            library_olean=self.library_olean if condition == "L" else None,
            model="test-model",
            reasoning_effort="medium",
            token_limit=1234,
            network_violation_marker=self.network_marker,
        )

    def lean_args(self, condition: str) -> argparse.Namespace:
        return argparse.Namespace(
            bwrap=self.bwrap,
            workspace=self.workspace,
            toolchain_root=self.toolchain,
            packages_root=self.packages,
            shared_olean_root=self.shared_olean,
            shared_root_relative="task/shared",
            condition=condition,
            library_source=self.library_source if condition == "L" else None,
            library_root_file=self.library_root if condition == "L" else None,
            library_olean=self.library_olean if condition == "L" else None,
        )

    def test_prompt_construction_has_fixed_sections_and_one_final_newline(self) -> None:
        prompt_file = self.root / "prompt.md"
        context_file = self.root / "context.md"
        target_file = self.root / "Target.lean"
        prompt_file.write_text("Instructions.\n\n", encoding="utf-8")
        context_file.write_text("Paper context.   \n", encoding="utf-8")
        target_file.write_text("theorem fixed : True := by\n  sorry\n\n", encoding="utf-8")
        self.assertEqual(
            build_prompt(prompt_file, context_file, target_file),
            "Instructions.\n\n"
            "## Task context\n\nPaper context.\n\n"
            "## Fixed Lean target\n\n```lean\n"
            "theorem fixed : True := by\n  sorry\n```\n",
        )

    def test_usage_parser_accepts_only_exact_nonnegative_integer_fields(self) -> None:
        self.assertEqual(
            normalized_usage(
                {
                    "type": "turn.completed",
                    "usage": {
                        "input_tokens": 10,
                        "cached_input_tokens": 4,
                        "output_tokens": 3,
                        "ignored": 99,
                    },
                }
            ),
            {"input_tokens": 10, "cached_input_tokens": 4, "output_tokens": 3},
        )
        self.assertIsNone(normalized_usage({"type": "item.completed", "usage": {}}))
        self.assertIsNone(
            normalized_usage(
                {
                    "type": "turn.completed",
                    "usage": {
                        "input_tokens": True,
                        "cached_input_tokens": 0,
                        "output_tokens": 1,
                    },
                }
            )
        )
        self.assertIsNone(
            normalized_usage(
                {
                    "type": "turn.completed",
                    "usage": {
                        "input_tokens": 1,
                        "cached_input_tokens": -1,
                        "output_tokens": 1,
                    },
                }
            )
        )

    def test_codex_n_and_l_mounts_are_separate_and_controlled_tree_is_read_only(self) -> None:
        n_args = self.codex_args("N")
        # Even accidental L-only arguments must not leak into condition N.
        n_args.library_source = self.library_source
        n_args.library_root_file = self.library_root
        n_args.library_olean = self.library_olean
        n_command = bubblewrap_command(n_args, self.state_home)
        l_command = bubblewrap_command(self.codex_args("L"), self.state_home)
        n_mounts = mounts(n_command)
        l_mounts = mounts(l_command)

        workspace_bind = next(
            mount for mount in n_mounts if mount[2] == "/workspace"
        )
        controlled_bind = next(
            mount for mount in n_mounts if mount[2] == "/workspace/task"
        )
        self.assertEqual(workspace_bind[0], "--bind")
        self.assertEqual(controlled_bind[0], "--ro-bind")
        self.assertLess(workspace_bind[3], controlled_bind[3])

        n_destinations = {mount[2] for mount in n_mounts}
        l_destinations = {mount[2] for mount in l_mounts}
        self.assertNotIn("/library/NumStability", n_destinations)
        self.assertNotIn("/library/NumStability.lean", n_destinations)
        self.assertNotIn("/library-olean", n_destinations)
        self.assertIn("/library/NumStability", l_destinations)
        self.assertIn("/library/NumStability.lean", l_destinations)
        self.assertIn("/library-olean", l_destinations)
        for destination in (
            "/library/NumStability",
            "/library/NumStability.lean",
            "/library-olean",
        ):
            self.assertEqual(
                next(mount[0] for mount in l_mounts if mount[2] == destination),
                "--ro-bind",
            )

        self.assertIn(("--ro-bind", str(self.shared_olean), "/shared-olean"), {
            mount[:3] for mount in n_mounts
        })
        self.assertIn("/shared-olean", setenv_value(n_command, "LEAN_PATH").split(":"))
        self.assertIn("/shared-olean", setenv_value(l_command, "LEAN_PATH").split(":"))
        self.assertEqual(setenv_value(n_command, "SHELL"), "/offline-bash")
        self.assertEqual(
            setenv_value(n_command, NETWORK_VIOLATION_MARKER_ENV),
            "/workspace/.network-marker",
        )
        self.assertIn(
            ("--ro-bind", str(self.offline_shell), "/offline-bash"),
            {mount[:3] for mount in n_mounts},
        )
        self.assertIn("--share-net", n_command)
        self.assertIn("--share-net", l_command)

        n_lean_path = setenv_value(n_command, "LEAN_PATH").split(":")
        l_lean_path = setenv_value(l_command, "LEAN_PATH").split(":")
        self.assertEqual(
            n_lean_path,
            [
                "/shared-olean",
                "/workspace/task/shared",
                "/packages/mathlib/.lake/build/lib/lean",
                "/packages/batteries/.lake/build/lib/lean",
                "/lean/lib/lean",
                "/workspace",
            ],
        )
        self.assertEqual(
            l_lean_path,
            [
                "/shared-olean",
                "/workspace/task/shared",
                "/library-olean",
                "/packages/mathlib/.lake/build/lib/lean",
                "/packages/batteries/.lake/build/lib/lean",
                "/lean/lib/lean",
                "/workspace",
            ],
        )

    def test_lean_validator_namespace_has_shared_olean_but_only_l_has_library(self) -> None:
        n_args = self.lean_args("N")
        n_args.library_source = self.library_source
        n_args.library_root_file = self.library_root
        n_args.library_olean = self.library_olean
        n_command = namespace_prefix(n_args)
        l_command = namespace_prefix(self.lean_args("L"))
        n_destinations = {mount[2] for mount in mounts(n_command)}
        l_destinations = {mount[2] for mount in mounts(l_command)}
        self.assertIn("/shared-olean", n_destinations)
        self.assertIn("/shared-olean", l_destinations)
        self.assertNotIn("/library-olean", n_destinations)
        self.assertNotIn("/library/NumStability", n_destinations)
        self.assertIn("/library-olean", l_destinations)
        self.assertIn("/library/NumStability", l_destinations)
        self.assertNotIn("--share-net", n_command)
        self.assertNotIn("--share-net", l_command)

    def test_positive_token_limit_is_required_and_encoded_once(self) -> None:
        self.assertEqual(positive_int("7"), 7)
        for raw in ("0", "-1", "not-an-int"):
            with self.assertRaises(argparse.ArgumentTypeError):
                positive_int(raw)
        args = self.codex_args("N")
        command = bubblewrap_command(args, self.state_home)
        self.assertEqual(
            command.count("features.rollout_budget.limit_tokens=1234"), 1
        )
        args.token_limit = 0
        with self.assertRaisesRegex(RuntimeError, "token limit must be positive"):
            bubblewrap_command(args, self.state_home)

    def test_condition_l_requires_both_library_mounts(self) -> None:
        args = self.codex_args("L")
        args.library_olean = None
        with self.assertRaisesRegex(RuntimeError, "condition L requires"):
            bubblewrap_command(args, self.state_home)
        lean_args = self.lean_args("L")
        lean_args.library_source = None
        with self.assertRaisesRegex(RuntimeError, "condition L requires"):
            namespace_prefix(lean_args)


class OfflineShellTests(unittest.TestCase):
    @unittest.skipUnless(shutil.which("cc"), "C compiler is unavailable")
    @unittest.skipUnless(platform.machine() == "x86_64", "seccomp launcher is x86-64 only")
    def test_launcher_preserves_bash_lc_argument_shape_and_blocks_sockets(self) -> None:
        with tempfile.TemporaryDirectory() as raw:
            root = Path(raw)
            executable = root / "offline-shell"
            compiled = subprocess.run(
                [
                    shutil.which("cc") or "cc",
                    "-std=c11",
                    "-O2",
                    "-Wall",
                    "-Wextra",
                    "-Werror",
                    str(TOOLS / "offline_shell.c"),
                    "-o",
                    str(executable),
                ],
                text=True,
                stdout=subprocess.PIPE,
                stderr=subprocess.STDOUT,
                check=False,
            )
            self.assertEqual(compiled.returncode, 0, compiled.stdout)
            marker = root / "network-violation.marker"
            marker.write_bytes(b"")
            launcher_environment = {
                "HOME": str(root),
                "PATH": "/usr/bin:/bin",
                "SHELL": str(executable),
                NETWORK_VIOLATION_MARKER_ENV: str(marker),
            }
            socket_check = (
                "import errno,socket,sys; "
                "\ntry: socket.socket()"
                "\nexcept OSError as error: "
                "sys.exit(0 if error.errno == errno.EPERM else 2)"
                "\nsys.exit(3)"
            )
            direct = subprocess.run(
                [sys.executable, "-c", socket_check],
                cwd=root,
                env={"HOME": str(root), "PATH": "/usr/bin:/bin"},
                text=True,
                stdout=subprocess.PIPE,
                stderr=subprocess.STDOUT,
                check=False,
            )
            shaped = subprocess.run(
                [
                    str(executable),
                    "-lc",
                    'printf "%s|%s|%s" "$0" "$1" '
                    '"${HIGHAMBENCH_NETWORK_VIOLATION_MARKER-unset}"',
                    "shape-zero",
                    "shape-one",
                ],
                cwd=root,
                env=launcher_environment,
                text=True,
                stdout=subprocess.PIPE,
                stderr=subprocess.STDOUT,
                check=False,
            )
            self.assertEqual(shaped.returncode, 0, shaped.stdout)
            self.assertTrue(
                shaped.stdout.endswith("shape-zero|shape-one|unset"), shaped.stdout
            )
            if direct.returncode == 3:
                self.assertEqual(marker.read_bytes(), b"", shaped.stdout)
            else:
                marker.write_bytes(b"")
            blocked = subprocess.run(
                [
                    str(executable),
                    "-c",
                    f"{shlex.quote(sys.executable)} -c {shlex.quote(socket_check)}",
                ],
                cwd=root,
                env=launcher_environment,
                text=True,
                stdout=subprocess.PIPE,
                stderr=subprocess.STDOUT,
                check=False,
            )
            self.assertEqual(blocked.returncode, 0, blocked.stdout)
            if direct.returncode == 3:
                self.assertEqual(marker.read_bytes(), b"N")
            else:
                # Some test sandboxes already deny socket() with a higher-
                # priority outer seccomp rule, so the inner listener cannot
                # observe that call.  The unsandboxed regression path above is
                # exercised whenever the host itself permits socket creation.
                self.assertEqual(direct.returncode, 0, direct.stdout)

            marker.write_bytes(b"")
            ordinary_signals = subprocess.run(
                [
                    str(executable),
                    "-c",
                    "sleep 5 & victim=$!; "
                    "kill -TERM \"$victim\"; wait \"$victim\" 2>/dev/null || :; "
                    "timeout 0.05 sleep 5; test $? -eq 124",
                ],
                cwd=root,
                env=launcher_environment,
                text=True,
                stdout=subprocess.PIPE,
                stderr=subprocess.STDOUT,
                check=False,
            )
            self.assertEqual(ordinary_signals.returncode, 0, ordinary_signals.stdout)
            self.assertEqual(marker.read_bytes(), b"", ordinary_signals.stdout)

            marker.write_bytes(b"")
            blocked_kill = subprocess.run(
                [
                    str(executable),
                    "-c",
                    'kill -KILL "$PPID" 2>/dev/null; test "$?" -ne 0',
                ],
                cwd=root,
                env=launcher_environment,
                text=True,
                stdout=subprocess.PIPE,
                stderr=subprocess.STDOUT,
                check=False,
            )
            self.assertEqual(blocked_kill.returncode, 0, blocked_kill.stdout)
            self.assertGreaterEqual(len(marker.read_bytes()), 1)
            self.assertEqual(set(marker.read_bytes()), {ord("N")})

            marker.write_bytes(b"")
            inherited_source = root / "inherited.txt"
            inherited_source.write_text("secret", encoding="utf-8")
            source_fd = os.open(inherited_source, os.O_RDONLY)
            inherited_fd = 77
            os.dup2(source_fd, inherited_fd, inheritable=True)
            os.close(source_fd)
            try:
                closed_fd = subprocess.run(
                    [
                        str(executable),
                        "-c",
                        f"test ! -e /proc/self/fd/{inherited_fd} && "
                        f"test ! -e /proc/$PPID/fd/{inherited_fd}",
                    ],
                    cwd=root,
                    env=launcher_environment,
                    pass_fds=(inherited_fd,),
                    text=True,
                    stdout=subprocess.PIPE,
                    stderr=subprocess.STDOUT,
                    check=False,
                )
            finally:
                os.close(inherited_fd)
            self.assertEqual(closed_fd.returncode, 0, closed_fd.stdout)


if __name__ == "__main__":
    unittest.main()
