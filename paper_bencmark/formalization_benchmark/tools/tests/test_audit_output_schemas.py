from __future__ import annotations

import json
from pathlib import Path
import unittest


SCHEMAS = Path(__file__).resolve().parents[2] / "audit" / "schemas"
AUDITOR_SCHEMAS = (
    "blind_translation.schema.json",
    "direct_judgment.schema.json",
    "roundtrip_judgment.schema.json",
    "adjudication.schema.json",
)


def assert_strict_output_schema(test: unittest.TestCase, schema: dict, path: str) -> None:
    """Check the provider's typed, closed-object Structured Outputs subset.

    The pilot-2 incident was an API 400 for ``properties.role`` lacking ``type``;
    a JSON Schema validator alone would not catch that provider requirement.
    """

    test.assertIn("type", schema, path)
    test.assertNotIn("const", schema, path)
    kind = schema["type"]
    test.assertIn(kind, {"object", "array", "string", "number", "integer", "boolean"}, path)
    if "enum" in schema:
        test.assertTrue(schema["enum"], path)
        test.assertTrue(
            all(isinstance(value, str) for value in schema["enum"]), path
        )
        test.assertEqual(kind, "string", path)
    if kind == "object":
        properties = schema.get("properties")
        test.assertIsInstance(properties, dict, path)
        test.assertIs(schema.get("additionalProperties"), False, path)
        required = schema.get("required")
        test.assertIsInstance(required, list, path)
        test.assertEqual(set(required), set(properties), path)
        test.assertEqual(len(required), len(set(required)), path)
        for name, child in properties.items():
            test.assertIsInstance(child, dict, f"{path}.properties.{name}")
            assert_strict_output_schema(test, child, f"{path}.properties.{name}")
    elif kind == "array":
        items = schema.get("items")
        test.assertIsInstance(items, dict, f"{path}.items")
        assert_strict_output_schema(test, items, f"{path}.items")


class AuditorOutputSchemaTests(unittest.TestCase):
    def test_every_frozen_auditor_schema_is_typed_and_strict(self) -> None:
        self.assertEqual(
            {path.name for path in SCHEMAS.glob("*.schema.json")},
            set(AUDITOR_SCHEMAS),
        )
        for name in AUDITOR_SCHEMAS:
            with self.subTest(schema=name):
                schema = json.loads((SCHEMAS / name).read_text(encoding="utf-8"))
                assert_strict_output_schema(self, schema, name)

    def test_semantic_verdicts_are_binary(self) -> None:
        schema = json.loads(
            (SCHEMAS / "adjudication.schema.json").read_text(encoding="utf-8")
        )
        self.assertEqual(
            schema["properties"]["verdict"]["enum"],
            ["faithful", "unfaithful"],
        )
        for name in ("direct_judgment.schema.json", "roundtrip_judgment.schema.json"):
            with self.subTest(schema=name):
                judge = json.loads((SCHEMAS / name).read_text(encoding="utf-8"))
                self.assertNotIn("verdict", judge["properties"])
                self.assertIn("undetermined", judge["properties"]["classification"]["enum"])

    def test_adjudicator_schema_cannot_report_remaining_uncertainty(self) -> None:
        schema = json.loads(
            (SCHEMAS / "adjudication.schema.json").read_text(encoding="utf-8")
        )
        self.assertEqual(
            schema["properties"]["remaining_uncertainties"]["maxItems"],
            0,
        )

    def test_regression_catches_untyped_role_before_provider_call(self) -> None:
        schema = json.loads(
            (SCHEMAS / "blind_translation.schema.json").read_text(encoding="utf-8")
        )
        del schema["properties"]["role"]["type"]
        with self.assertRaisesRegex(AssertionError, "role"):
            assert_strict_output_schema(self, schema, "blind_translation.schema.json")


if __name__ == "__main__":
    unittest.main()
