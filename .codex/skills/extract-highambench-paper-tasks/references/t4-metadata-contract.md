# T4 metadata contract

Read this reference after `t4-construction.md` and before creating or revising
`source_inventory.json`, `task.json`, or any construction-input hash. This is
the paper-neutral authoring contract for every T4 shard; another paper's files
are never a schema or template.

## Frozen starter assets

Use these exact repository assets:

- `paper_bencmark/highambench/schemas/highambench-t4-source-inventory-0.3.schema.json`
- `paper_bencmark/highambench/schemas/highambench-t4-task-0.4.schema.json`
- `paper_bencmark/highambench/templates/T4/source_inventory.pending.template.json`
- `paper_bencmark/highambench/templates/T4/task.pending.template.json`

Copy each pending template only into the selected paper's owned T4 directory,
then replace its illustrative records with the complete paper-specific corpus.
Do not preserve an example claim merely to satisfy a shape requirement. A
paper extraction invocation treats schemas and shared templates as read-only.
If they cannot represent a source object, report a bootstrap infrastructure
gap rather than inventing a paper-local dialect.

Templates are valid JSON before expansion. Every placeholder is a string token
of the form `__UPPER_SNAKE_TOKEN__`. Replace tokens through a JSON-aware
operation, not blind text replacement:

- tokens ending in `_INTEGER__` become JSON integers, not numeric strings;
- `__RESULT_FORM_TAG__` becomes `BND`, `EQ`, `CMP`, `EX`, or JSON `null`;
- SHA-256 tokens become 64 lowercase hexadecimal characters; and
- all other tokens become context-appropriate strings.

After expansion, no token may remain. Check the two selected-paper metadata
files for the pattern `__[A-Z0-9_]+__` before validation.

## One canonical inventory, two synchronized views

The external `tasks/P0X/T4/source_inventory.json` is the canonical coverage
ledger. `task.json.source_inventory_file` records its repository-relative path.
The raw bytes of that file hash to
`task.json.construction_inputs.source_inventory_sha256`.

`task.json.source_inventory` is an embedded projection that must deep-equal
the external file's `items` array, including item order and every normalized
field. The normalized item fields are exactly:

```text
source_order
inventory_id
source_kind
scope
source_locations
disposition
declaration_ids
exclusion_reason
assumptions
source_status
source_tags
author_label
source_issue_notes
declaration_mappings
duplicate_of_source_item_ids
review_unit_id
smallest_group_reason
```

Do not hand-maintain divergent summaries. Finish the external ledger first,
then copy its complete `items` value into the task object and validate equality.
The external and embedded views preserve the same array ordering. The external
`paper_id`, source path, and PDF hash must also match the task and the selected
paper record.

Use stable IDs for joins. A declaration mapping names `declaration_id`, never a
mutable Lean name. For an included item, `declaration_ids` is the
declaration-order union of mappings whose role is `primary_carrier` or
`duplicate_anchor`. A `semantic_context` mapping is excluded from that carrier
list and from the review unit's `declaration_ids`; it enters the packet through
the semantic dependency closure. Excluded items have no declaration mappings,
declaration IDs, or review unit, and require a specific exclusion reason.

Every included atomic item belongs to exactly one review unit. Its unit's
declarations are exactly the declaration-order union of the item's primary
carriers and duplicate anchors. Declare genuine carrier reuse explicitly in
each affected unit. Keep `source_order`, `declaration_order`,
`review_unit_order`, and `placeholder_order` contiguous and aligned with source
or controlled-file order. Backlinks among inventory items, declarations,
review units, required declarations, and controlled placeholders must agree in
both directions.

## Construction inputs and campaign state

`construction_inputs` contains exactly these four fields:

```text
paper_definitions_sha256
target_sha256
source_inventory_sha256
review_campaign_status
```

Hash exact frozen bytes only; never preserve a provisional hash after editing.
The definitions hash is paper-local. Do not add `semantic_core_sha256`, another
paper-specific key, or packet-level campaign hashes. Immutable paper-local
campaign receipts remain authoritative for detailed packet and output hashes.

The campaign status enum is exact:

- `not_started`: units are pending and accepted review records are absent;
- `in_progress`: units remain pending and accepted review records are absent;
- `replacement_required`: failed or stale evidence cannot be accepted, units
  are pending, and accepted review records are absent; or
- `accepted`: every unit is accepted and complete accepted
  `faithfulness_reviews` bind the frozen artifacts.

Only `accepted` permits `classification_frozen_before_runs: true`. Pending
construction normally uses `not_started`, pending review units, an empty
`faithfulness_reviews` array, and `classification_frozen_before_runs: false`.

## Authoring and validation sequence

1. Initialize the paper-local workspace as described in `t4-construction.md`.
2. Copy the two pending templates to the selected paper's owned T4 paths
   without overwriting existing work.
3. Replace the inventory examples with the complete source-order ledger and
   construct the paper-local Lean declarations.
4. Synchronize the task's embedded inventory from the canonical external
   `items`, then complete declarations, units, backlinks, and placeholders.
5. Freeze the exact paper definitions, target, and external-inventory bytes
   with the paper-local helper (the PDF hash remains in `paper_source`):

   ```text
   python3 paper_bencmark/highambench/tools/t4_metadata.py freeze \
     --benchmark-root paper_bencmark/highambench --paper-id P0X
   ```

   `freeze` may write only `tasks/P0X/T4/task.json`; inspect `write-set` first
   when auditing scope. Here `freeze` only refreshes hashes for the current
   snapshot. It does not make construction files read-only, set
   `classification_frozen_before_runs: true`, or prevent further extraction.
   Before an accepted campaign, edit as needed and rerun `freeze` plus the
   direct N/L gate; it refuses hash drift only after an accepted campaign.
6. Parse both metadata files as JSON, validate them against the frozen schemas,
   then run both read-only hand-off checks:

   ```text
   python3 paper_bencmark/highambench/tools/t4_metadata.py check \
     --benchmark-root paper_bencmark/highambench --paper-id P0X
   python3 paper_bencmark/highambench/tools/t4_workspace.py check \
     --benchmark-root paper_bencmark/highambench \
     --reference-root paper_bencmark/reference_papers --paper-id P0X
   ```

   The metadata check authenticates the three paper-local construction hashes
   and exact external/embedded inventory equality. Workspace `check` verifies
   only descriptor identity, bindings, and generic-contract hashes; it does not
   establish metadata completeness or stage readiness by itself. Both checks
   must pass for this hand-off. Run `task_tags.py --paper-id P0X` as the full
   paper-shard catalog check.

JSON Schema enforces paper-neutral record shapes. Generic validators additionally
enforce actual file bytes, contiguous ordering, cross-record equality and
backlinks, controlled Lean declarations and holes, source coverage, and review
state. Passing schema validation alone is not a completion gate.
