# R0008 approval addendum

- Approval authority: `primary-human`
- Approval recorded: `2026-08-16`
- Amendment: `R0008`
- Reviewed input: `R0008-review.md`
- Reviewed-input SHA-256: `7A4529D9994506AD3EEBD17504BDE331DC95F42CBF3B5307643D44F97D726338`
- Authorized patch SHA-256: `2FB6F4D07E8EBB270BF710D972958F20F1F53452A52DB081D953B231742D66D4`
- Decision: approved for the sequential R05/R06 integration candidate based on `main` at `deee8e7ea0aeac7cfbd9fc2582eaf1f5b841fd0c` with 78 paths already staged.

The packaged review is immutable pre-decision evidence. Its `DRAFT FOR REVIEW` label, open sign-off checklist, and 101-path shadow-replay count describe the state presented for review; this addendum is the durable approval disposition and does not rewrite that evidence.

## Binding disposition

1. **D1 - Variant A approved.** Trim the `NumStability.Algorithms` umbrella's `NumStability.Source.*` closure. Keep the `NumStability.Source.*` ceiling at 49. Do not amend `docs/architecture/layout-exceptions.json` for R0008.
2. **D2 - Approved.** Apply the reviewed direct-import compatibility repair.
3. **D3 - Confirmed policy.** The facade-to-facade exemption is intentional.
4. **D4 - Confirmed gate classification.** The five W04 retained-closure files are production files for gate purposes.
5. **D5 - Registration approved.** Register R0008 under the completion phase's integration-amendment lifecycle and completion conventions.
6. **D6 - Chain authority approved.** Leave `R0006-R0007-union-postimages.tsv` untouched as the immutable predecessor record. `R0008-postimages.tsv` is authoritative for the four overlapping paths, and each predecessor postimage SHA-256 must equal the corresponding R0008 preimage SHA-256.

Approval is conditional on the independently replayed 27/27 patch custody checks and on the complete post-repair battery, build, and test gates remaining green before integration.
