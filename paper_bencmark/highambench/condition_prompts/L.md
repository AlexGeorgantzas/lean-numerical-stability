## Condition-specific library notice (L)

This is a library-available attempt. You can and should consider searching the
frozen NumStability library for relevant results, and you may import and use
any available declaration that helps. You must determine relevance yourself;
no theorem or module is being recommended.

Frozen snapshot:

- Git commit: `4ec1ec874353010ad93cc0bb76370ac321da4681`
- read-only source tree: `/library/NumStability`
- read-only root source file: `/library/NumStability.lean`
- read-only navigation index: `/library/docs/LIBRARY_LOOKUP.md`
- read-only lookup example: `/library/examples/LibraryLookup.lean`
- read-only compiled Lean tree: `/library-olean`

`/library-olean` is already on `LEAN_PATH`; do not modify `LEAN_PATH`. A module
is importable exactly when its corresponding `.olean` is present below
`/library-olean`. Source-only files may be inspected but are not part of the
importable frozen object set. For example,
`/library-olean/NumStability/A/B.olean` is imported as `NumStability.A.B`.

Useful local discovery commands include:

```sh
sed -n '1,240p' /library/docs/LIBRARY_LOOKUP.md

find /library-olean/NumStability -type f -name '*.olean' -print | sort

find /library-olean/NumStability -type f -name '*.olean' -print \
  | sed -e 's#^/library-olean/##' -e 's#/#.#g' \
        -e 's#\.olean$##' | sort

PATTERN='replace with search terms chosen from the target'
rg -n --glob '*.lean' "$PATTERN" \
  /library/NumStability /library/NumStability.lean
```

To test a declaration without modifying the submission:

```sh
MODULE='replace.with.a.module.from.the.compiled.list'
DECL='replace.with.a.fully.qualified.declaration.found.by.your.search'
printf 'import %s\n#check @%s\n#print %s\n' \
  "$MODULE" "$DECL" "$DECL" > /tmp/NumStabilityProbe.lean
lean /tmp/NumStabilityProbe.lean
```

Keep the fixed target import unchanged. You may add required
`import NumStability...` lines to `Candidate.lean`. You remain free to prove
the target directly if no library result helps.
