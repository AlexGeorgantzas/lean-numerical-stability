# R04 projection replay

Baseline projection `P0008`, base checkpoint C0004
`783ae9a4951407ece046adb8631d5a8ff1795a18`.

## Result: PASSED (exit 0, zero mismatch)

The frozen projection was hash-verified against the P0008 pin
(`5207DDA1BBA72F0802ACDA0A286611B62A07A72C9DF4E50E0E5F1EC048887540`); the
candidate is a fresh format-2 graph generated from the built worktree under
the named mutex; the private map is the frozen 115-row B0008 map
(`2349DFA9F94EEB183359B57A870E8F2CC5068662FB69EC4799FE7D99914858C1`),
101 nonidentity + 14 identity rows; the allow-module vector is P0008's,
verbatim.

```
phase projection contract passed
projection_sha256: 5207DDA1BBA72F0802ACDA0A286611B62A07A72C9DF4E50E0E5F1EC048887540
candidate_sha256: 0FCCBD73B4F5B8F10D3F71CC057DD316EED57DB9170C07821391E8C278A99D08
selected_declarations: 289
relocated_declarations: 252
signature_edges: 990
body_edges: 2239
candidate_declarations_scanned: 56903
candidate_edges_scanned: 649259
allowed_exact_modules: 50
allowed_prefixes: 0
private_map_sha256: 2349DFA9F94EEB183359B57A870E8F2CC5068662FB69EC4799FE7D99914858C1
private_normalizations: 115
```
