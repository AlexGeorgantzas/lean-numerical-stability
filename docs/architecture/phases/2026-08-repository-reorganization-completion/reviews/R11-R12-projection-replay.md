# R11/R12 C0001 projection replay

Authority: `primary-human`

The two planned projections were independently replayed against the same exact
C0001 format-2 candidate:

- code checkpoint: `117aa2bb7e61f41e1531a78452f9f7f6cd5b0771`
- candidate SHA-256:
  `55E0D29D626D746CB165DD7C874DA11A96B72602A66C1A6D8173F986178536C4`
- checker SHA-256:
  `0F32935ED1EFDD2BD4D6A4C346F3E8300C86DB1D4A3551A17165479226109220`

P0003 passed with projection SHA-256
`31EC591D949DB6041078C036F0CFF74A0A3EE229B35E351DDF999D15F494D60E`:
1,477 selected declarations, 15,172 signature edges, 18,056 body/proof
edges, and 19,873 union edges. The preimage replay deliberately omitted the
two `--private-map` arguments. P0003's tracked private map names the expected
post-delivery private owners (16 rewrites plus the retained Core identity), so
it is applied to the worker candidate at delivery replay, not to the unchanged
C0001 preimage whose private names are still the projection names. The tracked
map remains total over all 17 selected private declarations and is pinned at
`12E4D4F517D3678DABA4A11F57D36E22EE4428BC3598D3CA0FC7E41A9323E70E`.

P0004 passed with its exact tracked argument vector and projection SHA-256
`E84302EC06E0215758B91F9B179D89E0A5E17931CF42734828F1253BB4C129D2`:
34 selected declarations, 80 signature edges, 133 body/proof edges, and 139
union edges. Its private map is header-only and reports zero normalizations.

Both replays scanned the same 56,903 declarations and 649,259 typed edges.
Neither replay relocated a declaration in the unchanged preimage, as expected;
the declaration route contracts separately freeze 412 R11 relocations, 1,065
R11 retained declarations, and all 34 R12 relocations for delivery validation.
