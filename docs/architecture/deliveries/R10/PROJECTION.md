# R10 projection replay

P0012 is active against C0006. Its deterministic gzip graph has SHA-256
`2E5A95D8EFF802AD5894189D6ECCDC1BAD764CA28DBCC47B4C43AEBACF381FC3`
and size 33,943 bytes. The decompressed format-2 payload has SHA-256
`23CB17D005A208685C315AF3BABA9A0D6D50685F89A309F7D20D75A8DD7D6ED3`
and size 1,411,110 bytes.

The projection selects 225 declarations and freezes 2710 signature edges and
3327 body edges (3579 distinct union edges).
Its checker contract permits exactly 35 modules and a total 3-row private-normalization map.

`CHECK_PROJECTION.py` substitutes only the generated candidate format-2 graph, hash-pins that candidate during the replay, and requires the exact expected
counts from the official checker.

Candidate evidence:

- TSV: 117,181,324 bytes, SHA-256 `E1F7289370F9FD862F6DEA729FD2F114AF2187461E16B2CD1E8FFB12B68D4F0B`;
- JSON: 128,655 bytes, SHA-256 `A6E7E393729B5F9733FD35C990D9CA6F7E8195223C8726902C538AB4499351C9`;
- Markdown: 42,947 bytes, SHA-256 `EE6FD0151D29AA47BE814CD1FDCC1FF9BDB897A09DD4604D3873ECD1A2E74D94`;
- source tree: `105959E16BF3C7500CBD91928EE677888D47D9F65F4967F32AD4F9AFBF7018C8`;
- census: 56,900 declarations in 1,718 modules.

