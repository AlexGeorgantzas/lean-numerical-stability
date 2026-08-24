# R09 projection replay

P0011 is active against C0006. Its deterministic gzip graph has SHA-256
`9816398C44FF1CC53332AF4723A5AAD2DAD0C8407A6BCAA6132B8A70C299050F`
and size 37,738 bytes. The decompressed format-2 payload has SHA-256
`BE76202C62D14FD1F985A2B51CB510DB27E8B649B104FC9F79A2BD1A1AFE36D1`
and size 647,746 bytes.

The projection selects 570 declarations and freezes 1400 signature edges and
3120 body edges (3254 distinct union edges).
Its checker contract permits exactly 113 modules and a total 165-row private-normalization map.

`CHECK_PROJECTION.py` substitutes only the generated candidate format-2 graph, hash-pins that candidate during the replay, and requires the exact expected
counts from the official checker.

Candidate evidence:

- TSV: 117,210,899 bytes, SHA-256 `A4C92C7286EAC42963C77BB899EC698E98F1C7CF5604B6B6076BF1438C91681D`;
- JSON: 113,449 bytes, SHA-256 `EF6AE5D6D237D4AE39DC65740A3B2DC721CBF42EF7E4451E5E1F3231C9815A55`;
- Markdown: 36,501 bytes, SHA-256 `96897B64A93662B7E44987C6E9486E604DF3149B3B1529D436A9D552AD762582`;
- source tree: `105959E16BF3C7500CBD91928EE677888D47D9F65F4967F32AD4F9AFBF7018C8`;
- census: 56,913 declarations in 1,697 modules.

