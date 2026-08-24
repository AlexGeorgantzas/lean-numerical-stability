# R0012/R0013 shared-file union review

The primary-human reviewed both active shared-file requests independently against exact
C0006 code `fda296b2079acae3bf1d3565b2dc6e45dc8f6ef5`. The integration postimage is a separate common-base union; it
is not the result of applying either whole-file request after the other.

- R0012 paths: 23; patch SHA-256 `286035E05241C89BA3A5005BACBA1F20429B218381B44027D485E46AE1C5A9AE`.
- R0013 paths: 7; patch SHA-256 `1C716FF5B10C4907BE42F9139A99906B11F616A5512EB10CFBCCD767A77A4ECE`.
- Exact/casefold intersection: 5; no non-equal ancestor relations.
- Sorted intersection SHA-256: `D251C487ABEE9E25B128B92F63DC8A81B993C011FDDE6F1A57DCB66B09966BFC`.
- Sorted union: 25 paths; path-list SHA-256 `0F0BA2210CD4A10A5C5A5E5A841AD1DD63C8FB87EF4EB91F95069963F965EBDF`.
- Union patch SHA-256: `C3E16C4D303BEDB97220006850A4621E372705D68EE4B9F41D2A418773FA7C8F`.
- Union postimage ledger SHA-256: `498E048EBA346B65051615400038A66C2FDE3DD6CF10D4E5384A911C85BD3F60`.

The shared postimages are:
`NumStability/Algorithms.lean`
`NumStabilityTest.lean`
`docs/architecture/COMPATIBILITY.md`
`docs/architecture/layout-exceptions.json`
`docs/architecture/tiers.json`

No request writes a worker-owned selector path.
