# R0009/R0010 shared-file union review

The primary-human reviewed both active shared-file requests independently against exact
C0004 code `783ae9a4951407ece046adb8631d5a8ff1795a18`. The integration postimage is a separate common-base union; it
is not the result of applying either whole-file request after the other.

- R0009 paths: 28; patch SHA-256 `3277A434AEA678551274D55953FDBA72A44A46DE1235C1B747126A39DC0E1BCA`.
- R0010 paths: 14; patch SHA-256 `DE6D0A2217D3644D8957830C02F91C99FB44E863FA973CAA698794A498D19A2B`.
- Exact/casefold intersection: 5; no non-equal ancestor relations.
- Sorted intersection SHA-256: `D251C487ABEE9E25B128B92F63DC8A81B993C011FDDE6F1A57DCB66B09966BFC`.
- Sorted union: 37 paths; path-list SHA-256 `6DB1CD2A1AAB1DAD67924B2FA0ECD5F3FA2B315AB18BED68F7A3559C2DF63B81`.
- Union patch SHA-256: `0D646D4658D0AEDBEDCDE397553B1AEF31662130545750DA27061299BD11545B`.
- Union postimage ledger SHA-256: `22C2D8B31096FC7B9268C3B75FC1C243A652C3916FC496FC07F61E90995DCE5C`.
- Replay: `git apply --cached --check --unidiff-zero` and exact postimage verification pass
  from C0004; reverse replay reconstructs tree `122bf65c2e13840ca8251ec0eb7ed7e9cf3e653d`.

The five shared postimages are `NumStability/Algorithms.lean`, `NumStabilityTest.lean`,
`docs/architecture/COMPATIBILITY.md`, `docs/architecture/layout-exceptions.json`, and
`docs/architecture/tiers.json`. No request writes a worker-owned selector path.
