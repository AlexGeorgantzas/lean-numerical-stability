# Fresh R11/R12 graph-disjointness and shared-path facts

Authority timestamp: `2026-08-11T22:53:46Z`. Exact code preimage/checkpoint: C0001 `117aa2bb7e61f41e1531a78452f9f7f6cd5b0771`. Raw format-2 graph SHA-256: `55E0D29D626D746CB165DD7C874DA11A96B72602A66C1A6D8173F986178536C4`.

The fresh selectors are R11 `461D1A0E09A0EADD02B57F3FEB6E097508D02F769A13A11E1CF6896B289A3F23` and R12 `2A45891E56E976DEAC01B791293D4DF05A4C1A045498D98B7D087B940582AD0F`. Their deterministic format-2 projections are P0003 `31EC591D949DB6041078C036F0CFF74A0A3EE229B35E351DDF999D15F494D60E` and P0004 `E84302EC06E0215758B91F9B179D89E0A5E17931CF42734828F1253BB4C129D2`.

| Measure | R11 | R12 | Cross-wave result |
| --- | ---: | ---: | --- |
| Selected owners | 65 | 3 | equal-or-ancestor owner overlap 0 |
| Owner declarations | 1,477 | 34 | declaration overlap 0 |
| Signature closure edges | 15,172 | 80 | directed cross-owner edges 0 both ways |
| Body/proof closure edges | 18,056 | 133 | directed cross-owner edges 0 both ways |
| Signature/body union | 19,873 | 139 | union overlap 0 |
| Direct module-import edges | — | — | 0 both ways |
| Transitive owner reachability | — | — | 0 both ways |
| Shared direct module dependencies | — | — | 0 |
| Common direct project dependencies | — | — | 0 |
| Shared external dependent declarations | — | — | 0 |

Destination paths are vacant and have zero equal-or-ancestor overlap. The waves have no shared direct production consumer. Their harmless common transitive umbrella set is exactly `NumStability`, `NumStability.Algorithms`, `NumStability.All`, `NumStability.Higham`, `NumStability.Source`, and `NumStability.Source.Higham`; the common transitive foundation-module count is 40. Common declaration dependencies are the four signature foundations `FPModel`, `FPModel.u`, `IsRightInverse`, and `nonsingInv`; body/proof dependence adds only `gamma`. These common downstream foundations do not create an owner, destination, direct-import, signature-edge, or body-edge crossing.

R0003 has 133 paths and newline-delimited path-list SHA-256 `B98B986ED724D1B90DB2C368E4ADAE6046002DD05820883D0A8B1EBD445714FD`: 129 exact direct production consumers plus `NumStabilityTest.lean`, `docs/architecture/tiers.json`, `docs/architecture/COMPATIBILITY.md`, and `docs/architecture/layout-exceptions.json`. The consumers comprise 118 already-complete rows, ten future R05 rows, and one future R09 row. The five exact import maps produce 209 replacements; 43 consumer paths contain more than one replacement. Exact occurrence evidence is in `reviews/R11-shared-import-replacements.tsv` (SHA-256 `7EE5623EB236248C96A8C65A3A4601A6819495A40B3F067BC9A6639836D38611`).

R0004 has three paths and newline-delimited path-list SHA-256 `D9BB4F3E7F383A45EB84DF97977D766925CCFD2FF85508077CEFE6F8F952049A`. The request intersection is exactly `NumStabilityTest.lean`, `docs/architecture/layout-exceptions.json`, and `docs/architecture/tiers.json`; there is no shared production path. Those three paths are primary-human integration controls, and their reviewed union is generated directly from the same C0001 preimages rather than by sequential whole-file replacement.
