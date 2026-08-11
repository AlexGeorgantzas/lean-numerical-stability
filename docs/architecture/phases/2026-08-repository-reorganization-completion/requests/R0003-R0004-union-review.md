# R0003/R0004 reviewed union of shared postimages

Both active requests were independently constructed against exact C0001 code preimage `117aa2bb7e61f41e1531a78452f9f7f6cd5b0771` at `2026-08-11T22:53:46Z`. R0003 has 133 paths (path-list SHA-256 `B98B986ED724D1B90DB2C368E4ADAE6046002DD05820883D0A8B1EBD445714FD`), and R0004 has three (path-list SHA-256 `D9BB4F3E7F383A45EB84DF97977D766925CCFD2FF85508077CEFE6F8F952049A`). Their exact intersection is `NumStabilityTest.lean`, `docs/architecture/layout-exceptions.json`, and `docs/architecture/tiers.json`; no production module is shared between the requests.

The three intersections commute semantically and byte-for-byte:

- `NumStabilityTest.lean`: R0003 adds the sorted `NumStabilityTest.Reorganization.R11.All` import; R0004 adds the distinct sorted `NumStabilityTest.Reorganization.R12.All` import.
- `docs/architecture/tiers.json`: R0003 adds five exact R11 rules (three compatibility support wrappers and two source aggregates); R0004 adds three disjoint Chapter 13 aggregate rules. Both postimages retain canonical JSON ordering.
- `docs/architecture/layout-exceptions.json`: R0003 removes 59 QR wrapper documentation exceptions, three support-path naming exceptions, and two Chapter 19 declaration-bearing-umbrella exceptions, then adds two complete aggregate contracts. R0004 removes three disjoint Chapter 13 umbrella exceptions and adds their three complete aggregate contracts. Both postimages retain canonical JSON ordering.

Applying the semantic R0003 delta then R0004 and applying R0004 then R0003 produced identical bytes on all three intersecting paths. The ordered postimage witness SHA-256 is `C45978C19A8CB19311A299B8ADB92DC38F927D020195D86A63151A91FEFA4711`. The union patch was generated directly from the C0001 preimages, never as a sequential whole-file replacement.

| Artifact | Paths | SHA-256 | Forward tree |
| --- | ---: | --- | --- |
| R0003 patch | 133 | `E1BFBF147D61FFE2CA08090B91DE362A2C089709221624AB2F9B36F9F4E2F4D3` | `290661700cdf3d8c303115b47cfc817455ab2a52` |
| R0003 postimages | 133 | `6799789E9E739095C49E409799F17D723C4EE038E2E341105BD38595F26CC5D2` | — |
| R0004 patch | 3 | `449E350993D72F8A38A894CAF8DA245E06ED66D48A176EAE66EC65364F8D7BEB` | `0532bae565cc8f5090029da5aaf366e6f0bcfe0f` |
| R0004 postimages | 3 | `6CC237E4F8F99328DAA098591F3551A8FF6A452AFF908E81B37C4AFABCF8900E` | — |
| Reviewed union patch | 133 | `A6AB1307D19CBF2BEDDA37EAC8C68FFB405292B405E068908E6E4F15406A3E3B` | `439514c9ebaf7fb9cd2420ed92121a55a04ab9fa` |
| Reviewed union postimages | 133 | `7279EDF6AF7277C2A4DD45286AEE97878EBFD025A89B240A6A644EE6FB665701` | — |

Each patch passed an isolated temporary-index forward `git apply --cached --check`, exact postimage-byte verification, reverse `--check`, and reverse replay. All three reverse trees equal C0001 tree `e469422446623d74309e5994fa8b1ff3457fdfa3` (R0004 `e469422446623d74309e5994fa8b1ff3457fdfa3`, union `e469422446623d74309e5994fa8b1ff3457fdfa3`). The union manifest's `source_requests` column is `R0003+R0004` on exactly the three intersecting controls and `R0003` on every other row. Import occurrence evidence is SHA-256 `7EE5623EB236248C96A8C65A3A4601A6819495A40B3F067BC9A6639836D38611`; graph/overlap facts are SHA-256 `3BC917D2E25E2CB795C4C4094F06DD2A72F2DA0030F5DFCECA4BB8BA31A0E412`; the temporary operator authorization is SHA-256 `E6CBEFC8E640603A8FB176268301A34727D777120B3ED3386517403A4A8DCB5D`.
