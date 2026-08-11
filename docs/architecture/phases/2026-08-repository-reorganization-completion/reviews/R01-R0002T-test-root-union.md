# R01 and R0002T test-root union review

Authority: `primary-human`

Base checkpoint: `C0000`

Base code SHA: `b1b18772d80185ec08f49c818919558645c330a1`

The supplemental R02 request `R0002T` is independently replayable from the
exact C0000 `NumStabilityTest.lean` blob
`eb23b5792e054e4e75d062f47a9f67ab978c3934`. Its standalone root postimage is
blob `e95f1a6654f89e350c531ae8138887fd68612a4c`, SHA-256
`D2B53F45FF8EA8A1E2A7D91CA3151EFB97755F0A22FD6E092298B877BE9E2ED2`,
and adds only `NumStabilityTest.Reorganization.R02`.

The integrated root is a reviewed union, not a sequential whole-file
replacement. It adds the declaration-free R01 and R02 aggregates together,
plus the integrator-owned direct compatibility smoke test needed for the
existing reusable `NumStability.Algorithms.LU.TridiagonalCond` target. The
three new root imports are sorted at the existing import boundary.

Exact integrated artifacts:

- `NumStabilityTest.lean`: blob
  `35510507568f31138cd2b1a6fc7c8979a0deef9e`, SHA-256
  `D40BAE6EC7C6FE3580322D4552FAE02E7FFA140F0F1CC38A75DCC86D498BFBD1`.
- `NumStabilityTest/Reorganization/R01.lean`: 41 sorted test imports, blob
  `794264e7e822fda30694c12a0b479a766d060eb6`, SHA-256
  `A100CFEF30182C86A4737D9C7F4BD0A8644B86D693D4EE4C8C5847F12C8B6338`.
- `NumStabilityTest/Reorganization/R02.lean`: 63 sorted test imports, blob
  `efbfe76e4b0ceb2a66be256b1571227fdb17d693`, SHA-256
  `C560026FCCD0F74A5B4CBB133FBBD6018A38C97F68156FAE66CA157AD6C533F8`.
- `NumStabilityTest/Import/TridiagonalCondCanonical.lean`: blob
  `821aefe352b59e393223f282c074f9325d0240c6`, SHA-256
  `F5B18C9B9F87EA53EFE7B67C146E0C12739D1CDDA179EB6062778E05E8594F3C`.

This deliberate union explains why the integrated root is not byte-identical
to the standalone R0002T root postimage. Layout reachability, the exact 41/63
aggregate inventories, compatibility, all four focused build profiles, both
aggregate roots, the full two-root build, and `lake test` all pass on the
integrated body.
