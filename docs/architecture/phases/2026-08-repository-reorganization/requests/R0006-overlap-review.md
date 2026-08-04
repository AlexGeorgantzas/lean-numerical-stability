# R0006 integration-overlap evidence

Base checkpoint: C0005 / `240c0d041781385a647fbec461d6863537e562cb`.

Every existing path below was verified to change import lines only: after
removing import commands, the C0005 and integrated texts are identical.
Every null-preimage path is an import-and-docstring-only aggregate. Blob
OIDs are Git SHA-1 object IDs; rows are sorted by path.

| Path | C0005 preimage | Integrated postimage | Class |
| --- | --- | --- | --- |
| `NumStability/Algorithms/RandNLA/LowRankApprox.lean` | `b7216d46614595a6e6c4f12ea984c874de81bb27` | `ffa4cfee7974d2c943b5d51b4923427c1924a62d` | W11-import-only-refresh |
| `NumStability/Source/Higham/Chapter13/Equation23/PointRowGrowth.lean` | `2057170f2e377b82dbec3001a97da8ccbf353558` | `c7e42912a0a7d30b792d51ca23eae3bd6f01e0bc` | accepted-consumer |
| `NumStability/Source/Higham/Chapter14/Discrepancies.lean` | `f976c3d793051b47f87214cfedae0e13dd4518a3` | `ac3f454df2c0d91d48ff79171668b712b30fc1a0` | accepted-consumer |
| `NumStability/Source/Higham/Chapter14/Problem13.lean` | `2773688fdeb7a747d42191ed061b4aeb84c76ff3` | `f524e25f485f0ba1a7629bc258dd70f4aadbd56d` | accepted-consumer |
| `NumStability/Source/Higham/Chapter14/Problem14.lean` | `7fd3da4651593340db45aa74dfe9e933ccd8f265` | `0d0b74a6875d45629c70933b682036924bf9bf44` | accepted-consumer |
| `NumStability/Source/Higham/Chapter14/Problem15.lean` | `fa43c8ab7376b5f8585b1e18bbd75eef19e19104` | `1d61212d03fa20573eef691d550a92941c53ba5c` | accepted-consumer |

Verified rows: 6.
