# R04/R08 C0004 projection replay

Both baseline projections are deterministic format-2 subsets of exact C0004. Freeze replay
uses the accepted graph as candidate and deliberately omits private normalization because the
baseline still contains the historical private names.

| Projection | declarations | signature edges | body edges | union pairs | gzip SHA-256 |
| --- | ---: | ---: | ---: | ---: | --- |
| P0008/R04 | 289 | 990 | 2,239 | 2,293 | `5207DDA1BBA72F0802ACDA0A286611B62A07A72C9DF4E50E0E5F1EC048887540` |
| P0009/R08 | 211 | 1,229 | 2,886 | 2,912 | `CE770EBE7B3170BA808D22D2AD603B7266A8AADC550864902423FD33162FA1FF` |

Delivery replay must add the total private map: B0008 has 115 rows (101 nonidentity and 14
identity), while B0009 has 48 nonidentity rows. The accepted projection checker is pinned at
`0F32935ED1EFDD2BD4D6A4C346F3E8300C86DB1D4A3551A17165479226109220`. No delivery candidate exists during planning.
