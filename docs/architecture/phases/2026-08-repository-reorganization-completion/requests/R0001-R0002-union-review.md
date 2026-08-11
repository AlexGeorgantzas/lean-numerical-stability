# R0001/R0002 reviewed union of shared postimages

Both requests are independently based on C0000 `b1b18772d80185ec08f49c818919558645c330a1`. Their only common path is `NumStability/Algorithms.lean`; R0001 and R0002 delete disjoint old import lines and add disjoint canonical/source aggregate lines. Applying either logical import delta first yields the exact same casefold-sorted union postimage. No request consumes the other request's postimage.

R0001 manifest: `C19BCD0823E2A6279E54DEF210F37D11DBFB7C6D06A5507B74E851CFB97CDA5E`. R0002 manifest: `3C2E64B3421D23BBF99749E4637D83F97794A18020E67700548A54754FE3FF6E`. Union manifest: `67AFB0F6FBADBB33B5755E9300972A7F4431EB22330F1366D1165EFBCC3FB163`. Exact C0000-to-union patch: `E73A8D881DD51CCE710CCB1B4C30320DFE0E6B666F6FC8C0A3E9C167588957E6`.
