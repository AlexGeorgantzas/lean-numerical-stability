# W10 integrator request

Create R0011 from exact C0007 code SHA
`9eb534a06db267203c2b9b88227edd44fc64f5db`. The request is the deterministic
14-path patch `R0011.patch`:

- size: 34,111 bytes;
- SHA-256: `6AA9A9070BDA882DB9AA482D695F74CB15C9379BB8147B52F89BDB05CD4AA97C`;
- forward and reverse application are checked by `CHECK_INTEGRATOR_PATCH.py`;
- the zero-context payload is applied with explicit `git apply --unidiff-zero`;
- no accepted-consumer or historical-root import is changed.

## Exact C0007 paths

| path | C0007 preimage |
| --- | --- |
| `NumStability/Algorithms/NormEstimation.lean` | `4b0177b71c16ef1b56f43a34bb8d1b1fa705a0c2` |
| `NumStability/Algorithms/NormEstimation/OneNorm/All.lean` | `143df085a9ff19500ae64311662f7549dd461c61` |
| `NumStability/Source/Higham.lean` | `8e8fe02ca14854d7c9193cd3673c0150aa538bc9` |
| `NumStabilityTest.lean` | `a3e450a3790c414dfee8f2c6eb8f1fee7e9cec74` |
| `docs/architecture/tiers.json` | `c1afc0ad364fc908364114bfd63c5e0a2058baee` |
| `docs/architecture/layout-exceptions.json` | `bbedd2a796aa7b003f89193e746599140fb03524` |

The following eight paths are absent at C0007 and must be created only by the
integrator:

- `NumStability/Algorithms/NormEstimation/PNorm.lean`;
- `NumStability/Algorithms/NormEstimation/PNorm/All.lean`;
- `NumStability/Algorithms/NormEstimation/PNorm/Boyd.lean`;
- `NumStability/Algorithms/NormEstimation/TwoNorm.lean`;
- `NumStability/Algorithms/NormEstimation/TwoNorm/All.lean`;
- `NumStability/Algorithms/NormEstimation/TwoNorm/Dixon.lean`;
- `NumStability/Source/Higham/Chapter15.lean`;
- `NumStabilityTest/Reorganization/W10.lean`.

## Discovery and test wiring

The patch creates declaration-free PNorm and TwoNorm family aggregates, adds
them to `Algorithms.NormEstimation`, refreshes the existing OneNorm `All`
aggregate, creates the complete Chapter 15 Source aggregate, wires it through
`Source.Higham`, creates the complete 135-test W10 aggregate, and wires it
through `NumStabilityTest`.

Chapter 15 discovery contains 47 files: 46 selected-declaration owners plus the
declaration-free
`Source.Higham.Chapter15.Section01.ConditionNumbers.CondEstimation`
correspondence wrapper. That wrapper imports the reusable finite-index norm
identities and introduces no reusable-to-Source path.

## Classification and layout

Classify `NumStability.Algorithms.CondEstimation` exact `reusable`. Its retained
private closure is source-neutral, and its worker postimage imports only
reusable modules. Classify the other 26 W10 owners exact `mixed`; fourteen are
currently import-only but remain reviewed mixed debt because other historical
owners and the preserved root aggregate still import them. They are not yet
eligible for the compatibility tier.

Add the six new reusable-family aggregates and the Chapter 15 aggregate as
exact `aggregate`, and add the reusable
`NumStability.Algorithms.NormEstimation.` prefix. The resulting exact-tier
counts are:

| tier | count |
| --- | ---: |
| aggregate | 368 |
| compatibility | 337 |
| internal | 2 |
| mixed | 35 |
| reusable | 378 |
| source | 283 |

There are 1,403 exact assignments and 24 prefixes.

The reviewed layout postimage removes all 27 owners from unclassified debt,
removes the 14 documented owners from missing-docstring debt, adds the 26
historical facades to mixed debt, removes the now-reusable `CondEstimation`
name from stale noncanonical debt, and records the two PNorm endpoint names as
noncanonical. Exact counts are:

- 282 unclassified modules;
- 77 missing module docstrings;
- 35 mixed modules;
- 268 noncanonical modules;
- 21 declaration-bearing umbrellas;
- 0 unsorted-import exceptions.

## Boundary decision

The 74 non-root accepted consumers import only
`NumStability.Algorithms.CondEstimation`. After its honest reusable-in-place
classification and removal of its former Source import, those imports are
valid reusable dependencies and must be preserved. The root
`NumStability.Algorithms` imports remain preserved as aggregate discovery.

`CHECK_INTEGRATOR_PATCH.py` overlays the immutable worker production tree on
the exact C0007 request postimage and proves zero reusable-to-Source/mixed and
zero canonical-to-the-other-26-owner reachability. With `--full`, it also runs
layout, compatibility, provenance, and strict-source gates in the disposable
postimage.
