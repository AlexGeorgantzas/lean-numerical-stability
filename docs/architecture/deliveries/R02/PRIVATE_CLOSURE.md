# R02 private reverse closure and normalization

Recomputed from the frozen P0002 graph, then reconciled against B0002's reviewed sheet
rather than trusting it. The reverse closure of the 76 private declarations over the
union of signature and body edges has **123 members = 76 private +
47 public**, and that set is **identical** to `B0002-private-closure.tsv`.

## The normalization is relocation, not renaming

All 76 reviewed renames are **module-prefix-only**. The logical name is
byte-identical on both sides; only the `_private.<module>.0.` prefix changes, and the new
prefix equals the routed `destination_module` in 76/76 cases. So no
source identifier is rewritten anywhere in this wave -- Lean re-derives each mangled name
from the module the declaration now lives in.

That is only safe if no destination receives two privates sharing a logical name, because
Lean disambiguates homonyms by counting them and the frozen graph pins the exact ordinal.
Checked: **zero collisions**, and every new name carries ordinal `0`.

## Verification performed

| check | result |
| --- | --- |
| computed closure == reviewed sheet | yes (123 members) |
| normalization rows cover the privates exactly | yes (76) |
| new-private prefix == routed destination | 76/76 |
| distinct new-private names | 76/76 |
| logical-name collisions inside a destination | 0 |
| private logical name present in its destination file | all 76 |

Privates are never `#check`ed by the test suite: a mangled `_private.…` name is not
addressable from another module, which is the same fact that makes these renames automatic.
The closure is pinned observably through its 47 public dependents instead.
