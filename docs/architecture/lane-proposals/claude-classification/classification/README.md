# Frozen classification proposal

This proposal reviews every row of the packet's immutable 386-module queue. It
does not modify production Lean sources or the shared tier manifest. Decisions
use module documentation, declaration roles, direct imports, and source/body
markers; filenames are evidence only when confirmed by the source body.

The queue and the 217-row exclusion inventory are tracked byte-for-byte so the
original 603-module partition remains reproducible after the external packet is
removed. The frozen partition is at `6487fc33088523b8f27ecde9ad613515b78f9977`; source/import refresh evidence
is taken from published main `6ecc4d5513226e67594bb22985913f6a4a383e5c`.

| Proposed category | Modules |
| --- | ---: |
| reusable | 129 |
| source | 212 |
| compatibility | 0 |
| aggregate | 1 |
| mixed_pending_split | 44 |
| internal | 0 |

`mixed_pending_split` is an implementation queue, not an exception. Every row
contains a concrete reusable/source split action. `modules.tsv` is sorted and
has exactly one row per tracked input module.

## Post-packet refresh

Six inventory blobs changed between the packet base and the reviewed main:

- `NumStability.Algorithms.Ch14Problem142`: `16c55f505385983fc9b10e426dc1b4e1040cd099` -> `09680f5d1000524225c0329d574cf5e62e100545`
- `NumStability.Algorithms.HighamChapter9`: `714585c4069df967e465ce4e1efd08c9f2302e6b` -> `35f2078dcaed7444199e0cc6d23dfc5c59267470`
- `NumStability.Algorithms.MatrixInversion`: `22575f92f7a266dfeb2c85c25303bf46be8260d3` -> `91dd01ea7be2aa4ac7a69f728fd6b6c9e8ab5dfd`
- `NumStability.Algorithms.MatrixInversionMethod2BInstance`: `41754b827feb4c55fdfcec077ae05c97886e65ee` -> `826109bcaf98b9f4787fb16bf993732c3e7bc0b8`
- `NumStability.Algorithms.RandNLA.LeastSquaresSketch`: `4c7a83beb97b26732db4951bd3b6f1aa853bc1f8` -> `eb25e270ace83b6515d0a9112928bf2be3e775b1`
- `NumStability.Algorithms.StationaryIteration`: `446b8df875feea3c149c564a144a1e90b208f51b` -> `34c1d8e3a7511878e18449282e7928f467009272`

The three BlockLU consumers were re-read after the Phase 12 integration. The
least-squares consumers were re-read after their canonical import cutover.
`StationaryIteration` gained two public Chapter 17 declarations, which are
included in its current declaration count and mixed-file action.

## Applying the proposal

`apply_tier_proposal.py` writes only to an explicit output distinct from its
input and refuses the shared `docs/architecture/tiers.json` path. The proposal
must be reviewed and all mixed rows split before an integrator applies it.
