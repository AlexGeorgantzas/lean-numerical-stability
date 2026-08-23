# R07 integrator request

The worker requests application of active shared-file request R0011 against
exact C0005 code `ad92bbfae62d538f3e52829a269a846688a8e213`, followed by the normal
integrator-owned gates. The worker delivery itself contains none of these 46
shared paths.

Exact request evidence:

- request JSON: `EA1DB32ACE4243F8223696D2A2AFAAB43C24AC97187861D0A07462B722E4C28C`
- sorted path list (46 paths): `C05FA858BF0B5CC3A23F06DEC83F0738780566EA89A172DCA446D4F7129CB901`
- patch: `6C4BCAFDEB8CF97197F7A46D2CAA5BF05F5A1F81A1DAC4284A615B5AD8E9C122`
- postimage ledger: `C7B86B602A290650F8ABEA64281DF02A7C6DF94202C4C3FEB5694566A748D0DE`
- import manifest: `3F25D0F9A5F1BE095870F96ADD1F6A8E3341176668CB770D4AC917796A69D853`
- request plan: `9316DE9A594E7E924CC2213692ED23B49DCBB5BCCD21285642A60D5B0E09E35D`
- reversible forward tree: `1f5daf23bec193dc68c932f854f754a6b6bcb01e`
- reviewed compatibility postimage: `FB8C43F1FB8AB3974B0DF4AB1A646A440BCCDBB519D59E2B01773EFDA5B37D67`

## Required post-R0011 correction

The immutable approved R0011 bytes are preserved exactly. Disposable gate
replay exposed three integrator-owned layout defects in those postimages:

- `NumStability.Algorithms` and `NumStability.Analysis` were sorted by Python's
  case-sensitive order rather than the repository's case-folded import law;
- the retained exact Higham source supplier raises the reviewed
  `NumStability.Algorithms` direct `NumStability.Source.` count from 72 to 73;
- complete public aggregates incorrectly require deliberately unsupported
  `internal` modules to be re-exported, contrary to the internal-tier contract.

After applying exact R0011, the integrator must review and apply
`R0011-CORRECTION.patch`, SHA-256
`DFF0256BCDAB3DA2A3248D85A5A390E345AE5C49D45C6E099E26E315CF03B909`.
It touches exactly four shared/integrator-owned paths and produces:

- `NumStability/Algorithms.lean`:
  `2A3D0971877BDCB5A9FEF1C35F0897242BE75B51E4B12F30348BA4009F5B737F`;
- `NumStability/Analysis.lean`:
  `E7E0DA9DAA5C8E7EC88212BDF68B94A9F55FABBA09E65A23ADB6E7CB410ABD57`;
- `docs/architecture/layout-exceptions.json`:
  `FD58D44C5C9150A3EE2AC4007B4F1D4523735DAFD6CAE93B7D4538E796E96CE6`;
- `tools/architecture/check_layout.py`:
  `FDDED75CF63F0C59EA09E345E4062DBB55E99CA34ABC1289EB2AE5DEEFBF878D`.

The exact corrected shared tree before the worker overlay is
`6c1127df3be9221aa9b51e3b93bfd20ef168f3a6`. The checker change excludes only
modules whose reviewed tier is exactly `internal` from public aggregate
completeness; it does not relax classification, structural-wrapper, import,
source-separation, naming, or legacy-debt gates. None of the three internal
notation leaves is added to a public umbrella, compatibility row, or historical
wrapper. This supplemental correction is a request for integrator review, not
worker approval or integration authority.

On a disposable exact-base checkout, the integrator should replay R0011
forward, verify all 46 postimages and the forward tree, replay it in reverse to
the exact base tree, apply it again, apply the four-path correction, and overlay
the worker delivery. The combined tree must have no canonical-destination
reachability to a historical owner and no reusable/internal reachability into
`NumStability.Source`.

The expected post-overlay classification is 2,860 production modules, 2,770
classified, 90 unclassified, and zero mixed. The remaining reviewed queue is
exactly R09=72 and R10=18. Integration, acceptance, checkpoint state, main push,
and branch retirement remain primary-human/integrator controls and are not
authorized by this request.
