# B0005 C0004 activation and W03/W05 overlap review

Branch base checkpoint: `C0004`

Branch base commit: `b56f609f3bf66b5d7d0b677567cce82fee0c275b`

Wave: `W05`

This review is pinned to C0004 inventory SHA-256
`26706ADEF2B255BD929572C8EC325E7B1A5F79906929A23DBEC26093D657B463`
and combined format-2 baseline SHA-256
`CCF7ACAE1D9306C03D79495B548E598C9A3132DC99A98C4212219A453CB27FA8`.
The immutable W05 selector contains exactly 10 production owners and has
SHA-256
`19865961584C60D54FF5D054541D32E698F69545465BFDD869D11CC6B4A8CAEF`.
Projection P0006 has SHA-256
`6A15BC343C895BCE66A92B09EC333300CA842BEC249DDF2DC723D0832098FFB5`
and freezes 921 declarations--121 definitions and 800 theorems--with 8,562
signature edges, 6,894 body/proof edges, and 11,020 union edges. The projection
checker artifact has SHA-256
`29691CD63DB83A156247EA2C627407F4E90D127128A945B5AF97D014E11AB443`.

Every one of B0005's 14 production destination prefixes and its two worker
evidence prefixes has zero tracked descendants at C0004. The check was
case-insensitive as well as exact. The prefixes are pairwise non-overlapping,
do not intersect a historical owner, phase-shared path, forbidden path, or
other C0004 production path, and authorize only reviewed children below the
new matrix-equations family, existing analysis families, and exact Chapter 16
and Chapter 18 sections. No broad parent tree is authorized.

The declaration audit separates the nine generic spectral results in
`InverseOpNorm2` from its three Sylvester/Lyapunov bridge results. The generic
results route to `Analysis/SingularValues/InverseBounds/`; the bridges route to
Sylvester conditioning. The three reusable Schur/invariant-subspace owners
contain 89 declarations and no H16/H18-prefixed names, so they route to
`Analysis/LinearOperators/Schur/`, with source correspondence surfaces beneath
exact Chapter 16 and Chapter 18 sections. Stable `SectionNN` directories and
`EquationNN` leaves are required by the naming contract.

`Higham16` contains three private theorems whose union reverse closure contains
138 declarations. B0005 therefore permits a declaration-bearing historical
facade and does not promise ten pure import shims. Private names and their
closure must remain at the historical owner while movable declarations are
relocated without renaming.

## Cross-wave proof

W05 and W03 have zero exact owned-path overlap and zero ancestor/descendant
destination-prefix overlap. Parsing the C0004 imports finds zero direct imports
from a W05 owner to a W03 owner and zero in the reverse direction. Filtering
the hash-verified C0004 combined declaration graph finds zero W05-to-W03 and
zero W03-to-W05 signature edges, and zero body/proof edges in either direction.

The sole common direct downstream importer of both owner sets is
`NumStability/Algorithms.lean`. It, `NumStability/Algorithms/Sylvester.lean`,
the other root/family/chapter aggregates, root tests, manifests, and all phase
controls remain integrator-owned and are forbidden to both workers. This
shared downstream aggregate is an integration obligation, not worker
ownership and not evidence of a cross-wave dependency.

## Integration obligations

- Retarget `NumStability/Analysis/SemiconvergentExistenceFull.lean`, accepted
  through W02, to the reviewed W05 canonical Schur leaf during integration.
- Leave the 12 W06 consumers carrying 13 direct W06-to-W05 imports outside
  worker scope; retarget them only after M05 is accepted and W06 is activated.
- Create or update family, chapter, source, global, and test umbrellas only in
  the integration worktree.
- Preserve old imports and declarations, and require canonical-only and
  old-only focused tests from the worker.
- Rerun P0006, strict-source, layout, compatibility, provenance, full build,
  full tests, and a fresh combined baseline before accepting M05.

No W05 source migration is part of this activation record.
