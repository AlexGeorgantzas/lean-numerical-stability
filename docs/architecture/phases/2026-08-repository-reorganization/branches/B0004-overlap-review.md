# B0004 C0004 activation and W03/W05 overlap review

Branch base checkpoint: `C0004`

Branch base commit: `b56f609f3bf66b5d7d0b677567cce82fee0c275b`

Wave: `W03`

This review is pinned to C0004 inventory SHA-256
`26706ADEF2B255BD929572C8EC325E7B1A5F79906929A23DBEC26093D657B463`
and combined format-2 baseline SHA-256
`CCF7ACAE1D9306C03D79495B548E598C9A3132DC99A98C4212219A453CB27FA8`.
The immutable W03 selector contains exactly 26 production owners and has
SHA-256
`3BD8827FD306E748AC4150AFC7881FD229BFF10096BDF0C70E9BDDCDBFA36430`.
Projection P0005 has SHA-256
`7B5A07528409CCCDC8B45F94B8F5FC977A2749601F8ED2D6B18D161CD27838B7`
and freezes 1,034 declarations, 8,056 signature edges, 11,608 body/proof
edges, and 11,932 union edges. The projection checker artifact has SHA-256
`29691CD63DB83A156247EA2C627407F4E90D127128A945B5AF97D014E11AB443`.

Every one of B0004's 32 production destination prefixes and its two worker
evidence prefixes has zero tracked descendants at C0004. The check was
case-insensitive as well as exact. The prefixes are pairwise non-overlapping,
do not intersect a historical owner, phase-shared path, forbidden path, or
other C0004 production path, and authorize only semantic child directories;
no Chapter 10, Chapter 11, Cholesky, analysis, or source parent tree is
authorized wholesale.

The declaration audit required four narrow exceptions to an otherwise
Cholesky/Chapter-10 routing. `CholeskyIndefinite` contains reusable
symmetric-indefinite Block-LDLT/Aasen material and 13 Chapter 11 printed
endpoints. `CholeskyNonsym` contains no-pivot LU for matrices with a positive
definite symmetric part. `Ch10Ch14Lemma66Op2Bridge` spans a reusable matrix
norm result and exact Chapter 6, 10, and 14 endpoints. The `HighamMathias*`
owners are Chapter 10 equation 10.29, not Chapter 11. The resulting exceptional
prefixes are equally narrow, vacant, and semantically reviewed; placing these
declarations under Cholesky or Chapter 10 merely to reduce the prefix count
would violate the repository's reusable/source boundary.

P0005 contains 93 private declarations. Private names and their reverse
dependency closures encode the historical defining module, so B0004 permits
declaration-bearing historical facades and does not promise 26 pure import
shims. In particular, `Ch10ComplexPositiveDefiniteSourceClosure` owns 52 of
those private declarations. The worker must preserve all public names and may
retain pinned declarations at their historical owners.

## Cross-wave proof

W03 and W05 have zero exact owned-path overlap and zero ancestor/descendant
destination-prefix overlap. Parsing the C0004 imports finds zero direct imports
from a W03 owner to a W05 owner and zero in the reverse direction. Filtering
the hash-verified C0004 combined declaration graph finds zero W03-to-W05 and
zero W05-to-W03 signature edges, and zero body/proof edges in either direction.

The sole common direct downstream importer of both owner sets is
`NumStability/Algorithms.lean`. It, the other root/family/chapter aggregates,
root tests, manifests, and all phase controls remain integrator-owned and are
forbidden to both workers. This shared downstream aggregate is an integration
obligation, not worker ownership and not evidence of a cross-wave dependency.

## Integration obligations

- Retarget the 34 non-owner C0004 files that directly import W03 historical
  owners only during integration, after reviewing which canonical leaf each
  consumer needs.
- Create or update family, chapter, source, global, and test umbrellas only in
  the integration worktree.
- Preserve old imports and declarations, and require canonical-only and
  old-only focused tests from the worker.
- Rerun P0005, strict-source, layout, compatibility, provenance, full build,
  full tests, and a fresh combined baseline before accepting M03.

No W03 source migration is part of this activation record.
