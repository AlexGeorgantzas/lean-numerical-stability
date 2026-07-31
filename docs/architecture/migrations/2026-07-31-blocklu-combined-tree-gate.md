# BlockLU combined-tree acceptance gate (2026-07-31)

The Phase 11B2 dependency stream is the correct frozen input for the BlockLU
source split, but it is not a valid whole-repository baseline for the final
combined tree. QR, Chapter 9, and Chapter 20 subsequently moved unrelated
declarations and therefore changed the full stream's ownership-encoded names.
Running the historical whole-stream `post` comparison against that final tree
reports thousands of unrelated rows (`missing=23838, extra=23878`). Treating
that result as a BlockLU failure would be incorrect; treating it as a waiver
would also be incorrect.

The resolution is a compositional acceptance contract:

1. The historical BlockLU source-split evidence remains frozen and exact. Its
   clean candidate stream is the prior checkpoint with SHA-256
   `AC7DB49BEA92D0FFA4753B43851C02FE0306CF8CC4A5EA8B593DE735CCE6E6F5`,
   compared with the immutable Phase 11B2 stream
   `FD37F73D83F0206E40291576E1F9496185F09C21928ABED147B5CE2A6EF83AED`.
2. Final-tree validation uses `--mode post-combined`. It retains the frozen
   Phase 11B2 hash, the reviewed 1,990-row ownership manifest, all private
   rewrite checks, the acyclic destination graph, and the structural-module
   checks.
3. Its graph comparison is limited to the exact typed edge projection
   incident to those 1,990 selected declarations. Every declared endpoint is
   canonicalized through its module-encoded private identity; public and
   unknown compiler endpoints remain exact. Thus an unrelated later move is
   normalized, while any BlockLU declaration or incident semantic-edge change
   still fails.
4. The only permitted graph delta remains the four individually reviewed
   `private-helper-proof-inlined` body edges. No general difference allowlist
   was added.

The final combined candidate stream is
`benchmark-results/architecture/integrator-2026-07-30-declarations.tsv`,
SHA-256
`B1BE6E856F457FF5AECE84092E6008B4BAD9D5035278AF331BA317A090E2E70C8`.
The combined gate reports 31,311 baseline incident edges and 31,307 candidate
incident edges, with exactly the four reviewed body-edge drops and no other
delta.

The reproducible final-tree command is:

```text
python3 tools/architecture/check_blocklu_phase12_ownership.py \
  --mode post-combined \
  --dependency-tsv benchmark-results/architecture/integrator-2026-07-30-declarations.tsv \
  --baseline-tsv /home/mymel/lean/reorg/integrator-blocklu/recovery-evidence/phase11b2-format2.tsv \
  --manifest docs/architecture/declaration-ownership/blocklu-phase12-v2.tsv \
  --private-rewrites docs/architecture/declaration-ownership/blocklu-phase12-private-rewrites.tsv \
  --reviewed-body-edge-drops docs/architecture/declaration-ownership/blocklu-phase12-reviewed-body-edge-drops.tsv \
  --expected-manifest-sha256 90F28D568A611035DE20839F2C30CB2800B75F2FC1DF2CE1373E9FFDD3D11287 \
  --project-root .
```
