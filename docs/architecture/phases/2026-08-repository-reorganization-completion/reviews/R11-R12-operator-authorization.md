# Temporary second-operator authorization for R11/R12

Authorized at `2026-08-11T22:53:46Z` by `primary-human` against exact C0001 code base `117aa2bb7e61f41e1531a78452f9f7f6cd5b0771`.

The immutable `claude-lane` assignment is preserved for both R11 and R12. For this one concurrent pair, `codex-local` is explicitly authorized as the lane's temporary second operator solely for B0004/R12; `claude-local` remains the B0003/R11 operator. This authorization does not permit either operator to work another block, change either selector or projection, consume the other branch's postimage, or broaden either branch scope.

The exception is justified by the fresh same-base graph review: 65 versus 3 owners; zero owner/destination equal-or-ancestor overlap; zero direct import, transitive owner reachability, declaration, signature-edge, body-edge, shared direct-consumer, shared direct-module-dependency, and common direct-project-dependency overlap. The only shared request paths are the three primary-human integration controls recorded in `R11-R12-overlap-facts.md`; workers do not edit them.

Activation remains conditional on planned-control CI and exact C0001-based refs/worktrees. The authorization expires automatically when C0002 is recorded or when both B0003 and B0004 become terminal, whichever occurs first. At expiry `codex-local` must be removed from the `claude-lane` operator set; it confers no continuing authority and cannot be reused by a later pair without a fresh primary-human review.
