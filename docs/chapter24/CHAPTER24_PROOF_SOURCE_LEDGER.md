# Higham Chapter 24 Proof-Source Ledger

| Source item | Chapter proof status | External source named by Higham | Local use |
|---|---|---|---|
| Theorem 24.1 | No chapter proof; “See” citation | Van Loan, *Computational Frameworks for the Fast Fourier Transform* (1992), Thm. 1.3.3 | Reconstructed locally: transparent source stages, their ordered matrix product, the bit-reversal permutation, and exact equality to the DFT are all proved without taking the citation as an assumption. |
| (24.3) | Proof printed in chapter | Elementary butterfly/Kronecker norm calculation | Reconstructed locally from Fourier-weight modulus one, exact Gram identities, the Mathlib matrix C*-identity, and explicit entrywise-modulus matrices; all four printed norms are closed. |
| (24.4) | Proof printed in chapter | Computed-weight model (24.2) plus the butterfly structure | Reconstructed locally with explicit computed and perturbation stages; their Gram diagonals give the printed spectral-norm estimate without an assumed matrix bound. |
| Weight methods after (24.2) | Bibliographic accuracy claims only | Van Loan (1992), §1.4 | The local model assumes the printed error certificate; it does not claim a particular weight generator. |
| Theorem 24.2 | Proof printed in chapter | Uses Higham Lemmas 3.6 and 3.1 | Chapter 3 product machinery is reused. A primitive butterfly error lemma and explicit nonvacuous stage-execution contract expose the local obligations; the printed endpoint is derived from them. |
| DFT inverse formula | Stated in prose | Standard Fourier orthogonality | Reuses the complete Chapter 9 roots-of-unity Gram proof and scaled-adjoint inverse. |
| Circulant diagonalization and exact solver | Standard result stated without proof | Standard Fourier convolution identity | Reconstructed locally from cyclic reindexing and the proved primitive-root law; exact four-stage correctness follows without an external assumption. |
| Theorem 24.3 | Attributed result; chapter gives derivation through first order | Yalamov (2000) | Exact (24.8) algebra and an explicit componentwise execution family are proved; its actual `IsBigO` remainder yields the standard `O(u²)` conclusion. |
| Circulant backward-error limitation | Experimental/reference discussion | Higham and Higham (1992), cited as [574] | Not selected as a formal theorem. |
| Problem 24.1 | Exercise, no Appendix solution row | Bailey (1993), Percival (2002) | Excluded optional exercise. |

No claim in the Lean files is closed merely by citing an external reference.
