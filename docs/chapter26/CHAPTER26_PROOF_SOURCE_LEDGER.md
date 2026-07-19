# Chapter 26 Proof-Source Ledger

Proof-source acquisition was not triggered for the selected core. Equations
(26.5)-(26.6) are proved directly by field algebra and `Real.sq_sqrt`; the
interval endpoint theorems are proved directly from ordered-field lemmas.

| Selected claim | Source proof | External source | Route/status | Local closure |
|---|---|---|---|---|
| (26.5)-(26.6) | derivation in chapter | none | formalized directly | `cubicWCubePlus_quadratic`, `cubicWCubeMinus_quadratic`, `stableCubicWCube_quadratic` |
| Section 26.4 endpoint operations | direct formulas | none | formalized directly | `add_contains`, `sub_contains`, `mul_contains`, `reciprocal_contains`, `div_contains` |
| Section 26.4 dependency examples | direct endpoint evaluation | none | formalized directly | `dependency_sub_example`, `dependency_div_example` |
| Section 26.4 outward-rounded computed enclosure | explanatory prose | repository `FloatingPointFormat` directed selectors | formalized for finite real endpoints; endpoint range separates the IEEE infinity layer | `outwardRounded_contains`, `outwardAdd_contains`, `outwardSub_contains`, `outwardMul_contains`, `outwardDiv_contains` |
