import HighamBench.P12Definitions

namespace HighamBench

/-- P12-T3: certificate form of Lemma 4's exact ThreeProduct transformation. -/
theorem p12_t3_three_product_exact
    (representable : ℝ → Prop) (x1 x2 x3 : ℝ)
    (tr : P12ThreeProductTrace)
    (h23 : tr.th + tr.tl = x2 * x3)
    (hhigh : tr.s1 + tr.a2 = x1 * tr.th)
    (hlow : tr.a3 + tr.a4 = x1 * tr.tl)
    (ha2 : representable tr.a2)
    (hmergeS : p12Nearest representable (tr.a2 + tr.a3) tr.s2)
    (hmergeTMem : representable (tr.s2 - tr.a2))
    (hmergeT : p12Nearest representable (tr.s2 - tr.a2) tr.t)
    (hmergeRMem : representable (tr.a3 - tr.t))
    (hmergeR : p12Nearest representable (tr.a3 - tr.t) tr.r)
    (hfinalMem : representable (tr.r + tr.a4))
    (hfinal : p12Nearest representable (tr.r + tr.a4) tr.s3) :
    tr.s1 + tr.s2 + tr.s3 = x1 * x2 * x3 := by
  -- PROOF_START
  sorry

end HighamBench
