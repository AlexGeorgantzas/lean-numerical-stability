# R0009 integration-overlap evidence

Base checkpoint: C0006 / `a32095e6e50189f7dcc39312bb4c6a36f421fab5`.

R0009 was applied and validated independently in a disposable C0006 Git index.
Its seven sorted patch paths exactly match the request record. The null-preimage
W11 test root is import-and-docstring-only. Every existing consumer below
changes import lines only: after removing import commands, C0006 and integrated
texts are identical. Blob OIDs are Git SHA-1 object IDs.

| Path | C0006 preimage | Integrated postimage | Class |
| --- | --- | --- | --- |
| `NumStability/Algorithms/LinearSystems/LeastSquares/Equality/Basic.lean` | `d2ab6d9ea8689c3fd9fd0e2b134856e9484c149a` | `227d2fe497fac8bb191785335a4151f4502a1da8` | R0007/R0009 shared consumer, import-only |
| `NumStability/Algorithms/LinearSystems/LeastSquares/GramBasis.lean` | `c8052a308d6f12efed291ff07eccc3098f8f3f48` | `fd95214cb59c58c57f965ae9b441cd521b8f24fb` | accepted consumer, import-only |
| `NumStability/Algorithms/LinearSystems/QR/GramSchmidtPolar.lean` | `9efd74d56bc571d424cec540eb97405e0015eea8` | `c4a111f2617ee6e92ffef4532f5b95fa528cd26f` | accepted consumer, import-only |
| `NumStability/Analysis/Perturbation/LeastSquares/GramBasis.lean` | `77b5699877195fe29ff9184626e9822141bac479` | `43650e9c37a693acdfff430922cbf12784a3526c` | accepted consumer, import-only |
| `NumStability/Source/Higham/Chapter20/Theorem03/QRSolve.lean` | `702d660203a57d55dc0d8e46858e88b333c03485` | `21a5fa03e53cfac48cd6f0abc7274b05cb2f0666` | accepted source consumer, import-only |
| `NumStabilityTest/Import/Compatibility/Algorithms/LeastSquares/CanonicalDependencies.lean` | `4a6412b18db3f23622d1b2c545b3e4c209874abc` | `928fc4000355b78e4ca8d381a7c7af8c588376aa` | shared canonical-dependency test, import-only |
| `NumStabilityTest/Reorganization/W11.lean` | `null` | `c14f410f86dcfd584c6ca2eff772d2cf780fa67f` | import-only test aggregate |

The combined strict-source audit also found one exact W04/W11 import-only
refresh. Each of the 28 reusable W04 destinations below is absent at C0006,
so its immutable W04 delivery blob is the declaration-bearing preimage. Each
integrated postimage deletes only
`import NumStability.Algorithms.RandNLA.Preconditioning`; no import is added
and all non-import text is byte-identical. This removes 28 direct W04-to-W11
historical-facade edges and the resulting 196 strict-source reachability pairs
(28 roots times seven W11 source targets).

| Path | W04 delivery preimage | Integrated postimage | Class |
| --- | --- | --- | --- |
| `NumStability/Algorithms/LinearSystems/Underdetermined/BackwardError/Normwise/UnderdeterminedSolve.lean` | `3f5a73afb7a4f8a8f0c00bc2b23381e59513e809` | `2c0f25ba492b5a3c1f573c0062db266032aaa6be` | W04 import-only refresh |
| `NumStability/Algorithms/LinearSystems/Underdetermined/BackwardError/Rowwise/UnderdeterminedSolve.lean` | `856ff672db847631822d25d00981566aa4d4d070` | `c20b094c7dc209c7199543b133f37a932aebbb1f` | W04 import-only refresh |
| `NumStability/Algorithms/LinearSystems/Underdetermined/Conditioning/Componentwise/Radius.lean` | `a1a681a917f166c5da167bd2dc0f2d0d1b98ccfd` | `48339019fc80700cceb321932de2576856790a2e` | W04 import-only refresh |
| `NumStability/Algorithms/LinearSystems/Underdetermined/Conditioning/Componentwise/UnderdeterminedSolve.lean` | `4683179006a1401daecd0ee8ff4640b7b3f2cf42` | `ecf3565929b3e192dcfac1aa792d4f55337efb18` | W04 import-only refresh |
| `NumStability/Algorithms/LinearSystems/Underdetermined/MinimumNorm/Solvers/UnderdeterminedSolve.lean` | `7c138eb2ab8186661999bc4ca6ee914cebcde2db` | `a60c06a1aac5093673059a6ca16b53d96ad329b8` | W04 import-only refresh |
| `NumStability/Algorithms/LinearSystems/Underdetermined/MinimumNorm/Specifications/UnderdeterminedSolve.lean` | `ced8d78f1e443fefb4166a7ab537d3f6524a92b5` | `cae3af7378f7a5bc7817d4331ec23727492e4fd7` | W04 import-only refresh |
| `NumStability/Algorithms/LinearSystems/Underdetermined/Perturbation/Componentwise/Radius.lean` | `4b7ffc22ce5c3f3263733682156408660d19ee4d` | `611e090fa10443f439370f00f4032699c93ef3e3` | W04 import-only refresh |
| `NumStability/Algorithms/LinearSystems/Underdetermined/Perturbation/Componentwise/UnderdeterminedSolve.lean` | `f1ee67f6730af251f22e885268666b47f0c08840` | `8d5be8457af7f993a3711a1ac7aa3fc55810df42` | W04 import-only refresh |
| `NumStability/Algorithms/LinearSystems/Underdetermined/Perturbation/FixedRadius/Radius.lean` | `ebbc63c2f9ac3a78a04fb8111e386ba15c848c64` | `bad6c697d55fdce3f208d66cdb06f6da4d573903` | W04 import-only refresh |
| `NumStability/Algorithms/LinearSystems/Underdetermined/Projectors/ComplementNorm/ProjectorNorm.lean` | `4febcb205a4abc1ed0abfd972a58d097fc3439d1` | `2a2012a4c330e70edb8d65efa09eee0f8373fb8b` | W04 import-only refresh |
| `NumStability/Algorithms/LinearSystems/Underdetermined/QR/Foundations/UnderdeterminedSolve.lean` | `f863ad7dd1e727552ee07694cbfe4cbd8a6fa699` | `8486a99d4ddf9b2d0b45eb58757b11abff5e6e66` | W04 import-only refresh |
| `NumStability/Algorithms/LinearSystems/Underdetermined/QR/Givens/BackwardError/Core.lean` | `b8a6358111f98df2ced00d912e846a1efbf4095f` | `e73e48a67818448b43d09142d860edeb9a851ab8` | W04 import-only refresh |
| `NumStability/Algorithms/LinearSystems/Underdetermined/QR/Givens/StoredReplay/Closure.lean` | `f78c31e3caa7198d49f151abb533e47f1f9d3bac` | `544e87447d31c51de52d683c9e2df2ac66b664be` | W04 import-only refresh |
| `NumStability/Algorithms/LinearSystems/Underdetermined/QR/Givens/StoredReplay/RoundedReplay.lean` | `3b1b0881308d02763bd5c81bd307bb3dc8c30d8d` | `fa1882983fbda7b37861c0b377c23281e7bc7243` | W04 import-only refresh |
| `NumStability/Algorithms/LinearSystems/Underdetermined/QR/ModifiedGramSchmidt/CorrectedRecurrence/Core.lean` | `3a343143e61b92d78f2b7027edb1f80a82f32b2b` | `3eb6688a2bbcbd64c8cae401705817128625eebe` | W04 import-only refresh |
| `NumStability/Algorithms/LinearSystems/Underdetermined/QR/ModifiedGramSchmidt/RoundedReplay/RoundedReplay.lean` | `0ed255bbb50e17a042f83b1a89ee07c980415715` | `ba002452aab5f890984ca100ee1535471b7e2c70` | W04 import-only refresh |
| `NumStability/Algorithms/LinearSystems/Underdetermined/RankStability/FullRowRank/UnderdeterminedSolve.lean` | `f015ebf5f7dab87c83bf169190c859aebe214f65` | `4dfac28d715ada6d045bf31346db5b6ed928ca84` | W04 import-only refresh |
| `NumStability/Algorithms/LinearSystems/Underdetermined/SeminormalEquations/ForwardError/ActualOutput.lean` | `0fa2f0b28d3dd27d920325d134c297b4a2934578` | `76ec3be0431d00fcf272a4ff49458110b2e4e052` | W04 import-only refresh |
| `NumStability/Algorithms/LinearSystems/Underdetermined/SeminormalEquations/ForwardError/Forward.lean` | `166592ac02655c04a526865537b808a75846130b` | `cd0e12e7fc981efa8ada9250845db1287932d1cc` | W04 import-only refresh |
| `NumStability/Algorithms/LinearSystems/Underdetermined/SeminormalEquations/ForwardError/RemainderBounds.lean` | `442cc9c0bfb81b43ab1048c9435349f1b4ab9d0d` | `9fde8028193d71b82694f00b6dadf8d54f59bba0` | W04 import-only refresh |
| `NumStability/Algorithms/LinearSystems/Underdetermined/SeminormalEquations/ForwardError/UnderdeterminedSolve.lean` | `4ff057f7757e9432b5de4609eac86102f20e31f2` | `da7856c9cb1bcb61c4945c613694b095b9519a43` | W04 import-only refresh |
| `NumStability/Algorithms/LinearSystems/Underdetermined/SeminormalEquations/HouseholderClosure/Closure.lean` | `a96910eb55eaf2a98ad81dad345f82f7ea13015d` | `e99fd65835b77e3bb248cdd8b255132cc596c1cf` | W04 import-only refresh |
| `NumStability/Algorithms/LinearSystems/Underdetermined/SeminormalEquations/HouseholderClosure/Uniform.lean` | `71d603d5ce8b5b500f36b3fe0ffd75083a1dac21` | `41290e05db5784032832f633a0e8c8956f71c276` | W04 import-only refresh |
| `NumStability/Algorithms/LinearSystems/Underdetermined/SeminormalEquations/QRTransfer/EnvelopeTransfer.lean` | `53560a11d956caba9df984eacde4ef0a0782e4ce` | `d20717df9197024847cb25652ca7f138166c51da` | W04 import-only refresh |
| `NumStability/Algorithms/LinearSystems/Underdetermined/SeminormalEquations/QRTransfer/QRMajorant.lean` | `dd39f161adb93959c40f72dee2a8dc01545c2aae` | `44824e25c137aec44dd7324bb7165d37a0a49a21` | W04 import-only refresh |
| `NumStability/Algorithms/LinearSystems/Underdetermined/SeminormalEquations/QRTransfer/Signed.lean` | `e38d68c1041205fccaa7a0517a0a68eddb7a82c5` | `0e0c1efaafb5f254b87477ee85cf2cc3004dfcc7` | W04 import-only refresh |
| `NumStability/Algorithms/LinearSystems/Underdetermined/SeminormalEquations/TriangularSolves/EnvelopeTransfer.lean` | `273edd13453a99bda12d9284e27b3270ab27a1d3` | `10201b74b6ca87a7658e89ded09d1f0fb7ea6c7c` | W04 import-only refresh |
| `NumStability/Algorithms/LinearSystems/Underdetermined/SeminormalEquations/TriangularSolves/UnderdeterminedSolve.lean` | `cb6fe9eb25451f723ec2ec364b734d8e1261f4f4` | `eb581610e24b3bd7ac94228cc3629b4536374d1f` | W04 import-only refresh |

R0009 intersects R0007 at the Equality consumer, `NumStabilityTest.lean`,
`docs/architecture/layout-exceptions.json`, and `docs/architecture/tiers.json`;
it intersects R0008 only at the latter three paths. The combined Equality
postimage was produced atomically. Source reachability additionally required an
explicit import of the Equation 09 endpoint after canonical retargeting removed
its accidental historical-facade route; the request therefore records eleven,
not ten, direct W11 source imports.

The preserved `NumStability.Algorithms.RandNLA` aggregate, LSQRSolve import,
W06 protected imports, and three accepted MatrixInversion leaves remain
unchanged. The historical MatrixInversion umbrella was not restored.
