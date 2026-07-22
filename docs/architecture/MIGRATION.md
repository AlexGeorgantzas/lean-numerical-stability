# Book-formalization migration gates

This is the executable migration sequence for NumStability.  A gate is complete
only when its stated evidence is checked into the repository or recorded by CI.

1. **Current baseline.** Regenerate and version the architecture and build
   report at the exact migration commit using tracked tooling.
2. **Safety net.** Track CI, a test target, API/import smoke tests, and clean and
   incremental benchmark tooling.
3. **Architecture contract.** Define API tiers, dependency directions,
   placement rules, and compatibility policy in `ARCHITECTURE.md`.
4. **Explicit entry points.** Add `Core`, `Higham`, and `All` without changing
   the historical meaning of `import NumStability`.
5. **Separate graphs.** Generate module-import, declaration-signature, and
   proof-body graphs; compute candidate communities and validate them against
   mathematical subject boundaries.
6. **Endpoint pilot.** Review the report's seven all-leaf modules, plus any
   additional endpoints exposed by the corrected declaration extractor;
   classify them without treating endpoint status as deletion evidence.
7. **Performance pilot.** Profile `NonrandomRounding`; change it only when the
   measured elaboration, tactic, or import bottleneck supports a specific fix.
8. **Reusable-family pilot.** Reorganize a contained family such as summation
   with precise imports, compatibility modules, tests, and modern visibility
   where the dependency-closed family permits it. Retain legacy `import`
   syntax when introducing `module` / `public import` would force a repository-
   wide module-system migration.
9. **Semantic source extraction.** Move book-specific aliases, corrections,
   capstones, discrepancies, and cross-chapter glue by meaning and provenance.
10. **Outlier refactoring.** Address the measured compilation queue using
    semantic seams, rebuild fanout, and stable interfaces rather than size alone.
11. **Physical-target decision.** Create a separate source library only if the
    evidence gates in `ARCHITECTURE.md` justify it; otherwise record the decision.
12. **Compatibility release.** Remove forwarding paths only in a planned
    breaking release, then rerun every baseline, build, test, lint, and API gate.

The migration is incremental.  Do not combine mass file moves, declaration
renames, visibility changes, and compatibility removal in one change.
