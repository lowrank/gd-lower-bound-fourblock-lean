# Manuscript-to-Lean traceability

| Manuscript item | Lean declaration | Status |
|---|---|---|
| Main theorem (`thm:main`) | `GDLowerBound.mainTheorem`; reductions `mainStatement_of_normalizedFloor`, `mainClaim_of_functional` | complete |
| Projection characterization (`lem:moreau-projection`) | `hasGradientAt_projectionEnvelope`, `convexProj_nonexpansive`, `projectionEnvelope_value` | complete |
| Geometric realization (`thm:geometric-realization`) | `GeometricRealization.geometricRealization`, `chainValueRealization` | complete |
| Functional attainment (`cor:functional-attainment`) | `GDLowerBound.functionalAttainment` | complete |
| Budget equalization (`lem:budget-equalization`) | `RankAnalysis.budgetEqualization` | complete |
| Order-independent matching (`prop:endpoint-matching`) | `Matching.endpoint_matching_bound` | complete |
| Total-weight matching (`lem:total-mass-matching`) | `Matching.Pψ_geomMean_le_total`, `topPath_matching_geomMean_le` | complete |
| Adjacent ranks (`lem:adjacent-rank-relations`) | `oneRankMassRatio`, `massProduct`, `massIncrementBound`, `zetaRecursion` | complete |
| Density bound (`eq:zeta-density-bound`) | `zeta_mul_relativeMassIncrement_le_one` | complete |
| One-step Lyapunov (`lem:one-step-lyapunov`) | `RankAnalysis.oneStepLyapunov` | complete |
| Boundary propagation (`lem:boundary-propagation`) | `RankAnalysis.boundaryPropagation` | complete |
| Bounded rank (`lem:bounded-rank`) | `RankAnalysis.boundedRankPrefix`, `boundedRankPrefix_uniform` | complete |
| Normalized lower bound (`prop:normalized-floor`) | `normalizedLowerBound`, `normalizedFloorTheorem` | complete |
| Scaling (`lem:scaling`) | `SmoothConvexFn.scale`, `scale_gd_trajectory`, `normalizedClaim_to_mainClaim` | complete |
