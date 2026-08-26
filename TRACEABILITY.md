# Manuscript-to-Lean traceability

| Manuscript item | Lean declaration | Status |
|---|---|---|
| Original main theorem (`thm:main`) | `GDLowerBound.mainTheorem`; reductions `mainStatement_of_normalizedFloor`, `mainClaim_of_functional` | complete |
| Exact-envelope improved theorem (`p > 1.8565576222695287`) | `FourBlock.exactEnvelopeMainTheorem`, `exactEnvelopeNormalizedLowerBound` in `FourBlock/ExactEnvelopeNormalized.lean` | complete |
| All-rank exact-envelope cutoff | `chronologicalEdgeKernelProduct_lt_one_of_zeta_le`, `quarter_div_unresolvedMass_lt_functional_of_zeta_le`, `criticalCutoffConditions_of_no_small_state` in `FourBlock/AllRankCutoff.lean` | complete |
| Sharp four-block rigidity budgets | `scheduleSharpRigidityBudget` in `FourBlock/SharpScheduleDrift.lean`; `scheduleMomentRigidityBudget` in `FourBlock/MomentRigidity.lean` | complete local/global-budget input |
| Fixed-dilation endpoint sampling | `fixedDilationHarmonicSample_le` in `FourBlock/FixedDilationSampling.lean`; `endpointDefect_fixedDilationHarmonicSample`, `squareDeviation_fixedDilationHarmonicSample` in `FourBlock/FixedDilationApplications.lean` | complete with explicit finite errors |
| Finite dilation-defect upper expansion | `sub_half_sq_le_log_one_add`, `log_ratio_le_adjacentHarmonic_add_inv`, `dilationBlockH_upper` in `FourBlock/BlockDefectUpper.lean` | complete with explicit finite errors |
| Middle-block Fubini/occupancy identity | `middleBlockOccupancy`, `sum_middleBlocks_eq_occupancy` in `FourBlock/MiddleBlockOccupancy.lean` | exact rearrangement and support complete |
| Interior occupancy asymptotics | `middleBlockOccupancy_two_sub_log_abs_le`, `middleBlockOccupancy_three_sub_log_abs_le` in `FourBlock/MiddleBlockOccupancyAsymptotic.lean` and `FourBlock/MiddleBlockOccupancyAsymptoticThree.lean` | explicit `6/n` and `8/n` errors complete |
| Uniform boundary occupancy and signed deficit | `middleBlockOccupancy_two_le_log_add`, `middleBlockOccupancy_three_le_log_add`, and weighted variants in `FourBlock/MiddleBlockOccupancyUniversal.lean` and `FourBlock/MiddleBlockOccupancyWeighted.lean` | complete |
| Common-rank occupancy summation | `sum_middleBlocks_two_eq_common_occupancy`, `sum_two_occupancy_weighted_deficit_le` and three-block analogues in `FourBlock/MiddleBlockOccupancySummation.lean` | complete |
| Averaged dilation and schedule energy | `averagedDilationBlock_two_upper`, `averagedDilationBlock_three_upper` in `FourBlock/AveragedDilationBlocks.lean`; `averagedScheduleEnergy_upper` in `FourBlock/AveragedScheduleEnergy.lean` | complete with named finite errors |
| Common finite rigidity budgets | `commonMomentRigidityBudget`, `commonSharpRigidityBudget` in `FourBlock/CommonRigidityBudgets.lean` | complete, including endpoint shift |
| Normalized four-block composition | `normalizedAveragedScheduleEnergy_lt_robustLocalGap` in `FourBlock/NormalizedAveragingComposition.lean` | complete conditional on explicit window mean-growth and error-margin hypotheses |
| Averaged good-scale extraction | `normalizedAveraging_forces_small_scale` in `FourBlock/AveragedGoodScale.lean` | complete conditional on the same window hypotheses and the certified exponential threshold |
| Schedule-independent rigidity error | `normalizedErrorBudget_le_window`, `fourBlockWindowError` in `FourBlock/FiniteWindowRigidityErrors.lean` | complete |
| Dyadic harmonic window | `dyadic_averagingHarmonicWeight_lower`, `exists_dyadicDepth_harmonicWeight_gt` in `FourBlock/FiniteWindowHarmonic.lean` | complete with rational `log 2` certificate |
| Endpoint mass to mean growth | `massExponent_le_effectiveMeanGrowth_of_log_ratio` in `FourBlock/FiniteWindowMeanGrowth.lean` | complete |
| Reciprocal-square sampling errors | `controlAveragingError_le_inv`, `dilationBlockUpperRemainder_le_inv` in `FourBlock/FiniteWindowSamplingBounds.lean` | complete `O(1/M)` bounds |
| Dyadic endpoint sampling | `endpointDefectSamplingError_dyadic_le`, `squareDeviationSamplingError_dyadic_le` in `FourBlock/FiniteWindowEndpointSamplingBounds.lean` | complete `O(R/M)` bounds, uniform in dilation |
| Occupancy boundary bands | `sum_twoOccupancyFiniteError_le`, `sum_threeOccupancyFiniteError_le` in `FourBlock/FiniteWindowOccupancyBounds.lean` | complete fixed-ratio bounds |
| Complete dyadic schedule error | `normalizedScheduleAveragingError_dyadic_le` in `FourBlock/FiniteWindowScheduleErrorBounds.lean` | complete |
| Master dyadic window bound and selection | `fourBlockWindowError_dyadic_le`, `exists_dyadicFourBlockWindow` in `FourBlock/FiniteWindowDyadicError.lean` and `FourBlock/FiniteWindowDyadicSelection.lean` | complete; finite-margin hypothesis is existentially discharged |
| Endpoint-growth good scale | `finiteWindowEndpointGrowth_forces_small_scale` in `FourBlock/FiniteWindowEndpointGoodScale.lean` | complete conditional on explicit window-error and endpoint-ratio hypotheses |
| Uniform dyadic tail | `exists_uniform_dyadicFourBlockWindow` in `FourBlock/FiniteWindowDyadicUniform.lean` | complete for all sufficiently large depths and bases |
| Exact dyadic growth dichotomy | `dyadicEndpointGrowthThreshold_le`, `finiteWindowDyadic_functional_or_massRatio_lt`, and `exists_uniform_finiteWindowDyadic_dichotomy` in `FourBlock/FiniteWindowDyadicGrowthThreshold.lean` and `FourBlock/FiniteWindowDyadicDichotomy.lean` | complete with exact `log 2` coefficient |
| Maximal-window propagation | `exists_maximalDyadicDepth`, `unresolvedMass_le_two_pow_gap_mul_of_cutoff`, `unresolvedMass_lt_dyadicTerminalMassConstant`, and `unresolvedMass_le_dyadicShortMassConstant` in the `FiniteWindow*Propagation.lean` modules | complete |
| Terminating global scan | `dyadicScanStep` and `dyadicScan_normalizedFunctional` in `FourBlock/FiniteWindowDyadicScan.lean` and `FourBlock/FiniteWindowDyadicGlobal.lean` | complete by well-founded recursion on the remaining rank gap |
| Four-block exact `1.8288` normalized floor and `p > 1.8288` main theorem | `sharperNormalizedLowerBound` and `sharperMainTheorem` in `FourBlock/SharperNormalized.lean` | complete end-to-end, no `sorry` |
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
