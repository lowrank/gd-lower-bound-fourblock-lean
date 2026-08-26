import GDLowerBound.FourBlock.SmallPrefixKernel
import GDLowerBound.FourBlock.CutoffMatchingDichotomy

/-!
# The small reciprocal-prefix branch forces a small exact score

This module closes the `r < 1/20` case left by the finite matching
perturbation estimate.  Four-block concavity compresses the exact score to
the coupled scalar kernel.  The explicit `O(m⁻²)` scale and coordinate
errors fit inside the certified `10⁻⁷` buffers at `m ≥ 2000`.
-/

namespace GDLowerBound.FourBlock

open GDLowerBound.Schedule GDLowerBound.RankAnalysis

noncomputable section

/-- A second Jensen step compresses the two four-block kernels to the total
mass split at the half-prefix coordinate `r`. -/
theorem outsideInLogScore_average_le_splitKernel {m : ℕ} (hm : 0 < m)
    (w : Fin (2 * (m + m)) → ℝ) (hw : ∀ i, 0 < w i) :
    outsideInLogScore (m + m) w / (2 * m) ≤
      logKernel (4 * fourBlockZ w * fourBlockR w)
        (4 * fourBlockZ w * (1 - fourBlockR w)) := by
  have hscore := outsideInLogScore_average_le_fourBlockMatching hm w hw
  have hq1 : 0 < finMean (outsideQuarterOne w) := by
    unfold finMean
    exact div_pos (quarterSum_pos hm _ (fun i ↦ hw _)) (by positivity)
  have hq2 : 0 < finMean (outsideQuarterTwo w) := by
    unfold finMean
    exact div_pos (quarterSum_pos hm _ (fun i ↦ hw _)) (by positivity)
  have hq3 : 0 < finMean (outsideQuarterThree w) := by
    unfold finMean
    exact div_pos (quarterSum_pos hm _ (fun i ↦ hw _)) (by positivity)
  have hq4 : 0 < finMean (outsideQuarterFour w) := by
    unfold finMean
    exact div_pos (quarterSum_pos hm _ (fun i ↦ hw _)) (by positivity)
  have hconc := average_logKernel_le_logKernel_midpoint hq1 hq4 hq2 hq3
  calc
    outsideInLogScore (m + m) w / (2 * m) ≤
        fourBlockMatching (fourBlockZ w) (fourBlockA w)
          (fourBlockR w) (fourBlockS w) := hscore
    _ = (logKernel (finMean (outsideQuarterOne w))
            (finMean (outsideQuarterFour w)) +
          logKernel (finMean (outsideQuarterTwo w))
            (finMean (outsideQuarterThree w))) / 2 := by
      rw [finMean_outsideQuarterOne_eq hm hw,
        finMean_outsideQuarterTwo_eq hm hw,
        finMean_outsideQuarterThree_eq hm hw,
        finMean_outsideQuarterFour_eq hm hw]
      rfl
    _ ≤ logKernel
          ((finMean (outsideQuarterOne w) +
            finMean (outsideQuarterTwo w)) / 2)
          ((finMean (outsideQuarterFour w) +
            finMean (outsideQuarterThree w)) / 2) := hconc
    _ = logKernel (4 * fourBlockZ w * fourBlockR w)
          (4 * fourBlockZ w * (1 - fourBlockR w)) := by
      rw [finMean_outsideQuarterOne_eq hm hw,
        finMean_outsideQuarterTwo_eq hm hw,
        finMean_outsideQuarterThree_eq hm hw,
        finMean_outsideQuarterFour_eq hm hw]
      congr 1 <;> ring

theorem scheduleCoordinateError_le_smallPrefixBuffer
    {T m : ℕ} {h : StepSchedule T} (hm : 2000 ≤ m)
    (hzlo : (centralThetaLowerQ : ℝ) ≤
      zetaState h (2 * (m + m))) :
    scheduleCoordinateError h m ≤ (1 / 10000000 : ℝ) := by
  have hmR : (2000 : ℝ) ≤ m := by exact_mod_cast hm
  have hz04 : (2 / 5 : ℝ) ≤ zetaState h (2 * (m + m)) := by
    have hconst : (2 / 5 : ℝ) ≤ (centralThetaLowerQ : ℝ) := by
      norm_num [centralThetaLowerQ]
    exact hconst.trans hzlo
  have hfirst : (7999 : ℝ) ≤ 4 * m - 1 := by nlinarith
  have hsecond : (6400 : ℝ) ≤
      8 * m * zetaState h (2 * (m + m)) := by
    have hm8 : (16000 : ℝ) ≤ 8 * m := by nlinarith
    nlinarith [mul_le_mul hm8 hz04 (by norm_num : (0 : ℝ) ≤ 2 / 5)
      (by positivity : (0 : ℝ) ≤ 8 * m)]
  have hden : (10000000 : ℝ) ≤
      (4 * m - 1) * (8 * m * zetaState h (2 * (m + m))) := by
    have hprod := mul_le_mul hfirst hsecond (by norm_num : (0 : ℝ) ≤ 6400)
      (by nlinarith : (0 : ℝ) ≤ 4 * m - 1)
    norm_num at hprod ⊢
    linarith
  have hden0 : 0 <
      (4 * (m : ℝ) - 1) *
        (8 * m * zetaState h (2 * (m + m))) := by
    linarith
  have herr : scheduleCoordinateError h m =
      1 / ((4 * (m : ℝ) - 1) *
        (8 * m * zetaState h (2 * (m + m)))) := by
    unfold scheduleCoordinateError
    norm_num [Nat.cast_mul, Nat.cast_add]
    field_simp
    ring
  rw [herr, div_le_iff₀ hden0]
  norm_num
  linarith

/-- Below the half-prefix threshold, the exact score necessarily falls in
the uniform small branch. -/
theorem smallExactMatchingScoreRank_of_prefixR_lt
    {T m : ℕ} {h : StepSchedule T} (hh : IsNonnegativeSchedule h)
    (hm : 2000 ≤ m) (hq : 2 * (m + m) ≤ longCount h)
    (hzlo : (centralThetaLowerQ : ℝ) ≤
      zetaState h (2 * (m + m)))
    (hzhi : zetaState h (2 * (m + m)) ≤ (119 / 250 : ℝ))
    (hrsmall : schedulePrefixR h m < (1 / 20 : ℝ)) :
    SmallExactMatchingScoreRank h m := by
  have hm0 : 0 < m := by omega
  let w := scheduleFourBlockWeights h hq
  have hw : ∀ i, 0 < w i := scheduleFourBlockWeights_pos hh hm0 hq
  have hzW0 : 0 < fourBlockZ w := by
    unfold fourBlockZ
    exact div_pos (fourBlockTotal_pos hm0 hw) (by positivity)
  have hrW0 : 0 < fourBlockR w := by
    unfold fourBlockR
    have h1 := quarterSum_pos hm0 (outsideQuarterOne w) (fun i ↦ hw _)
    have h2 := quarterSum_pos hm0 (outsideQuarterTwo w) (fun i ↦ hw _)
    exact div_pos (add_pos h1 h2) (fourBlockTotal_pos hm0 hw)
  have hzSandwich := scheduleFourBlockZ_sandwich hh hm0 hq
  have haux := scheduleFourBlock_aux_le_score_cap hm
  have haux' :
      1 / ((8 * (m : ℝ)) * (((2 * (m + m) : ℕ) : ℝ) - 1)) ≤
        (1 / 100000000 : ℝ) := by
    convert haux using 1 <;> norm_num [Nat.cast_add]
  have hzW : fourBlockZ w ≤ (smallPrefixZCapQ : ℝ) := by
    dsimp only [w] at hzSandwich ⊢
    norm_num [smallPrefixZCapQ] at ⊢
    linarith
  have hclose := (scheduleFourBlockCoordinates_close hh hm0 hq).2.1
  have herr := scheduleCoordinateError_le_smallPrefixBuffer hm hzlo
  have hdiff : fourBlockR w - schedulePrefixR h m ≤
      scheduleCoordinateError h m := by
    exact (le_abs_self _).trans hclose
  have hrW : fourBlockR w ≤ (smallPrefixRCapQ : ℝ) := by
    dsimp only [w] at hdiff ⊢
    norm_num [smallPrefixRCapQ] at ⊢
    linarith
  have hscore := outsideInLogScore_average_le_splitKernel hm0 w hw
  have hkernel := splitLogKernel_le_smallPrefixCap hzW0 hzW hrW0 hrW
  have hsmall : outsideInLogScore (m + m) w / (2 * m) <
      matchingScoreCutoff :=
    hscore.trans_lt (hkernel.trans_lt smallPrefixKernel_at_cap_lt)
  exact (smallExactMatchingScoreRank_iff hq).2 (by simpa only [w] using hsmall)

/-- Complete cutoff-rank alternative: no prefix lower bound remains. -/
theorem exactMatchingScoreDichotomy_of_cutoff_complete
    {T lo m : ℕ} {h : StepSchedule T} (hh : IsNonnegativeSchedule h)
    (hm : 2000 ≤ m) (hlo : lo ≤ 4 * m)
    (hq : 4 * m ≤ longCount h)
    (hcut : CutoffConditions criticalP h lo (longCount h))
    (hzhi : zetaState h (4 * m) ≤ (119 / 250 : ℝ)) :
    (4 : ℝ)⁻¹ / unresolvedMass h (4 * m) < lowerBoundFunctional h ∨
      (centralMatchingFloorQ : ℝ) ≤
        fourBlockMatching (zetaState h (4 * m))
          (schedulePrefixA h m) (schedulePrefixR h m)
          (schedulePrefixS h m) := by
  have hm0 : 0 < m := by omega
  have hq' : 2 * (m + m) ≤ longCount h := by omega
  have hstate := (hcut (4 * m) (Finset.mem_Icc.mpr ⟨hlo, hq⟩)).1
  have hzcrit : criticalTheta < zetaState h (2 * (m + m)) := by
    simpa only [criticalTheta, show 2 * (m + m) = 4 * m by omega] using hstate
  have htheta : (centralThetaLowerQ : ℝ) < criticalTheta := by
    rw [criticalTheta_eq]
    norm_num [centralThetaLowerQ, betaLower]
  have hzlo : (centralThetaLowerQ : ℝ) ≤
      zetaState h (2 * (m + m)) := (htheta.trans hzcrit).le
  by_cases hrlo : (1 / 20 : ℝ) ≤ schedulePrefixR h m
  · exact exactMatchingScoreDichotomy_of_cutoff hh hm hlo hq hcut hrlo
  · have hsmall := smallExactMatchingScoreRank_of_prefixR_lt
      hh hm hq' hzlo (by simpa only [show 2 * (m + m) = 4 * m by omega] using hzhi)
      (lt_of_not_ge hrlo)
    exact Or.inl (by
      have hfun := quarter_div_unresolvedMass_lt_functional_of_smallMatchingScore
        hh hm0 hq' hsmall
      simpa only [show 2 * (m + m) = 4 * m by omega] using hfun)

end

end GDLowerBound.FourBlock
