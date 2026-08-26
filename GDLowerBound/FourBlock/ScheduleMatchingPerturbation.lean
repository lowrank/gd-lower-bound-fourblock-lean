import GDLowerBound.FourBlock.ScheduleMatchingDomination

/-!
# Quantitative transfer of the augmented matching constraint

The augmented endpoint tuple dominates the genuine reciprocal-prefix tuple,
but that monotonicity has the wrong direction for transferring a lower bound.
This file supplies the missing reverse estimate.  The total added weight is
one auxiliary endpoint, and concavity plus a uniform gradient bound makes its
effect on the four-block matching functional explicitly `O(m⁻²)`.
-/

namespace GDLowerBound.FourBlock

open scoped BigOperators
open GDLowerBound.Schedule GDLowerBound.RankAnalysis

noncomputable section

theorem logEnvelopeSlope_le_one {b : ℝ} (hb : 0 ≤ b) :
    logEnvelopeSlope b ≤ 1 := by
  have hd := delta_le_one hb
  unfold logEnvelopeSlope
  nlinarith [sq_nonneg (delta b - 1)]

theorem kernelGradU_le_seven {u v : ℝ}
    (hu : 0 ≤ u) (hv : 0 ≤ v) (hsum : (4 / 25 : ℝ) ≤ u + v) :
    kernelGradU u v ≤ 7 := by
  have hsum0 : 0 < u + v := (by norm_num : (0 : ℝ) < 4 / 25).trans_le hsum
  have hb := edgeParameter_nonneg hu hv
  have hslope0 := logEnvelopeSlope_nonneg hb
  have hslope1 := logEnvelopeSlope_le_one hb
  have hvsum : v ≤ u + v := by linarith
  have hv2 : v ^ 2 ≤ (u + v) ^ 2 := by nlinarith
  have hfrac : v ^ 2 / (2 * (u + v) ^ 2) ≤ 1 / 2 := by
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * (u + v) ^ 2)).2
    nlinarith
  have hinv : 1 / (u + v) ≤ 25 / 4 := by
    apply (div_le_iff₀ hsum0).2
    nlinarith
  have hprod : logEnvelopeSlope (edgeParameter u v) *
      (v ^ 2 / (2 * (u + v) ^ 2)) ≤ 1 / 2 := by
    calc
      _ ≤ 1 * (v ^ 2 / (2 * (u + v) ^ 2)) :=
        mul_le_mul_of_nonneg_right hslope1 (by positivity)
      _ ≤ 1 * (1 / 2) := mul_le_mul_of_nonneg_left hfrac (by norm_num)
      _ = 1 / 2 := by ring
  unfold kernelGradU
  calc
    1 / (u + v) + logEnvelopeSlope (edgeParameter u v) * v ^ 2 /
        (2 * (u + v) ^ 2) =
      1 / (u + v) + logEnvelopeSlope (edgeParameter u v) *
        (v ^ 2 / (2 * (u + v) ^ 2)) := by ring
    _ ≤ 25 / 4 + 1 / 2 := add_le_add hinv hprod
    _ ≤ 7 := by norm_num

theorem kernelGradV_le_seven {u v : ℝ}
    (hu : 0 ≤ u) (hv : 0 ≤ v) (hsum : (4 / 25 : ℝ) ≤ u + v) :
    kernelGradV u v ≤ 7 := by
  rw [show kernelGradV u v = kernelGradU v u by
    unfold kernelGradU kernelGradV edgeParameter
    congr 1 <;> ring]
  exact kernelGradU_le_seven hv hu (by linarith)

/-- A pointwise enlargement with total added mass at most `e` changes the
four-block matching value by at most `7e/(2m)` on the certified central
domain. -/
theorem fourBlockMatching_le_add_of_pointwise
    {m : ℕ} (hm : 0 < m) {x y : Fin (2 * (m + m)) → ℝ} {e : ℝ}
    (hx : ∀ i, 0 < x i) (hxy : ∀ i, x i ≤ y i)
    (hYe : fourBlockTotal y ≤ fourBlockTotal x + e)
    (hzlo : (centralThetaLowerQ : ℝ) ≤ fourBlockZ x)
    (hord : OrderedFourBlocks (fourBlockA x) (fourBlockR x) (fourBlockS x))
    (hrlo : (1 / 20 : ℝ) ≤ fourBlockR x) :
    fourBlockMatching (fourBlockZ y) (fourBlockA y)
        (fourBlockR y) (fourBlockS y) ≤
      fourBlockMatching (fourBlockZ x) (fourBlockA x)
        (fourBlockR x) (fourBlockS x) + 7 * e / (2 * m) := by
  let x1 := finMean (outsideQuarterOne x)
  let x2 := finMean (outsideQuarterTwo x)
  let x3 := finMean (outsideQuarterThree x)
  let x4 := finMean (outsideQuarterFour x)
  let y1 := finMean (outsideQuarterOne y)
  let y2 := finMean (outsideQuarterTwo y)
  let y3 := finMean (outsideQuarterThree y)
  let y4 := finMean (outsideQuarterFour y)
  have hy : ∀ i, 0 < y i := fun i ↦ (hx i).trans_le (hxy i)
  have hx1 : 0 < x1 := by
    dsimp only [x1, finMean]
    positivity [quarterSum_pos hm (outsideQuarterOne x) (fun i ↦ hx _)]
  have hx2 : 0 < x2 := by
    dsimp only [x2, finMean]
    positivity [quarterSum_pos hm (outsideQuarterTwo x) (fun i ↦ hx _)]
  have hx3 : 0 < x3 := by
    dsimp only [x3, finMean]
    positivity [quarterSum_pos hm (outsideQuarterThree x) (fun i ↦ hx _)]
  have hx4 : 0 < x4 := by
    dsimp only [x4, finMean]
    positivity [quarterSum_pos hm (outsideQuarterFour x) (fun i ↦ hx _)]
  have hy1 : 0 < y1 := by
    dsimp only [y1, finMean]
    positivity [quarterSum_pos hm (outsideQuarterOne y) (fun i ↦ hy _)]
  have hy2 : 0 < y2 := by
    dsimp only [y2, finMean]
    positivity [quarterSum_pos hm (outsideQuarterTwo y) (fun i ↦ hy _)]
  have hy3 : 0 < y3 := by
    dsimp only [y3, finMean]
    positivity [quarterSum_pos hm (outsideQuarterThree y) (fun i ↦ hy _)]
  have hy4 : 0 < y4 := by
    dsimp only [y4, finMean]
    positivity [quarterSum_pos hm (outsideQuarterFour y) (fun i ↦ hy _)]
  have hd1 : 0 ≤ y1 - x1 := by
    dsimp only [x1, y1, finMean]
    apply sub_nonneg.mpr
    apply div_le_div_of_nonneg_right _ (by positivity : (0 : ℝ) ≤ m)
    exact Finset.sum_le_sum fun i hi ↦ hxy _
  have hd2 : 0 ≤ y2 - x2 := by
    dsimp only [x2, y2, finMean]
    apply sub_nonneg.mpr
    apply div_le_div_of_nonneg_right _ (by positivity : (0 : ℝ) ≤ m)
    exact Finset.sum_le_sum fun i hi ↦ hxy _
  have hd3 : 0 ≤ y3 - x3 := by
    dsimp only [x3, y3, finMean]
    apply sub_nonneg.mpr
    apply div_le_div_of_nonneg_right _ (by positivity : (0 : ℝ) ≤ m)
    exact Finset.sum_le_sum fun i hi ↦ hxy _
  have hd4 : 0 ≤ y4 - x4 := by
    dsimp only [x4, y4, finMean]
    apply sub_nonneg.mpr
    apply div_le_div_of_nonneg_right _ (by positivity : (0 : ℝ) ≤ m)
    exact Finset.sum_le_sum fun i hi ↦ hxy _
  have hsumDelta :
      (y1 - x1) + (y2 - x2) + (y3 - x3) + (y4 - x4) ≤ e / m := by
    have hmR : (0 : ℝ) < m := by exact_mod_cast hm
    dsimp only [x1, x2, x3, x4, y1, y2, y3, y4, finMean]
    unfold fourBlockTotal quarterSumOne quarterSumTwo quarterSumThree quarterSumFour at hYe
    field_simp [hmR.ne']
    linarith
  have hdomain := orderedFourBlocks_domain hord
  have hzfour : (2 / 5 : ℝ) < fourBlockZ x := by
    have htheta : (2 / 5 : ℝ) < (centralThetaLowerQ : ℝ) := by
      norm_num [centralThetaLowerQ]
    exact htheta.trans_le hzlo
  have houterSum : (4 / 25 : ℝ) ≤ x1 + x4 := by
    rw [show x1 = 8 * fourBlockZ x * fourBlockA x by
      exact finMean_outsideQuarterOne_eq hm hx]
    rw [show x4 = 8 * fourBlockZ x * (1 - fourBlockS x) by
      exact finMean_outsideQuarterFour_eq hm hx]
    have ha0 := (orderedFourBlocks_mass_nonneg hord).1
    have hs : fourBlockS x ≤ 3 / 4 := hdomain.2.2.2.1.trans (by linarith [hdomain.2])
    nlinarith
  have hinnerSum : (4 / 25 : ℝ) ≤ x2 + x3 := by
    rw [show x2 = 8 * fourBlockZ x * (fourBlockR x - fourBlockA x) by
      exact finMean_outsideQuarterTwo_eq hm hx]
    rw [show x3 = 8 * fourBlockZ x * (fourBlockS x - fourBlockR x) by
      exact finMean_outsideQuarterThree_eq hm hx]
    have haUpper := hdomain.2.2.2.2.2
    have hsLower := hdomain.2.2.1
    nlinarith
  have hg1 := kernelGradU_le_seven hx1.le hx4.le houterSum
  have hg4 := kernelGradV_le_seven hx1.le hx4.le houterSum
  have hg2 := kernelGradU_le_seven hx2.le hx3.le hinnerSum
  have hg3 := kernelGradV_le_seven hx2.le hx3.le hinnerSum
  have hout := pairLogKernelClosed_le_support hx1 hx4 hy1 hy4
  have hin := pairLogKernelClosed_le_support hx2 hx3 hy2 hy3
  rw [pairLogKernelClosed_eq ⟨hy1, hy4⟩,
    pairLogKernelClosed_eq ⟨hx1, hx4⟩] at hout
  rw [pairLogKernelClosed_eq ⟨hy2, hy3⟩,
    pairLogKernelClosed_eq ⟨hx2, hx3⟩] at hin
  have hout' : logKernel y1 y4 ≤ logKernel x1 x4 +
      7 * (y1 - x1) + 7 * (y4 - x4) := by
    nlinarith [mul_le_mul_of_nonneg_right hg1 hd1,
      mul_le_mul_of_nonneg_right hg4 hd4]
  have hin' : logKernel y2 y3 ≤ logKernel x2 x3 +
      7 * (y2 - x2) + 7 * (y3 - x3) := by
    nlinarith [mul_le_mul_of_nonneg_right hg2 hd2,
      mul_le_mul_of_nonneg_right hg3 hd3]
  have hlogs :
      logKernel y1 y4 + logKernel y2 y3 ≤
        logKernel x1 x4 + logKernel x2 x3 +
          7 * ((y1 - x1) + (y2 - x2) + (y3 - x3) + (y4 - x4)) := by
    linarith
  have herror :
      7 * ((y1 - x1) + (y2 - x2) + (y3 - x3) + (y4 - x4)) ≤
        7 * (e / m) := mul_le_mul_of_nonneg_left hsumDelta (by norm_num)
  have htotal :
      logKernel y1 y4 + logKernel y2 y3 ≤
        logKernel x1 x4 + logKernel x2 x3 + 7 * (e / m) := by
    calc
      _ ≤ logKernel x1 x4 + logKernel x2 x3 +
          7 * ((y1 - x1) + (y2 - x2) + (y3 - x3) + (y4 - x4)) := hlogs
      _ ≤ _ := by linarith
  unfold fourBlockMatching
  rw [← finMean_outsideQuarterOne_eq hm hy,
    ← finMean_outsideQuarterTwo_eq hm hy,
    ← finMean_outsideQuarterThree_eq hm hy,
    ← finMean_outsideQuarterFour_eq hm hy,
    ← finMean_outsideQuarterOne_eq hm hx,
    ← finMean_outsideQuarterTwo_eq hm hx,
    ← finMean_outsideQuarterThree_eq hm hx,
    ← finMean_outsideQuarterFour_eq hm hx]
  dsimp only [x1, x2, x3, x4, y1, y2, y3, y4] at htotal ⊢
  calc
    _ ≤ (logKernel (finMean (outsideQuarterOne x))
          (finMean (outsideQuarterFour x)) +
        logKernel (finMean (outsideQuarterTwo x))
          (finMean (outsideQuarterThree x)) + 7 * (e / m)) / 2 :=
      div_le_div_of_nonneg_right htotal (by norm_num)
    _ = _ := by ring

end

end GDLowerBound.FourBlock
