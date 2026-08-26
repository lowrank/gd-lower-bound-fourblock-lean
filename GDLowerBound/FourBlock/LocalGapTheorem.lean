import GDLowerBound.FourBlock.LocalEnergyComposition

/-! # Exhaustive central/tail local-gap theorem -/

namespace GDLowerBound.FourBlock

noncomputable section

def qState (z v : ℝ) : ℝ :=
  z * Real.exp (-betaLower * v * (z - criticalTheta))

theorem qState_pos {z v : ℝ} (hz : 0 < z) : 0 < qState z v := by
  unfold qState
  positivity

theorem log_qState {z v : ℝ} (hz : 0 < z) :
    Real.log (qState z v) =
      Real.log z - betaLower * v * (z - criticalTheta) := by
  unfold qState
  rw [Real.log_mul hz.ne' (Real.exp_pos _).ne', Real.log_exp]
  ring

theorem logConstraint_of_qState_le {z v R : ℝ}
    (hz : 0 < z) (hR : 0 < R) (hq : qState z v ≤ R) :
    Real.log z - betaLower * v * (z - criticalTheta) ≤ Real.log R := by
  have hlog := Real.log_le_log (qState_pos hz) hq
  rwa [log_qState hz] at hlog

/-- Once the exact block decomposition and geometric hypotheses are supplied,
the central and tail certificates cover every value of `R`. -/
theorem fourBlockLocalGap
    {w z₂ v₂ z₃ v₃ R z a r s : ℝ}
    (hz₂ : criticalTheta ≤ z₂)
    (hz₂lo : (7982344478949 / 19531250000000 : ℝ) ≤ z₂)
    (hz₂hi : z₂ ≤ (29 / 10 : ℝ))
    (hz₃ : criticalTheta ≤ z₃)
    (hz₃lo : (7982344478949 / 19531250000000 : ℝ) ≤ z₃)
    (hz₃hi : z₃ ≤ (121 / 100 : ℝ))
    (hv₃ : 0 ≤ v₃)
    (hv₃hi : v₃ ≤ (19531250000000 / 7982344478949 : ℝ))
    (hv₃z : v₃ ≤ 1 / z₃)
    (hR0 : 0 < R) (hRhi : R ≤ (41 / 50 : ℝ))
    (hqR : qState z₃ v₃ ≤ R)
    (hR : R = s * z / tailR30)
    (hz0 : 0 < z) (hzlo : (centralThetaLowerQ : ℝ) ≤ z)
    (hzhi : z ≤ (centralZUpperQ : ℝ))
    (ha : 0 < a) (h2 : 0 < r - a) (h3 : 0 < s - r) (h4 : 0 < 1 - s)
    (hord : OrderedFourBlocks a r s) (hmatch : (centralMatchingFloorQ : ℝ) ≤ fourBlockMatching z a r s)
    (hrlo : (1 / 20 : ℝ) ≤ r) (hrhi : r ≤ (1 / 2 : ℝ))
    (hslo : (3 / 40 : ℝ) ≤ s) (hshi : s ≤ (3 / 4 : ℝ))
    (hendpoint : centralEndpoint z ≤ w)
    (hlocal : fourBlockLocalEnergy z₂ v₂ z₃ v₃ R z r ≤ w) :
    (31 / 1250 : ℝ) < w := by
  have hz₃pos : 0 < z₃ := criticalTheta_pos.trans_le hz₃
  have hqLog := logConstraint_of_qState_le hz₃pos hR0 hqR
  by_cases hcentral : R ≤ (33 / 50 : ℝ)
  · have hlogR := Real.log_le_log hR0 hcentral
    have hq66 : Real.log z₃ - betaLower * v₃ * (z₃ - criticalTheta) ≤
        Real.log (33 / 50 : ℝ) := hqLog.trans hlogR
    exact centralLocalGap_of_splitEnergy hz₂ hz₂lo hz₂hi
      hz₃ hz₃lo hz₃hi hv₃ hv₃hi hv₃z hq66 hR
      hz0 hzlo hzhi ha h2 h3 h4 hord hmatch hrlo hrhi hslo hshi
      hendpoint hlocal
  · have hRlo : (33 / 50 : ℝ) ≤ R := le_of_not_ge hcentral
    have hlogR := Real.log_le_log hR0 hRhi
    have hq82 : Real.log z₃ - betaLower * v₃ * (z₃ - criticalTheta) ≤
        Real.log (41 / 50 : ℝ) := hqLog.trans hlogR
    have hr30 : 0 < tailR30 := by
      unfold tailR30
      exact Real.rpow_pos_of_pos (by norm_num) _
    have hsMass : (33 / 50 : ℝ) * tailR30 ≤ s * z := by
      rw [hR] at hRlo
      exact (le_div_iff₀ hr30).mp hRlo
    have hsUpper := (orderedFourBlocks_domain hord).2.2.2.1
    have hsScaled := mul_le_mul_of_nonneg_right hsUpper hz0.le
    have hrTail : (tailRatioQ : ℝ) * tailR30 / z - 1 ≤ r := by
      rw [sub_le_iff_le_add, div_le_iff₀ hz0]
      norm_num [tailRatioQ] at ⊢
      nlinarith
    have hzlo' : (7982344478949 / 19531250000000 : ℝ) ≤ z := by
      norm_num [centralThetaLowerQ] at hzlo ⊢
      exact hzlo
    have hzhi' : z ≤ (119 / 250 : ℝ) := by
      norm_num [centralZUpperQ] at hzhi ⊢
      exact hzhi
    have hr0 : 0 < r := (by norm_num : (0 : ℝ) < 1 / 20).trans_le hrlo
    exact tailLocalGap_of_splitEnergy hz₂ hz₂lo hz₂hi
      hz₃ hz₃lo hz₃hi hv₃ hv₃hi hv₃z hq82 hRlo
      hzlo' hzhi' hr0 hrTail hlocal

end

end GDLowerBound.FourBlock
