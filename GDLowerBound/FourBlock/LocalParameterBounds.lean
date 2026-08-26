import GDLowerBound.FourBlock.LocalGapTheorem

/-! # Derived parameter bounds used by the local-gap interface -/

namespace GDLowerBound.FourBlock

noncomputable section

theorem certificateThetaLower_le_criticalTheta :
    (7982344478949 / 19531250000000 : ℝ) ≤ criticalTheta := by
  rw [criticalTheta_eq]
  norm_num [betaLower]

theorem certificate_state_lower {z : ℝ} (hz : criticalTheta ≤ z) :
    (7982344478949 / 19531250000000 : ℝ) ≤ z :=
  certificateThetaLower_le_criticalTheta.trans hz

theorem certificate_velocity_upper {z v : ℝ}
    (hz : criticalTheta ≤ z) (hvz : v ≤ 1 / z) :
    v ≤ (19531250000000 / 7982344478949 : ℝ) := by
  have hzlo := certificate_state_lower hz
  have hroot0 : (0 : ℝ) < 7982344478949 / 19531250000000 := by norm_num
  have hinv := one_div_le_one_div_of_le hroot0 hzlo
  norm_num at hinv ⊢
  rw [one_div] at hvz
  exact hvz.trans hinv

theorem tailRatio_upper
    {R z r s : ℝ}
    (hR : R = s * z / tailR30)
    (hz0 : 0 < z) (hzhi : z ≤ (119 / 250 : ℝ))
    (hs0 : 0 ≤ s) (hshi : s ≤ (3 / 4 : ℝ)) :
    R < (41 / 50 : ℝ) := by
  have hr30 : 0 < tailR30 := by
    unfold tailR30
    exact Real.rpow_pos_of_pos (by norm_num) _
  have hsz : s * z ≤ (3 / 4 : ℝ) * (119 / 250 : ℝ) :=
    mul_le_mul hshi hzhi hz0.le (by norm_num)
  have hconst : (3 / 4 : ℝ) * (119 / 250 : ℝ) <
      (4469 / 12500 : ℝ) := by norm_num
  have hpow := mul_lt_mul_of_pos_left tailR30Lower_lt
    (by norm_num : (0 : ℝ) < 41 / 50)
  norm_num [tailR30LowerQ] at hpow
  rw [hR, div_lt_iff₀ hr30]
  exact hsz.trans_lt (hconst.trans hpow)

theorem tail_rank_relation
    {R z r s : ℝ}
    (hR : R = s * z / tailR30)
    (hRlo : (33 / 50 : ℝ) ≤ R) (hz0 : 0 < z)
    (hsUpper : s ≤ (1 + r) / 2) :
    (tailRatioQ : ℝ) * tailR30 / z - 1 ≤ r := by
  have hr30 : 0 < tailR30 := by
    unfold tailR30
    exact Real.rpow_pos_of_pos (by norm_num) _
  have hsMass : (33 / 50 : ℝ) * tailR30 ≤ s * z := by
    rw [hR] at hRlo
    exact (le_div_iff₀ hr30).mp hRlo
  have hsScaled := mul_le_mul_of_nonneg_right hsUpper hz0.le
  rw [sub_le_iff_le_add, div_le_iff₀ hz0]
  norm_num [tailRatioQ] at ⊢
  nlinarith

end

end GDLowerBound.FourBlock
