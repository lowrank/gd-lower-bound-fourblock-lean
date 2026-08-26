import GDLowerBound.FourBlock.CentralComposition
import GDLowerBound.FourBlock.TailTrueProxy

/-! # Central/tail composition for the common four-block split energy -/

namespace GDLowerBound.FourBlock

noncomputable section

def q3Contribution (z v R : ℝ) : ℝ :=
  sideG z v + (centralAlphaQ : ℝ) * Real.log R

def fourBlockLocalEnergy
    (z₂ v₂ z₃ v₃ R z r : ℝ) : ℝ :=
  sideQ2 z₂ v₂ +
    (centralLambda2Q : ℝ) * Real.log (r / tailR20) +
    (centralLambda2Q : ℝ) * Real.log z +
    q3Contribution z₃ v₃ R + centralEndpoint z

theorem centralSplitEnergy_lt_localEnergy
    {z₂ v₂ z₃ v₃ R z r s : ℝ}
    (hz₂ : criticalTheta ≤ z₂)
    (hz₂lo : (7982344478949 / 19531250000000 : ℝ) ≤ z₂)
    (hz₂hi : z₂ ≤ (29 / 10 : ℝ))
    (hz₃ : criticalTheta ≤ z₃)
    (hz₃lo : (7982344478949 / 19531250000000 : ℝ) ≤ z₃)
    (hz₃hi : z₃ ≤ (121 / 100 : ℝ))
    (hv₃ : 0 ≤ v₃)
    (hv₃hi : v₃ ≤ (19531250000000 / 7982344478949 : ℝ))
    (hv₃z : v₃ ≤ 1 / z₃)
    (hq66 : Real.log z₃ - betaLower * v₃ * (z₃ - criticalTheta) ≤
      Real.log (33 / 50 : ℝ))
    (hR : R = s * z / tailR30) :
    centralSplitEnergy z r s <
      fourBlockLocalEnergy z₂ v₂ z₃ v₃ R z r := by
  have hq₂ := sideQ2Certificate_sound hz₂ hz₂lo hz₂hi (v := v₂)
  have hg₃ := sideG66Certificate_sound hz₃ hz₃lo hz₃hi
    hv₃ hv₃hi hv₃z hq66
  unfold centralSplitEnergy fourBlockLocalEnergy q3Contribution
  rw [hR]
  norm_num [tailQ2LowerQ, sideQ2CertificateTarget,
    sideG66CertificateTarget] at hq₂ hg₃ ⊢
  linarith

theorem tailTrueProxy_lt_localEnergy
    {z₂ v₂ z₃ v₃ R z r : ℝ}
    (hz₂ : criticalTheta ≤ z₂)
    (hz₂lo : (7982344478949 / 19531250000000 : ℝ) ≤ z₂)
    (hz₂hi : z₂ ≤ (29 / 10 : ℝ))
    (hz₃ : criticalTheta ≤ z₃)
    (hz₃lo : (7982344478949 / 19531250000000 : ℝ) ≤ z₃)
    (hz₃hi : z₃ ≤ (121 / 100 : ℝ))
    (hv₃ : 0 ≤ v₃)
    (hv₃hi : v₃ ≤ (19531250000000 / 7982344478949 : ℝ))
    (hv₃z : v₃ ≤ 1 / z₃)
    (hq82 : Real.log z₃ - betaLower * v₃ * (z₃ - criticalTheta) ≤
      Real.log (41 / 50 : ℝ))
    (hRlo : (33 / 50 : ℝ) ≤ R)
    (hz0 : 0 < z) (hzhi : z ≤ (119 / 250 : ℝ)) (hr0 : 0 < r)
    (hr : (tailRatioQ : ℝ) * tailR30 / z - 1 ≤ r) :
    tailTrueProxy z <
      fourBlockLocalEnergy z₂ v₂ z₃ v₃ R z r := by
  have hq₂ := sideQ2Certificate_sound hz₂ hz₂lo hz₂hi (v := v₂)
  have hg₃ := sideG82Certificate_sound hz₃ hz₃lo hz₃hi
    hv₃ hv₃hi hv₃z hq82
  have hR0 : 0 < R := (by norm_num : (0 : ℝ) < 33 / 50).trans_le hRlo
  have hlogR := Real.log_le_log (by norm_num : (0 : ℝ) < 33 / 50) hRlo
  have ha0 : (0 : ℝ) ≤ centralAlphaQ := by norm_num [centralAlphaQ]
  have hq₃log := mul_le_mul_of_nonneg_left hlogR ha0
  have hr20 : 0 < tailR20 := by
    unfold tailR20
    exact Real.rpow_pos_of_pos (by norm_num) _
  have hmass : (tailRatioQ : ℝ) * tailR30 - z ≤ r * z := by
    have hmul := mul_le_mul_of_nonneg_right hr hz0.le
    field_simp [hz0.ne'] at hmul
    linarith
  have hnum0 : 0 < (tailRatioQ : ℝ) * tailR30 - z := by
    have hcap : z < (tailRatioQ : ℝ) * (tailR30LowerQ : ℝ) := by
      norm_num [tailRatioQ, tailR30LowerQ] at hzhi ⊢
      linarith
    have hscale := mul_lt_mul_of_pos_left tailR30Lower_lt
      (by norm_num [tailRatioQ] : (0 : ℝ) < tailRatioQ)
    exact sub_pos.mpr (hcap.trans hscale)
  have hratio :
      ((tailRatioQ : ℝ) * tailR30 - z) / tailR20 ≤
        r * z / tailR20 := div_le_div_of_nonneg_right hmass hr20.le
  have hleft0 : 0 < ((tailRatioQ : ℝ) * tailR30 - z) / tailR20 :=
    div_pos hnum0 hr20
  have hlogMass := Real.log_le_log hleft0 hratio
  have hlogRewrite : Real.log (r * z / tailR20) =
      Real.log (r / tailR20) + Real.log z := by
    rw [Real.log_div (mul_pos hr0 hz0).ne' hr20.ne',
      Real.log_mul hr0.ne' hz0.ne', Real.log_div hr0.ne' hr20.ne']
    ring
  rw [hlogRewrite] at hlogMass
  have hl2 : (0 : ℝ) ≤ centralLambda2Q := by norm_num [centralLambda2Q]
  have hmassTerm := mul_le_mul_of_nonneg_left hlogMass hl2
  have hendpoint : centralEndpointRaw z ≤ centralEndpoint z := by
    unfold centralEndpoint
    exact le_max_right _ _
  unfold tailTrueProxy fourBlockLocalEnergy q3Contribution
  norm_num [tailQ2LowerQ, sideQ2CertificateTarget, tailG82LowerQ,
    sideG82CertificateTarget, tailQmaxQ] at hq₂ hg₃ hq₃log ⊢
  linarith

theorem centralLocalGap_of_splitEnergy
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
    (hq66 : Real.log z₃ - betaLower * v₃ * (z₃ - criticalTheta) ≤
      Real.log (33 / 50 : ℝ))
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
  have hsplit := (centralSplitEnergy_lt_localEnergy hz₂ hz₂lo hz₂hi
    hz₃ hz₃lo hz₃hi hv₃ hv₃hi hv₃z hq66 hR).le.trans hlocal
  exact centralLocalGap_of_lower_bounds hz0 hzlo hzhi ha h2 h3 h4 hord hmatch
    hrlo hrhi hslo hshi hendpoint hsplit

theorem tailLocalGap_of_splitEnergy
    {w z₂ v₂ z₃ v₃ R z r : ℝ}
    (hz₂ : criticalTheta ≤ z₂)
    (hz₂lo : (7982344478949 / 19531250000000 : ℝ) ≤ z₂)
    (hz₂hi : z₂ ≤ (29 / 10 : ℝ))
    (hz₃ : criticalTheta ≤ z₃)
    (hz₃lo : (7982344478949 / 19531250000000 : ℝ) ≤ z₃)
    (hz₃hi : z₃ ≤ (121 / 100 : ℝ))
    (hv₃ : 0 ≤ v₃)
    (hv₃hi : v₃ ≤ (19531250000000 / 7982344478949 : ℝ))
    (hv₃z : v₃ ≤ 1 / z₃)
    (hq82 : Real.log z₃ - betaLower * v₃ * (z₃ - criticalTheta) ≤
      Real.log (41 / 50 : ℝ))
    (hRlo : (33 / 50 : ℝ) ≤ R)
    (hzlo : (7982344478949 / 19531250000000 : ℝ) ≤ z)
    (hzhi : z ≤ (119 / 250 : ℝ)) (hr0 : 0 < r)
    (hr : (tailRatioQ : ℝ) * tailR30 / z - 1 ≤ r)
    (hlocal : fourBlockLocalEnergy z₂ v₂ z₃ v₃ R z r ≤ w) :
    (31 / 1250 : ℝ) < w := by
  have hz0 : 0 < z := (by norm_num : (0 : ℝ) <
    7982344478949 / 19531250000000).trans_le hzlo
  have htail := tailTrueProxy_lt_localEnergy (v₂ := v₂) hz₂ hz₂lo hz₂hi
    hz₃ hz₃lo hz₃hi hv₃ hv₃hi hv₃z hq82 hRlo hz0 hzhi hr0 hr
  exact (certifiedTrueTailProxy hzlo hzhi).trans_le (htail.le.trans hlocal)

end

end GDLowerBound.FourBlock
