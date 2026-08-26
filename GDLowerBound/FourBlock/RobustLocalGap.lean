import GDLowerBound.FourBlock.LocalGapTheorem
import GDLowerBound.FourBlock.SideGRobustCertificateData
import GDLowerBound.FourBlock.GlobalCertificate

/-!
# A finite-error robust local gap

The original local certificate uses the sharp cutoffs q ≤ 0.66 and
q ≤ 0.82.  The exact block drift supplies q ≤ R * exp eps, so this module
checks slightly enlarged side domains, 0.6601 and 0.8201.  The resulting
energy loss is exactly 1/200000, leaving the local gap 0.024795.
-/

namespace GDLowerBound.FourBlock

noncomputable section

def robustSideLoss : ℝ := 1 / 200000
def robustLocalGap : ℝ := 4959 / 200000

theorem robustLocalGap_eq : robustLocalGap = localGap - robustSideLoss := by
  norm_num [robustLocalGap, localGap, robustSideLoss]

theorem centralSplitEnergy_sub_loss_lt_localEnergy
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
    (hq6601 : Real.log z₃ - betaLower * v₃ * (z₃ - criticalTheta) ≤
      Real.log (6601 / 10000 : ℝ))
    (hR : R = s * z / tailR30) :
    centralSplitEnergy z r s - robustSideLoss <
      fourBlockLocalEnergy z₂ v₂ z₃ v₃ R z r := by
  have hq₂ := sideQ2Certificate_sound hz₂ hz₂lo hz₂hi (v := v₂)
  have hg₃ := sideG6601Certificate_sound hz₃ hz₃lo hz₃hi
    hv₃ hv₃hi hv₃z hq6601
  unfold centralSplitEnergy fourBlockLocalEnergy q3Contribution robustSideLoss
  rw [hR]
  norm_num [tailQ2LowerQ, sideQ2CertificateTarget,
    sideG66CertificateTarget] at hq₂ hg₃ ⊢
  linarith

theorem tailTrueProxy_sub_loss_lt_localEnergy
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
    (hq8201 : Real.log z₃ - betaLower * v₃ * (z₃ - criticalTheta) ≤
      Real.log (8201 / 10000 : ℝ))
    (hRlo : (33 / 50 : ℝ) ≤ R)
    (hz0 : 0 < z) (hzhi : z ≤ (119 / 250 : ℝ)) (hr0 : 0 < r)
    (hr : (tailRatioQ : ℝ) * tailR30 / z - 1 ≤ r) :
    tailTrueProxy z - robustSideLoss <
      fourBlockLocalEnergy z₂ v₂ z₃ v₃ R z r := by
  have hq₂ := sideQ2Certificate_sound hz₂ hz₂lo hz₂hi (v := v₂)
  have hg₃ := sideG8201Certificate_sound hz₃ hz₃lo hz₃hi
    hv₃ hv₃hi hv₃z hq8201
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
  unfold tailTrueProxy fourBlockLocalEnergy q3Contribution robustSideLoss
  norm_num [tailQ2LowerQ, sideQ2CertificateTarget, tailG82LowerQ,
    sideG82CertificateTarget, tailQmaxQ] at hq₂ hg₃ hq₃log ⊢
  linarith

theorem centralRobustLocalGap
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
    (hq6601 : Real.log z₃ - betaLower * v₃ * (z₃ - criticalTheta) ≤
      Real.log (6601 / 10000 : ℝ))
    (hR : R = s * z / tailR30)
    (hz0 : 0 < z) (hzlo : (centralThetaLowerQ : ℝ) ≤ z)
    (hzhi : z ≤ (centralZUpperQ : ℝ))
    (ha : 0 < a) (h2 : 0 < r - a) (h3 : 0 < s - r) (h4 : 0 < 1 - s)
    (hord : OrderedFourBlocks a r s) (hmatch : (centralMatchingFloorQ : ℝ) ≤ fourBlockMatching z a r s)
    (hrlo : (1 / 20 : ℝ) ≤ r) (hrhi : r ≤ (1 / 2 : ℝ))
    (hslo : (3 / 40 : ℝ) ≤ s) (hshi : s ≤ (3 / 4 : ℝ))
    (hendpoint : centralEndpoint z ≤ w)
    (hlocal : fourBlockLocalEnergy z₂ v₂ z₃ v₃ R z r ≤ w) :
    robustLocalGap < w := by
  have hsplit := centralSplitEnergy_sub_loss_lt_localEnergy (v₂ := v₂) (r := r)
    hz₂ hz₂lo hz₂hi hz₃ hz₃lo hz₃hi hv₃ hv₃hi hv₃z hq6601 hR
  have hcert := certifiedCentralTrueEnergy hz0 hzlo hzhi ha h2 h3 h4
    hord hmatch hrlo hrhi hslo hshi
  have hr0 : 0 < r := (by norm_num : (0 : ℝ) < 1 / 20).trans_le hrlo
  have hs0 : 0 < s := (by norm_num : (0 : ℝ) < 3 / 40).trans_le hslo
  rw [centralTrueEnergy, ← centralSplitEnergy_eq hz0 hr0 hs0] at hcert
  have hcertPrime : localGap < max (centralEndpoint z) (centralSplitEnergy z r s) := by
    simpa [localGap] using hcert
  have hloss : 0 ≤ robustSideLoss := by norm_num [robustSideLoss]
  have henergy :
      max (centralEndpoint z) (centralSplitEnergy z r s) ≤
        w + robustSideLoss := by
    apply max_le
    · linarith
    · linarith
  rw [robustLocalGap_eq]
  linarith

theorem tailRobustLocalGap
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
    (hq8201 : Real.log z₃ - betaLower * v₃ * (z₃ - criticalTheta) ≤
      Real.log (8201 / 10000 : ℝ))
    (hRlo : (33 / 50 : ℝ) ≤ R)
    (hzlo : (7982344478949 / 19531250000000 : ℝ) ≤ z)
    (hzhi : z ≤ (119 / 250 : ℝ)) (hr0 : 0 < r)
    (hr : (tailRatioQ : ℝ) * tailR30 / z - 1 ≤ r)
    (hlocal : fourBlockLocalEnergy z₂ v₂ z₃ v₃ R z r ≤ w) :
    robustLocalGap < w := by
  have hz0 : 0 < z := (by norm_num : (0 : ℝ) <
    7982344478949 / 19531250000000).trans_le hzlo
  have htail := tailTrueProxy_sub_loss_lt_localEnergy (v₂ := v₂)
    hz₂ hz₂lo hz₂hi hz₃ hz₃lo hz₃hi hv₃ hv₃hi hv₃z hq8201
    hRlo hz0 hzhi hr0 hr
  have hcert := certifiedTrueTailProxy hzlo hzhi
  have hcertPrime : localGap < tailTrueProxy z := by
    simpa [localGap] using hcert
  rw [robustLocalGap_eq]
  linarith

/-- Robust version of fourBlockLocalGap.  A multiplicative side-constraint
error bounded by 8201/8200 costs only 1/200000 in the local gap. -/
theorem fourBlockRobustLocalGap
    {w z₂ v₂ z₃ v₃ R z a r s eps : ℝ}
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
    (hqR : qState z₃ v₃ ≤ R * Real.exp eps)
    (hexp : Real.exp eps ≤ (8201 / 8200 : ℝ))
    (hR : R = s * z / tailR30)
    (hz0 : 0 < z) (hzlo : (centralThetaLowerQ : ℝ) ≤ z)
    (hzhi : z ≤ (centralZUpperQ : ℝ))
    (ha : 0 < a) (h2 : 0 < r - a) (h3 : 0 < s - r) (h4 : 0 < 1 - s)
    (hord : OrderedFourBlocks a r s) (hmatch : (centralMatchingFloorQ : ℝ) ≤ fourBlockMatching z a r s)
    (hrlo : (1 / 20 : ℝ) ≤ r) (hrhi : r ≤ (1 / 2 : ℝ))
    (hslo : (3 / 40 : ℝ) ≤ s) (hshi : s ≤ (3 / 4 : ℝ))
    (hendpoint : centralEndpoint z ≤ w)
    (hlocal : fourBlockLocalEnergy z₂ v₂ z₃ v₃ R z r ≤ w) :
    robustLocalGap < w := by
  have hz₃pos : 0 < z₃ := criticalTheta_pos.trans_le hz₃
  by_cases hcentral : R ≤ (33 / 50 : ℝ)
  · have hq6601 : qState z₃ v₃ ≤ (6601 / 10000 : ℝ) := by
      calc
        qState z₃ v₃ ≤ R * Real.exp eps := hqR
        _ ≤ (33 / 50 : ℝ) * (8201 / 8200 : ℝ) :=
          mul_le_mul hcentral hexp (Real.exp_pos eps).le (by norm_num)
        _ ≤ (6601 / 10000 : ℝ) := by norm_num
    have hqLog := logConstraint_of_qState_le hz₃pos
      (by norm_num : (0 : ℝ) < 6601 / 10000) hq6601
    exact centralRobustLocalGap hz₂ hz₂lo hz₂hi
      hz₃ hz₃lo hz₃hi hv₃ hv₃hi hv₃z hqLog hR
      hz0 hzlo hzhi ha h2 h3 h4 hord hmatch hrlo hrhi hslo hshi
      hendpoint hlocal
  · have hRlo : (33 / 50 : ℝ) ≤ R := le_of_not_ge hcentral
    have hq8201 : qState z₃ v₃ ≤ (8201 / 10000 : ℝ) := by
      calc
        qState z₃ v₃ ≤ R * Real.exp eps := hqR
        _ ≤ (41 / 50 : ℝ) * (8201 / 8200 : ℝ) :=
          mul_le_mul hRhi hexp (Real.exp_pos eps).le (by norm_num)
        _ = (8201 / 10000 : ℝ) := by norm_num
    have hqLog := logConstraint_of_qState_le hz₃pos
      (by norm_num : (0 : ℝ) < 8201 / 10000) hq8201
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
    exact tailRobustLocalGap hz₂ hz₂lo hz₂hi
      hz₃ hz₃lo hz₃hi hv₃ hv₃hi hv₃z hqLog hRlo
      hzlo' hzhi' hr0 hrTail hlocal

end

end GDLowerBound.FourBlock
