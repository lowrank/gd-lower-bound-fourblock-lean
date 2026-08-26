import GDLowerBound.FourBlock.SideQ2Checker
import GDLowerBound.FourBlock.TailCertificate

/-! # Analytic endpoint caps for the practical local gap -/

namespace GDLowerBound.FourBlock

noncomputable section

def endpointCost (c d z v : ℝ) : ℝ :=
  c * (v - betaLower) ^ 2 + d * v * (z - criticalTheta)

theorem endpointCost_stationary_lower {c d z₀ z v : ℝ}
    (hc : 0 < c) (hd : 0 ≤ d) (hz₀ : criticalTheta ≤ z₀)
    (hzz : z₀ ≤ z) (hv : 0 ≤ v) :
    d * betaLower * (z₀ - criticalTheta) -
        d ^ 2 * (z₀ - criticalTheta) ^ 2 / (4 * c) ≤
      endpointCost c d z v := by
  have hmono : endpointCost c d z₀ v ≤ endpointCost c d z v := by
    unfold endpointCost
    have hdv : 0 ≤ d * v := mul_nonneg hd hv
    nlinarith
  have hden : 0 < 4 * c := mul_pos (by norm_num) hc
  have hid :
      endpointCost c d z₀ v -
          (d * betaLower * (z₀ - criticalTheta) -
            d ^ 2 * (z₀ - criticalTheta) ^ 2 / (4 * c)) =
        (2 * c * (v - betaLower) + d * (z₀ - criticalTheta)) ^ 2 /
          (4 * c) := by
    unfold endpointCost
    field_simp [hden.ne']
    ring
  have hstationary :
      d * betaLower * (z₀ - criticalTheta) -
          d ^ 2 * (z₀ - criticalTheta) ^ 2 / (4 * c) ≤
        endpointCost c d z₀ v := by
    rw [← sub_nonneg, hid]
    exact div_nonneg (sq_nonneg _) hden.le
  exact hstationary.trans hmono

theorem endpointTwo_cap {z v : ℝ}
    (hz : (29 / 10 : ℝ) ≤ z) (hv : 0 ≤ v) :
    (tailTargetQ : ℝ) < endpointCost sideC2Q sideD2Q z v := by
  have hlower := endpointCost_stationary_lower
    (c := (sideC2Q : ℝ)) (d := (sideD2Q : ℝ))
    (z₀ := (29 / 10 : ℝ)) (z := z) (v := v)
    (by norm_num [sideC2Q]) (by norm_num [sideD2Q])
    (by rw [criticalTheta_eq]; norm_num [betaLower]) hz hv
  have hmargin : (tailTargetQ : ℝ) <
      (sideD2Q : ℝ) * betaLower * ((29 / 10 : ℝ) - criticalTheta) -
        (sideD2Q : ℝ) ^ 2 * ((29 / 10 : ℝ) - criticalTheta) ^ 2 /
          (4 * (sideC2Q : ℝ)) := by
    rw [criticalTheta_eq]
    norm_num [tailTargetQ, sideD2Q, sideC2Q, betaLower]
  exact hmargin.trans_le hlower

theorem endpointThree_cap {z v : ℝ}
    (hz : (121 / 100 : ℝ) ≤ z) (hv : 0 ≤ v) :
    (tailTargetQ : ℝ) < endpointCost sideC3Q sideD3Q z v := by
  have hlower := endpointCost_stationary_lower
    (c := (sideC3Q : ℝ)) (d := (sideD3Q : ℝ))
    (z₀ := (121 / 100 : ℝ)) (z := z) (v := v)
    (by norm_num [sideC3Q]) (by norm_num [sideD3Q])
    (by rw [criticalTheta_eq]; norm_num [betaLower]) hz hv
  have hmargin : (tailTargetQ : ℝ) <
      (sideD3Q : ℝ) * betaLower * ((121 / 100 : ℝ) - criticalTheta) -
        (sideD3Q : ℝ) ^ 2 * ((121 / 100 : ℝ) - criticalTheta) ^ 2 /
          (4 * (sideC3Q : ℝ)) := by
    rw [criticalTheta_eq]
    norm_num [tailTargetQ, sideD3Q, sideC3Q, betaLower]
  exact hmargin.trans_le hlower

theorem endpointFour_cap {z v : ℝ}
    (hz : (119 / 250 : ℝ) ≤ z) (hv : 0 ≤ v) :
    (tailTargetQ : ℝ) < endpointCost centralC4Q centralD4Q z v := by
  have hlower := endpointCost_stationary_lower
    (c := (centralC4Q : ℝ)) (d := (centralD4Q : ℝ))
    (z₀ := (119 / 250 : ℝ)) (z := z) (v := v)
    (by norm_num [centralC4Q]) (by norm_num [centralD4Q])
    (by rw [criticalTheta_eq]; norm_num [betaLower]) hz hv
  have hmargin : (tailTargetQ : ℝ) <
      (centralD4Q : ℝ) * betaLower * ((119 / 250 : ℝ) - criticalTheta) -
        (centralD4Q : ℝ) ^ 2 * ((119 / 250 : ℝ) - criticalTheta) ^ 2 /
          (4 * (centralC4Q : ℝ)) := by
    rw [criticalTheta_eq]
    norm_num [tailTargetQ, centralD4Q, centralC4Q, betaLower]
  exact hmargin.trans_le hlower

end

end GDLowerBound.FourBlock
