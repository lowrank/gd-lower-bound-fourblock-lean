import GDLowerBound.FourBlock.EndpointCaps

/-! # Consequences of the endpoint caps and the fourth-endpoint envelope -/

namespace GDLowerBound.FourBlock

noncomputable section

theorem endpointTwo_below_cap {w z v : ℝ}
    (hv : 0 ≤ v) (hcost : endpointCost sideC2Q sideD2Q z v ≤ w)
    (hw : w ≤ (tailTargetQ : ℝ)) :
    z < (29 / 10 : ℝ) := by
  by_contra hnot
  have hcap := endpointTwo_cap (le_of_not_gt hnot) hv
  linarith

theorem endpointThree_below_cap {w z v : ℝ}
    (hv : 0 ≤ v) (hcost : endpointCost sideC3Q sideD3Q z v ≤ w)
    (hw : w ≤ (tailTargetQ : ℝ)) :
    z < (121 / 100 : ℝ) := by
  by_contra hnot
  have hcap := endpointThree_cap (le_of_not_gt hnot) hv
  linarith

theorem endpointFour_below_cap {w z v : ℝ}
    (hv : 0 ≤ v) (hcost : endpointCost centralC4Q centralD4Q z v ≤ w)
    (hw : w ≤ (tailTargetQ : ℝ)) :
    z < (119 / 250 : ℝ) := by
  by_contra hnot
  have hcap := endpointFour_cap (le_of_not_gt hnot) hv
  linarith

theorem centralEndpointRaw_le_exactStationary {z : ℝ}
    (hz : criticalTheta ≤ z) (hzhi : z ≤ (119 / 250 : ℝ)) :
    centralEndpointRaw z ≤
      (centralD4Q : ℝ) * betaLower * (z - criticalTheta) -
        (centralD4Q : ℝ) ^ 2 * (z - criticalTheta) ^ 2 /
          (4 * (centralC4Q : ℝ)) := by
  have hthetaLo : (centralThetaLowerQ : ℝ) < criticalTheta := by
    rw [criticalTheta_eq]
    norm_num [centralThetaLowerQ, betaLower]
  have hthetaHi : criticalTheta < (centralThetaUpperQ : ℝ) := by
    rw [criticalTheta_eq]
    norm_num [centralThetaUpperQ, betaLower]
  unfold centralEndpointRaw
  norm_num [centralD4Q, centralC4Q, centralBetaLowerQ,
    centralThetaLowerQ, centralThetaUpperQ, betaLower] at hz hzhi hthetaLo hthetaHi ⊢
  nlinarith [sq_nonneg (z - criticalTheta)]

theorem centralEndpoint_le_endpointCost {z v : ℝ}
    (hz : criticalTheta ≤ z) (hzhi : z ≤ (119 / 250 : ℝ))
    (hv : 0 ≤ v) :
    centralEndpoint z ≤ endpointCost centralC4Q centralD4Q z v := by
  have hstationary := endpointCost_stationary_lower
    (c := (centralC4Q : ℝ)) (d := (centralD4Q : ℝ))
    (z₀ := z) (z := z) (v := v)
    (by norm_num [centralC4Q]) (by norm_num [centralD4Q]) hz le_rfl hv
  have hraw := centralEndpointRaw_le_exactStationary hz hzhi
  have hcost0 : 0 ≤ endpointCost centralC4Q centralD4Q z v := by
    unfold endpointCost
    have hdz : 0 ≤ z - criticalTheta := sub_nonneg.mpr hz
    exact add_nonneg
      (mul_nonneg (by norm_num [centralC4Q]) (sq_nonneg _))
      (mul_nonneg (mul_nonneg (by norm_num [centralD4Q]) hv) hdz)
  unfold centralEndpoint
  exact max_le hcost0 (hraw.trans hstationary)

end

end GDLowerBound.FourBlock
