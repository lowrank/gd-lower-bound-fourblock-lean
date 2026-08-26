import GDLowerBound.FourBlock.CentralBaseCertificate
import GDLowerBound.FourBlock.CentralCertificateData

/-! # Composition of the central numerical tree with the true side constants -/

namespace GDLowerBound.FourBlock

noncomputable section

def centralTrueEnergy (z r s : ℝ) : ℝ :=
  max (centralEndpoint z)
    (centralTrueBase + centralEndpoint z +
      (centralLambda2Q : ℝ) * Real.log r +
      (centralAlphaQ : ℝ) * Real.log s +
      (centralLambda3Q : ℝ) * Real.log z)

theorem centralEnergy_le_trueEnergy (z r s : ℝ) :
    centralEnergy z r s ≤ centralTrueEnergy z r s := by
  unfold centralEnergy centralTrueEnergy
  apply max_le_max le_rfl
  linarith [centralCBase_lt_trueBase]

theorem certifiedCentralTrueEnergy {z a r s : ℝ}
    (hz0 : 0 < z) (hzlo : (centralThetaLowerQ : ℝ) ≤ z)
    (hzhi : z ≤ (centralZUpperQ : ℝ))
    (ha : 0 < a) (h2 : 0 < r - a) (h3 : 0 < s - r) (h4 : 0 < 1 - s)
    (hord : OrderedFourBlocks a r s) (hmatch : (centralMatchingFloorQ : ℝ) ≤ fourBlockMatching z a r s)
    (hrlo : (1 / 20 : ℝ) ≤ r) (hrhi : r ≤ (1 / 2 : ℝ))
    (hslo : (3 / 40 : ℝ) ≤ s) (hshi : s ≤ (3 / 4 : ℝ)) :
    (31 / 1250 : ℝ) < centralTrueEnergy z r s := by
  have hcert := certifiedCentralEnergy hz0 hzlo hzhi ha h2 h3 h4
    hord hmatch hrlo hrhi hslo hshi
  exact hcert.trans_le (centralEnergy_le_trueEnergy z r s)

/-- The lower bound obtained by inserting the two side certificates in the
split energy, before logarithms are regrouped. -/
def centralSplitEnergy (z r s : ℝ) : ℝ :=
  (tailQ2LowerQ : ℝ) + (sideG66CertificateTarget : ℝ) +
    centralEndpoint z +
    (centralLambda2Q : ℝ) * Real.log (r / tailR20) +
    (centralLambda2Q : ℝ) * Real.log z +
    (centralAlphaQ : ℝ) * Real.log (s * z / tailR30)

theorem centralSplitEnergy_eq {z r s : ℝ}
    (hz : 0 < z) (hr : 0 < r) (hs : 0 < s) :
    centralSplitEnergy z r s =
      centralTrueBase + centralEndpoint z +
        (centralLambda2Q : ℝ) * Real.log r +
        (centralAlphaQ : ℝ) * Real.log s +
        (centralLambda3Q : ℝ) * Real.log z := by
  have hr20 : 0 < tailR20 := by
    unfold tailR20
    exact Real.rpow_pos_of_pos (by norm_num) _
  have hr30 : 0 < tailR30 := by
    unfold tailR30
    exact Real.rpow_pos_of_pos (by norm_num) _
  rw [centralSplitEnergy, centralTrueBase, Real.log_div hr.ne' hr20.ne',
    Real.log_div (mul_pos hs hz).ne' hr30.ne', Real.log_mul hs.ne' hz.ne']
  norm_num [centralLambda3Q, centralLambda2Q, centralAlphaQ]
  ring

theorem centralLocalGap_of_lower_bounds {w z a r s : ℝ}
    (hz0 : 0 < z) (hzlo : (centralThetaLowerQ : ℝ) ≤ z)
    (hzhi : z ≤ (centralZUpperQ : ℝ))
    (ha : 0 < a) (h2 : 0 < r - a) (h3 : 0 < s - r) (h4 : 0 < 1 - s)
    (hord : OrderedFourBlocks a r s) (hmatch : (centralMatchingFloorQ : ℝ) ≤ fourBlockMatching z a r s)
    (hrlo : (1 / 20 : ℝ) ≤ r) (hrhi : r ≤ (1 / 2 : ℝ))
    (hslo : (3 / 40 : ℝ) ≤ s) (hshi : s ≤ (3 / 4 : ℝ))
    (hendpoint : centralEndpoint z ≤ w)
    (hsplit : centralSplitEnergy z r s ≤ w) :
    (31 / 1250 : ℝ) < w := by
  have hcert := certifiedCentralTrueEnergy hz0 hzlo hzhi ha h2 h3 h4
    hord hmatch hrlo hrhi hslo hshi
  have hr0 : 0 < r := (by norm_num : (0 : ℝ) < 1 / 20).trans_le hrlo
  have hs0 : 0 < s := (by norm_num : (0 : ℝ) < 3 / 40).trans_le hslo
  rw [centralTrueEnergy, ← centralSplitEnergy_eq hz0 hr0 hs0] at hcert
  exact hcert.trans_le (max_le hendpoint hsplit)

end

end GDLowerBound.FourBlock
