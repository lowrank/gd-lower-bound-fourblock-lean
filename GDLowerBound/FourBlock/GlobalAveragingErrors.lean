import GDLowerBound.FourBlock.GlobalAveragingAlgebra
import GDLowerBound.FourBlock.MiddleBlockOccupancyWeighted

/-!
# Global four-block algebra with finite additive errors

The asymptotic two-budget calculation is stable under explicit finite-rank
slack.  This module records exactly how joint-rigidity slack, defect-rigidity
slack, and all other averaging errors consume the strict numerical margin.
-/

namespace GDLowerBound.FourBlock

noncomputable section

def defectSlackCoefficient : ℝ :=
  defectWeightSum + blockWeightSum * betaLower -
    squareWeightSum / criticalTheta

theorem defectSlackCoefficient_nonneg : 0 ≤ defectSlackCoefficient := by
  exact defect_objective_coefficient_nonneg

/-- The exact positive room left between the certified asymptotic global
budget and the robust local gap. -/
def fourBlockFiniteMargin : ℝ :=
  robustLocalGap -
    globalCoefficientUpper * (betaUpper - massExponent)

theorem fourBlockFiniteMargin_pos : 0 < fourBlockFiniteMargin := by
  unfold fourBlockFiniteMargin
  linarith [global_budget_lt_robustLocalGap]

/-- Version of the two-budget linear program retaining additive slack in
both rigidity inequalities. -/
theorem averagedEnergyBudget_le_globalCoefficient_add_errors
    {U E d J D : ℝ} (hE : 0 ≤ E) (hd : 0 ≤ d)
    (hjoint : U + E / criticalTheta ≤
      2 * (betaLower + 1) * d + J)
    (hdefect : E ≤ d / betaLower + D) :
    averagedEnergyBudget U E d ≤
      globalCoefficient * d + squareWeightSum * J +
        defectSlackCoefficient * D := by
  have hC : 0 ≤ squareWeightSum := by norm_num [squareWeightSum]
  have hb : 0 < betaLower := betaLower_pos
  have hq : 0 ≤ defectSlackCoefficient := defectSlackCoefficient_nonneg
  have hj := mul_le_mul_of_nonneg_left hjoint hC
  have he := mul_le_mul_of_nonneg_left hdefect hq
  have hid :
      squareWeightSum * U +
          (defectWeightSum + blockWeightSum * betaLower) * E =
        squareWeightSum * (U + E / criticalTheta) +
          defectSlackCoefficient * E := by
    unfold defectSlackCoefficient
    ring
  have hthetaInv : criticalTheta⁻¹ = betaLower * (betaLower + 2) := by
    rw [criticalTheta_eq, inv_inv]
  have hbetaUpper : betaLower * d ≤ betaUpper * d :=
    mul_le_mul_of_nonneg_right betaLower_le_betaUpper hd
  unfold averagedEnergyBudget logarithmicBlockCoefficient globalCoefficient
  rw [hid]
  calc
    squareWeightSum * (U + E / criticalTheta) +
          defectSlackCoefficient * E +
        (lambdaTwo * Real.log (3 / 2) +
            lambdaThree * Real.log (4 / 3)) * d ≤
      squareWeightSum * (2 * (betaLower + 1) * d + J) +
          defectSlackCoefficient * (d / betaLower + D) +
        (lambdaTwo * Real.log (3 / 2) +
            lambdaThree * Real.log (4 / 3)) * d := by linarith
    _ = (squareWeightSum * betaLower + defectWeightSum / betaLower +
          blockWeightSum + lambdaTwo * Real.log (3 / 2) +
          lambdaThree * Real.log (4 / 3)) * d +
        squareWeightSum * J + defectSlackCoefficient * D := by
      unfold defectSlackCoefficient
      rw [div_eq_mul_inv, hthetaInv]
      field_simp [betaLower_pos.ne']
      ring
    _ ≤ (squareWeightSum * betaUpper + defectWeightSum / betaLower +
          blockWeightSum + lambdaTwo * Real.log (3 / 2) +
          lambdaThree * Real.log (4 / 3)) * d +
        squareWeightSum * J + defectSlackCoefficient * D := by
      nlinarith

/-- If all explicitly accumulated finite errors fit inside
`fourBlockFiniteMargin`, the perturbed averaged budget remains below the
robust local gap. -/
theorem averagedEnergyBudget_add_errors_lt_robustLocalGap
    {U E gamma J D A : ℝ} (hE : 0 ≤ E)
    (hgammaLo : massExponent ≤ gamma) (hgammaHi : gamma ≤ betaLower)
    (hjoint : U + E / criticalTheta ≤
      2 * (betaLower + 1) * (betaLower - gamma) + J)
    (hdefect : E ≤ (betaLower - gamma) / betaLower + D)
    (herrors : squareWeightSum * J + defectSlackCoefficient * D + A <
      fourBlockFiniteMargin) :
    averagedEnergyBudget U E (betaLower - gamma) + A < robustLocalGap := by
  have hd : 0 ≤ betaLower - gamma := sub_nonneg.mpr hgammaHi
  have hbudget := averagedEnergyBudget_le_globalCoefficient_add_errors
    hE hd hjoint hdefect
  have hK0 : 0 ≤ globalCoefficient := by
    unfold globalCoefficient squareWeightSum defectWeightSum blockWeightSum
      lambdaTwo lambdaThree
    have hlog32 : 0 ≤ Real.log (3 / 2 : ℝ) :=
      Real.log_nonneg (by norm_num)
    have hlog43 : 0 ≤ Real.log (4 / 3 : ℝ) :=
      Real.log_nonneg (by norm_num)
    have hs : 0 ≤ (17658 / 100000 : ℝ) * betaUpper := by
      exact mul_nonneg (by norm_num) (by norm_num [betaUpper])
    have hd0 : 0 ≤ (57012 / 100000 : ℝ) / betaLower := by
      exact div_nonneg (by norm_num) betaLower_pos.le
    have hl2 : 0 ≤ (11 / 1000 : ℝ) * Real.log (3 / 2) := by
      exact mul_nonneg (by norm_num) hlog32
    have hl3 : 0 ≤ (468 / 10000 : ℝ) * Real.log (4 / 3) := by
      exact mul_nonneg (by norm_num) hlog43
    nlinarith
  have hdUpper : betaLower - gamma ≤ betaUpper - massExponent := by
    linarith [betaLower_le_betaUpper]
  have hscale := mul_le_mul_of_nonneg_left hdUpper hK0
  have htargetNonneg : 0 ≤ betaUpper - massExponent := by
    norm_num [betaUpper, massExponent]
  have hcoeff := mul_le_mul_of_nonneg_right globalCoefficient_le_upper
    htargetNonneg
  have hbase :
      globalCoefficient * (betaLower - gamma) ≤
        globalCoefficientUpper * (betaUpper - massExponent) :=
    hscale.trans hcoeff
  unfold fourBlockFiniteMargin at herrors
  linarith

end

end GDLowerBound.FourBlock
