import GDLowerBound.FourBlock.RobustFiniteThreshold

/-!
# Exact algebra of the global four-scale budget

This module verifies the two-dimensional linear optimization used after
four-scale averaging.  Unlike the bare numerical comparison, the main lemma
starts from the joint moment/defect and sharpened defect budgets and derives
the advertised coefficient.
-/

namespace GDLowerBound.FourBlock

noncomputable section

def logarithmicBlockCoefficient : ℝ :=
  lambdaTwo * Real.log (3 / 2) + lambdaThree * Real.log (4 / 3)

def averagedEnergyBudget (U E d : ℝ) : ℝ :=
  squareWeightSum * U +
    (defectWeightSum + blockWeightSum * betaLower) * E +
    logarithmicBlockCoefficient * d

theorem defect_objective_coefficient_nonneg :
    0 ≤ defectWeightSum + blockWeightSum * betaLower -
      squareWeightSum / criticalTheta := by
  rw [criticalTheta_eq]
  norm_num [defectWeightSum, blockWeightSum, squareWeightSum, betaLower]

/-- Exact solution of the two-budget linear program. -/
theorem averagedEnergyBudget_le_globalCoefficient
    {U E d : ℝ} (hE : 0 ≤ E) (hd : 0 ≤ d)
    (hjoint : U + E / criticalTheta ≤ 2 * (betaLower + 1) * d)
    (hdefect : E ≤ d / betaLower) :
    averagedEnergyBudget U E d ≤ globalCoefficient * d := by
  have hC : 0 ≤ squareWeightSum := by norm_num [squareWeightSum]
  have hb : 0 < betaLower := betaLower_pos
  have hq := defect_objective_coefficient_nonneg
  have hj := mul_le_mul_of_nonneg_left hjoint hC
  have he := mul_le_mul_of_nonneg_left hdefect hq
  have hid :
      squareWeightSum * U +
          (defectWeightSum + blockWeightSum * betaLower) * E =
        squareWeightSum * (U + E / criticalTheta) +
          (defectWeightSum + blockWeightSum * betaLower -
            squareWeightSum / criticalTheta) * E := by ring
  have hthetaInv : criticalTheta⁻¹ = betaLower * (betaLower + 2) := by
    rw [criticalTheta_eq, inv_inv]
  have hbetaUpper : betaLower * d ≤ betaUpper * d :=
    mul_le_mul_of_nonneg_right betaLower_le_betaUpper hd
  unfold averagedEnergyBudget logarithmicBlockCoefficient globalCoefficient
  rw [hid]
  calc
    squareWeightSum * (U + E / criticalTheta) +
          (defectWeightSum + blockWeightSum * betaLower -
              squareWeightSum / criticalTheta) * E +
        (lambdaTwo * Real.log (3 / 2) +
            lambdaThree * Real.log (4 / 3)) * d ≤
      squareWeightSum * (2 * (betaLower + 1) * d) +
          (defectWeightSum + blockWeightSum * betaLower -
              squareWeightSum / criticalTheta) * (d / betaLower) +
        (lambdaTwo * Real.log (3 / 2) +
            lambdaThree * Real.log (4 / 3)) * d := by linarith
    _ = (squareWeightSum * betaLower + defectWeightSum / betaLower +
          blockWeightSum + lambdaTwo * Real.log (3 / 2) +
          lambdaThree * Real.log (4 / 3)) * d := by
      rw [div_eq_mul_inv, hthetaInv]
      field_simp [betaLower_pos.ne']
      ring
    _ ≤ (squareWeightSum * betaUpper + defectWeightSum / betaLower +
          blockWeightSum + lambdaTwo * Real.log (3 / 2) +
          lambdaThree * Real.log (4 / 3)) * d := by
      nlinarith

/-- At mean growth at least the practical target, the two rigidity budgets
force an averaged energy strictly below the robust local gap. -/
theorem averagedEnergyBudget_lt_robustLocalGap
    {U E gamma : ℝ} (hE : 0 ≤ E)
    (hgammaLo : massExponent ≤ gamma) (hgammaHi : gamma ≤ betaLower)
    (hjoint : U + E / criticalTheta ≤
      2 * (betaLower + 1) * (betaLower - gamma))
    (hdefect : E ≤ (betaLower - gamma) / betaLower) :
    averagedEnergyBudget U E (betaLower - gamma) < robustLocalGap := by
  have hd : 0 ≤ betaLower - gamma := sub_nonneg.mpr hgammaHi
  have hbudget := averagedEnergyBudget_le_globalCoefficient hE hd hjoint hdefect
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
  have hKupper : globalCoefficient ≤ globalCoefficientUpper :=
    globalCoefficient_le_upper
  have htargetNonneg : 0 ≤ betaUpper - massExponent := by
    norm_num [betaUpper, massExponent]
  have hcoeff := mul_le_mul_of_nonneg_right hKupper htargetNonneg
  exact (hbudget.trans (hscale.trans hcoeff)).trans_lt
    global_budget_lt_robustLocalGap

end

end GDLowerBound.FourBlock
