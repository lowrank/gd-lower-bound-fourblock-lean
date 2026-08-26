import GDLowerBound.FourBlock.Constants
import GDLowerBound.FourBlock.LogBounds

/-!
# Verified global numerical comparison

This module checks the final rigidity-budget comparison using the proved
logarithm remainder theorem.  All remaining computation is exact rational
normalization.
-/

namespace GDLowerBound.FourBlock

noncomputable section

def squareWeightSum : ℝ := 17658 / 100000
def defectWeightSum : ℝ := 57012 / 100000
def blockWeightSum : ℝ := 578 / 10000
def lambdaTwo : ℝ := 11 / 1000
def lambdaThree : ℝ := 468 / 10000

/-- A directed upper bound for the coefficient `K`.  Six atanh-series terms
already make the logarithm error negligible for `3/2` and `4/3`. -/
def globalCoefficientUpper : ℝ :=
  squareWeightSum * betaUpper + defectWeightSum / betaLower + blockWeightSum +
    lambdaTwo * logUpper (3 / 2) 6 +
    lambdaThree * logUpper (4 / 3) 6

def localGap : ℝ := 31 / 1250

theorem globalCoefficient_lt : globalCoefficientUpper < 89257 / 100000 := by
  norm_num [globalCoefficientUpper, squareWeightSum, defectWeightSum,
    blockWeightSum, lambdaTwo, lambdaThree, betaUpper, betaLower,
    logUpper, logSeries, logSeriesError, logRadius, abs_of_nonneg]

theorem global_budget_lt_localGap :
    globalCoefficientUpper * (betaUpper - massExponent) < localGap := by
  have hK := globalCoefficient_lt
  have hd : 0 < betaUpper - massExponent := by
    norm_num [betaUpper, massExponent]
  calc
    globalCoefficientUpper * (betaUpper - massExponent) <
        (89257 / 100000 : ℝ) * (betaUpper - massExponent) :=
      mul_lt_mul_of_pos_right hK hd
    _ < localGap := by
      norm_num [betaUpper, massExponent, localGap]

/-- The actual coefficient, with real logarithms, is below the rational
certificate endpoint. -/
def globalCoefficient : ℝ :=
  squareWeightSum * betaUpper + defectWeightSum / betaLower + blockWeightSum +
    lambdaTwo * Real.log (3 / 2) + lambdaThree * Real.log (4 / 3)

theorem globalCoefficient_le_upper :
    globalCoefficient ≤ globalCoefficientUpper := by
  have h32 := le_logUpper (y := (3 / 2 : ℝ)) (by norm_num) 6
  have h43 := le_logUpper (y := (4 / 3 : ℝ)) (by norm_num) 6
  unfold globalCoefficient globalCoefficientUpper
  have hl2 : 0 ≤ lambdaTwo := by norm_num [lambdaTwo]
  have hl3 : 0 ≤ lambdaThree := by norm_num [lambdaThree]
  gcongr

theorem actual_global_budget_lt_localGap :
    globalCoefficient * (betaUpper - massExponent) < localGap := by
  have hd : 0 ≤ betaUpper - massExponent := by
    norm_num [betaUpper, massExponent]
  exact (mul_le_mul_of_nonneg_right globalCoefficient_le_upper hd).trans_lt
    global_budget_lt_localGap

end

end GDLowerBound.FourBlock
