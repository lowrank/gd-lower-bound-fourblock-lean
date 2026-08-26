import GDLowerBound.Basic

namespace GDLowerBound.FourBlock

noncomputable section

/-- The mass-growth exponent certified by the four-block argument. -/
def massExponent : ℝ := 20720 / 25000

/-- The exponent in the final prescribed-schedule lower bound. -/
def exponent : ℝ := 45720 / 25000

/-- Directed rational enclosure for the critical reciprocal-mass state. -/
def thetaLower : ℝ := 4086960373221888 / 10000000000000000
def thetaUpper : ℝ := 40869603732218882 / 100000000000000000

/-- Directed rational enclosure for the critical scalar growth exponent. -/
def betaLower : ℝ := 8565576222695287 / 10000000000000000
def betaUpper : ℝ := 8565576222695288 / 10000000000000000

theorem exponent_eq_one_add_massExponent : exponent = 1 + massExponent := by
  norm_num [exponent, massExponent]

theorem massExponent_pos : 0 < massExponent := by norm_num [massExponent]
theorem massExponent_lt_one : massExponent < 1 := by norm_num [massExponent]
theorem one_lt_exponent : 1 < exponent := by norm_num [exponent]
theorem exponent_lt_two : exponent < 2 := by norm_num [exponent]
theorem thetaLower_pos : 0 < thetaLower := by norm_num [thetaLower]
theorem thetaLower_le_thetaUpper : thetaLower ≤ thetaUpper := by
  norm_num [thetaLower, thetaUpper]
theorem betaLower_pos : 0 < betaLower := by norm_num [betaLower]
theorem betaLower_le_betaUpper : betaLower ≤ betaUpper := by
  norm_num [betaLower, betaUpper]
theorem massExponent_lt_betaLower : massExponent < betaLower := by
  norm_num [massExponent, betaLower]

theorem criticalProduct_lower :
    thetaLower * betaLower * (betaLower + 2) < 1 := by
  norm_num [thetaLower, betaLower]

/-- A purely rational version of the coefficient in the discrete drift. -/
def driftCoeff (v : ℝ) : ℝ :=
  (v ^ 2 + 2 * v + betaLower + 2) /
    (thetaLower * (v + betaLower + 2) ^ 2)

theorem betaLower_le_driftCoeff {v : ℝ} (hv : 0 ≤ v) :
    betaLower ≤ driftCoeff v := by
  have hden : 0 < thetaLower * (v + betaLower + 2) ^ 2 := by
    have : 0 < v + betaLower + 2 := by
      nlinarith [betaLower_pos]
    positivity [thetaLower_pos]
  rw [driftCoeff, le_div_iff₀ hden]
  have h1 : 0 < 1 - thetaLower * betaLower := by
    norm_num [thetaLower, betaLower]
  have h2 : 0 < 1 - thetaLower * betaLower * (betaLower + 2) :=
    sub_pos.mpr criticalProduct_lower
  have hid :
      v ^ 2 + 2 * v + betaLower + 2 -
          betaLower * (thetaLower * (v + betaLower + 2) ^ 2) =
        (1 - thetaLower * betaLower) * v ^ 2 +
          2 * (1 - thetaLower * betaLower * (betaLower + 2)) * v +
          (betaLower + 2) *
            (1 - thetaLower * betaLower * (betaLower + 2)) := by
    ring
  apply sub_nonneg.mp
  rw [hid]
  have hb2 : 0 ≤ betaLower + 2 := by nlinarith [betaLower_pos]
  exact add_nonneg
    (add_nonneg (mul_nonneg h1.le (sq_nonneg v))
      (mul_nonneg (mul_nonneg (by norm_num) h2.le) hv))
    (mul_nonneg hb2 h2.le)

end

end GDLowerBound.FourBlock
