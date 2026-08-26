import GDLowerBound.FourBlock.RationalBounds

/-! # Dyadically range-reduced rational logarithm lower bounds -/

namespace GDLowerBound.FourBlock

def qLogScale (y : ℚ) : ℕ :=
  if y < 1 / 8 then 4 else if y < 1 / 4 then 3 else if y < 1 / 2 then 2 else 1

def qScaledLogLower (y : ℚ) : ℚ :=
  let k := qLogScale y
  qLogLower (y * 2 ^ k) 8 - k * qLogUpper 2 8

def qScaledLogUpper (y : ℚ) : ℚ :=
  let k := qLogScale y
  qLogUpper (y * 2 ^ k) 8 - k * qLogLower 2 8

theorem qScaledLogLower_sound {y : ℚ} (hy : 0 < y) :
    (qScaledLogLower y : ℝ) ≤ Real.log (y : ℝ) := by
  let k := qLogScale y
  have hyR : (0 : ℝ) < y := by exact_mod_cast hy
  have hpow : (0 : ℝ) < 2 ^ k := by positivity
  have hscaledQ : (0 : ℚ) < y * 2 ^ k := by positivity
  have hscaled := logLower_le
    (y := ((y * 2 ^ k : ℚ) : ℝ)) (by exact_mod_cast hscaledQ) 8
  rw [← coe_qLogLower] at hscaled
  push_cast at hscaled
  have htwo := le_logUpper (y := ((2 : ℚ) : ℝ)) (by norm_num) 8
  rw [← coe_qLogUpper] at htwo
  have hk0 : (0 : ℝ) ≤ k := by positivity
  have hkbound := mul_le_mul_of_nonneg_left htwo hk0
  have hmul := Real.log_mul hyR.ne' hpow.ne'
  rw [Real.log_pow] at hmul
  dsimp only [k] at hscaled hkbound hmul
  norm_num at htwo hkbound hmul
  unfold qScaledLogLower
  dsimp only [k]
  push_cast
  linarith

theorem qScaledLogUpper_sound {y : ℚ} (hy : 0 < y) :
    Real.log (y : ℝ) ≤ (qScaledLogUpper y : ℝ) := by
  let k := qLogScale y
  have hyR : (0 : ℝ) < y := by exact_mod_cast hy
  have hpow : (0 : ℝ) < 2 ^ k := by positivity
  have hscaledQ : (0 : ℚ) < y * 2 ^ k := by positivity
  have hscaled := le_logUpper
    (y := ((y * 2 ^ k : ℚ) : ℝ)) (by exact_mod_cast hscaledQ) 8
  rw [← coe_qLogUpper] at hscaled
  push_cast at hscaled
  have htwo := logLower_le (y := ((2 : ℚ) : ℝ)) (by norm_num) 8
  rw [← coe_qLogLower] at htwo
  have hk0 : (0 : ℝ) ≤ k := by positivity
  have hkbound := mul_le_mul_of_nonneg_left htwo hk0
  have hmul := Real.log_mul hyR.ne' hpow.ne'
  rw [Real.log_pow] at hmul
  dsimp only [k] at hscaled hkbound hmul
  norm_num at htwo hkbound hmul
  unfold qScaledLogUpper
  dsimp only [k]
  push_cast
  linarith

end GDLowerBound.FourBlock
