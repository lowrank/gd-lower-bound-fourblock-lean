import GDLowerBound.FourBlock.AutoKernel
import GDLowerBound.FourBlock.KernelGradient

/-!
# Automatic rational enclosures for kernel gradients

These bounds are the derivative counterpart of `qKernelUpperAuto`.  They are
used to check supporting planes using rational arithmetic only.
-/

namespace GDLowerBound.FourBlock

def qAutoSlopeLower (b : ℚ) (sqrtSteps : ℕ) : ℚ :=
  let d := qAutoDeltaLower b sqrtSteps
  d * (2 - d)

def qAutoSlopeUpper (b : ℚ) : ℚ :=
  let d := qAutoDeltaUpper b
  d * (2 - d)

def qKernelGradULower (u v : ℚ) (sqrtSteps : ℕ) : ℚ :=
  1 / (u + v) + qAutoSlopeLower (qEdgeParameter u v) sqrtSteps *
    v ^ 2 / (2 * (u + v) ^ 2)

def qKernelGradUUpper (u v : ℚ) : ℚ :=
  1 / (u + v) + qAutoSlopeUpper (qEdgeParameter u v) *
    v ^ 2 / (2 * (u + v) ^ 2)

def qKernelGradVLower (u v : ℚ) (sqrtSteps : ℕ) : ℚ :=
  1 / (u + v) + qAutoSlopeLower (qEdgeParameter u v) sqrtSteps *
    u ^ 2 / (2 * (u + v) ^ 2)

def qKernelGradVUpper (u v : ℚ) : ℚ :=
  1 / (u + v) + qAutoSlopeUpper (qEdgeParameter u v) *
    u ^ 2 / (2 * (u + v) ^ 2)

theorem qAutoDeltaLower_sound' {b : ℚ} (hb : 0 ≤ b) (n : ℕ) :
    (qAutoDeltaLower b n : ℝ) ≤ delta (b : ℝ) := by
  have hx : (1 : ℚ) ≤ 4 * b ^ 2 + 1 := by nlinarith [sq_nonneg b]
  have hu := qSqrtNewtonUpper_sound hx n
  have hbR : (0 : ℝ) ≤ b := by exact_mod_cast hb
  have hden : 0 < 2 * (b : ℝ) + 1 + Real.sqrt (4 * (b : ℝ) ^ 2 + 1) :=
    delta_denominator_pos hbR
  have huPos := (qSqrtNewtonUpper_valid hx n).1
  have huPosR : (0 : ℝ) < qSqrtNewtonUpper (4 * b ^ 2 + 1) n := by
    exact_mod_cast huPos
  have hsqrtLe : Real.sqrt (4 * (b : ℝ) ^ 2 + 1) ≤
      (qSqrtNewtonUpper (4 * b ^ 2 + 1) n : ℝ) := by
    have hcast : ((4 * b ^ 2 + 1 : ℚ) : ℝ) = 4 * (b : ℝ) ^ 2 + 1 := by
      push_cast
      rfl
    rw [← hcast]
    exact hu
  have hfrac := div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 2)
    hden (by linarith :
      2 * (b : ℝ) + 1 + Real.sqrt (4 * (b : ℝ) ^ 2 + 1) ≤
        2 * (b : ℝ) + 1 + (qSqrtNewtonUpper (4 * b ^ 2 + 1) n : ℝ))
  unfold qAutoDeltaLower delta
  push_cast
  exact hfrac

theorem qAutoDeltaUpper_sound' {b : ℚ} (hb : 0 ≤ b) :
    delta (b : ℝ) ≤ (qAutoDeltaUpper b : ℝ) := by
  have hbR : (0 : ℝ) ≤ b := by exact_mod_cast hb
  have hsqrtOne : (1 : ℝ) ≤ Real.sqrt (4 * (b : ℝ) ^ 2 + 1) := by
    have hsqrt0 := Real.sqrt_nonneg (4 * (b : ℝ) ^ 2 + 1)
    have hsqrtSq := Real.sq_sqrt (by positivity :
      (0 : ℝ) ≤ 4 * (b : ℝ) ^ 2 + 1)
    nlinarith
  have hbplus : 0 < (b : ℝ) + 1 := by positivity
  have hfrac := div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 2)
    (by positivity : (0 : ℝ) < 2 * ((b : ℝ) + 1))
    (by linarith : 2 * ((b : ℝ) + 1) ≤
      2 * (b : ℝ) + 1 + Real.sqrt (4 * (b : ℝ) ^ 2 + 1))
  unfold qAutoDeltaUpper delta
  push_cast
  calc
    2 / (2 * (b : ℝ) + 1 + Real.sqrt (4 * (b : ℝ) ^ 2 + 1)) ≤
        2 / (2 * ((b : ℝ) + 1)) := hfrac
    _ = 1 / ((b : ℝ) + 1) := by field_simp [hbplus.ne']

theorem qAutoSlope_bounds {b : ℚ} (hb : 0 ≤ b) (n : ℕ) :
    (qAutoSlopeLower b n : ℝ) ≤ logEnvelopeSlope (b : ℝ) ∧
      logEnvelopeSlope (b : ℝ) ≤ (qAutoSlopeUpper b : ℝ) := by
  have hlo := qAutoDeltaLower_sound' hb n
  have hhi := qAutoDeltaUpper_sound' hb
  have hbR : (0 : ℝ) ≤ b := by exact_mod_cast hb
  have hd0 := delta_pos hbR
  have hd1 := delta_le_one hbR
  have hdlo0q := qAutoDeltaLower_pos hb n
  have hdlo0 : (0 : ℝ) < qAutoDeltaLower b n := by exact_mod_cast hdlo0q
  have hdhi1q : qAutoDeltaUpper b ≤ 1 := by
    unfold qAutoDeltaUpper
    have : (0 : ℚ) < b + 1 := by positivity
    apply (div_le_iff₀ this).2
    linarith
  have hdhi1 : (qAutoDeltaUpper b : ℝ) ≤ 1 := by exact_mod_cast hdhi1q
  constructor
  · unfold qAutoSlopeLower logEnvelopeSlope
    push_cast
    nlinarith
  · unfold qAutoSlopeUpper logEnvelopeSlope
    push_cast
    nlinarith

theorem qKernelGradU_bounds {u v : ℚ} (hu : 0 < u) (hv : 0 < v) (n : ℕ) :
    (qKernelGradULower u v n : ℝ) ≤ kernelGradU (u : ℝ) (v : ℝ) ∧
      kernelGradU (u : ℝ) (v : ℝ) ≤ (qKernelGradUUpper u v : ℝ) := by
  have hbq : 0 ≤ qEdgeParameter u v := by
    unfold qEdgeParameter
    positivity
  have hs := qAutoSlope_bounds hbq n
  have hratio : (0 : ℝ) ≤ (v : ℝ) ^ 2 / (2 * ((u : ℝ) + v) ^ 2) := by
    positivity
  unfold qKernelGradULower qKernelGradUUpper kernelGradU
  push_cast
  rw [coe_qEdgeParameter] at hs
  constructor
  · have hm := mul_le_mul_of_nonneg_right hs.1 hratio
    simpa only [div_eq_mul_inv, mul_assoc] using
      add_le_add_right hm (1 / ((u : ℝ) + v))
  · have hm := mul_le_mul_of_nonneg_right hs.2 hratio
    simpa only [div_eq_mul_inv, mul_assoc] using
      add_le_add_right hm (1 / ((u : ℝ) + v))

theorem qKernelGradV_bounds {u v : ℚ} (hu : 0 < u) (hv : 0 < v) (n : ℕ) :
    (qKernelGradVLower u v n : ℝ) ≤ kernelGradV (u : ℝ) (v : ℝ) ∧
      kernelGradV (u : ℝ) (v : ℝ) ≤ (qKernelGradVUpper u v : ℝ) := by
  have hbq : 0 ≤ qEdgeParameter u v := by
    unfold qEdgeParameter
    positivity
  have hs := qAutoSlope_bounds hbq n
  have hratio : (0 : ℝ) ≤ (u : ℝ) ^ 2 / (2 * ((u : ℝ) + v) ^ 2) := by
    positivity
  unfold qKernelGradVLower qKernelGradVUpper kernelGradV
  push_cast
  rw [coe_qEdgeParameter] at hs
  constructor
  · have hm := mul_le_mul_of_nonneg_right hs.1 hratio
    simpa only [div_eq_mul_inv, mul_assoc] using
      add_le_add_right hm (1 / ((u : ℝ) + v))
  · have hm := mul_le_mul_of_nonneg_right hs.2 hratio
    simpa only [div_eq_mul_inv, mul_assoc] using
      add_le_add_right hm (1 / ((u : ℝ) + v))

end GDLowerBound.FourBlock
