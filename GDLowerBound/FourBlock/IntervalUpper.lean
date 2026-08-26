import Mathlib

/-! # A small exact interval-arithmetic primitive -/

namespace GDLowerBound.FourBlock

def qMulUpper (xl xh yl yh : ℚ) : ℚ :=
  max (xl * yl) (max (xl * yh) (max (xh * yl) (xh * yh)))

theorem mul_le_four_corners {xl xh yl yh x y : ℝ}
    (hxl : xl ≤ x) (hxh : x ≤ xh) (hyl : yl ≤ y) (hyh : y ≤ yh) :
    x * y ≤ max (xl * yl) (max (xl * yh) (max (xh * yl) (xh * yh))) := by
  by_cases hy0 : 0 ≤ y
  · have hxstep : x * y ≤ xh * y := mul_le_mul_of_nonneg_right hxh hy0
    by_cases hxh0 : 0 ≤ xh
    · have hcorner : xh * y ≤ xh * yh := mul_le_mul_of_nonneg_left hyh hxh0
      exact hxstep.trans (hcorner.trans (le_max_of_le_right (le_max_of_le_right (le_max_right _ _))))
    · have hxhneg : xh ≤ 0 := le_of_not_ge hxh0
      have hcorner : xh * y ≤ xh * yl := mul_le_mul_of_nonpos_left hyl hxhneg
      exact hxstep.trans (hcorner.trans
        (le_max_of_le_right (le_max_of_le_right (le_max_left _ _))))
  · have hyneg : y ≤ 0 := le_of_not_ge hy0
    have hxstep : x * y ≤ xl * y := mul_le_mul_of_nonpos_right hxl hyneg
    by_cases hxl0 : 0 ≤ xl
    · have hcorner : xl * y ≤ xl * yh := mul_le_mul_of_nonneg_left hyh hxl0
      exact hxstep.trans (hcorner.trans (le_max_of_le_right (le_max_left _ _)))
    · have hxlneg : xl ≤ 0 := le_of_not_ge hxl0
      have hcorner : xl * y ≤ xl * yl := mul_le_mul_of_nonpos_left hyl hxlneg
      exact hxstep.trans (hcorner.trans (le_max_left _ _))

theorem qMulUpper_sound {xl xh yl yh : ℚ} {x y : ℝ}
    (hxl : (xl : ℝ) ≤ x) (hxh : x ≤ (xh : ℝ))
    (hyl : (yl : ℝ) ≤ y) (hyh : y ≤ (yh : ℝ)) :
    x * y ≤ (qMulUpper xl xh yl yh : ℝ) := by
  have h := mul_le_four_corners hxl hxh hyl hyh
  simpa only [qMulUpper, Rat.cast_max, Rat.cast_mul] using h

end GDLowerBound.FourBlock
