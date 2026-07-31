import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace GDLowerBound

open scoped Real

/-- The exponent appearing in the lower-bound theorem. -/
noncomputable def pStar : ℝ := Real.sqrt (2 + Real.sqrt 3)

theorem pStar_nonneg : 0 ≤ pStar := by
  exact Real.sqrt_nonneg _

theorem pStar_sq : pStar ^ 2 = 2 + Real.sqrt 3 := by
  rw [pStar, Real.sq_sqrt]
  positivity

theorem one_lt_pStar : 1 < pStar := by
  have hs_nonneg : 0 ≤ Real.sqrt 3 := Real.sqrt_nonneg _
  have hs_sq : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hs_gt : 1 < Real.sqrt 3 := by nlinarith
  have hp_nonneg := pStar_nonneg
  have hp_sq := pStar_sq
  nlinarith

theorem pStar_lt_two : pStar < 2 := by
  have hs_nonneg : 0 ≤ Real.sqrt 3 := Real.sqrt_nonneg _
  have hs_sq : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hs_lt : Real.sqrt 3 < 2 := by nlinarith
  have hp_nonneg := pStar_nonneg
  have hp_sq := pStar_sq
  nlinarith

end GDLowerBound
