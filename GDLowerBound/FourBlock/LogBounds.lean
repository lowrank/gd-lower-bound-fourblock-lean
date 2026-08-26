import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Verified rational bounds for logarithms

For `y > 0` set `x = (y-1)/(y+1)`.  Then
`log y = 2 * (x + x^3/3 + ...)`.  Mathlib supplies a proved remainder
bound.  The definitions here package it in a form suitable for generated
rational certificates.
-/

namespace GDLowerBound.FourBlock

open scoped BigOperators

noncomputable section

def logRadius (y : ℝ) : ℝ := (y - 1) / (y + 1)

def logSeries (y : ℝ) (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range n,
    logRadius y ^ (2 * i + 1) / (2 * i + 1)

def logSeriesError (y : ℝ) (n : ℕ) : ℝ :=
  |logRadius y| ^ (2 * n + 1) / (1 - logRadius y ^ 2)

def logLower (y : ℝ) (n : ℕ) : ℝ :=
  2 * (logSeries y n - logSeriesError y n)

def logUpper (y : ℝ) (n : ℕ) : ℝ :=
  2 * (logSeries y n + logSeriesError y n)

theorem abs_logRadius_lt_one {y : ℝ} (hy : 0 < y) :
    |logRadius y| < 1 := by
  have hy1 : 0 < y + 1 := by linarith
  rw [abs_lt]
  constructor
  · unfold logRadius
    apply (lt_div_iff₀ hy1).2
    linarith
  · unfold logRadius
    apply (div_lt_iff₀ hy1).2
    linarith

theorem one_add_logRadius_div_one_sub {y : ℝ} (hy : 0 < y) :
    (1 + logRadius y) / (1 - logRadius y) = y := by
  have hy1 : y + 1 ≠ 0 := by linarith
  unfold logRadius
  field_simp [hy1]
  ring

/-- Sound lower and upper logarithm bounds.  When `y` is rational, both
endpoints reduce to rational arithmetic and can be discharged by `norm_num`
or by a generated native checker. -/
theorem log_mem_series_bounds {y : ℝ} (hy : 0 < y) (n : ℕ) :
    logLower y n ≤ Real.log y ∧ Real.log y ≤ logUpper y n := by
  let x := logRadius y
  have hx : |x| < 1 := abs_logRadius_lt_one hy
  have hrem := Real.sum_range_sub_log_div_le hx n
  have hratio : (1 + x) / (1 - x) = y :=
    one_add_logRadius_div_one_sub hy
  rw [hratio] at hrem
  have hbounds := abs_le.mp hrem
  unfold logLower logUpper logSeries logSeriesError
  dsimp only [x] at hbounds
  constructor <;> linarith

theorem logLower_le {y : ℝ} (hy : 0 < y) (n : ℕ) :
    logLower y n ≤ Real.log y :=
  (log_mem_series_bounds hy n).1

theorem le_logUpper {y : ℝ} (hy : 0 < y) (n : ℕ) :
    Real.log y ≤ logUpper y n :=
  (log_mem_series_bounds hy n).2

end

end GDLowerBound.FourBlock
