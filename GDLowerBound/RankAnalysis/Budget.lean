import GDLowerBound.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset

namespace GDLowerBound.RankAnalysis

open scoped BigOperators

/-- The elementary tangent-line bound used in budget equalization. -/
theorem self_le_exp_sub_one (x : ℝ) : x ≤ Real.exp (x - 1) := by
  nlinarith [Real.add_one_le_exp (x - 1)]

/-- The second elementary exponential bound used in budget equalization.
The assumption `0 ≤ x` is exactly what is available for normalized gap
masses. -/
theorem sq_div_two_le_exp_sub_one {x : ℝ} (hx : 0 ≤ x) :
    x ^ 2 / 2 ≤ Real.exp (x - 1) := by
  by_cases hx2 : x ≤ 2
  · have hlin := self_le_exp_sub_one x
    nlinarith [sq_nonneg x]
  · have htwo : 2 ≤ x := le_of_not_ge hx2
    have hhalf_nonneg : 0 ≤ x / 2 := by positivity
    have hhalf : x / 2 ≤ Real.exp (x / 2 - 1) :=
      self_le_exp_sub_one (x / 2)
    have hsquare : (x / 2) ^ 2 ≤ (Real.exp (x / 2 - 1)) ^ 2 := by
      nlinarith [Real.exp_pos (x / 2 - 1)]
    have htwo_exp : (2 : ℝ) ≤ Real.exp 1 := by
      nlinarith [Real.add_one_le_exp (1 : ℝ)]
    calc
      x ^ 2 / 2 = 2 * (x / 2) ^ 2 := by ring
      _ ≤ 2 * (Real.exp (x / 2 - 1)) ^ 2 := by gcongr
      _ = 2 * Real.exp (x - 2) := by
        rw [pow_two, ← Real.exp_add]
        congr 2
        ring
      _ ≤ Real.exp 1 * Real.exp (x - 2) := by gcongr
      _ = Real.exp (x - 1) := by
        rw [← Real.exp_add]
        congr 1
        ring

/-- Pointwise factor estimate behind the product bound.  It is stated
without auxiliary names or divisions: after normalizing `u = ū x`, the
linear part uses `x ≤ exp(x-1)` and the quadratic part uses
`x²/2 ≤ exp(x-1)`. -/
theorem budgetFactor_le_exp {ubar u A B : ℝ}
    (hubar : 0 < ubar) (hu : 0 ≤ u) (hA : 0 ≤ A) (hB : 0 ≤ B) :
    u * (A + B * u) ≤
      ubar * (A + 2 * ubar * B) * Real.exp (u / ubar - 1) := by
  let x := u / ubar
  have hx : 0 ≤ x := div_nonneg hu hubar.le
  have hlin : A * x ≤ A * Real.exp (x - 1) :=
    mul_le_mul_of_nonneg_left (self_le_exp_sub_one x) hA
  have hquad : ubar * B * x ^ 2 ≤
      2 * ubar * B * Real.exp (x - 1) := by
    have hscale : 0 ≤ 2 * ubar * B := by positivity
    have := mul_le_mul_of_nonneg_left (sq_div_two_le_exp_sub_one hx) hscale
    nlinarith
  have hnormalized :
      x * (A + ubar * B * x) ≤
        (A + 2 * ubar * B) * Real.exp (x - 1) := by
    nlinarith
  have hscaled := mul_le_mul_of_nonneg_left hnormalized hubar.le
  dsimp only [x] at hscaled ⊢
  field_simp [hubar.ne'] at hscaled ⊢
  nlinarith

/-- Product equalization with a prescribed positive average.  This slightly
stronger form permits a quadratic factor at every coordinate; setting one
`B_i` to zero recovers the manuscript's terminal linear factor. -/
theorem budgetEqualizationAverage {q : ℕ} {ubar : ℝ} (hubar : 0 < ubar)
    (u A B : Fin q → ℝ)
    (hu : ∀ i, 0 ≤ u i) (hA : ∀ i, 0 ≤ A i) (hB : ∀ i, 0 ≤ B i)
    (hmass : ∑ i, u i ≤ (q : ℝ) * ubar) :
    (∏ i, u i) * ∏ i, (A i + B i * u i) ≤
      ubar ^ q * ∏ i, (A i + 2 * ubar * B i) := by
  have hpoint (i : Fin q) := budgetFactor_le_exp hubar (hu i) (hA i) (hB i)
  have hprod :
      ∏ i, (u i * (A i + B i * u i)) ≤
        ∏ i, (ubar * (A i + 2 * ubar * B i) *
          Real.exp (u i / ubar - 1)) := by
    apply Finset.prod_le_prod
    · intro i hi
      exact mul_nonneg (hu i) (add_nonneg (hA i) (mul_nonneg (hB i) (hu i)))
    · intro i hi
      exact hpoint i
  have hsum : ∑ i, (u i / ubar - 1) ≤ 0 := by
    have hdiv : (∑ i, u i) / ubar ≤ q := by
      rw [div_le_iff₀ hubar]
      simpa [mul_comm] using hmass
    calc
      ∑ i, (u i / ubar - 1) = (∑ i, u i) / ubar - q := by
        rw [Finset.sum_sub_distrib]
        simp [div_eq_mul_inv, Finset.sum_mul]
      _ ≤ 0 := by linarith
  have hexp : Real.exp (∑ i, (u i / ubar - 1)) ≤ 1 := by
    exact Real.exp_le_one_iff.mpr hsum
  have hbase_nonneg :
      0 ≤ ubar ^ q * ∏ i, (A i + 2 * ubar * B i) := by
    apply mul_nonneg (pow_nonneg hubar.le q)
    apply Finset.prod_nonneg
    intro i hi
    exact add_nonneg (hA i) (mul_nonneg (mul_nonneg (by norm_num) hubar.le) (hB i))
  calc
    (∏ i, u i) * ∏ i, (A i + B i * u i) =
        ∏ i, (u i * (A i + B i * u i)) := by
      rw [Finset.prod_mul_distrib]
    _ ≤ ∏ i, (ubar * (A i + 2 * ubar * B i) *
          Real.exp (u i / ubar - 1)) := hprod
    _ = (ubar ^ q * ∏ i, (A i + 2 * ubar * B i)) *
          Real.exp (∑ i, (u i / ubar - 1)) := by
      rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib]
      rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      rw [← Real.exp_sum]
    _ ≤ (ubar ^ q * ∏ i, (A i + 2 * ubar * B i)) * 1 := by
      exact mul_le_mul_of_nonneg_left hexp hbase_nonneg
    _ = ubar ^ q * ∏ i, (A i + 2 * ubar * B i) := by ring

/-- Manuscript form of budget equalization, with `ū=D/q`. -/
theorem budgetEqualization {q : ℕ} (hq : 0 < q)
    {D : ℝ} (hD : 0 < D)
    (u A B : Fin q → ℝ)
    (hu : ∀ i, 0 ≤ u i) (hA : ∀ i, 0 ≤ A i) (hB : ∀ i, 0 ≤ B i)
    (hmass : ∑ i, u i ≤ D) :
    (∏ i, u i) * ∏ i, (A i + B i * u i) ≤
      (D / q) ^ q * ∏ i, (A i + 2 * (D / q) * B i) := by
  have hqreal : (0 : ℝ) < q := by exact_mod_cast hq
  have hubar : 0 < D / (q : ℝ) := div_pos hD hqreal
  apply budgetEqualizationAverage hubar u A B hu hA hB
  convert hmass using 1
  field_simp

end GDLowerBound.RankAnalysis
