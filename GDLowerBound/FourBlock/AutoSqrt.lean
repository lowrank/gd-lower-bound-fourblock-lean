import GDLowerBound.FourBlock.RationalBounds

/-!
# Automatically checked rational square-root upper bounds

For `x ≥ 1`, `(x+1)/2` is an upper bound for `sqrt x`.  Newton's map
`u ↦ (u+x/u)/2` preserves upper bounds and rapidly sharpens them.  Since all
iterations are rational, large generated certificates need record only an
iteration count, not a separate square-root enclosure at every node.
-/

namespace GDLowerBound.FourBlock

def qSqrtNewtonStep (x u : ℚ) : ℚ := (u + x / u) / 2

def qSqrtNewtonUpper (x : ℚ) : ℕ → ℚ
  | 0 => (x + 1) / 2
  | n + 1 => qSqrtNewtonStep x (qSqrtNewtonUpper x n)

theorem qSqrtNewtonStep_valid {x u : ℚ} (hx : 0 ≤ x)
    (hu : 0 < u) (hxu : x ≤ u ^ 2) :
    0 < qSqrtNewtonStep x u ∧
      x ≤ (qSqrtNewtonStep x u) ^ 2 := by
  have hu0 : u ≠ 0 := hu.ne'
  have hxdiv : 0 ≤ x / u := div_nonneg hx hu.le
  constructor
  · unfold qSqrtNewtonStep
    positivity
  · have hid :
        (qSqrtNewtonStep x u) ^ 2 - x =
          (u ^ 2 - x) ^ 2 / (4 * u ^ 2) := by
      unfold qSqrtNewtonStep
      field_simp [hu0]
      ring
    rw [← sub_nonneg, hid]
    positivity

theorem qSqrtNewtonUpper_valid {x : ℚ} (hx : 1 ≤ x) (n : ℕ) :
    0 < qSqrtNewtonUpper x n ∧ x ≤ (qSqrtNewtonUpper x n) ^ 2 := by
  induction n with
  | zero =>
      constructor
      · simp [qSqrtNewtonUpper]
        linarith
      · simp only [qSqrtNewtonUpper]
        have hs := sq_nonneg (x - 1)
        nlinarith
  | succ n ih =>
      simp only [qSqrtNewtonUpper]
      exact qSqrtNewtonStep_valid (zero_le_one.trans hx) ih.1 ih.2

theorem qSqrtNewtonUpper_sound {x : ℚ} (hx : 1 ≤ x) (n : ℕ) :
    Real.sqrt (x : ℝ) ≤ (qSqrtNewtonUpper x n : ℝ) := by
  have hvalid := qSqrtNewtonUpper_valid hx n
  have hx0 : (0 : ℝ) ≤ x := by exact_mod_cast (zero_le_one.trans hx)
  have hu0 : (0 : ℝ) ≤ qSqrtNewtonUpper x n := by
    exact_mod_cast hvalid.1.le
  have hsq : (x : ℝ) ≤ (qSqrtNewtonUpper x n : ℝ) ^ 2 := by
    exact_mod_cast hvalid.2
  have hsqrt0 := Real.sqrt_nonneg (x : ℝ)
  have hsqrtSq := Real.sq_sqrt hx0
  nlinarith [sq_nonneg
    ((qSqrtNewtonUpper x n : ℝ) - Real.sqrt (x : ℝ))]

end GDLowerBound.FourBlock
