import GDLowerBound.FourBlock.FiniteWindowMeanGrowth

/-!
# Basic finite-window sampling bounds

The control allowance and the two block remainders are reciprocal-square
sums.  They therefore have window-length-independent `O(1/M)` bounds.  This
separates them from the occupancy boundary bands, which are handled by a
different argument.
-/

namespace GDLowerBound.FourBlock

open scoped BigOperators
open GDLowerBound.RankAnalysis

noncomputable section

def controlAveragingCoefficient : ℝ :=
  (centralLambda2Q : ℝ) * oneStepLyapunovConstant criticalP / 2 +
    (centralLambda3Q : ℝ) * oneStepLyapunovConstant criticalP / 3

def dilationRemainderCoefficient (j : ℕ) : ℝ :=
  (betaLower + 9 / 2) / (j : ℝ)

theorem controlAveragingCoefficient_nonneg :
    0 ≤ controlAveragingCoefficient := by
  unfold controlAveragingCoefficient
  have hC : 0 ≤ oneStepLyapunovConstant criticalP :=
    zero_le_one.trans (oneStepLyapunovConstant_ge_one criticalP)
  have hl2 : (0 : ℝ) ≤ centralLambda2Q := by norm_num [centralLambda2Q]
  have hl3 : (0 : ℝ) ≤ centralLambda3Q := by norm_num [centralLambda3Q]
  positivity

theorem dilationRemainderCoefficient_nonneg {j : ℕ} (hj : 1 ≤ j) :
    0 ≤ dilationRemainderCoefficient j := by
  unfold dilationRemainderCoefficient
  positivity [betaLower_pos]

/-- The full averaged pointwise control allowance is `O(1/M)`. -/
theorem controlAveragingError_le_inv
    {M N : ℕ} (hM : 1 ≤ M) (hMN : M ≤ N) :
    controlAveragingError M N ≤
      controlAveragingCoefficient / (M : ℝ) := by
  have hpoint : ∀ m ∈ Finset.Ico (M + 1) (N + 1),
      scheduleControlError m / (m : ℝ) =
        controlAveragingCoefficient * (1 / (m : ℝ) ^ 2) := by
    intro m hm
    have hmIco := Finset.mem_Ico.mp hm
    have hm0 : (m : ℝ) ≠ 0 := by
      exact_mod_cast (show m ≠ 0 by omega)
    unfold scheduleControlError controlAveragingCoefficient
    push_cast
    field_simp [hm0]
  unfold controlAveragingError
  calc
    (∑ m ∈ Finset.Ico (M + 1) (N + 1),
        scheduleControlError m / (m : ℝ)) =
      controlAveragingCoefficient *
        ∑ m ∈ Finset.Ico (M + 1) (N + 1),
          1 / (m : ℝ) ^ 2 := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        exact hpoint
    _ ≤ controlAveragingCoefficient * (1 / (M : ℝ)) := by
      apply mul_le_mul_of_nonneg_left
      · exact reciprocalSquareBlock_le_inv hM hMN
      · exact controlAveragingCoefficient_nonneg
    _ = controlAveragingCoefficient / (M : ℝ) := by ring

/-- Each averaged dilation upper remainder is `O(1/M)`, uniformly in the
upper endpoint of the window. -/
theorem dilationBlockUpperRemainder_le_inv
    {j M N : ℕ} (hj : 1 ≤ j) (hM : 1 ≤ M) (hMN : M ≤ N) :
    dilationBlockUpperRemainder j M N ≤
      dilationRemainderCoefficient j / (M : ℝ) := by
  have hpoint : ∀ m ∈ Finset.Ico (M + 1) (N + 1),
      (betaLower / ((j * m : ℕ) : ℝ) +
          (9 / 2 : ℝ) *
            ∑ n ∈ Finset.Ico (j * m + 1) ((j + 1) * m + 1),
              1 / (n : ℝ) ^ 2) / (m : ℝ) ≤
        dilationRemainderCoefficient j * (1 / (m : ℝ) ^ 2) := by
    intro m hm
    have hmIco := Finset.mem_Ico.mp hm
    have hmNat : 1 ≤ m := by omega
    have hjm : 1 ≤ j * m := Nat.mul_pos (by omega) (by omega)
    have hjmhi : j * m ≤ (j + 1) * m :=
      Nat.mul_le_mul_right m (Nat.le_succ j)
    have hsquare := reciprocalSquareBlock_le_inv hjm hjmhi
    have hsquareWeighted := mul_le_mul_of_nonneg_left hsquare
      (by norm_num : (0 : ℝ) ≤ 9 / 2)
    have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
    have hj0 : (j : ℝ) ≠ 0 := by exact_mod_cast (show j ≠ 0 by omega)
    have hjm0 : (((j * m : ℕ) : ℝ)) ≠ 0 := by positivity
    have hdiv := div_le_div_of_nonneg_right
      (add_le_add_right hsquareWeighted
        (betaLower / (((j * m : ℕ) : ℝ))))
      (by positivity : (0 : ℝ) ≤ m)
    calc
      (betaLower / ((j * m : ℕ) : ℝ) +
          (9 / 2 : ℝ) *
            ∑ n ∈ Finset.Ico (j * m + 1) ((j + 1) * m + 1),
              1 / (n : ℝ) ^ 2) / (m : ℝ) ≤
        (betaLower / ((j * m : ℕ) : ℝ) +
          (9 / 2 : ℝ) * (1 / ((j * m : ℕ) : ℝ))) / (m : ℝ) := hdiv
      _ = dilationRemainderCoefficient j * (1 / (m : ℝ) ^ 2) := by
        unfold dilationRemainderCoefficient
        push_cast
        field_simp [hm0, hj0, hjm0]
  unfold dilationBlockUpperRemainder
  calc
    (∑ m ∈ Finset.Ico (M + 1) (N + 1),
        (betaLower / ((j * m : ℕ) : ℝ) +
          (9 / 2 : ℝ) *
            ∑ n ∈ Finset.Ico (j * m + 1) ((j + 1) * m + 1),
              1 / (n : ℝ) ^ 2) / (m : ℝ)) ≤
      ∑ m ∈ Finset.Ico (M + 1) (N + 1),
        dilationRemainderCoefficient j * (1 / (m : ℝ) ^ 2) :=
          Finset.sum_le_sum hpoint
    _ = dilationRemainderCoefficient j *
        ∑ m ∈ Finset.Ico (M + 1) (N + 1),
          1 / (m : ℝ) ^ 2 := by rw [Finset.mul_sum]
    _ ≤ dilationRemainderCoefficient j * (1 / (M : ℝ)) := by
      exact mul_le_mul_of_nonneg_left
        (reciprocalSquareBlock_le_inv hM hMN)
        (dilationRemainderCoefficient_nonneg hj)
    _ = dilationRemainderCoefficient j / (M : ℝ) := by ring

end

end GDLowerBound.FourBlock
