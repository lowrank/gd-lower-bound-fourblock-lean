import GDLowerBound.FourBlock.FiniteWindowSamplingBounds

/-!
# Dyadic endpoint-sampling bounds

The fixed-dilation variation errors contain a harmonic block on `(j*M,j*N]`.
The dilation factor cancels its denominator, and scale invariance of the
logarithmic ratio gives explicit `O(R/M)` bounds when `N = 2^R M`.
-/

namespace GDLowerBound.FourBlock

open scoped BigOperators

noncomputable section

/-- Scaling both endpoints by the same positive natural number does not
change the logarithmic ratio controlling the adjacent harmonic weight. -/
theorem fixedDilationAdjacentHarmonicWeight_le_log_ratio
    {j M N : ℕ} (hj : 1 ≤ j) (hM : 1 ≤ M) (hMN : M ≤ N) :
    adjacentHarmonicWeight (j * M) (j * N) ≤
      Real.log ((N : ℝ) / (M : ℝ)) := by
  have hsum := harmonicBlock_le_log_ratio
    (show 1 ≤ j * M from Nat.mul_pos (by omega) (by omega))
    (Nat.mul_le_mul_left j hMN)
  have hj0 : (j : ℝ) ≠ 0 := by positivity
  have hM0 : (M : ℝ) ≠ 0 := by positivity
  have hratio :
      (((j * N : ℕ) : ℝ) / ((j * M : ℕ) : ℝ)) =
        (N : ℝ) / (M : ℝ) := by
    push_cast
    field_simp [hj0, hM0]
  unfold adjacentHarmonicWeight
  rwa [hratio] at hsum

/-- Generic logarithmic bound for the endpoint-defect sampling allowance. -/
theorem endpointDefectSamplingError_le_log_ratio
    {j M N : ℕ} (hj : 1 ≤ j) (hM : 1 ≤ M) (hMN : M ≤ N) :
    endpointDefectSamplingError j M N ≤
      (104 * Real.log ((N : ℝ) / (M : ℝ)) + 2) / (M : ℝ) := by
  have hh := fixedDilationAdjacentHarmonicWeight_le_log_ratio hj hM hMN
  have hweighted := mul_le_mul_of_nonneg_left hh (by norm_num : (0 : ℝ) ≤ 104)
  have hj0 : (j : ℝ) ≠ 0 := by positivity
  have hM0 : (M : ℝ) ≠ 0 := by positivity
  unfold endpointDefectSamplingError
  push_cast
  have hnum :
      104 * adjacentHarmonicWeight (j * M) (j * N) + 2 ≤
        104 * Real.log ((N : ℝ) / (M : ℝ)) + 2 := by
    linarith
  have hdiv := div_le_div_of_nonneg_right hnum (by positivity : (0 : ℝ) ≤ j * M)
  calc
    (j : ℝ) *
        ((104 * adjacentHarmonicWeight (j * M) (j * N) + 2) /
          ((j : ℝ) * (M : ℝ))) ≤
      (j : ℝ) *
        ((104 * Real.log ((N : ℝ) / (M : ℝ)) + 2) /
          ((j : ℝ) * (M : ℝ))) :=
            mul_le_mul_of_nonneg_left hdiv (by positivity)
    _ = (104 * Real.log ((N : ℝ) / (M : ℝ)) + 2) / (M : ℝ) := by
      field_simp [hj0, hM0]

/-- Generic logarithmic bound for the square-deviation sampling allowance. -/
theorem squareDeviationSamplingError_le_log_ratio
    {j M N : ℕ} (hj : 1 ≤ j) (hM : 1 ≤ M) (hMN : M ≤ N) :
    squareDeviationSamplingError j M N ≤
      (288 * Real.log ((N : ℝ) / (M : ℝ)) + 27) / (M : ℝ) := by
  have hh := fixedDilationAdjacentHarmonicWeight_le_log_ratio hj hM hMN
  have hweighted := mul_le_mul_of_nonneg_left hh (by norm_num : (0 : ℝ) ≤ 288)
  have hj0 : (j : ℝ) ≠ 0 := by positivity
  have hM0 : (M : ℝ) ≠ 0 := by positivity
  unfold squareDeviationSamplingError
  push_cast
  have hnum :
      288 * adjacentHarmonicWeight (j * M) (j * N) + 27 ≤
        288 * Real.log ((N : ℝ) / (M : ℝ)) + 27 := by
    linarith
  have hdiv := div_le_div_of_nonneg_right hnum (by positivity : (0 : ℝ) ≤ j * M)
  calc
    (j : ℝ) *
        ((288 * adjacentHarmonicWeight (j * M) (j * N) + 27) /
          ((j : ℝ) * (M : ℝ))) ≤
      (j : ℝ) *
        ((288 * Real.log ((N : ℝ) / (M : ℝ)) + 27) /
          ((j : ℝ) * (M : ℝ))) :=
            mul_le_mul_of_nonneg_left hdiv (by positivity)
    _ = (288 * Real.log ((N : ℝ) / (M : ℝ)) + 27) / (M : ℝ) := by
      field_simp [hj0, hM0]

theorem log_two_le_one : Real.log 2 ≤ (1 : ℝ) := by
  simpa [logTwoLowerCert] using
    (LogBoundCert.sound (c := logTwoLowerCert) (by native_decide)).2

theorem dyadic_log_ratio_le_depth
    {M R : ℕ} (hM : 1 ≤ M) :
    Real.log (((((2 ^ R) * M : ℕ) : ℝ) / (M : ℝ))) ≤ (R : ℝ) := by
  have hM0 : (M : ℝ) ≠ 0 := by positivity
  have hratio :
      (((((2 ^ R) * M : ℕ) : ℝ) / (M : ℝ))) = (2 : ℝ) ^ R := by
    push_cast
    field_simp [hM0]
  rw [hratio, Real.log_pow]
  exact mul_le_of_le_one_right (by positivity) log_two_le_one

/-- On a dyadic window, every fixed-dilation endpoint-defect sampling error
is at most `(104*R+2)/M`, independently of the dilation `j`. -/
theorem endpointDefectSamplingError_dyadic_le
    {j M R : ℕ} (hj : 1 ≤ j) (hM : 1 ≤ M) :
    endpointDefectSamplingError j M ((2 ^ R) * M) ≤
      (104 * (R : ℝ) + 2) / (M : ℝ) := by
  have hMN : M ≤ (2 ^ R) * M := by
    exact Nat.le_mul_of_pos_left M (pow_pos (by omega : 0 < 2) R)
  have hgeneric := endpointDefectSamplingError_le_log_ratio hj hM hMN
  have hlog := dyadic_log_ratio_le_depth (R := R) hM
  have hnum := mul_le_mul_of_nonneg_left hlog (by norm_num : (0 : ℝ) ≤ 104)
  exact hgeneric.trans (div_le_div_of_nonneg_right (by linarith) (by positivity))

/-- The square-deviation sampling error has the analogous dyadic bound
`(288*R+27)/M`. -/
theorem squareDeviationSamplingError_dyadic_le
    {j M R : ℕ} (hj : 1 ≤ j) (hM : 1 ≤ M) :
    squareDeviationSamplingError j M ((2 ^ R) * M) ≤
      (288 * (R : ℝ) + 27) / (M : ℝ) := by
  have hMN : M ≤ (2 ^ R) * M := by
    exact Nat.le_mul_of_pos_left M (pow_pos (by omega : 0 < 2) R)
  have hgeneric := squareDeviationSamplingError_le_log_ratio hj hM hMN
  have hlog := dyadic_log_ratio_le_depth (R := R) hM
  have hnum := mul_le_mul_of_nonneg_left hlog (by norm_num : (0 : ℝ) ≤ 288)
  exact hgeneric.trans (div_le_div_of_nonneg_right (by linarith) (by positivity))

end

end GDLowerBound.FourBlock
