import GDLowerBound.FourBlock.FiniteWindowOccupancyBounds

/-!
# Explicit dyadic bound for the complete schedule-averaging error

All endpoint, block, occupancy, and control sampling terms are collected into
one expression.  The only depth-independent numerator is the fixed-ratio
occupancy boundary constant; every other term is `O(R/M)` or `O(1/M)`.
-/

namespace GDLowerBound.FourBlock

noncomputable section

def endpointSamplingDyadicNumerator (R : ℕ) : ℝ :=
  ((sideC2Q : ℝ) + (sideC3Q : ℝ) + (centralC4Q : ℝ)) *
      (288 * (R : ℝ) + 27) +
    ((sideD2Q : ℝ) + (sideD3Q : ℝ) + (centralD4Q : ℝ)) *
      (104 * (R : ℝ) + 2)

def occupancyBoundaryConstant : ℝ :=
  lambdaTwo * 6 + lambdaThree * 9

def blockSamplingDyadicNumerator (R : ℕ) : ℝ :=
  lambdaTwo *
      (9 + betaLower * (104 * (R : ℝ) + 2) +
        dilationRemainderCoefficient 2) +
    lambdaThree *
      (12 + betaLower * (104 * (R : ℝ) + 2) +
        dilationRemainderCoefficient 3)

def scheduleSamplingDyadicNumerator (R : ℕ) : ℝ :=
  endpointSamplingDyadicNumerator R +
    blockSamplingDyadicNumerator R + controlAveragingCoefficient

theorem occupancyBoundaryConstant_nonneg :
    0 ≤ occupancyBoundaryConstant := by
  unfold occupancyBoundaryConstant
  norm_num [lambdaTwo, lambdaThree]

theorem endpointSamplingDyadicNumerator_nonneg (R : ℕ) :
    0 ≤ endpointSamplingDyadicNumerator R := by
  unfold endpointSamplingDyadicNumerator
  have hR : (0 : ℝ) ≤ R := by positivity
  norm_num [sideC2Q, sideC3Q, centralC4Q,
    sideD2Q, sideD3Q, centralD4Q]
  positivity

theorem blockSamplingDyadicNumerator_nonneg (R : ℕ) :
    0 ≤ blockSamplingDyadicNumerator R := by
  unfold blockSamplingDyadicNumerator
  have hR : (0 : ℝ) ≤ R := by positivity
  have hd2 := dilationRemainderCoefficient_nonneg (j := 2) (by omega)
  have hd3 := dilationRemainderCoefficient_nonneg (j := 3) (by omega)
  have hb := betaLower_pos.le
  norm_num [lambdaTwo, lambdaThree] at *
  positivity

theorem scheduleSamplingDyadicNumerator_nonneg (R : ℕ) :
    0 ≤ scheduleSamplingDyadicNumerator R := by
  unfold scheduleSamplingDyadicNumerator
  positivity [endpointSamplingDyadicNumerator_nonneg R,
    blockSamplingDyadicNumerator_nonneg R,
    controlAveragingCoefficient_nonneg]

/-- The three endpoint energies contribute a completely explicit `O(R/M)`
sampling error on a dyadic window. -/
theorem endpointSamplingFiniteError_dyadic_le
    {M R : ℕ} (hM : 1 ≤ M) :
    endpointSamplingFiniteError M ((2 ^ R) * M) ≤
      endpointSamplingDyadicNumerator R / (M : ℝ) := by
  have hs2 := squareDeviationSamplingError_dyadic_le
    (j := 2) (R := R) (by omega) hM
  have hd2 := endpointDefectSamplingError_dyadic_le
    (j := 2) (R := R) (by omega) hM
  have hs3 := squareDeviationSamplingError_dyadic_le
    (j := 3) (R := R) (by omega) hM
  have hd3 := endpointDefectSamplingError_dyadic_le
    (j := 3) (R := R) (by omega) hM
  have hs4 := squareDeviationSamplingError_dyadic_le
    (j := 4) (R := R) (by omega) hM
  have hd4 := endpointDefectSamplingError_dyadic_le
    (j := 4) (R := R) (by omega) hM
  have hs2w := mul_le_mul_of_nonneg_left hs2
    (by norm_num [sideC2Q] : (0 : ℝ) ≤ sideC2Q)
  have hd2w := mul_le_mul_of_nonneg_left hd2
    (by norm_num [sideD2Q] : (0 : ℝ) ≤ sideD2Q)
  have hs3w := mul_le_mul_of_nonneg_left hs3
    (by norm_num [sideC3Q] : (0 : ℝ) ≤ sideC3Q)
  have hd3w := mul_le_mul_of_nonneg_left hd3
    (by norm_num [sideD3Q] : (0 : ℝ) ≤ sideD3Q)
  have hs4w := mul_le_mul_of_nonneg_left hs4
    (by norm_num [centralC4Q] : (0 : ℝ) ≤ centralC4Q)
  have hd4w := mul_le_mul_of_nonneg_left hd4
    (by norm_num [centralD4Q] : (0 : ℝ) ≤ centralD4Q)
  unfold endpointSamplingFiniteError endpointSamplingDyadicNumerator
  calc
    _ ≤
        (sideC2Q : ℝ) * ((288 * (R : ℝ) + 27) / (M : ℝ)) +
        (sideD2Q : ℝ) * ((104 * (R : ℝ) + 2) / (M : ℝ)) +
        (sideC3Q : ℝ) * ((288 * (R : ℝ) + 27) / (M : ℝ)) +
        (sideD3Q : ℝ) * ((104 * (R : ℝ) + 2) / (M : ℝ)) +
        (centralC4Q : ℝ) * ((288 * (R : ℝ) + 27) / (M : ℝ)) +
        (centralD4Q : ℝ) * ((104 * (R : ℝ) + 2) / (M : ℝ)) := by
          linarith
    _ = (((sideC2Q : ℝ) + (sideC3Q : ℝ) + (centralC4Q : ℝ)) *
          (288 * (R : ℝ) + 27) +
        ((sideD2Q : ℝ) + (sideD3Q : ℝ) + (centralD4Q : ℝ)) *
          (104 * (R : ℝ) + 2)) / (M : ℝ) := by ring

/-- Both dilation-block errors consist of a fixed boundary constant and an
explicit reciprocal term. -/
theorem blockSamplingFiniteError_dyadic_le
    {M R : ℕ} (hM : 2 ≤ M) :
    blockSamplingFiniteError M ((2 ^ R) * M) ≤
      occupancyBoundaryConstant +
        blockSamplingDyadicNumerator R / (M : ℝ) := by
  have hMN : M ≤ (2 ^ R) * M := by
    exact Nat.le_mul_of_pos_left M (pow_pos (by omega : 0 < 2) R)
  have ho2 := sum_twoOccupancyFiniteError_le hM hMN
  have ho3 := sum_threeOccupancyFiniteError_le hM hMN
  have hd2 := endpointDefectSamplingError_dyadic_le
    (j := 2) (M := M) (R := R) (by omega) (by omega)
  have hd3 := endpointDefectSamplingError_dyadic_le
    (j := 3) (M := M) (R := R) (by omega) (by omega)
  have hr2 := dilationBlockUpperRemainder_le_inv
    (j := 2) (N := (2 ^ R) * M) (by omega) (by omega) hMN
  have hr3 := dilationBlockUpperRemainder_le_inv
    (j := 3) (N := (2 ^ R) * M) (by omega) (by omega) hMN
  have hd2w := mul_le_mul_of_nonneg_left hd2 betaLower_pos.le
  have hd3w := mul_le_mul_of_nonneg_left hd3 betaLower_pos.le
  have hb2 :
      (∑ n ∈ Finset.Ico (2 * M + 1) (4 * ((2 ^ R) * M) + 1),
          twoOccupancyFiniteError M ((2 ^ R) * M) n) +
          betaLower * endpointDefectSamplingError 2 M ((2 ^ R) * M) +
          dilationBlockUpperRemainder 2 M ((2 ^ R) * M) ≤
        6 + (9 + betaLower * (104 * (R : ℝ) + 2) +
          dilationRemainderCoefficient 2) / (M : ℝ) := by
    calc
      _ ≤ (6 + 9 / (M : ℝ)) +
          betaLower * ((104 * (R : ℝ) + 2) / (M : ℝ)) +
          dilationRemainderCoefficient 2 / (M : ℝ) := by linarith
      _ = _ := by ring
  have hb3 :
      (∑ n ∈ Finset.Ico (2 * M + 1) (4 * ((2 ^ R) * M) + 1),
          threeOccupancyFiniteError M ((2 ^ R) * M) n) +
          betaLower * endpointDefectSamplingError 3 M ((2 ^ R) * M) +
          dilationBlockUpperRemainder 3 M ((2 ^ R) * M) ≤
        9 + (12 + betaLower * (104 * (R : ℝ) + 2) +
          dilationRemainderCoefficient 3) / (M : ℝ) := by
    calc
      _ ≤ (9 + 12 / (M : ℝ)) +
          betaLower * ((104 * (R : ℝ) + 2) / (M : ℝ)) +
          dilationRemainderCoefficient 3 / (M : ℝ) := by linarith
      _ = _ := by ring
  have hb2w := mul_le_mul_of_nonneg_left hb2
    (by norm_num [lambdaTwo] : 0 ≤ lambdaTwo)
  have hb3w := mul_le_mul_of_nonneg_left hb3
    (by norm_num [lambdaThree] : 0 ≤ lambdaThree)
  unfold blockSamplingFiniteError occupancyBoundaryConstant
    blockSamplingDyadicNumerator
  calc
    _ ≤ lambdaTwo *
          (6 + (9 + betaLower * (104 * (R : ℝ) + 2) +
            dilationRemainderCoefficient 2) / (M : ℝ)) +
        lambdaThree *
          (9 + (12 + betaLower * (104 * (R : ℝ) + 2) +
            dilationRemainderCoefficient 3) / (M : ℝ)) := by linarith
    _ = lambdaTwo * 6 + lambdaThree * 9 +
        (lambdaTwo *
            (9 + betaLower * (104 * (R : ℝ) + 2) +
              dilationRemainderCoefficient 2) +
          lambdaThree *
            (12 + betaLower * (104 * (R : ℝ) + 2) +
              dilationRemainderCoefficient 3)) / (M : ℝ) := by ring

/-- Complete unnormalized schedule-averaging error on the dyadic window. -/
theorem scheduleAveragingFiniteError_dyadic_le
    {M R : ℕ} (hM : 2 ≤ M) :
    scheduleAveragingFiniteError M ((2 ^ R) * M) ≤
      occupancyBoundaryConstant +
        scheduleSamplingDyadicNumerator R / (M : ℝ) := by
  have hMN : M ≤ (2 ^ R) * M := by
    exact Nat.le_mul_of_pos_left M (pow_pos (by omega : 0 < 2) R)
  have he := endpointSamplingFiniteError_dyadic_le (R := R) (by omega : 1 ≤ M)
  have hb := blockSamplingFiniteError_dyadic_le (R := R) hM
  have hc := controlAveragingError_le_inv (N := (2 ^ R) * M)
    (by omega : 1 ≤ M) hMN
  unfold scheduleAveragingFiniteError scheduleSamplingDyadicNumerator
  calc
    _ ≤ endpointSamplingDyadicNumerator R / (M : ℝ) +
        (occupancyBoundaryConstant +
          blockSamplingDyadicNumerator R / (M : ℝ)) +
        controlAveragingCoefficient / (M : ℝ) := by linarith
    _ = occupancyBoundaryConstant +
        (endpointSamplingDyadicNumerator R +
          blockSamplingDyadicNumerator R + controlAveragingCoefficient) /
            (M : ℝ) := by ring

/-- Normalized form used directly by the global four-block composition. -/
theorem normalizedScheduleAveragingError_dyadic_le
    {M R : ℕ} (hM : 2 ≤ M) (hR : 1 ≤ R) :
    normalizedScheduleAveragingError M ((2 ^ R) * M) ≤
      (occupancyBoundaryConstant +
          scheduleSamplingDyadicNumerator R / (M : ℝ)) /
        averagingHarmonicWeight M ((2 ^ R) * M) := by
  unfold normalizedScheduleAveragingError
  have hMN : M < (2 ^ R) * M := by
    have hp : 2 ≤ 2 ^ R := by
      have hp_prime : 2 ^ 1 ≤ 2 ^ R :=
        Nat.pow_le_pow_right (by omega : 0 < 2) hR
      norm_num at hp_prime ⊢
      exact hp_prime
    have hp_one : 1 < 2 ^ R := by omega
    have hmul := Nat.mul_lt_mul_of_pos_right hp_one (by omega : 0 < M)
    simpa using hmul
  exact div_le_div_of_nonneg_right
    (scheduleAveragingFiniteError_dyadic_le (R := R) hM)
    (averagingHarmonicWeight_pos (by omega) hMN).le

end

end GDLowerBound.FourBlock
