import GDLowerBound.FourBlock.FiniteWindowScheduleErrorBounds

/-!
# A single explicit dyadic bound for the finite-window error

This module adds the two rigidity terms to the complete schedule-sampling
bound.  It reduces `fourBlockWindowError M (2^R*M)` to a fixed numerator plus
an explicit reciprocal correction, divided by the exact harmonic mass.
-/

namespace GDLowerBound.FourBlock

noncomputable section

def dyadicJointNumerator (R : ℕ) : ℝ :=
  momentDriftConstant / 2 +
    ((104 * ((R : ℝ) + 1) + 1) / 2) / criticalTheta

def dyadicDefectNumerator : ℝ :=
  sharpDriftConstant / (2 * betaLower)

def dyadicWindowConstant : ℝ :=
  squareWeightSum * (1 / criticalTheta) +
    defectSlackCoefficient + occupancyBoundaryConstant

def dyadicWindowNumerator (R : ℕ) : ℝ :=
  squareWeightSum * dyadicJointNumerator R +
    defectSlackCoefficient * dyadicDefectNumerator +
    scheduleSamplingDyadicNumerator R

theorem dyadicJointNumerator_nonneg (R : ℕ) :
    0 ≤ dyadicJointNumerator R := by
  unfold dyadicJointNumerator
  have hR : (0 : ℝ) ≤ R := by positivity
  have ht := criticalTheta_pos.le
  norm_num [momentDriftConstant]
  positivity

theorem dyadicDefectNumerator_nonneg :
    0 ≤ dyadicDefectNumerator := by
  unfold dyadicDefectNumerator
  norm_num [sharpDriftConstant]
  positivity [betaLower_pos]

theorem dyadicWindowConstant_nonneg :
    0 ≤ dyadicWindowConstant := by
  unfold dyadicWindowConstant
  have hs : (0 : ℝ) ≤ squareWeightSum := by norm_num [squareWeightSum]
  positivity [criticalTheta_pos, defectSlackCoefficient_nonneg,
    occupancyBoundaryConstant_nonneg]

theorem dyadicWindowNumerator_nonneg (R : ℕ) :
    0 ≤ dyadicWindowNumerator R := by
  unfold dyadicWindowNumerator
  have hs : (0 : ℝ) ≤ squareWeightSum := by norm_num [squareWeightSum]
  positivity [dyadicJointNumerator_nonneg R,
    defectSlackCoefficient_nonneg, dyadicDefectNumerator_nonneg,
    scheduleSamplingDyadicNumerator_nonneg R]

/-- The larger harmonic block appearing in the endpoint-shift rigidity term
has only one more dyadic unit of logarithmic length. -/
theorem shiftedDyadicAdjacentHarmonicWeight_le
    {M R : ℕ} (hM : 1 ≤ M) :
    adjacentHarmonicWeight (2 * M) (4 * ((2 ^ R) * M)) ≤
      (R : ℝ) + 1 := by
  have hlo : 1 ≤ 2 * M := by omega
  have hlohi : 2 * M ≤ 4 * ((2 ^ R) * M) := by
    have hp : 1 ≤ 2 ^ R := one_le_pow₀ (by omega)
    nlinarith
  have hlog := harmonicBlock_le_log_ratio hlo hlohi
  have hM0 : (M : ℝ) ≠ 0 := by positivity
  have hratio :
      (((4 * ((2 ^ R) * M) : ℕ) : ℝ) / ((2 * M : ℕ) : ℝ)) =
        (2 : ℝ) ^ (R + 1) := by
    push_cast
    rw [pow_succ]
    field_simp [hM0]
    ring
  unfold adjacentHarmonicWeight
  rw [hratio, Real.log_pow] at hlog
  have hR : (0 : ℝ) ≤ R + 1 := by positivity
  have hupper := mul_le_mul_of_nonneg_left log_two_le_one hR
  norm_num at hupper
  exact hlog.trans (by simpa using hupper)

theorem jointRigidityWindowBound_dyadic_le
    {M R : ℕ} (hM : 1 ≤ M) (hR : 1 ≤ R) :
    jointRigidityWindowBound M ((2 ^ R) * M) ≤
      (1 / criticalTheta + dyadicJointNumerator R / (M : ℝ)) /
        averagingHarmonicWeight M ((2 ^ R) * M) := by
  have hshift := shiftedDyadicAdjacentHarmonicWeight_le (R := R) hM
  have hshift104 := mul_le_mul_of_nonneg_left hshift
    (by norm_num : (0 : ℝ) ≤ 104)
  have hshiftNum :
      104 * adjacentHarmonicWeight (2 * M) (4 * ((2 ^ R) * M)) + 1 ≤
        104 * ((R : ℝ) + 1) + 1 := by linarith
  have h2M : (0 : ℝ) ≤ ((2 * M : ℕ) : ℝ) := by positivity
  have hshiftDiv := div_le_div_of_nonneg_right hshiftNum h2M
  have hshiftTheta := div_le_div_of_nonneg_right hshiftDiv criticalTheta_pos.le
  have hMN : M < (2 ^ R) * M := by
    have hp : 2 ^ 1 ≤ 2 ^ R :=
      Nat.pow_le_pow_right (by omega : 0 < 2) hR
    norm_num at hp
    have hmul := Nat.mul_lt_mul_of_pos_right (show 1 < 2 ^ R by omega)
      (show 0 < M by omega)
    simpa using hmul
  have hH := averagingHarmonicWeight_pos hM hMN
  unfold jointRigidityWindowBound
  apply div_le_div_of_nonneg_right _ hH.le
  calc
    1 / criticalTheta +
          momentDriftConstant / (((2 * M : ℕ) : ℝ)) +
          ((104 * adjacentHarmonicWeight (2 * M)
                (4 * ((2 ^ R) * M)) + 1) /
            (((2 * M : ℕ) : ℝ))) /
            criticalTheta ≤
      1 / criticalTheta +
          momentDriftConstant / (((2 * M : ℕ) : ℝ)) +
          ((104 * ((R : ℝ) + 1) + 1) /
            (((2 * M : ℕ) : ℝ))) /
            criticalTheta := by linarith
    _ = 1 / criticalTheta + dyadicJointNumerator R / (M : ℝ) := by
      unfold dyadicJointNumerator
      have hM0 : (M : ℝ) ≠ 0 := by positivity
      push_cast
      field_simp [hM0]
      ring

theorem defectRigidityWindowBound_dyadic_eq
    {M R : ℕ} (hM : 1 ≤ M) :
    defectRigidityWindowBound M ((2 ^ R) * M) =
      (1 + dyadicDefectNumerator / (M : ℝ)) /
        averagingHarmonicWeight M ((2 ^ R) * M) := by
  unfold defectRigidityWindowBound dyadicDefectNumerator
  have hM0 : (M : ℝ) ≠ 0 := by positivity
  have hb0 : betaLower ≠ 0 := betaLower_pos.ne'
  push_cast
  field_simp [hM0, hb0]

/-- Master upper bound for every finite-window error in the sharper route. -/
theorem fourBlockWindowError_dyadic_le
    {M R : ℕ} (hM : 2 ≤ M) (hR : 1 ≤ R) :
    fourBlockWindowError M ((2 ^ R) * M) ≤
      (dyadicWindowConstant + dyadicWindowNumerator R / (M : ℝ)) /
        averagingHarmonicWeight M ((2 ^ R) * M) := by
  have hj := jointRigidityWindowBound_dyadic_le
    (R := R) (by omega : 1 ≤ M) hR
  have hd := defectRigidityWindowBound_dyadic_eq
    (R := R) (by omega : 1 ≤ M)
  have hs := normalizedScheduleAveragingError_dyadic_le hM hR
  have hjw := mul_le_mul_of_nonneg_left hj
    (by norm_num [squareWeightSum] : (0 : ℝ) ≤ squareWeightSum)
  have hdw := congrArg (fun x : ℝ ↦ defectSlackCoefficient * x) hd
  have hH : 0 < averagingHarmonicWeight M ((2 ^ R) * M) := by
    have hp : 2 ^ 1 ≤ 2 ^ R :=
      Nat.pow_le_pow_right (by omega : 0 < 2) hR
    norm_num at hp
    have hmul := Nat.mul_lt_mul_of_pos_right (show 1 < 2 ^ R by omega)
      (show 0 < M by omega)
    exact averagingHarmonicWeight_pos (by omega) (by simpa using hmul)
  unfold fourBlockWindowError dyadicWindowConstant dyadicWindowNumerator
  rw [hdw]
  calc
    _ ≤ squareWeightSum *
          ((1 / criticalTheta + dyadicJointNumerator R / (M : ℝ)) /
            averagingHarmonicWeight M ((2 ^ R) * M)) +
        defectSlackCoefficient *
          ((1 + dyadicDefectNumerator / (M : ℝ)) /
            averagingHarmonicWeight M ((2 ^ R) * M)) +
        (occupancyBoundaryConstant +
            scheduleSamplingDyadicNumerator R / (M : ℝ)) /
          averagingHarmonicWeight M ((2 ^ R) * M) := by linarith
    _ = (squareWeightSum * (1 / criticalTheta) +
          defectSlackCoefficient + occupancyBoundaryConstant +
          (squareWeightSum * dyadicJointNumerator R +
            defectSlackCoefficient * dyadicDefectNumerator +
            scheduleSamplingDyadicNumerator R) / (M : ℝ)) /
          averagingHarmonicWeight M ((2 ^ R) * M) := by ring

end

end GDLowerBound.FourBlock
