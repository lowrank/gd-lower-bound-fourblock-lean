import GDLowerBound.FourBlock.NormalizedAveragingComposition

/-!
# Uniform finite-window bounds for the rigidity slacks

The normalized composition theorem initially retains two errors depending on
the schedule.  Cutoff bounds at the endpoints, telescoping reciprocal
squares, and the adjacent-variation estimate replace both by explicit
functions of the averaging window.
-/

namespace GDLowerBound.FourBlock

open scoped BigOperators
open GDLowerBound.Schedule GDLowerBound.RankAnalysis

noncomputable section

def jointRigidityWindowBound (M N : ℕ) : ℝ :=
  (1 / criticalTheta +
      momentDriftConstant / (((2 * M : ℕ) : ℝ)) +
      ((104 * adjacentHarmonicWeight (2 * M) (4 * N) + 1) /
        (((2 * M : ℕ) : ℝ))) / criticalTheta) /
    averagingHarmonicWeight M N

def defectRigidityWindowBound (M N : ℕ) : ℝ :=
  ((betaLower + sharpDriftConstant / (((2 * M : ℕ) : ℝ))) /
      betaLower) /
    averagingHarmonicWeight M N

/-- A completely schedule-independent version of the normalized finite error
appearing in the global four-block composition. -/
def fourBlockWindowError (M N : ℕ) : ℝ :=
  squareWeightSum * jointRigidityWindowBound M N +
    defectSlackCoefficient * defectRigidityWindowBound M N +
    normalizedScheduleAveragingError M N

theorem commonReciprocalSquareSum_le_inv
    {M N : ℕ} (hM : 1 ≤ M) (hMN : M ≤ N) :
    commonReciprocalSquareSum M N ≤ 1 / (((2 * M : ℕ) : ℝ)) := by
  unfold commonReciprocalSquareSum
  exact reciprocalSquareBlock_le_inv (by omega : 1 ≤ 2 * M)
    (by omega : 2 * M ≤ 4 * N)

/-- The one-rank endpoint shift is uniformly bounded by the cutoff variation
budget on the common interval. -/
theorem commonEndpointShiftError_le_window
    {T Q : ℕ} (hQ : criticalTheta⁻¹ < (Q : ℝ))
    {h : StepSchedule T} (hh : IsNonnegativeSchedule h)
    {M N : ℕ} (hM : 1 ≤ M) (hMN : M ≤ N)
    (hQ2M : Q ≤ 2 * M) (h4N : 4 * N ≤ longCount h)
    (hcut : CutoffConditions criticalP h (2 * M) (longCount h)) :
    commonEndpointShiftError h M N ≤
      (104 * adjacentHarmonicWeight (2 * M) (4 * N) + 1) /
        (((2 * M : ℕ) : ℝ)) := by
  have hweighted := adjacentWeightedVariation_le_total_div
    (x := endpointDefect h) (lo := 2 * M) (hi := 4 * N)
    (by omega : 1 ≤ 2 * M)
  have htotal := endpointDefect_totalVariation hQ hh hQ2M
    (by omega : 2 * M ≤ 4 * N) h4N hcut
  unfold commonEndpointShiftError
  exact hweighted.trans
    (div_le_div_of_nonneg_right htotal (by positivity))

/-- Schedule-independent upper bound for the joint moment/defect rigidity
slack. -/
theorem commonJointRigidityError_le_window
    {T Q : ℕ} (hQ : criticalTheta⁻¹ < (Q : ℝ))
    {h : StepSchedule T} (hh : IsNonnegativeSchedule h)
    {M N : ℕ} (hM : 1 ≤ M) (hMN : M ≤ N)
    (hQ2M : Q ≤ 2 * M) (h4N : 4 * N ≤ longCount h)
    (hcut : CutoffConditions criticalP h (2 * M) (longCount h)) :
    commonJointRigidityError h M N ≤
      1 / criticalTheta +
        momentDriftConstant / (((2 * M : ℕ) : ℝ)) +
        ((104 * adjacentHarmonicWeight (2 * M) (4 * N) + 1) /
          (((2 * M : ℕ) : ℝ))) / criticalTheta := by
  have hstartMem : 2 * M ∈ Finset.Icc (2 * M) (longCount h) :=
    Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩
  have hendMem : 4 * N ∈ Finset.Icc (2 * M) (longCount h) :=
    Finset.mem_Icc.mpr ⟨by omega, h4N⟩
  obtain ⟨hstart0, hstart1⟩ := endpointDefect_cutoff_bounds hcut hstartMem
  obtain ⟨hend0, _hend1⟩ := endpointDefect_cutoff_bounds hcut hendMem
  have hendpoint :
      (endpointDefect h (2 * M) - endpointDefect h (4 * N)) /
          criticalTheta ≤ 1 / criticalTheta := by
    exact div_le_div_of_nonneg_right (by linarith) criticalTheta_pos.le
  have hsquare := commonReciprocalSquareSum_le_inv hM hMN
  have hsquareWeighted := mul_le_mul_of_nonneg_left hsquare
    (by norm_num [momentDriftConstant] : 0 ≤ momentDriftConstant)
  have hsquareWeighted' :
      momentDriftConstant * commonReciprocalSquareSum M N ≤
        momentDriftConstant / (((2 * M : ℕ) : ℝ)) := by
    simpa [div_eq_mul_inv] using hsquareWeighted
  have hshift := commonEndpointShiftError_le_window hQ hh hM hMN
    hQ2M h4N hcut
  have hshiftScaled := div_le_div_of_nonneg_right hshift criticalTheta_pos.le
  unfold commonJointRigidityError
  linarith

/-- Schedule-independent upper bound for the sharp defect rigidity slack. -/
theorem commonDefectRigidityError_le_window
    {T : ℕ} {h : StepSchedule T}
    {M N : ℕ} (hM : 1 ≤ M) (hMN : M ≤ N)
    (h4N : 4 * N ≤ longCount h)
    (hcut : CutoffConditions criticalP h (2 * M) (longCount h)) :
    commonDefectRigidityError h M N ≤
      (betaLower + sharpDriftConstant / (((2 * M : ℕ) : ℝ))) /
        betaLower := by
  have hstartMem : 2 * M ∈ Finset.Icc (2 * M) (longCount h) :=
    Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩
  have hendMem : 4 * N ∈ Finset.Icc (2 * M) (longCount h) :=
    Finset.mem_Icc.mpr ⟨by omega, h4N⟩
  obtain ⟨hzstart, hvstart, _hvstartHi, _⟩ := hcut (2 * M) hstartMem
  obtain ⟨hzend, hvend, _hvendHi, _⟩ := hcut (4 * N) hendMem
  have hestart := endpointDefect_cutoff_bounds hcut hstartMem
  have hpstart := scheduleCriticalPotential_le_endpointDefect
    hvstart.le hzstart.le
  have hpstart' : scheduleCriticalPotential h (2 * M) ≤ betaLower := by
    have hmul := mul_le_mul_of_nonneg_left hestart.2 betaLower_pos.le
    linarith
  have hpend := scheduleCriticalPotential_nonneg hvend.le hzend.le
  have hpotential :
      scheduleCriticalPotential h (2 * M) -
          scheduleCriticalPotential h (4 * N) ≤ betaLower := by
    linarith
  have hsquare := commonReciprocalSquareSum_le_inv hM hMN
  have hsquareWeighted := mul_le_mul_of_nonneg_left hsquare
    (by norm_num [sharpDriftConstant] : 0 ≤ sharpDriftConstant)
  have hsquareWeighted' :
      sharpDriftConstant * commonReciprocalSquareSum M N ≤
        sharpDriftConstant / (((2 * M : ℕ) : ℝ)) := by
    simpa [div_eq_mul_inv] using hsquareWeighted
  have hnumerator :
      scheduleCriticalPotential h (2 * M) -
          scheduleCriticalPotential h (4 * N) +
          sharpDriftConstant * commonReciprocalSquareSum M N ≤
        betaLower +
          sharpDriftConstant / (((2 * M : ℕ) : ℝ)) := by
    linarith
  unfold commonDefectRigidityError
  exact div_le_div_of_nonneg_right hnumerator betaLower_pos.le

theorem normalizedJointRigidityError_le_window
    {T Q : ℕ} (hQ : criticalTheta⁻¹ < (Q : ℝ))
    {h : StepSchedule T} (hh : IsNonnegativeSchedule h)
    {M N : ℕ} (hM : 1 ≤ M) (hMN : M < N)
    (hQ2M : Q ≤ 2 * M) (h4N : 4 * N ≤ longCount h)
    (hcut : CutoffConditions criticalP h (2 * M) (longCount h)) :
    normalizedJointRigidityError h M N ≤
      (1 / criticalTheta +
          momentDriftConstant / (((2 * M : ℕ) : ℝ)) +
          ((104 * adjacentHarmonicWeight (2 * M) (4 * N) + 1) /
            (((2 * M : ℕ) : ℝ))) / criticalTheta) /
        averagingHarmonicWeight M N := by
  unfold normalizedJointRigidityError
  exact div_le_div_of_nonneg_right
    (commonJointRigidityError_le_window hQ hh hM hMN.le
      hQ2M h4N hcut)
    (averagingHarmonicWeight_pos hM hMN).le

theorem normalizedDefectRigidityError_le_window
    {T : ℕ} {h : StepSchedule T}
    {M N : ℕ} (hM : 1 ≤ M) (hMN : M < N)
    (h4N : 4 * N ≤ longCount h)
    (hcut : CutoffConditions criticalP h (2 * M) (longCount h)) :
    normalizedDefectRigidityError h M N ≤
      ((betaLower + sharpDriftConstant / (((2 * M : ℕ) : ℝ))) /
          betaLower) /
        averagingHarmonicWeight M N := by
  unfold normalizedDefectRigidityError
  exact div_le_div_of_nonneg_right
    (commonDefectRigidityError_le_window hM hMN.le h4N hcut)
    (averagingHarmonicWeight_pos hM hMN).le

theorem normalizedErrorBudget_le_window
    {T Q : ℕ} (hQ : criticalTheta⁻¹ < (Q : ℝ))
    {h : StepSchedule T} (hh : IsNonnegativeSchedule h)
    {M N : ℕ} (hM : 1 ≤ M) (hMN : M < N)
    (hQ2M : Q ≤ 2 * M) (h4N : 4 * N ≤ longCount h)
    (hcut : CutoffConditions criticalP h (2 * M) (longCount h)) :
    squareWeightSum * normalizedJointRigidityError h M N +
        defectSlackCoefficient * normalizedDefectRigidityError h M N +
        normalizedScheduleAveragingError M N ≤
      fourBlockWindowError M N := by
  have hj := normalizedJointRigidityError_le_window hQ hh hM hMN
    hQ2M h4N hcut
  have hd := normalizedDefectRigidityError_le_window hM hMN h4N hcut
  have hjw := mul_le_mul_of_nonneg_left hj
    (by norm_num [squareWeightSum] : 0 ≤ squareWeightSum)
  have hdw := mul_le_mul_of_nonneg_left hd defectSlackCoefficient_nonneg
  unfold fourBlockWindowError jointRigidityWindowBound
    defectRigidityWindowBound
  linarith

end

end GDLowerBound.FourBlock
