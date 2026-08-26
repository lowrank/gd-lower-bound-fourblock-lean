import GDLowerBound.FourBlock.AveragedScheduleEnergy

/-!
# Finite rigidity budgets on the common averaging interval

The sharp and moment recurrences are rewritten in terms of the common sums
used by `averagedScheduleEnergy_upper`.  The one-rank endpoint-defect shift is
retained explicitly as weighted variation.
-/

namespace GDLowerBound.FourBlock

open scoped BigOperators
open GDLowerBound.Schedule GDLowerBound.RankAnalysis

noncomputable section

def commonPreviousDefectSum {T : ℕ}
    (h : StepSchedule T) (M N : ℕ) : ℝ :=
  ∑ n ∈ Finset.Ico (2 * M + 1) (4 * N + 1),
    endpointDefect h (n - 1) / (n : ℝ)

def commonReciprocalSquareSum (M N : ℕ) : ℝ :=
  ∑ n ∈ Finset.Ico (2 * M + 1) (4 * N + 1),
    1 / (n : ℝ) ^ 2

def commonEndpointShiftError {T : ℕ}
    (h : StepSchedule T) (M N : ℕ) : ℝ :=
  adjacentWeightedVariation (endpointDefect h) (2 * M) (4 * N)

def commonJointRigidityError {T : ℕ}
    (h : StepSchedule T) (M N : ℕ) : ℝ :=
  (endpointDefect h (2 * M) - endpointDefect h (4 * N)) /
      criticalTheta +
    momentDriftConstant * commonReciprocalSquareSum M N +
    commonEndpointShiftError h M N / criticalTheta

def commonDefectRigidityError {T : ℕ}
    (h : StepSchedule T) (M N : ℕ) : ℝ :=
  (scheduleCriticalPotential h (2 * M) -
      scheduleCriticalPotential h (4 * N) +
      sharpDriftConstant * commonReciprocalSquareSum M N) / betaLower

/-- Shifting `e_(n-1)` to `e_n` costs exactly the weighted adjacent
variation. -/
theorem commonDefectSum_le_previous_add_shift
    {T : ℕ} (h : StepSchedule T) {M N : ℕ} (hM : 1 ≤ M) :
    commonDefectSum h M N ≤
      commonPreviousDefectSum h M N + commonEndpointShiftError h M N := by
  have hterm : ∀ n ∈ Finset.Ico (2 * M + 1) (4 * N + 1),
      endpointDefect h n / (n : ℝ) ≤
        endpointDefect h (n - 1) / (n : ℝ) +
          |endpointDefect h n - endpointDefect h (n - 1)| / (n : ℝ) := by
    intro n hn
    have hnIco := Finset.mem_Ico.mp hn
    have hn0 : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
    have hdiff : endpointDefect h n - endpointDefect h (n - 1) ≤
        |endpointDefect h n - endpointDefect h (n - 1)| := le_abs_self _
    have hdiv := div_le_div_of_nonneg_right hdiff hn0.le
    ring_nf at hdiv ⊢
    linarith
  unfold commonDefectSum commonPreviousDefectSum commonEndpointShiftError
    adjacentWeightedVariation
  calc
    ∑ n ∈ Finset.Ico (2 * M + 1) (4 * N + 1),
        endpointDefect h n / (n : ℝ) ≤
      ∑ n ∈ Finset.Ico (2 * M + 1) (4 * N + 1),
        (endpointDefect h (n - 1) / (n : ℝ) +
          |endpointDefect h n - endpointDefect h (n - 1)| / (n : ℝ)) :=
      Finset.sum_le_sum hterm
    _ = (∑ n ∈ Finset.Ico (2 * M + 1) (4 * N + 1),
          endpointDefect h (n - 1) / (n : ℝ)) +
        ∑ n ∈ Finset.Ico (2 * M + 1) (4 * N + 1),
          |endpointDefect h n - endpointDefect h (n - 1)| / (n : ℝ) := by
      rw [Finset.sum_add_distrib]

/-- Moment rigidity expressed using the unshifted common endpoint defect. -/
theorem commonMomentRigidityBudget
    {T Q : ℕ} (hQ : criticalTheta⁻¹ < (Q : ℝ))
    {h : StepSchedule T} (hh : IsNonnegativeSchedule h)
    {M N : ℕ} (hM : 1 ≤ M) (hMN : M ≤ N)
    (hQ2M : Q ≤ 2 * M) (h4N : 4 * N ≤ longCount h)
    (hcut : CutoffConditions criticalP h (2 * M) (longCount h)) :
    commonSquareDeviationSum h M N +
        commonDefectSum h M N / criticalTheta ≤
      2 * (betaLower + 1) * commonMeanDeficitSum h M N +
        commonJointRigidityError h M N := by
  have hmoment := scheduleMomentRigidityBudget hQ hh hQ2M
    (by omega : 2 * M ≤ 4 * N) h4N hcut
  have hshift := commonDefectSum_le_previous_add_shift h (N := N) hM
  have hshiftScaled : commonDefectSum h M N / criticalTheta ≤
      commonPreviousDefectSum h M N / criticalTheta +
        commonEndpointShiftError h M N / criticalTheta := by
    have hs := div_le_div_of_nonneg_right hshift criticalTheta_pos.le
    calc
      commonDefectSum h M N / criticalTheta ≤
          (commonPreviousDefectSum h M N +
            commonEndpointShiftError h M N) / criticalTheta := hs
      _ = commonPreviousDefectSum h M N / criticalTheta +
          commonEndpointShiftError h M N / criticalTheta := by ring
  have hlhs :
      (∑ n ∈ Finset.Ico (2 * M + 1) (4 * N + 1),
        ((relativeMassIncrement h n - betaLower) ^ 2 +
          endpointDefect h (n - 1) / criticalTheta) / (n : ℝ)) =
        commonSquareDeviationSum h M N +
          commonPreviousDefectSum h M N / criticalTheta := by
    unfold commonSquareDeviationSum commonPreviousDefectSum
    calc
      (∑ n ∈ Finset.Ico (2 * M + 1) (4 * N + 1),
        ((relativeMassIncrement h n - betaLower) ^ 2 +
          endpointDefect h (n - 1) / criticalTheta) / (n : ℝ)) =
        ∑ n ∈ Finset.Ico (2 * M + 1) (4 * N + 1),
          ((relativeMassIncrement h n - betaLower) ^ 2 / (n : ℝ) +
            (endpointDefect h (n - 1) / (n : ℝ)) / criticalTheta) := by
          apply Finset.sum_congr rfl
          intro n _
          ring
      _ = (∑ n ∈ Finset.Ico (2 * M + 1) (4 * N + 1),
            (relativeMassIncrement h n - betaLower) ^ 2 / (n : ℝ)) +
          (∑ n ∈ Finset.Ico (2 * M + 1) (4 * N + 1),
            endpointDefect h (n - 1) / (n : ℝ)) / criticalTheta := by
          rw [Finset.sum_add_distrib, Finset.sum_div]
  have hmoment' :
      commonSquareDeviationSum h M N +
          commonPreviousDefectSum h M N / criticalTheta ≤
        2 * (betaLower + 1) * commonMeanDeficitSum h M N +
          (endpointDefect h (2 * M) - endpointDefect h (4 * N)) /
            criticalTheta +
          momentDriftConstant * commonReciprocalSquareSum M N := by
    rw [hlhs] at hmoment
    simpa [commonMeanDeficitSum, commonReciprocalSquareSum] using hmoment
  unfold commonJointRigidityError
  linarith

/-- Sharp defect rigidity in the additive-error form required by the robust
global linear program. -/
theorem commonSharpRigidityBudget
    {T Q : ℕ} (hQ : criticalTheta⁻¹ < (Q : ℝ))
    {h : StepSchedule T} (hh : IsNonnegativeSchedule h)
    {M N : ℕ} (hM : 1 ≤ M) (hMN : M ≤ N)
    (hQ2M : Q ≤ 2 * M) (h4N : 4 * N ≤ longCount h)
    (hcut : CutoffConditions criticalP h (2 * M) (longCount h)) :
    commonDefectSum h M N ≤
      commonMeanDeficitSum h M N / betaLower +
        commonDefectRigidityError h M N := by
  have hsharp := scheduleSharpRigidityBudget hQ hh hQ2M
    (by omega : 2 * M ≤ 4 * N) h4N hcut
  have hsharp' :
      -commonMeanDeficitSum h M N +
          betaLower * commonDefectSum h M N ≤
        scheduleCriticalPotential h (2 * M) -
          scheduleCriticalPotential h (4 * N) +
          sharpDriftConstant * commonReciprocalSquareSum M N := by
    unfold commonMeanDeficitSum commonDefectSum commonReciprocalSquareSum
    rw [Finset.mul_sum]
    rw [← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
    convert hsharp using 1
    apply Finset.sum_congr rfl
    intro n _
    ring
  unfold commonDefectRigidityError
  rw [← add_div]
  apply (le_div_iff₀ betaLower_pos).2
  linarith

end

end GDLowerBound.FourBlock
