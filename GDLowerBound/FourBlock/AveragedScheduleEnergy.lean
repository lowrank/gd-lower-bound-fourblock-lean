import GDLowerBound.FourBlock.AveragedDilationBlocks
import GDLowerBound.FourBlock.SchedulePointwise

/-!
# Full finite averaged schedule-energy upper bound

The three endpoint costs and two dilation blocks are combined here.  The
main theorem has exactly the asymptotic `averagedEnergyBudget` plus one
explicit finite error depending only on the averaging window.
-/

namespace GDLowerBound.FourBlock

open scoped BigOperators
open GDLowerBound.Schedule GDLowerBound.RankAnalysis

noncomputable section

def scheduleEndpointEnergy {T : ℕ} (h : StepSchedule T) (m : ℕ) : ℝ :=
  endpointCost sideC2Q sideD2Q
      (zetaState h (2 * m)) (relativeMassIncrement h (2 * m)) +
    endpointCost sideC3Q sideD3Q
      (zetaState h (3 * m)) (relativeMassIncrement h (3 * m)) +
    endpointCost centralC4Q centralD4Q
      (zetaState h (4 * m)) (relativeMassIncrement h (4 * m))

def endpointSamplingFiniteError (M N : ℕ) : ℝ :=
  (sideC2Q : ℝ) * squareDeviationSamplingError 2 M N +
    (sideD2Q : ℝ) * endpointDefectSamplingError 2 M N +
  (sideC3Q : ℝ) * squareDeviationSamplingError 3 M N +
    (sideD3Q : ℝ) * endpointDefectSamplingError 3 M N +
  (centralC4Q : ℝ) * squareDeviationSamplingError 4 M N +
    (centralD4Q : ℝ) * endpointDefectSamplingError 4 M N

def blockSamplingFiniteError (M N : ℕ) : ℝ :=
  lambdaTwo *
      ((∑ n ∈ Finset.Ico (2 * M + 1) (4 * N + 1),
          twoOccupancyFiniteError M N n) +
        betaLower * endpointDefectSamplingError 2 M N +
        dilationBlockUpperRemainder 2 M N) +
    lambdaThree *
      ((∑ n ∈ Finset.Ico (2 * M + 1) (4 * N + 1),
          threeOccupancyFiniteError M N n) +
        betaLower * endpointDefectSamplingError 3 M N +
        dilationBlockUpperRemainder 3 M N)

def controlAveragingError (M N : ℕ) : ℝ :=
  ∑ m ∈ Finset.Ico (M + 1) (N + 1),
    scheduleControlError m / (m : ℝ)

def scheduleAveragingFiniteError (M N : ℕ) : ℝ :=
  endpointSamplingFiniteError M N + blockSamplingFiniteError M N +
    controlAveragingError M N

private theorem averagedEndpointCost_fixedDilation_le_common
    {T Q : ℕ} (hQ : criticalTheta⁻¹ < (Q : ℝ))
    {h : StepSchedule T} (hh : IsNonnegativeSchedule h)
    {c d : ℝ} (hc : 0 ≤ c) (hd : 0 ≤ d)
    {j M N : ℕ} (hjlo : 2 ≤ j) (hjhi : j ≤ 4) (hMN : M ≤ N)
    (hM : 4 ≤ M) (hQ2M : Q ≤ 2 * M)
    (h4N : 4 * N ≤ longCount h)
    (hcut : CutoffConditions criticalP h (2 * M) (longCount h)) :
    ∑ m ∈ Finset.Ico (M + 1) (N + 1),
        endpointCost c d (zetaState h (j * m))
          (relativeMassIncrement h (j * m)) / (m : ℝ) ≤
      c * (commonSquareDeviationSum h M N +
          squareDeviationSamplingError j M N) +
        d * (commonDefectSum h M N +
          endpointDefectSamplingError j M N) := by
  have hsquare := squareDeviation_fixedDilationSample_le_common hh
    hjlo hjhi hMN (by omega : 8 ≤ 2 * M) h4N hcut
  have hdefect := endpointDefect_fixedDilationSample_le_common hQ hh
    hjlo hjhi hMN hQ2M h4N hcut
  have hcsquare := mul_le_mul_of_nonneg_left hsquare hc
  have hddefect := mul_le_mul_of_nonneg_left hdefect hd
  calc
    ∑ m ∈ Finset.Ico (M + 1) (N + 1),
        endpointCost c d (zetaState h (j * m))
          (relativeMassIncrement h (j * m)) / (m : ℝ) =
      c * ∑ m ∈ Finset.Ico (M + 1) (N + 1),
          (relativeMassIncrement h (j * m) - betaLower) ^ 2 / (m : ℝ) +
        d * ∑ m ∈ Finset.Ico (M + 1) (N + 1),
          endpointDefect h (j * m) / (m : ℝ) := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro m _
      unfold endpointCost endpointDefect
      ring
    _ ≤ c * (commonSquareDeviationSum h M N +
          squareDeviationSamplingError j M N) +
        d * (commonDefectSum h M N +
          endpointDefectSamplingError j M N) := add_le_add hcsquare hddefect

/-- All three sampled endpoint costs, with exact aggregate coefficients. -/
theorem averagedScheduleEndpointEnergy_upper
    {T Q : ℕ} (hQ : criticalTheta⁻¹ < (Q : ℝ))
    {h : StepSchedule T} (hh : IsNonnegativeSchedule h)
    {M N : ℕ} (hM : 8 ≤ M) (hMN : M ≤ N)
    (hQ2M : Q ≤ 2 * M) (h4N : 4 * N ≤ longCount h)
    (hcut : CutoffConditions criticalP h (2 * M) (longCount h)) :
    ∑ m ∈ Finset.Ico (M + 1) (N + 1),
        scheduleEndpointEnergy h m / (m : ℝ) ≤
      squareWeightSum * commonSquareDeviationSum h M N +
        defectWeightSum * commonDefectSum h M N +
        endpointSamplingFiniteError M N := by
  have h2 := averagedEndpointCost_fixedDilation_le_common hQ hh
    (c := (sideC2Q : ℝ)) (d := (sideD2Q : ℝ))
    (by norm_num [sideC2Q]) (by norm_num [sideD2Q])
    (j := 2) (by omega) (by omega) hMN (by omega) hQ2M h4N hcut
  have h3 := averagedEndpointCost_fixedDilation_le_common hQ hh
    (c := (sideC3Q : ℝ)) (d := (sideD3Q : ℝ))
    (by norm_num [sideC3Q]) (by norm_num [sideD3Q])
    (j := 3) (by omega) (by omega) hMN (by omega) hQ2M h4N hcut
  have h4 := averagedEndpointCost_fixedDilation_le_common hQ hh
    (c := (centralC4Q : ℝ)) (d := (centralD4Q : ℝ))
    (by norm_num [centralC4Q]) (by norm_num [centralD4Q])
    (j := 4) (by omega) (by omega) hMN (by omega) hQ2M h4N hcut
  have hsplit :
      ∑ m ∈ Finset.Ico (M + 1) (N + 1),
          scheduleEndpointEnergy h m / (m : ℝ) =
        (∑ m ∈ Finset.Ico (M + 1) (N + 1),
          endpointCost sideC2Q sideD2Q
            (zetaState h (2 * m)) (relativeMassIncrement h (2 * m)) /
              (m : ℝ)) +
        (∑ m ∈ Finset.Ico (M + 1) (N + 1),
          endpointCost sideC3Q sideD3Q
            (zetaState h (3 * m)) (relativeMassIncrement h (3 * m)) /
              (m : ℝ)) +
        ∑ m ∈ Finset.Ico (M + 1) (N + 1),
          endpointCost centralC4Q centralD4Q
            (zetaState h (4 * m)) (relativeMassIncrement h (4 * m)) /
              (m : ℝ) := by
    unfold scheduleEndpointEnergy
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro m _
    ring
  rw [hsplit]
  unfold endpointSamplingFiniteError
  norm_num [squareWeightSum, defectWeightSum, sideC2Q, sideD2Q,
    sideC3Q, sideD3Q, centralC4Q, centralD4Q] at h2 h3 h4 ⊢
  linarith

/-- Full averaged energy, including the pointwise control allowance. -/
theorem averagedScheduleEnergy_upper
    {T Q : ℕ} (hQ : criticalTheta⁻¹ < (Q : ℝ))
    {h : StepSchedule T} (hh : IsNonnegativeSchedule h)
    {M N : ℕ} (hM : 8 ≤ M) (hMN : M ≤ N)
    (hQ2M : Q ≤ 2 * M) (h4N : 4 * N ≤ longCount h)
    (hcut : CutoffConditions criticalP h (2 * M) (longCount h)) :
    ∑ m ∈ Finset.Ico (M + 1) (N + 1),
        (scheduleDilationEnergy h m + scheduleControlError m) / (m : ℝ) ≤
      averagedEnergyBudget (commonSquareDeviationSum h M N)
          (commonDefectSum h M N) (commonMeanDeficitSum h M N) +
        scheduleAveragingFiniteError M N := by
  have hend := averagedScheduleEndpointEnergy_upper hQ hh hM hMN
    hQ2M h4N hcut
  have hb2 := averagedDilationBlock_two_upper hQ hh hM hMN
    hQ2M h4N hcut
  have hb3 := averagedDilationBlock_three_upper hQ hh hM hMN
    hQ2M h4N hcut
  have hl2 : 0 ≤ lambdaTwo := by norm_num [lambdaTwo]
  have hl3 : 0 ≤ lambdaThree := by norm_num [lambdaThree]
  have hb2w := mul_le_mul_of_nonneg_left hb2 hl2
  have hb3w := mul_le_mul_of_nonneg_left hb3 hl3
  have hsplit :
      ∑ m ∈ Finset.Ico (M + 1) (N + 1),
          (scheduleDilationEnergy h m + scheduleControlError m) / (m : ℝ) =
        (∑ m ∈ Finset.Ico (M + 1) (N + 1),
          scheduleEndpointEnergy h m / (m : ℝ)) +
        lambdaTwo *
          (∑ m ∈ Finset.Ico (M + 1) (N + 1),
            dilationBlockH h (2 * m) (3 * m) / (m : ℝ)) +
        lambdaThree *
          (∑ m ∈ Finset.Ico (M + 1) (N + 1),
            dilationBlockH h (3 * m) (4 * m) / (m : ℝ)) +
        controlAveragingError M N := by
    unfold scheduleDilationEnergy weightedScheduleEnergy scheduleEndpointEnergy
      controlAveragingError lambdaTwo lambdaThree
    norm_num [centralLambda2Q, centralLambda3Q]
    rw [Finset.mul_sum, Finset.mul_sum]
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
      ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro m _
    ring
  rw [hsplit]
  unfold scheduleAveragingFiniteError blockSamplingFiniteError
    averagedEnergyBudget logarithmicBlockCoefficient
  norm_num [squareWeightSum, defectWeightSum, blockWeightSum, lambdaTwo,
    lambdaThree] at hend hb2w hb3w ⊢
  linarith

end

end GDLowerBound.FourBlock
