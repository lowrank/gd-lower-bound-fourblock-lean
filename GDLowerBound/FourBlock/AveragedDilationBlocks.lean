import GDLowerBound.FourBlock.MiddleBlockOccupancySummation

/-!
# Averaged upper bounds for the two dilation blocks

This module combines the finite block upper bound, fixed-dilation endpoint
sampling, the exact Fubini identities, and the signed occupancy estimates.
All terms are placed on the common rank interval `(2*M,4*N]`.
-/

namespace GDLowerBound.FourBlock

open scoped BigOperators
open GDLowerBound.Schedule GDLowerBound.RankAnalysis

noncomputable section

def commonDefectSum {T : ℕ} (h : StepSchedule T) (M N : ℕ) : ℝ :=
  ∑ n ∈ Finset.Ico (2 * M + 1) (4 * N + 1),
    endpointDefect h n / (n : ℝ)

def commonSquareDeviationSum {T : ℕ}
    (h : StepSchedule T) (M N : ℕ) : ℝ :=
  ∑ n ∈ Finset.Ico (2 * M + 1) (4 * N + 1),
    (relativeMassIncrement h n - betaLower) ^ 2 / (n : ℝ)

def commonMeanDeficitSum {T : ℕ}
    (h : StepSchedule T) (M N : ℕ) : ℝ :=
  ∑ n ∈ Finset.Ico (2 * M + 1) (4 * N + 1),
    (betaLower - relativeMassIncrement h n) / (n : ℝ)

def endpointDefectSamplingError (j M N : ℕ) : ℝ :=
  j * ((104 * adjacentHarmonicWeight (j * M) (j * N) + 2) /
    ((j * M : ℕ) : ℝ))

def squareDeviationSamplingError (j M N : ℕ) : ℝ :=
  j * ((288 * adjacentHarmonicWeight (j * M) (j * N) + 27) /
    ((j * M : ℕ) : ℝ))

def dilationBlockUpperRemainder (j M N : ℕ) : ℝ :=
  ∑ m ∈ Finset.Ico (M + 1) (N + 1),
    (betaLower / ((j * m : ℕ) : ℝ) +
      (9 / 2 : ℝ) *
        ∑ n ∈ Finset.Ico (j * m + 1) ((j + 1) * m + 1),
          1 / (n : ℝ) ^ 2) / (m : ℝ)

theorem commonDefectSum_nonneg
    {T : ℕ} {h : StepSchedule T} {M N : ℕ}
    (hcut : CutoffConditions criticalP h (2 * M) (4 * N)) :
    0 ≤ commonDefectSum h M N := by
  unfold commonDefectSum
  apply Finset.sum_nonneg
  intro n hn
  have hnIco := Finset.mem_Ico.mp hn
  obtain ⟨he0, _⟩ := endpointDefect_cutoff_bounds (q := n) hcut
    (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
  positivity

theorem commonSquareDeviationSum_nonneg
    {T : ℕ} (h : StepSchedule T) (M N : ℕ) :
    0 ≤ commonSquareDeviationSum h M N := by
  unfold commonSquareDeviationSum
  exact Finset.sum_nonneg (fun n _ ↦ by positivity)

/-- Every fixed-dilation endpoint-defect sample at scales `2`, `3`, or `4`
is bounded by the common defect sum plus its explicit variation error. -/
theorem endpointDefect_fixedDilationSample_le_common
    {T Q : ℕ} (hQ : criticalTheta⁻¹ < (Q : ℝ))
    {h : StepSchedule T} (hh : IsNonnegativeSchedule h)
    {j M N : ℕ} (hjlo : 2 ≤ j) (hjhi : j ≤ 4) (hMN : M ≤ N)
    (hQ2M : Q ≤ 2 * M) (h4N : 4 * N ≤ longCount h)
    (hcut : CutoffConditions criticalP h (2 * M) (longCount h)) :
    ∑ m ∈ Finset.Ico (M + 1) (N + 1),
        endpointDefect h (j * m) / (m : ℝ) ≤
      commonDefectSum h M N + endpointDefectSamplingError j M N := by
  have h2jM : 2 * M ≤ j * M := Nat.mul_le_mul_right M hjlo
  have hj4N : j * N ≤ 4 * N := Nat.mul_le_mul_right N hjhi
  have hcutj : CutoffConditions criticalP h (j * M) (longCount h) := by
    intro q hq
    have hqIcc := Finset.mem_Icc.mp hq
    exact hcut q (Finset.mem_Icc.mpr ⟨h2jM.trans hqIcc.1, hqIcc.2⟩)
  have hsample := endpointDefect_fixedDilationHarmonicSample hQ hh
    (by omega : 1 ≤ j) hMN (hQ2M.trans h2jM) (hj4N.trans h4N) hcutj
  have hsubset :
      Finset.Ico (j * M + 1) (j * N + 1) ⊆
        Finset.Ico (2 * M + 1) (4 * N + 1) := by
    intro n hn
    have hnIco := Finset.mem_Ico.mp hn
    exact Finset.mem_Ico.mpr ⟨by omega, by omega⟩
  have hrank :
      ∑ n ∈ Finset.Ico (j * M + 1) (j * N + 1),
          endpointDefect h n / (n : ℝ) ≤ commonDefectSum h M N := by
    unfold commonDefectSum
    apply Finset.sum_le_sum_of_subset_of_nonneg hsubset
    intro n hn _
    have hnIco := Finset.mem_Ico.mp hn
    obtain ⟨he0, _⟩ := endpointDefect_cutoff_bounds (q := n) hcut
      (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
    positivity
  unfold endpointDefectSamplingError
  exact hsample.trans (add_le_add hrank le_rfl)

/-- The corresponding common-range bound for squared deviations. -/
theorem squareDeviation_fixedDilationSample_le_common
    {T : ℕ} {h : StepSchedule T} (hh : IsNonnegativeSchedule h)
    {j M N : ℕ} (hjlo : 2 ≤ j) (hjhi : j ≤ 4) (hMN : M ≤ N)
    (hlo : 8 ≤ 2 * M) (h4N : 4 * N ≤ longCount h)
    (hcut : CutoffConditions criticalP h (2 * M) (longCount h)) :
    ∑ m ∈ Finset.Ico (M + 1) (N + 1),
        (relativeMassIncrement h (j * m) - betaLower) ^ 2 / (m : ℝ) ≤
      commonSquareDeviationSum h M N + squareDeviationSamplingError j M N := by
  have h2jM : 2 * M ≤ j * M := Nat.mul_le_mul_right M hjlo
  have hj4N : j * N ≤ 4 * N := Nat.mul_le_mul_right N hjhi
  have hcutj : CutoffConditions criticalP h (j * M) (longCount h) := by
    intro q hq
    have hqIcc := Finset.mem_Icc.mp hq
    exact hcut q (Finset.mem_Icc.mpr ⟨h2jM.trans hqIcc.1, hqIcc.2⟩)
  have hsample := squareDeviation_fixedDilationHarmonicSample hh
    (by omega : 1 ≤ j) hMN (hlo.trans h2jM) (hj4N.trans h4N) hcutj
  have hsubset :
      Finset.Ico (j * M + 1) (j * N + 1) ⊆
        Finset.Ico (2 * M + 1) (4 * N + 1) := by
    intro n hn
    have hnIco := Finset.mem_Ico.mp hn
    exact Finset.mem_Ico.mpr ⟨by omega, by omega⟩
  have hrank :
      ∑ n ∈ Finset.Ico (j * M + 1) (j * N + 1),
          (relativeMassIncrement h n - betaLower) ^ 2 / (n : ℝ) ≤
        commonSquareDeviationSum h M N := by
    unfold commonSquareDeviationSum
    apply Finset.sum_le_sum_of_subset_of_nonneg hsubset
    intro n _ _
    positivity
  unfold squareDeviationSamplingError
  exact hsample.trans (add_le_add hrank le_rfl)

private theorem averagedDilationBlock_pointwise
    {T : ℕ} {h : StepSchedule T} (hh : IsNonnegativeSchedule h)
    {j M N m : ℕ} (hj : 1 ≤ j)
    (hm : m ∈ Finset.Ico (M + 1) (N + 1))
    (h4N : (j + 1) * N ≤ longCount h)
    (hcut : CutoffConditions criticalP h (j * M) (longCount h)) :
    dilationBlockH h (j * m) ((j + 1) * m) / (m : ℝ) ≤
      (1 / (m : ℝ)) *
          ∑ n ∈ Finset.Ico (j * m + 1) ((j + 1) * m + 1),
            (betaLower - relativeMassIncrement h n) / (n : ℝ) +
        betaLower * endpointDefect h (j * m) / (m : ℝ) +
        (betaLower / ((j * m : ℕ) : ℝ) +
          (9 / 2 : ℝ) *
            ∑ n ∈ Finset.Ico (j * m + 1) ((j + 1) * m + 1),
              1 / (n : ℝ) ^ 2) / (m : ℝ) := by
  have hmIco := Finset.mem_Ico.mp hm
  have hm0 : 0 < (m : ℝ) := by exact_mod_cast (show 0 < m by omega)
  have hlo : 1 ≤ j * m := by
    calc
      1 = 1 * 1 := by norm_num
      _ ≤ j * m := Nat.mul_le_mul hj (by omega)
  have hhi : (j + 1) * m ≤ longCount h := by
    exact (Nat.mul_le_mul_left (j + 1) (by omega)).trans h4N
  have hcutBlock :
      CutoffConditions criticalP h (j * m) ((j + 1) * m) := by
    intro q hq
    have hqIcc := Finset.mem_Icc.mp hq
    exact hcut q (Finset.mem_Icc.mpr ⟨by
      have hJM : j * M ≤ j * m := Nat.mul_le_mul_left j (by omega)
      exact hJM.trans hqIcc.1, hqIcc.2.trans hhi⟩)
  have hup := dilationBlockH_upper hh hlo
    (Nat.mul_le_mul_right m (by omega : j ≤ j + 1)) hhi hcutBlock
  have hscaled := div_le_div_of_nonneg_right hup hm0.le
  ring_nf at hscaled ⊢
  exact hscaled

/-- Averaged `(2m,3m]` dilation defect on the common rank interval. -/
theorem averagedDilationBlock_two_upper
    {T Q : ℕ} (hQ : criticalTheta⁻¹ < (Q : ℝ))
    {h : StepSchedule T} (hh : IsNonnegativeSchedule h)
    {M N : ℕ} (hM : 8 ≤ M) (hMN : M ≤ N)
    (hQ2M : Q ≤ 2 * M) (h4N : 4 * N ≤ longCount h)
    (hcut : CutoffConditions criticalP h (2 * M) (longCount h)) :
    ∑ m ∈ Finset.Ico (M + 1) (N + 1),
        dilationBlockH h (2 * m) (3 * m) / (m : ℝ) ≤
      Real.log (3 / 2 : ℝ) * commonMeanDeficitSum h M N +
        (∑ n ∈ Finset.Ico (2 * M + 1) (4 * N + 1),
          twoOccupancyFiniteError M N n) +
        betaLower * (commonDefectSum h M N +
          endpointDefectSamplingError 2 M N) +
        dilationBlockUpperRemainder 2 M N := by
  have hcutCommon : CutoffConditions criticalP h (2 * M) (4 * N) := by
    intro q hq
    have hqIcc := Finset.mem_Icc.mp hq
    exact hcut q (Finset.mem_Icc.mpr ⟨hqIcc.1, hqIcc.2.trans h4N⟩)
  have hpoint : ∀ m ∈ Finset.Ico (M + 1) (N + 1),
      dilationBlockH h (2 * m) (3 * m) / (m : ℝ) ≤
        (1 / (m : ℝ)) *
            ∑ n ∈ Finset.Ico (2 * m + 1) (3 * m + 1),
              (betaLower - relativeMassIncrement h n) / (n : ℝ) +
          betaLower * endpointDefect h (2 * m) / (m : ℝ) +
          (betaLower / ((2 * m : ℕ) : ℝ) +
            (9 / 2 : ℝ) *
              ∑ n ∈ Finset.Ico (2 * m + 1) (3 * m + 1),
                1 / (n : ℝ) ^ 2) / (m : ℝ) := by
    intro m hm
    exact averagedDilationBlock_pointwise hh (j := 2) (m := m)
      (by omega) hm (by omega : 3 * N ≤ longCount h) hcut
  have hsum := Finset.sum_le_sum hpoint
  have hdouble :
      ∑ m ∈ Finset.Ico (M + 1) (N + 1),
          (1 / (m : ℝ)) *
            ∑ n ∈ Finset.Ico (2 * m + 1) (3 * m + 1),
              (betaLower - relativeMassIncrement h n) / (n : ℝ) ≤
        Real.log (3 / 2 : ℝ) * commonMeanDeficitSum h M N +
          ∑ n ∈ Finset.Ico (2 * M + 1) (4 * N + 1),
            twoOccupancyFiniteError M N n := by
    rw [sum_middleBlocks_two_eq_common_occupancy
      (fun n ↦ (betaLower - relativeMassIncrement h n) / (n : ℝ)) hMN]
    simpa [commonMeanDeficitSum, mul_div_assoc] using
      sum_two_occupancy_weighted_deficit_le (h := h) (by omega) hMN hcutCommon
  have hsample := endpointDefect_fixedDilationSample_le_common hQ hh
    (j := 2) (by omega) (by omega) hMN hQ2M h4N hcut
  have hsampleBeta := mul_le_mul_of_nonneg_left hsample betaLower_pos.le
  unfold commonMeanDeficitSum at hdouble ⊢
  unfold dilationBlockUpperRemainder at hsum ⊢
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib] at hsum
  have hdecomp :
      ∑ x ∈ Finset.Ico (M + 1) (N + 1),
          betaLower * endpointDefect h (2 * x) / (x : ℝ) =
        betaLower *
          ∑ x ∈ Finset.Ico (M + 1) (N + 1),
            endpointDefect h (2 * x) / (x : ℝ) := by
    simp only [mul_div_assoc]
    rw [Finset.mul_sum]
  rw [hdecomp] at hsum
  linarith

/-- Averaged `(3m,4m]` dilation defect on the common rank interval. -/
theorem averagedDilationBlock_three_upper
    {T Q : ℕ} (hQ : criticalTheta⁻¹ < (Q : ℝ))
    {h : StepSchedule T} (hh : IsNonnegativeSchedule h)
    {M N : ℕ} (hM : 8 ≤ M) (hMN : M ≤ N)
    (hQ2M : Q ≤ 2 * M) (h4N : 4 * N ≤ longCount h)
    (hcut : CutoffConditions criticalP h (2 * M) (longCount h)) :
    ∑ m ∈ Finset.Ico (M + 1) (N + 1),
        dilationBlockH h (3 * m) (4 * m) / (m : ℝ) ≤
      Real.log (4 / 3 : ℝ) * commonMeanDeficitSum h M N +
        (∑ n ∈ Finset.Ico (2 * M + 1) (4 * N + 1),
          threeOccupancyFiniteError M N n) +
        betaLower * (commonDefectSum h M N +
          endpointDefectSamplingError 3 M N) +
        dilationBlockUpperRemainder 3 M N := by
  have hcutCommon : CutoffConditions criticalP h (2 * M) (4 * N) := by
    intro q hq
    have hqIcc := Finset.mem_Icc.mp hq
    exact hcut q (Finset.mem_Icc.mpr ⟨hqIcc.1, hqIcc.2.trans h4N⟩)
  have hcut3 : CutoffConditions criticalP h (3 * M) (longCount h) := by
    intro q hq
    have hqIcc := Finset.mem_Icc.mp hq
    exact hcut q (Finset.mem_Icc.mpr ⟨by omega, hqIcc.2⟩)
  have hpoint : ∀ m ∈ Finset.Ico (M + 1) (N + 1),
      dilationBlockH h (3 * m) (4 * m) / (m : ℝ) ≤
        (1 / (m : ℝ)) *
            ∑ n ∈ Finset.Ico (3 * m + 1) (4 * m + 1),
              (betaLower - relativeMassIncrement h n) / (n : ℝ) +
          betaLower * endpointDefect h (3 * m) / (m : ℝ) +
          (betaLower / ((3 * m : ℕ) : ℝ) +
            (9 / 2 : ℝ) *
              ∑ n ∈ Finset.Ico (3 * m + 1) (4 * m + 1),
                1 / (n : ℝ) ^ 2) / (m : ℝ) := by
    intro m hm
    exact averagedDilationBlock_pointwise hh (j := 3) (m := m)
      (by omega) hm h4N hcut3
  have hsum := Finset.sum_le_sum hpoint
  have hdouble :
      ∑ m ∈ Finset.Ico (M + 1) (N + 1),
          (1 / (m : ℝ)) *
            ∑ n ∈ Finset.Ico (3 * m + 1) (4 * m + 1),
              (betaLower - relativeMassIncrement h n) / (n : ℝ) ≤
        Real.log (4 / 3 : ℝ) * commonMeanDeficitSum h M N +
          ∑ n ∈ Finset.Ico (2 * M + 1) (4 * N + 1),
            threeOccupancyFiniteError M N n := by
    rw [sum_middleBlocks_three_eq_common_occupancy
      (fun n ↦ (betaLower - relativeMassIncrement h n) / (n : ℝ)) hMN]
    simpa [commonMeanDeficitSum, mul_div_assoc] using
      sum_three_occupancy_weighted_deficit_le (h := h) hM hMN hcutCommon
  have hsample := endpointDefect_fixedDilationSample_le_common hQ hh
    (j := 3) (by omega) (by omega) hMN hQ2M h4N hcut
  have hsampleBeta := mul_le_mul_of_nonneg_left hsample betaLower_pos.le
  unfold commonMeanDeficitSum at hdouble ⊢
  unfold dilationBlockUpperRemainder at hsum ⊢
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib] at hsum
  have hdecomp :
      ∑ x ∈ Finset.Ico (M + 1) (N + 1),
          betaLower * endpointDefect h (3 * x) / (x : ℝ) =
        betaLower *
          ∑ x ∈ Finset.Ico (M + 1) (N + 1),
            endpointDefect h (3 * x) / (x : ℝ) := by
    simp only [mul_div_assoc]
    rw [Finset.mul_sum]
  rw [hdecomp] at hsum
  linarith

end

end GDLowerBound.FourBlock
