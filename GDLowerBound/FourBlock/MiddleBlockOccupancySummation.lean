import GDLowerBound.FourBlock.GlobalAveragingErrors

/-!
# Common-range summation of the two middle-block occupancies

Both Fubini sums are extended by zero to the common rank interval
`(2*M,4*N]`.  On that interval each summand uses the sharp interior estimate
when available and the boundary-safe estimate otherwise.
-/

namespace GDLowerBound.FourBlock

open scoped BigOperators
open GDLowerBound.Schedule GDLowerBound.RankAnalysis

noncomputable section

/-- Exact Fubini identity for `(2m,3m]`, extended by zero to `(2M,4N]`. -/
theorem sum_middleBlocks_two_eq_common_occupancy
    (f : ℕ → ℝ) {M N : ℕ} (hMN : M ≤ N) :
    ∑ m ∈ Finset.Ico (M + 1) (N + 1),
        (1 / (m : ℝ)) *
          ∑ n ∈ Finset.Ico (2 * m + 1) (3 * m + 1), f n =
      ∑ n ∈ Finset.Ico (2 * M + 1) (4 * N + 1),
        middleBlockOccupancy 2 M N n * f n := by
  rw [sum_middleBlocks_eq_occupancy]
  let g : ℕ → ℝ := fun n ↦ middleBlockOccupancy 2 M N n * f n
  have h34 : Finset.range (3 * N + 1) ⊆ Finset.range (4 * N + 1) :=
    Finset.range_mono (by omega)
  have hextend :
      ∑ n ∈ Finset.range (3 * N + 1), g n =
        ∑ n ∈ Finset.range (4 * N + 1), g n := by
    apply Finset.sum_subset h34
    intro n hn4 hn3
    have hn4r := Finset.mem_range.mp hn4
    have hn3r : 3 * N < n := by
      exact Nat.le_of_not_gt (fun h ↦ hn3 (Finset.mem_range.mpr (by omega)))
    unfold g
    rw [middleBlockOccupancy_eq_zero_of_lt hn3r]
    simp
  have hcommon :
      Finset.Ico (2 * M + 1) (4 * N + 1) ⊆
        Finset.range (4 * N + 1) := by
    intro n hn
    exact Finset.mem_range.mpr (Finset.mem_Ico.mp hn).2
  have htrim :
      ∑ n ∈ Finset.Ico (2 * M + 1) (4 * N + 1), g n =
        ∑ n ∈ Finset.range (4 * N + 1), g n := by
    apply Finset.sum_subset hcommon
    intro n hnRange hnCommon
    have hnR := Finset.mem_range.mp hnRange
    have hnLow : n ≤ 2 * M := by
      by_contra hnot
      apply hnCommon
      exact Finset.mem_Ico.mpr ⟨by omega, hnR⟩
    unfold g
    rw [middleBlockOccupancy_eq_zero_of_le (by omega : n ≤ 2 * (M + 1))]
    simp
  change (∑ n ∈ Finset.range (3 * N + 1), g n) = _
  rw [hextend, ← htrim]

/-- Exact Fubini identity for `(3m,4m]`, on the same common interval. -/
theorem sum_middleBlocks_three_eq_common_occupancy
    (f : ℕ → ℝ) {M N : ℕ} (hMN : M ≤ N) :
    ∑ m ∈ Finset.Ico (M + 1) (N + 1),
        (1 / (m : ℝ)) *
          ∑ n ∈ Finset.Ico (3 * m + 1) (4 * m + 1), f n =
      ∑ n ∈ Finset.Ico (2 * M + 1) (4 * N + 1),
        middleBlockOccupancy 3 M N n * f n := by
  rw [sum_middleBlocks_eq_occupancy]
  let g : ℕ → ℝ := fun n ↦ middleBlockOccupancy 3 M N n * f n
  have hcommon :
      Finset.Ico (2 * M + 1) (4 * N + 1) ⊆
        Finset.range (4 * N + 1) := by
    intro n hn
    exact Finset.mem_range.mpr (Finset.mem_Ico.mp hn).2
  have htrim :
      ∑ n ∈ Finset.Ico (2 * M + 1) (4 * N + 1), g n =
        ∑ n ∈ Finset.range (4 * N + 1), g n := by
    apply Finset.sum_subset hcommon
    intro n hnRange hnCommon
    have hnR := Finset.mem_range.mp hnRange
    have hnLow : n ≤ 2 * M := by
      by_contra hnot
      apply hnCommon
      exact Finset.mem_Ico.mpr ⟨by omega, hnR⟩
    unfold g
    rw [middleBlockOccupancy_eq_zero_of_le (by omega : n ≤ 3 * (M + 1))]
    simp
  change (∑ n ∈ Finset.range (4 * N + 1), g n) = _
  rw [← htrim]

def twoOccupancyFiniteError (M N n : ℕ) : ℝ :=
  if 3 * (M + 1) ≤ n ∧ n ≤ 2 * N then
    18 / (n : ℝ) ^ 2
  else
    3 * (Real.log (3 / 2 : ℝ) + 6 / (n : ℝ)) / (n : ℝ)

def threeOccupancyFiniteError (M N n : ℕ) : ℝ :=
  if 4 * (M + 1) ≤ n ∧ n ≤ 3 * N then
    24 / (n : ℝ) ^ 2
  else
    3 * (Real.log (4 / 3 : ℝ) + 8 / (n : ℝ)) / (n : ℝ)

theorem twoOccupancyFiniteError_nonneg (M N n : ℕ) :
    0 ≤ twoOccupancyFiniteError M N n := by
  unfold twoOccupancyFiniteError
  split_ifs <;> positivity

theorem threeOccupancyFiniteError_nonneg (M N n : ℕ) :
    0 ≤ threeOccupancyFiniteError M N n := by
  unfold threeOccupancyFiniteError
  split_ifs <;> positivity

/-- Summed signed-deficit comparison for the `(2m,3m]` occupancy. -/
theorem sum_two_occupancy_weighted_deficit_le
    {T : ℕ} {h : StepSchedule T} {M N : ℕ}
    (hM : 6 ≤ M) (hMN : M ≤ N)
    (hcut : CutoffConditions criticalP h (2 * M) (4 * N)) :
    ∑ n ∈ Finset.Ico (2 * M + 1) (4 * N + 1),
        middleBlockOccupancy 2 M N n *
          (betaLower - relativeMassIncrement h n) / (n : ℝ) ≤
      Real.log (3 / 2 : ℝ) *
        ∑ n ∈ Finset.Ico (2 * M + 1) (4 * N + 1),
          (betaLower - relativeMassIncrement h n) / (n : ℝ) +
        ∑ n ∈ Finset.Ico (2 * M + 1) (4 * N + 1),
          twoOccupancyFiniteError M N n := by
  have hterm : ∀ n ∈ Finset.Ico (2 * M + 1) (4 * N + 1),
      middleBlockOccupancy 2 M N n *
          (betaLower - relativeMassIncrement h n) / (n : ℝ) ≤
        Real.log (3 / 2 : ℝ) *
          (betaLower - relativeMassIncrement h n) / (n : ℝ) +
          twoOccupancyFiniteError M N n := by
    intro n hn
    have hnIco := Finset.mem_Ico.mp hn
    have hn12 : 12 ≤ n := by omega
    have hnRange : n ∈ Finset.Icc (2 * M) (4 * N) :=
      Finset.mem_Icc.mpr ⟨by omega, by omega⟩
    by_cases hinterior : 3 * (M + 1) ≤ n ∧ n ≤ 2 * N
    · simpa [twoOccupancyFiniteError, hinterior] using
        middleBlockOccupancy_two_weighted_deficit_le
          hn12 hnRange hinterior.1 hinterior.2 hcut
    · simpa [twoOccupancyFiniteError, hinterior] using
        middleBlockOccupancy_two_weighted_deficit_boundary_le
          hn12 hnRange hcut
  calc
    ∑ n ∈ Finset.Ico (2 * M + 1) (4 * N + 1),
        middleBlockOccupancy 2 M N n *
          (betaLower - relativeMassIncrement h n) / (n : ℝ) ≤
      ∑ n ∈ Finset.Ico (2 * M + 1) (4 * N + 1),
        (Real.log (3 / 2 : ℝ) *
          (betaLower - relativeMassIncrement h n) / (n : ℝ) +
          twoOccupancyFiniteError M N n) := Finset.sum_le_sum hterm
    _ = Real.log (3 / 2 : ℝ) *
        ∑ n ∈ Finset.Ico (2 * M + 1) (4 * N + 1),
          (betaLower - relativeMassIncrement h n) / (n : ℝ) +
        ∑ n ∈ Finset.Ico (2 * M + 1) (4 * N + 1),
          twoOccupancyFiniteError M N n := by
      rw [Finset.sum_add_distrib, Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro n _
      ring

/-- Summed signed-deficit comparison for the `(3m,4m]` occupancy. -/
theorem sum_three_occupancy_weighted_deficit_le
    {T : ℕ} {h : StepSchedule T} {M N : ℕ}
    (hM : 8 ≤ M) (hMN : M ≤ N)
    (hcut : CutoffConditions criticalP h (2 * M) (4 * N)) :
    ∑ n ∈ Finset.Ico (2 * M + 1) (4 * N + 1),
        middleBlockOccupancy 3 M N n *
          (betaLower - relativeMassIncrement h n) / (n : ℝ) ≤
      Real.log (4 / 3 : ℝ) *
        ∑ n ∈ Finset.Ico (2 * M + 1) (4 * N + 1),
          (betaLower - relativeMassIncrement h n) / (n : ℝ) +
        ∑ n ∈ Finset.Ico (2 * M + 1) (4 * N + 1),
          threeOccupancyFiniteError M N n := by
  have hterm : ∀ n ∈ Finset.Ico (2 * M + 1) (4 * N + 1),
      middleBlockOccupancy 3 M N n *
          (betaLower - relativeMassIncrement h n) / (n : ℝ) ≤
        Real.log (4 / 3 : ℝ) *
          (betaLower - relativeMassIncrement h n) / (n : ℝ) +
          threeOccupancyFiniteError M N n := by
    intro n hn
    have hnIco := Finset.mem_Ico.mp hn
    have hn16 : 16 ≤ n := by omega
    have hnRange : n ∈ Finset.Icc (2 * M) (4 * N) :=
      Finset.mem_Icc.mpr ⟨by omega, by omega⟩
    by_cases hinterior : 4 * (M + 1) ≤ n ∧ n ≤ 3 * N
    · simpa [threeOccupancyFiniteError, hinterior] using
        middleBlockOccupancy_three_weighted_deficit_le
          hn16 hnRange hinterior.1 hinterior.2 hcut
    · simpa [threeOccupancyFiniteError, hinterior] using
        middleBlockOccupancy_three_weighted_deficit_boundary_le
          hn16 hnRange hcut
  calc
    ∑ n ∈ Finset.Ico (2 * M + 1) (4 * N + 1),
        middleBlockOccupancy 3 M N n *
          (betaLower - relativeMassIncrement h n) / (n : ℝ) ≤
      ∑ n ∈ Finset.Ico (2 * M + 1) (4 * N + 1),
        (Real.log (4 / 3 : ℝ) *
          (betaLower - relativeMassIncrement h n) / (n : ℝ) +
          threeOccupancyFiniteError M N n) := Finset.sum_le_sum hterm
    _ = Real.log (4 / 3 : ℝ) *
        ∑ n ∈ Finset.Ico (2 * M + 1) (4 * N + 1),
          (betaLower - relativeMassIncrement h n) / (n : ℝ) +
        ∑ n ∈ Finset.Ico (2 * M + 1) (4 * N + 1),
          threeOccupancyFiniteError M N n := by
      rw [Finset.sum_add_distrib, Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro n _
      ring

end

end GDLowerBound.FourBlock
