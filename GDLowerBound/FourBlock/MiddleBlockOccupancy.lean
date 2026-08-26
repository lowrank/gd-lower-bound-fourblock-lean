import GDLowerBound.FourBlock.BlockDefectUpper

/-!
# Exact occupancy weights for averaged middle blocks

After averaging a block defect over `m`, the middle-block deficit is a
double finite sum.  This file performs the exact Fubini rearrangement and
isolates the only remaining arithmetic object: a truncated harmonic
occupancy weight.
-/

namespace GDLowerBound.FourBlock

open scoped BigOperators

noncomputable section

/-- Harmonic weight with which rank `n` occurs in the averaged blocks
`(j*m, (j+1)*m]`, for `M < m ≤ N`. -/
def middleBlockOccupancy (j M N n : ℕ) : ℝ :=
  ∑ m ∈ Finset.Ico (M + 1) (N + 1),
    if n ∈ Finset.Ico (j * m + 1) ((j + 1) * m + 1)
      then 1 / (m : ℝ) else 0

theorem middleBlockOccupancy_nonneg (j M N n : ℕ) :
    0 ≤ middleBlockOccupancy j M N n := by
  unfold middleBlockOccupancy
  exact Finset.sum_nonneg (fun m _ ↦ by
    split_ifs <;> positivity)

private theorem middleBlock_subset_range
    {j M N m : ℕ} (hm : m ∈ Finset.Ico (M + 1) (N + 1)) :
    Finset.Ico (j * m + 1) ((j + 1) * m + 1) ⊆
      Finset.range ((j + 1) * N + 1) := by
  intro n hn
  have hmIco := Finset.mem_Ico.mp hm
  have hmul : (j + 1) * m ≤ (j + 1) * N :=
    Nat.mul_le_mul_left (j + 1) (by omega)
  exact Finset.mem_range.mpr (by
    have hnIco := Finset.mem_Ico.mp hn
    omega)

private theorem sum_range_indicator_middleBlock
    (f : ℕ → ℝ) {j M N m : ℕ}
    (hm : m ∈ Finset.Ico (M + 1) (N + 1)) :
    ∑ n ∈ Finset.range ((j + 1) * N + 1),
        (if n ∈ Finset.Ico (j * m + 1) ((j + 1) * m + 1)
          then 1 / (m : ℝ) else 0) * f n =
      1 / (m : ℝ) *
        ∑ n ∈ Finset.Ico (j * m + 1) ((j + 1) * m + 1), f n := by
  let block := Finset.Ico (j * m + 1) ((j + 1) * m + 1)
  have hsub : block ⊆ Finset.range ((j + 1) * N + 1) :=
    middleBlock_subset_range hm
  calc
    ∑ n ∈ Finset.range ((j + 1) * N + 1),
        (if n ∈ Finset.Ico (j * m + 1) ((j + 1) * m + 1)
          then 1 / (m : ℝ) else 0) * f n =
      ∑ n ∈ block,
        (if n ∈ Finset.Ico (j * m + 1) ((j + 1) * m + 1)
          then 1 / (m : ℝ) else 0) * f n := by
        symm
        apply Finset.sum_subset hsub
        intro n _ hnBlock
        simp only [block] at hnBlock
        simp [hnBlock]
    _ = ∑ n ∈ block, (1 / (m : ℝ)) * f n := by
      apply Finset.sum_congr rfl
      intro n hn
      simp only [block] at hn
      simp [hn]
    _ = 1 / (m : ℝ) *
        ∑ n ∈ Finset.Ico (j * m + 1) ((j + 1) * m + 1), f n := by
      dsimp only [block]
      rw [Finset.mul_sum]

/-- Exact finite Fubini identity for averaged middle blocks. -/
theorem sum_middleBlocks_eq_occupancy
    (f : ℕ → ℝ) (j M N : ℕ) :
    ∑ m ∈ Finset.Ico (M + 1) (N + 1),
        (1 / (m : ℝ)) *
          ∑ n ∈ Finset.Ico (j * m + 1) ((j + 1) * m + 1), f n =
      ∑ n ∈ Finset.range ((j + 1) * N + 1),
        middleBlockOccupancy j M N n * f n := by
  calc
    ∑ m ∈ Finset.Ico (M + 1) (N + 1),
        (1 / (m : ℝ)) *
          ∑ n ∈ Finset.Ico (j * m + 1) ((j + 1) * m + 1), f n =
      ∑ m ∈ Finset.Ico (M + 1) (N + 1),
        ∑ n ∈ Finset.range ((j + 1) * N + 1),
          (if n ∈ Finset.Ico (j * m + 1) ((j + 1) * m + 1)
            then 1 / (m : ℝ) else 0) * f n := by
        apply Finset.sum_congr rfl
        intro m hm
        exact (sum_range_indicator_middleBlock f hm).symm
    _ = ∑ n ∈ Finset.range ((j + 1) * N + 1),
        ∑ m ∈ Finset.Ico (M + 1) (N + 1),
          (if n ∈ Finset.Ico (j * m + 1) ((j + 1) * m + 1)
            then 1 / (m : ℝ) else 0) * f n := by
      rw [Finset.sum_comm]
    _ = ∑ n ∈ Finset.range ((j + 1) * N + 1),
        middleBlockOccupancy j M N n * f n := by
      apply Finset.sum_congr rfl
      intro n _
      unfold middleBlockOccupancy
      rw [Finset.sum_mul]

/-- No rank below the first possible block can carry occupancy. -/
theorem middleBlockOccupancy_eq_zero_of_le
    {j M N n : ℕ} (hn : n ≤ j * (M + 1)) :
    middleBlockOccupancy j M N n = 0 := by
  unfold middleBlockOccupancy
  apply Finset.sum_eq_zero
  intro m hm
  have hmIco := Finset.mem_Ico.mp hm
  have hmul : j * (M + 1) ≤ j * m :=
    Nat.mul_le_mul_left j hmIco.1
  simp only [ite_eq_right_iff]
  intro hnMem
  have hnIco := Finset.mem_Ico.mp hnMem
  omega

/-- No rank above the last possible block can carry occupancy. -/
theorem middleBlockOccupancy_eq_zero_of_lt
    {j M N n : ℕ} (hn : (j + 1) * N < n) :
    middleBlockOccupancy j M N n = 0 := by
  unfold middleBlockOccupancy
  apply Finset.sum_eq_zero
  intro m hm
  have hmIco := Finset.mem_Ico.mp hm
  have hmul : (j + 1) * m ≤ (j + 1) * N :=
    Nat.mul_le_mul_left (j + 1) (by omega)
  simp only [ite_eq_right_iff]
  intro hnMem
  have hnIco := Finset.mem_Ico.mp hnMem
  omega

end

end GDLowerBound.FourBlock
