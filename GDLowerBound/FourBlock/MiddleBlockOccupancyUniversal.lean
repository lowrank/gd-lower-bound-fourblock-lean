import GDLowerBound.FourBlock.MiddleBlockOccupancyAsymptoticThree

/-!
# Uniform upper bounds for truncated middle-block occupancies

The interior occupancy estimates extend to one-sided bounds everywhere: a
truncated averaging interval can only remove nonnegative harmonic summands.
This observation avoids a separate analysis of the lower and upper boundary
bands when an upper bound is all that is needed.
-/

namespace GDLowerBound.FourBlock

open scoped BigOperators

noncomputable section

/-- Truncating the averaging interval cannot increase the `(2m,3m]`
occupancy. -/
theorem middleBlockOccupancy_two_le_full
    (M N n : ℕ) :
    middleBlockOccupancy 2 M N n ≤
      middleBlockOccupancy 2 0 n n := by
  unfold middleBlockOccupancy
  rw [← Finset.sum_filter]
  rw [← Finset.sum_filter]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro m hm
    simp only [Finset.mem_filter, Finset.mem_Ico] at hm ⊢
    obtain ⟨⟨hmM, hmN⟩, hnBlock⟩ := hm
    have hnIco := hnBlock
    exact ⟨⟨by omega, by omega⟩, hnBlock⟩
  · intro m _ _
    positivity

/-- Truncating the averaging interval cannot increase the `(3m,4m]`
occupancy. -/
theorem middleBlockOccupancy_three_le_full
    (M N n : ℕ) :
    middleBlockOccupancy 3 M N n ≤
      middleBlockOccupancy 3 0 n n := by
  unfold middleBlockOccupancy
  rw [← Finset.sum_filter]
  rw [← Finset.sum_filter]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro m hm
    simp only [Finset.mem_filter, Finset.mem_Ico] at hm ⊢
    obtain ⟨⟨hmM, hmN⟩, hnBlock⟩ := hm
    have hnIco := hnBlock
    exact ⟨⟨by omega, by omega⟩, hnBlock⟩
  · intro m _ _
    positivity

/-- Uniform, including both truncated boundary bands, upper estimate for the
`(2m,3m]` occupancy. -/
theorem middleBlockOccupancy_two_le_log_add
    {M N n : ℕ} (hn : 12 ≤ n) :
    middleBlockOccupancy 2 M N n ≤
      Real.log (3 / 2 : ℝ) + 6 / (n : ℝ) := by
  have hmono := middleBlockOccupancy_two_le_full M N n
  have hfull := middleBlockOccupancy_two_sub_log_abs_le
    (M := 0) (N := n) hn (by omega) (by omega)
  have hupper : middleBlockOccupancy 2 0 n n - Real.log (3 / 2 : ℝ) ≤
      6 / (n : ℝ) := le_trans (le_abs_self _) hfull
  linarith

/-- Uniform, including both truncated boundary bands, upper estimate for the
`(3m,4m]` occupancy. -/
theorem middleBlockOccupancy_three_le_log_add
    {M N n : ℕ} (hn : 16 ≤ n) :
    middleBlockOccupancy 3 M N n ≤
      Real.log (4 / 3 : ℝ) + 8 / (n : ℝ) := by
  have hmono := middleBlockOccupancy_three_le_full M N n
  have hfull := middleBlockOccupancy_three_sub_log_abs_le
    (M := 0) (N := n) hn (by omega) (by omega)
  have hupper : middleBlockOccupancy 3 0 n n - Real.log (4 / 3 : ℝ) ≤
      8 / (n : ℝ) := le_trans (le_abs_self _) hfull
  linarith

end

end GDLowerBound.FourBlock
