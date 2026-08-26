import GDLowerBound.FourBlock.MiddleBlockOccupancy

/-!
# Arithmetic form of the two middle-block occupancies

On the interior of the averaging range, the truncated occupancy weights are
ordinary harmonic sums with explicit floor/ceiling endpoints.  These formulas
are the input for the final `O(1/n)` comparison with `log (3/2)` and
`log (4/3)`.
-/

namespace GDLowerBound.FourBlock

open scoped BigOperators

noncomputable section

def twoBlockOccupancyLo (n : ℕ) : ℕ := (n + 2) / 3
def twoBlockOccupancyHi (n : ℕ) : ℕ := (n - 1) / 2

def threeBlockOccupancyLo (n : ℕ) : ℕ := (n + 3) / 4
def threeBlockOccupancyHi (n : ℕ) : ℕ := (n - 1) / 3

/-- Interior occupancy for blocks `(2m,3m]` is an explicit harmonic sum. -/
theorem middleBlockOccupancy_two_eq_harmonic
    {M N n : ℕ} (hM : 3 * (M + 1) ≤ n) (hN : n ≤ 2 * N) :
    middleBlockOccupancy 2 M N n =
      ∑ m ∈ Finset.Ico (twoBlockOccupancyLo n)
          (twoBlockOccupancyHi n + 1), 1 / (m : ℝ) := by
  let candidate := Finset.Ico (twoBlockOccupancyLo n)
    (twoBlockOccupancyHi n + 1)
  have hsub : candidate ⊆ Finset.Ico (M + 1) (N + 1) := by
    intro m hm
    have hmIco := Finset.mem_Ico.mp hm
    unfold twoBlockOccupancyLo twoBlockOccupancyHi at hmIco
    exact Finset.mem_Ico.mpr ⟨by omega, by omega⟩
  unfold middleBlockOccupancy
  calc
    ∑ m ∈ Finset.Ico (M + 1) (N + 1),
        (if n ∈ Finset.Ico (2 * m + 1) ((2 + 1) * m + 1)
          then 1 / (m : ℝ) else 0) =
      ∑ m ∈ candidate,
        (if n ∈ Finset.Ico (2 * m + 1) ((2 + 1) * m + 1)
          then 1 / (m : ℝ) else 0) := by
        symm
        apply Finset.sum_subset hsub
        intro m hmOuter hmNot
        have hmOuterIco := Finset.mem_Ico.mp hmOuter
        simp only [ite_eq_right_iff]
        intro hnBlock
        have hnBlockIco := Finset.mem_Ico.mp hnBlock
        have hmCandidate : m ∈ candidate := by
          apply Finset.mem_Ico.mpr
          unfold twoBlockOccupancyLo twoBlockOccupancyHi
          omega
        exact (hmNot hmCandidate).elim
    _ = ∑ m ∈ candidate, 1 / (m : ℝ) := by
      apply Finset.sum_congr rfl
      intro m hm
      have hmIco := Finset.mem_Ico.mp hm
      have hnBlock : n ∈ Finset.Ico (2 * m + 1) ((2 + 1) * m + 1) := by
        apply Finset.mem_Ico.mpr
        unfold twoBlockOccupancyLo twoBlockOccupancyHi at hmIco
        omega
      simp [hnBlock]
    _ = ∑ m ∈ Finset.Ico (twoBlockOccupancyLo n)
          (twoBlockOccupancyHi n + 1), 1 / (m : ℝ) := by rfl

/-- Interior occupancy for blocks `(3m,4m]` is an explicit harmonic sum. -/
theorem middleBlockOccupancy_three_eq_harmonic
    {M N n : ℕ} (hM : 4 * (M + 1) ≤ n) (hN : n ≤ 3 * N) :
    middleBlockOccupancy 3 M N n =
      ∑ m ∈ Finset.Ico (threeBlockOccupancyLo n)
          (threeBlockOccupancyHi n + 1), 1 / (m : ℝ) := by
  let candidate := Finset.Ico (threeBlockOccupancyLo n)
    (threeBlockOccupancyHi n + 1)
  have hsub : candidate ⊆ Finset.Ico (M + 1) (N + 1) := by
    intro m hm
    have hmIco := Finset.mem_Ico.mp hm
    unfold threeBlockOccupancyLo threeBlockOccupancyHi at hmIco
    exact Finset.mem_Ico.mpr ⟨by omega, by omega⟩
  unfold middleBlockOccupancy
  calc
    ∑ m ∈ Finset.Ico (M + 1) (N + 1),
        (if n ∈ Finset.Ico (3 * m + 1) ((3 + 1) * m + 1)
          then 1 / (m : ℝ) else 0) =
      ∑ m ∈ candidate,
        (if n ∈ Finset.Ico (3 * m + 1) ((3 + 1) * m + 1)
          then 1 / (m : ℝ) else 0) := by
        symm
        apply Finset.sum_subset hsub
        intro m hmOuter hmNot
        have hmOuterIco := Finset.mem_Ico.mp hmOuter
        simp only [ite_eq_right_iff]
        intro hnBlock
        have hnBlockIco := Finset.mem_Ico.mp hnBlock
        have hmCandidate : m ∈ candidate := by
          apply Finset.mem_Ico.mpr
          unfold threeBlockOccupancyLo threeBlockOccupancyHi
          omega
        exact (hmNot hmCandidate).elim
    _ = ∑ m ∈ candidate, 1 / (m : ℝ) := by
      apply Finset.sum_congr rfl
      intro m hm
      have hmIco := Finset.mem_Ico.mp hm
      have hnBlock : n ∈ Finset.Ico (3 * m + 1) ((3 + 1) * m + 1) := by
        apply Finset.mem_Ico.mpr
        unfold threeBlockOccupancyLo threeBlockOccupancyHi at hmIco
        omega
      simp [hnBlock]
    _ = ∑ m ∈ Finset.Ico (threeBlockOccupancyLo n)
          (threeBlockOccupancyHi n + 1), 1 / (m : ℝ) := by rfl

private theorem adjacent_log_le_inv
    {m : ℕ} (hm : 1 ≤ m) :
    Real.log (((m + 1 : ℕ) : ℝ) / (m : ℝ)) ≤ 1 / (m : ℝ) := by
  have hm0 : 0 < (m : ℝ) := by exact_mod_cast (show 0 < m by omega)
  have hm10 : 0 < ((m + 1 : ℕ) : ℝ) := by positivity
  have hlog := Real.log_le_sub_one_of_pos (div_pos hm10 hm0)
  have hid : ((m + 1 : ℕ) : ℝ) / (m : ℝ) - 1 =
      1 / (m : ℝ) := by
    field_simp [ne_of_gt hm0]
    norm_num
  rwa [hid] at hlog

private theorem sum_adjacent_log_eq
    {lo hi : ℕ} (hlo : 1 ≤ lo) (hlohi : lo ≤ hi) :
    ∑ m ∈ Finset.Ico lo (hi + 1),
        Real.log (((m + 1 : ℕ) : ℝ) / (m : ℝ)) =
      Real.log (((hi + 1 : ℕ) : ℝ) / (lo : ℝ)) := by
  have hlo0 : (lo : ℝ) ≠ 0 := by positivity
  calc
    ∑ m ∈ Finset.Ico lo (hi + 1),
        Real.log (((m + 1 : ℕ) : ℝ) / (m : ℝ)) =
      ∑ m ∈ Finset.Ico lo (hi + 1),
        (Real.log ((m + 1 : ℕ) : ℝ) - Real.log (m : ℝ)) := by
        apply Finset.sum_congr rfl
        intro m hm
        have hmIco := Finset.mem_Ico.mp hm
        rw [Real.log_div (by positivity)
          (by exact_mod_cast (show m ≠ 0 by omega))]
    _ = Real.log ((hi + 1 : ℕ) : ℝ) - Real.log (lo : ℝ) := by
      induction hi, hlohi using Nat.le_induction with
      | base => simp
      | succ hi hlohi ih =>
          rw [Finset.sum_Ico_succ_top (by omega), ih]
          ring
    _ = Real.log (((hi + 1 : ℕ) : ℝ) / (lo : ℝ)) := by
      rw [Real.log_div (by positivity) hlo0]

/-- Left-endpoint rectangles dominate the logarithmic integral. -/
theorem log_succ_ratio_le_harmonic_interval
    {lo hi : ℕ} (hlo : 1 ≤ lo) (hlohi : lo ≤ hi) :
    Real.log (((hi + 1 : ℕ) : ℝ) / (lo : ℝ)) ≤
      ∑ m ∈ Finset.Ico lo (hi + 1), 1 / (m : ℝ) := by
  rw [← sum_adjacent_log_eq hlo hlohi]
  exact Finset.sum_le_sum (fun m hm ↦
    adjacent_log_le_inv (by
      have hmIco := Finset.mem_Ico.mp hm
      omega))

end

end GDLowerBound.FourBlock
