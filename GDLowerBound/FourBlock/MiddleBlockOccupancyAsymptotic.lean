import GDLowerBound.FourBlock.MiddleBlockOccupancyLogBounds

/-! # Explicit `O(1/n)` occupancy estimates -/

namespace GDLowerBound.FourBlock

noncomputable section

private theorem two_upper_ratio
    {n : ℕ} (hn : 12 ≤ n) :
    (twoBlockOccupancyHi n : ℝ) /
        ((twoBlockOccupancyLo n - 1 : ℕ) : ℝ) ≤
      (3 / 2 : ℝ) * (1 + 6 / (n : ℝ)) := by
  have hLo : 2 ≤ twoBlockOccupancyLo n := by
    unfold twoBlockOccupancyLo
    omega
  have hU_nat : 2 * twoBlockOccupancyHi n ≤ n - 1 := by
    unfold twoBlockOccupancyHi
    omega
  have hL_nat : n ≤ 3 * twoBlockOccupancyLo n := by
    unfold twoBlockOccupancyLo
    omega
  have hU : 2 * (twoBlockOccupancyHi n : ℝ) ≤ (n : ℝ) - 1 := by
    have hcast : ((2 * twoBlockOccupancyHi n : ℕ) : ℝ) ≤
        ((n - 1 : ℕ) : ℝ) := by exact_mod_cast hU_nat
    norm_num [Nat.cast_mul, Nat.cast_sub (by omega : 1 ≤ n)] at hcast
    exact hcast
  have hL : (n : ℝ) - 3 ≤
      3 * ((twoBlockOccupancyLo n - 1 : ℕ) : ℝ) := by
    have hLcast : (n : ℝ) ≤ 3 * (twoBlockOccupancyLo n : ℝ) := by
      exact_mod_cast hL_nat
    rw [Nat.cast_sub (by omega : 1 ≤ twoBlockOccupancyLo n)]
    push_cast
    linarith
  have hnR : (12 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn0 : 0 < (n : ℝ) := by positivity
  have hleft := mul_le_mul_of_nonneg_left hU hn0.le
  have hright := mul_le_mul_of_nonneg_left hL (by linarith : 0 ≤ (n : ℝ) + 6)
  have hcross :
      2 * (n : ℝ) * (twoBlockOccupancyHi n : ℝ) ≤
        3 * ((n : ℝ) + 6) *
          ((twoBlockOccupancyLo n - 1 : ℕ) : ℝ) := by
    nlinarith
  have hden : 0 < ((twoBlockOccupancyLo n - 1 : ℕ) : ℝ) := by
    exact_mod_cast (show 0 < twoBlockOccupancyLo n - 1 by omega)
  apply (div_le_iff₀ hden).2
  have hfactor :
      (3 / 2 : ℝ) * (1 + 6 / (n : ℝ)) *
          ((twoBlockOccupancyLo n - 1 : ℕ) : ℝ) =
        (3 * ((n : ℝ) + 6) *
          ((twoBlockOccupancyLo n - 1 : ℕ) : ℝ)) /
            (2 * (n : ℝ)) := by
    field_simp [ne_of_gt hn0]
  rw [hfactor]
  exact (le_div_iff₀ (mul_pos (by norm_num) hn0)).2 (by nlinarith)

private theorem two_lower_ratio
    {n : ℕ} (hn : 12 ≤ n) :
    (3 / 2 : ℝ) ≤
      (((twoBlockOccupancyHi n + 1 : ℕ) : ℝ) /
          (twoBlockOccupancyLo n : ℝ)) *
        (1 + 3 / (n : ℝ)) := by
  have hLo : 1 ≤ twoBlockOccupancyLo n := by
    unfold twoBlockOccupancyLo
    omega
  have hU_nat : n ≤ 2 * (twoBlockOccupancyHi n + 1) := by
    unfold twoBlockOccupancyHi
    omega
  have hL_nat : 3 * twoBlockOccupancyLo n ≤ n + 2 := by
    unfold twoBlockOccupancyLo
    omega
  have hU : (n : ℝ) ≤
      2 * ((twoBlockOccupancyHi n + 1 : ℕ) : ℝ) := by
    exact_mod_cast hU_nat
  have hL : 3 * (twoBlockOccupancyLo n : ℝ) ≤ (n : ℝ) + 2 := by
    exact_mod_cast hL_nat
  have hnR : (12 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn0 : 0 < (n : ℝ) := by positivity
  have hleft := mul_le_mul_of_nonneg_right hL hn0.le
  have hright := mul_le_mul_of_nonneg_right hU (by linarith : 0 ≤ (n : ℝ) + 3)
  have hcross :
      3 * (twoBlockOccupancyLo n : ℝ) * (n : ℝ) ≤
        2 * ((twoBlockOccupancyHi n + 1 : ℕ) : ℝ) *
          ((n : ℝ) + 3) := by
    nlinarith
  have hden : 0 < (twoBlockOccupancyLo n : ℝ) := by positivity
  have hfactor :
      (((twoBlockOccupancyHi n + 1 : ℕ) : ℝ) /
          (twoBlockOccupancyLo n : ℝ)) *
        (1 + 3 / (n : ℝ)) =
      ( ((twoBlockOccupancyHi n + 1 : ℕ) : ℝ) *
          ((n : ℝ) + 3)) /
        ((twoBlockOccupancyLo n : ℝ) * (n : ℝ)) := by
    field_simp [ne_of_gt hn0, ne_of_gt hden]
  rw [hfactor]
  exact (le_div_iff₀ (mul_pos hden hn0)).2 (by nlinarith)

private theorem two_upper_log
    {n : ℕ} (hn : 12 ≤ n) :
    Real.log ((twoBlockOccupancyHi n : ℝ) /
        ((twoBlockOccupancyLo n - 1 : ℕ) : ℝ)) ≤
      Real.log (3 / 2 : ℝ) + 6 / (n : ℝ) := by
  have hratio := two_upper_ratio hn
  have hLo : 2 ≤ twoBlockOccupancyLo n := by
    unfold twoBlockOccupancyLo
    omega
  have hU : 1 ≤ twoBlockOccupancyHi n := by
    unfold twoBlockOccupancyHi
    omega
  have hratio0 : 0 < (twoBlockOccupancyHi n : ℝ) /
      ((twoBlockOccupancyLo n - 1 : ℕ) : ℝ) := by
    have hUnat : 0 < twoBlockOccupancyHi n := by omega
    have hLnat : 0 < twoBlockOccupancyLo n - 1 := by omega
    exact div_pos (by exact_mod_cast hUnat) (by exact_mod_cast hLnat)
  have hn0 : 0 < (n : ℝ) := by positivity
  have hfactor0 : 0 < 1 + 6 / (n : ℝ) := by positivity
  have hmono := Real.log_le_log hratio0 hratio
  rw [Real.log_mul (by norm_num : (3 / 2 : ℝ) ≠ 0) hfactor0.ne'] at hmono
  have hsmall := Real.log_le_sub_one_of_pos hfactor0
  have hid : 1 + 6 / (n : ℝ) - 1 = 6 / (n : ℝ) := by ring
  rw [hid] at hsmall
  linarith

private theorem two_lower_log
    {n : ℕ} (hn : 12 ≤ n) :
    Real.log (3 / 2 : ℝ) - 3 / (n : ℝ) ≤
      Real.log (((twoBlockOccupancyHi n + 1 : ℕ) : ℝ) /
        (twoBlockOccupancyLo n : ℝ)) := by
  have hratio := two_lower_ratio hn
  have hLo : 1 ≤ twoBlockOccupancyLo n := by
    unfold twoBlockOccupancyLo
    omega
  have hU : 1 ≤ twoBlockOccupancyHi n + 1 := by omega
  have hbase0 : 0 < (3 / 2 : ℝ) := by norm_num
  have hratio0 : 0 < ((twoBlockOccupancyHi n + 1 : ℕ) : ℝ) /
      (twoBlockOccupancyLo n : ℝ) := by positivity
  have hn0 : 0 < (n : ℝ) := by positivity
  have hfactor0 : 0 < 1 + 3 / (n : ℝ) := by positivity
  have hmono := Real.log_le_log hbase0 hratio
  rw [Real.log_mul hratio0.ne' hfactor0.ne'] at hmono
  have hsmall := Real.log_le_sub_one_of_pos hfactor0
  have hid : 1 + 3 / (n : ℝ) - 1 = 3 / (n : ℝ) := by ring
  rw [hid] at hsmall
  linarith

/-- On the interior, the `(2m,3m]` occupancy differs from `log (3/2)` by
at most `6/n`. -/
theorem middleBlockOccupancy_two_sub_log_abs_le
    {M N n : ℕ} (hn : 12 ≤ n)
    (hM : 3 * (M + 1) ≤ n) (hN : n ≤ 2 * N) :
    |middleBlockOccupancy 2 M N n - Real.log (3 / 2 : ℝ)| ≤
      6 / (n : ℝ) := by
  obtain ⟨hlower, hupper⟩ := middleBlockOccupancy_two_log_bounds hn hM hN
  have hlo := two_lower_log hn
  have hup := two_upper_log hn
  have hn0 : 0 < (n : ℝ) := by positivity
  have h36 : 3 / (n : ℝ) ≤ 6 / (n : ℝ) :=
    div_le_div_of_nonneg_right (by norm_num) hn0.le
  rw [abs_le]
  constructor <;> linarith

end

end GDLowerBound.FourBlock
