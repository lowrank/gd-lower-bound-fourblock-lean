import GDLowerBound.FourBlock.MiddleBlockOccupancyAsymptotic

/-! # Explicit `O(1/n)` estimate for the `(3m,4m]` occupancy -/

namespace GDLowerBound.FourBlock

noncomputable section

private theorem three_upper_ratio
    {n : ℕ} (hn : 16 ≤ n) :
    (threeBlockOccupancyHi n : ℝ) /
        ((threeBlockOccupancyLo n - 1 : ℕ) : ℝ) ≤
      (4 / 3 : ℝ) * (1 + 8 / (n : ℝ)) := by
  have hLo : 2 ≤ threeBlockOccupancyLo n := by
    unfold threeBlockOccupancyLo
    omega
  have hU_nat : 3 * threeBlockOccupancyHi n ≤ n - 1 := by
    unfold threeBlockOccupancyHi
    omega
  have hL_nat : n ≤ 4 * threeBlockOccupancyLo n := by
    unfold threeBlockOccupancyLo
    omega
  have hU : 3 * (threeBlockOccupancyHi n : ℝ) ≤ (n : ℝ) - 1 := by
    have hcast : ((3 * threeBlockOccupancyHi n : ℕ) : ℝ) ≤
        ((n - 1 : ℕ) : ℝ) := by exact_mod_cast hU_nat
    norm_num [Nat.cast_mul, Nat.cast_sub (by omega : 1 ≤ n)] at hcast
    exact hcast
  have hL : (n : ℝ) - 4 ≤
      4 * ((threeBlockOccupancyLo n - 1 : ℕ) : ℝ) := by
    have hLcast : (n : ℝ) ≤ 4 * (threeBlockOccupancyLo n : ℝ) := by
      exact_mod_cast hL_nat
    rw [Nat.cast_sub (by omega : 1 ≤ threeBlockOccupancyLo n)]
    push_cast
    linarith
  have hnR : (16 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn0 : 0 < (n : ℝ) := by positivity
  have hleft := mul_le_mul_of_nonneg_left hU hn0.le
  have hright := mul_le_mul_of_nonneg_left hL (by linarith : 0 ≤ (n : ℝ) + 8)
  have hcross :
      3 * (n : ℝ) * (threeBlockOccupancyHi n : ℝ) ≤
        4 * ((n : ℝ) + 8) *
          ((threeBlockOccupancyLo n - 1 : ℕ) : ℝ) := by
    nlinarith
  have hden : 0 < ((threeBlockOccupancyLo n - 1 : ℕ) : ℝ) := by
    exact_mod_cast (show 0 < threeBlockOccupancyLo n - 1 by omega)
  apply (div_le_iff₀ hden).2
  have hfactor :
      (4 / 3 : ℝ) * (1 + 8 / (n : ℝ)) *
          ((threeBlockOccupancyLo n - 1 : ℕ) : ℝ) =
        (4 * ((n : ℝ) + 8) *
          ((threeBlockOccupancyLo n - 1 : ℕ) : ℝ)) /
            (3 * (n : ℝ)) := by
    field_simp [ne_of_gt hn0]
  rw [hfactor]
  exact (le_div_iff₀ (mul_pos (by norm_num) hn0)).2 (by nlinarith)

private theorem three_lower_ratio
    {n : ℕ} (hn : 16 ≤ n) :
    (4 / 3 : ℝ) ≤
      (((threeBlockOccupancyHi n + 1 : ℕ) : ℝ) /
          (threeBlockOccupancyLo n : ℝ)) *
        (1 + 4 / (n : ℝ)) := by
  have hLo : 1 ≤ threeBlockOccupancyLo n := by
    unfold threeBlockOccupancyLo
    omega
  have hU_nat : n ≤ 3 * (threeBlockOccupancyHi n + 1) := by
    unfold threeBlockOccupancyHi
    omega
  have hL_nat : 4 * threeBlockOccupancyLo n ≤ n + 3 := by
    unfold threeBlockOccupancyLo
    omega
  have hU : (n : ℝ) ≤
      3 * ((threeBlockOccupancyHi n + 1 : ℕ) : ℝ) := by
    exact_mod_cast hU_nat
  have hL : 4 * (threeBlockOccupancyLo n : ℝ) ≤ (n : ℝ) + 3 := by
    exact_mod_cast hL_nat
  have hnR : (16 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn0 : 0 < (n : ℝ) := by positivity
  have hleft := mul_le_mul_of_nonneg_right hL hn0.le
  have hright := mul_le_mul_of_nonneg_right hU (by linarith : 0 ≤ (n : ℝ) + 4)
  have hcross :
      4 * (threeBlockOccupancyLo n : ℝ) * (n : ℝ) ≤
        3 * ((threeBlockOccupancyHi n + 1 : ℕ) : ℝ) *
          ((n : ℝ) + 4) := by
    nlinarith
  have hden : 0 < (threeBlockOccupancyLo n : ℝ) := by positivity
  have hfactor :
      (((threeBlockOccupancyHi n + 1 : ℕ) : ℝ) /
          (threeBlockOccupancyLo n : ℝ)) *
        (1 + 4 / (n : ℝ)) =
      (((threeBlockOccupancyHi n + 1 : ℕ) : ℝ) *
          ((n : ℝ) + 4)) /
        ((threeBlockOccupancyLo n : ℝ) * (n : ℝ)) := by
    field_simp [ne_of_gt hn0, ne_of_gt hden]
  rw [hfactor]
  exact (le_div_iff₀ (mul_pos hden hn0)).2 (by nlinarith)

private theorem three_upper_log
    {n : ℕ} (hn : 16 ≤ n) :
    Real.log ((threeBlockOccupancyHi n : ℝ) /
        ((threeBlockOccupancyLo n - 1 : ℕ) : ℝ)) ≤
      Real.log (4 / 3 : ℝ) + 8 / (n : ℝ) := by
  have hratio := three_upper_ratio hn
  have hLo : 2 ≤ threeBlockOccupancyLo n := by
    unfold threeBlockOccupancyLo
    omega
  have hU : 1 ≤ threeBlockOccupancyHi n := by
    unfold threeBlockOccupancyHi
    omega
  have hratio0 : 0 < (threeBlockOccupancyHi n : ℝ) /
      ((threeBlockOccupancyLo n - 1 : ℕ) : ℝ) := by
    have hUnat : 0 < threeBlockOccupancyHi n := by omega
    have hLnat : 0 < threeBlockOccupancyLo n - 1 := by omega
    exact div_pos (by exact_mod_cast hUnat) (by exact_mod_cast hLnat)
  have hn0 : 0 < (n : ℝ) := by positivity
  have hfactor0 : 0 < 1 + 8 / (n : ℝ) := by positivity
  have hmono := Real.log_le_log hratio0 hratio
  rw [Real.log_mul (by norm_num : (4 / 3 : ℝ) ≠ 0) hfactor0.ne'] at hmono
  have hsmall := Real.log_le_sub_one_of_pos hfactor0
  have hid : 1 + 8 / (n : ℝ) - 1 = 8 / (n : ℝ) := by ring
  rw [hid] at hsmall
  linarith

private theorem three_lower_log
    {n : ℕ} (hn : 16 ≤ n) :
    Real.log (4 / 3 : ℝ) - 4 / (n : ℝ) ≤
      Real.log (((threeBlockOccupancyHi n + 1 : ℕ) : ℝ) /
        (threeBlockOccupancyLo n : ℝ)) := by
  have hratio := three_lower_ratio hn
  have hLo : 1 ≤ threeBlockOccupancyLo n := by
    unfold threeBlockOccupancyLo
    omega
  have hU : 1 ≤ threeBlockOccupancyHi n + 1 := by omega
  have hbase0 : 0 < (4 / 3 : ℝ) := by norm_num
  have hratio0 : 0 < ((threeBlockOccupancyHi n + 1 : ℕ) : ℝ) /
      (threeBlockOccupancyLo n : ℝ) := by positivity
  have hn0 : 0 < (n : ℝ) := by positivity
  have hfactor0 : 0 < 1 + 4 / (n : ℝ) := by positivity
  have hmono := Real.log_le_log hbase0 hratio
  rw [Real.log_mul hratio0.ne' hfactor0.ne'] at hmono
  have hsmall := Real.log_le_sub_one_of_pos hfactor0
  have hid : 1 + 4 / (n : ℝ) - 1 = 4 / (n : ℝ) := by ring
  rw [hid] at hsmall
  linarith

/-- On the interior, the `(3m,4m]` occupancy differs from `log (4/3)` by
at most `8/n`. -/
theorem middleBlockOccupancy_three_sub_log_abs_le
    {M N n : ℕ} (hn : 16 ≤ n)
    (hM : 4 * (M + 1) ≤ n) (hN : n ≤ 3 * N) :
    |middleBlockOccupancy 3 M N n - Real.log (4 / 3 : ℝ)| ≤
      8 / (n : ℝ) := by
  obtain ⟨hlower, hupper⟩ := middleBlockOccupancy_three_log_bounds hn hM hN
  have hlo := three_lower_log hn
  have hup := three_upper_log hn
  have hn0 : 0 < (n : ℝ) := by positivity
  have h48 : 4 / (n : ℝ) ≤ 8 / (n : ℝ) :=
    div_le_div_of_nonneg_right (by norm_num) hn0.le
  rw [abs_le]
  constructor <;> linarith

end

end GDLowerBound.FourBlock
