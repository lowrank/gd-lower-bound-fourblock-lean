import GDLowerBound.FourBlock.MiddleBlockOccupancyUniversal

/-!
# Occupancy bounds multiplied by a signed deficit

The mean deficit `betaLower - relativeMassIncrement h n` has no fixed sign.
Consequently an upper bound for the occupancy cannot simply be multiplied by
it.  This file records the absolute-error argument needed by the averaged
block proof, both on the interior and on the truncated boundary bands.
-/

namespace GDLowerBound.FourBlock

open GDLowerBound.Schedule GDLowerBound.RankAnalysis

noncomputable section

private theorem weighted_mul_div_compare
    {w L a E B n : ℝ} (hn : 0 < n) (hE : 0 ≤ E) (hB : 0 ≤ B)
    (hw : |w - L| ≤ E) (ha : |a| ≤ B) :
    w * a / n ≤ L * a / n + E * B / n := by
  have hprodabs : |(w - L) * a| ≤ E * B := by
    rw [abs_mul]
    exact mul_le_mul hw ha (abs_nonneg _) hE
  have hprod : (w - L) * a ≤ E * B :=
    (le_abs_self _).trans hprodabs
  have hdiv := div_le_div_of_nonneg_right hprod hn.le
  calc
    w * a / n = L * a / n + (w - L) * a / n := by ring
    _ ≤ L * a / n + E * B / n := by linarith

/-- On the cutoff range, the signed mean deficit has absolute value at most
three. -/
theorem betaLower_sub_relativeMassIncrement_abs_le_three
    {T : ℕ} {h : StepSchedule T} {lo hi n : ℕ}
    (hcut : CutoffConditions criticalP h lo hi)
    (hn : n ∈ Finset.Icc lo hi) :
    |betaLower - relativeMassIncrement h n| ≤ 3 := by
  obtain ⟨hv0, hv3⟩ := relativeMassIncrement_cutoff_bounds hcut hn
  have hb0 := betaLower_pos
  have hb1 : betaLower < 1 := by norm_num [betaLower]
  rw [abs_le]
  constructor <;> linarith

/-- Interior `(2m,3m]` occupancy times the signed deficit, with a summable
`18/n^2` error. -/
theorem middleBlockOccupancy_two_weighted_deficit_le
    {T : ℕ} {h : StepSchedule T} {lo hi M N n : ℕ}
    (hn : 12 ≤ n) (hnRange : n ∈ Finset.Icc lo hi)
    (hM : 3 * (M + 1) ≤ n) (hN : n ≤ 2 * N)
    (hcut : CutoffConditions criticalP h lo hi) :
    middleBlockOccupancy 2 M N n *
          (betaLower - relativeMassIncrement h n) / (n : ℝ) ≤
      Real.log (3 / 2 : ℝ) *
          (betaLower - relativeMassIncrement h n) / (n : ℝ) +
        18 / (n : ℝ) ^ 2 := by
  have hn0 : 0 < (n : ℝ) := by positivity
  have hocc := middleBlockOccupancy_two_sub_log_abs_le hn hM hN
  have hdef := betaLower_sub_relativeMassIncrement_abs_le_three hcut hnRange
  have hraw := weighted_mul_div_compare hn0
    (show 0 ≤ 6 / (n : ℝ) by positivity) (by norm_num : (0 : ℝ) ≤ 3)
    hocc hdef
  convert hraw using 1 <;> field_simp [ne_of_gt hn0] <;> ring

/-- Interior `(3m,4m]` occupancy times the signed deficit, with a summable
`24/n^2` error. -/
theorem middleBlockOccupancy_three_weighted_deficit_le
    {T : ℕ} {h : StepSchedule T} {lo hi M N n : ℕ}
    (hn : 16 ≤ n) (hnRange : n ∈ Finset.Icc lo hi)
    (hM : 4 * (M + 1) ≤ n) (hN : n ≤ 3 * N)
    (hcut : CutoffConditions criticalP h lo hi) :
    middleBlockOccupancy 3 M N n *
          (betaLower - relativeMassIncrement h n) / (n : ℝ) ≤
      Real.log (4 / 3 : ℝ) *
          (betaLower - relativeMassIncrement h n) / (n : ℝ) +
        24 / (n : ℝ) ^ 2 := by
  have hn0 : 0 < (n : ℝ) := by positivity
  have hocc := middleBlockOccupancy_three_sub_log_abs_le hn hM hN
  have hdef := betaLower_sub_relativeMassIncrement_abs_le_three hcut hnRange
  have hraw := weighted_mul_div_compare hn0
    (show 0 ≤ 8 / (n : ℝ) by positivity) (by norm_num : (0 : ℝ) ≤ 3)
    hocc hdef
  convert hraw using 1 <;> field_simp [ne_of_gt hn0] <;> ring

/-- Boundary-safe `(2m,3m]` weighted estimate.  Its extra `1/n` term is used
only on fixed-ratio boundary bands. -/
theorem middleBlockOccupancy_two_weighted_deficit_boundary_le
    {T : ℕ} {h : StepSchedule T} {lo hi M N n : ℕ}
    (hn : 12 ≤ n) (hnRange : n ∈ Finset.Icc lo hi)
    (hcut : CutoffConditions criticalP h lo hi) :
    middleBlockOccupancy 2 M N n *
          (betaLower - relativeMassIncrement h n) / (n : ℝ) ≤
      Real.log (3 / 2 : ℝ) *
          (betaLower - relativeMassIncrement h n) / (n : ℝ) +
        3 * (Real.log (3 / 2 : ℝ) + 6 / (n : ℝ)) / (n : ℝ) := by
  have hn0 : 0 < (n : ℝ) := by positivity
  have hL : 0 ≤ Real.log (3 / 2 : ℝ) :=
    (Real.log_pos (by norm_num)).le
  have hw0 := middleBlockOccupancy_nonneg 2 M N n
  have hwU := middleBlockOccupancy_two_le_log_add (M := M) (N := N) hn
  have habs :
      |middleBlockOccupancy 2 M N n - Real.log (3 / 2 : ℝ)| ≤
        Real.log (3 / 2 : ℝ) + 6 / (n : ℝ) := by
    rw [abs_le]
    constructor <;> linarith [show 0 ≤ 6 / (n : ℝ) by positivity]
  have hdef := betaLower_sub_relativeMassIncrement_abs_le_three hcut hnRange
  have hraw := weighted_mul_div_compare hn0
    (by positivity) (by norm_num : (0 : ℝ) ≤ 3) habs hdef
  convert hraw using 1 <;> ring

/-- Boundary-safe `(3m,4m]` weighted estimate. -/
theorem middleBlockOccupancy_three_weighted_deficit_boundary_le
    {T : ℕ} {h : StepSchedule T} {lo hi M N n : ℕ}
    (hn : 16 ≤ n) (hnRange : n ∈ Finset.Icc lo hi)
    (hcut : CutoffConditions criticalP h lo hi) :
    middleBlockOccupancy 3 M N n *
          (betaLower - relativeMassIncrement h n) / (n : ℝ) ≤
      Real.log (4 / 3 : ℝ) *
          (betaLower - relativeMassIncrement h n) / (n : ℝ) +
        3 * (Real.log (4 / 3 : ℝ) + 8 / (n : ℝ)) / (n : ℝ) := by
  have hn0 : 0 < (n : ℝ) := by positivity
  have hL : 0 ≤ Real.log (4 / 3 : ℝ) :=
    (Real.log_pos (by norm_num)).le
  have hw0 := middleBlockOccupancy_nonneg 3 M N n
  have hwU := middleBlockOccupancy_three_le_log_add (M := M) (N := N) hn
  have habs :
      |middleBlockOccupancy 3 M N n - Real.log (4 / 3 : ℝ)| ≤
        Real.log (4 / 3 : ℝ) + 8 / (n : ℝ) := by
    rw [abs_le]
    constructor <;> linarith [show 0 ≤ 8 / (n : ℝ) by positivity]
  have hdef := betaLower_sub_relativeMassIncrement_abs_le_three hcut hnRange
  have hraw := weighted_mul_div_compare hn0
    (by positivity) (by norm_num : (0 : ℝ) ≤ 3) habs hdef
  convert hraw using 1 <;> ring

end

end GDLowerBound.FourBlock
