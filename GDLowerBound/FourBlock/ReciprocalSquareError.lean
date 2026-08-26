import GDLowerBound.FourBlock.ScheduleLocalEnergy

/-! # Explicit `C/m` bound for the finite block error -/

namespace GDLowerBound.FourBlock

open scoped BigOperators
open GDLowerBound.Schedule GDLowerBound.RankAnalysis

noncomputable section

theorem one_div_sq_le_reciprocal_diff {n : ℕ} (hn : 2 ≤ n) :
    1 / (n : ℝ) ^ 2 ≤ 1 / ((n - 1 : ℕ) : ℝ) - 1 / (n : ℝ) := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by positivity
  have hnsub0 : (0 : ℝ) < (n - 1 : ℕ) := by
    exact_mod_cast (by omega : 0 < n - 1)
  rw [Nat.cast_sub (by omega : 1 ≤ n)]
  have hdiff : 1 / ((n : ℝ) - 1) - 1 / (n : ℝ) =
      1 / ((n : ℝ) * ((n : ℝ) - 1)) := by
    field_simp [hn0.ne', (by linarith : (n : ℝ) - 1 ≠ 0)]
    ring
  norm_num only [Nat.cast_one]
  rw [hdiff]
  exact one_div_le_one_div_of_le (mul_pos hn0 (by linarith)) (by nlinarith)

theorem reciprocalSquareBlock_le_telescope
    {lo hi : ℕ} (hlo : 1 ≤ lo) (hlohi : lo ≤ hi) :
    ∑ n ∈ Finset.Ico (lo + 1) (hi + 1), 1 / (n : ℝ) ^ 2 ≤
      1 / (lo : ℝ) - 1 / (hi : ℝ) := by
  induction hi, hlohi using Nat.le_induction with
  | base => simp
  | succ hi hlohi ih =>
      rw [Finset.sum_Ico_succ_top (by omega)]
      have hstep := one_div_sq_le_reciprocal_diff
        (n := hi + 1) (by omega : 2 ≤ hi + 1)
      have hcast : (((hi + 1 : ℕ) - 1 : ℕ) : ℝ) = (hi : ℝ) := by
        norm_num
      rw [hcast] at hstep
      calc
        ∑ n ∈ Finset.Ico (lo + 1) (hi + 1), 1 / (n : ℝ) ^ 2 +
              1 / ((hi + 1 : ℕ) : ℝ) ^ 2 ≤
            (1 / (lo : ℝ) - 1 / (hi : ℝ)) +
              (1 / (hi : ℝ) - 1 / ((hi + 1 : ℕ) : ℝ)) :=
          add_le_add ih hstep
        _ = 1 / (lo : ℝ) - 1 / ((hi + 1 : ℕ) : ℝ) := by ring

theorem reciprocalSquareBlock_le_inv
    {lo hi : ℕ} (hlo : 1 ≤ lo) (hlohi : lo ≤ hi) :
    ∑ n ∈ Finset.Ico (lo + 1) (hi + 1), 1 / (n : ℝ) ^ 2 ≤
      1 / (lo : ℝ) := by
  have htelescope := reciprocalSquareBlock_le_telescope hlo hlohi
  have hhi0 : 0 ≤ 1 / (hi : ℝ) := by positivity
  linarith

/-- Sharp telescoping form of the finite-rank dilation defect.  Unlike
`dilationBlockH_lower_inv`, this retains the cancellation at the upper
endpoint of the block. -/
theorem dilationBlockH_lower_telescope
    {T Q : ℕ} (hQ : (criticalTheta)⁻¹ < (Q : ℝ))
    {h : StepSchedule T} (hh : IsNonnegativeSchedule h)
    {lo hi : ℕ} (hQlo : Q ≤ lo) (hlo : 1 ≤ lo)
    (hlohi : lo ≤ hi) (hhir : hi ≤ longCount h)
    (hcut : CutoffConditions criticalP h lo (longCount h)) :
    dilationBlockH h lo hi ≥
      -oneStepLyapunovConstant criticalP *
        (1 / (lo : ℝ) - 1 / (hi : ℝ)) := by
  have hraw := dilationBlockH_lower hQ hh hQlo hlo hlohi hhir hcut
  have hsum := reciprocalSquareBlock_le_telescope hlo hlohi
  have hC : 0 ≤ oneStepLyapunovConstant criticalP :=
    zero_le_one.trans (oneStepLyapunovConstant_ge_one criticalP)
  have hmul := mul_le_mul_of_nonneg_left hsum hC
  calc
    -oneStepLyapunovConstant criticalP *
          (1 / (lo : ℝ) - 1 / (hi : ℝ)) ≤
        -oneStepLyapunovConstant criticalP *
          (∑ n ∈ Finset.Ico (lo + 1) (hi + 1), 1 / (n : ℝ) ^ 2) := by
      nlinarith
    _ ≤ dilationBlockH h lo hi := hraw


/-- Clean finite-rank form of the dilation defect estimate. -/
theorem dilationBlockH_lower_inv
    {T Q : ℕ} (hQ : (criticalTheta)⁻¹ < (Q : ℝ))
    {h : StepSchedule T} (hh : IsNonnegativeSchedule h)
    {lo hi : ℕ} (hQlo : Q ≤ lo) (hlo : 1 ≤ lo)
    (hlohi : lo ≤ hi) (hhir : hi ≤ longCount h)
    (hcut : CutoffConditions criticalP h lo (longCount h)) :
    dilationBlockH h lo hi ≥
      -oneStepLyapunovConstant criticalP / (lo : ℝ) := by
  have hraw := dilationBlockH_lower hQ hh hQlo hlo hlohi hhir hcut
  have hsum := reciprocalSquareBlock_le_inv hlo hlohi
  have hC : 0 ≤ oneStepLyapunovConstant criticalP :=
    zero_le_one.trans (oneStepLyapunovConstant_ge_one criticalP)
  have hmul := mul_le_mul_of_nonneg_left hsum hC
  have heq : oneStepLyapunovConstant criticalP * (1 / (lo : ℝ)) =
      oneStepLyapunovConstant criticalP / (lo : ℝ) := by ring
  rw [heq] at hmul
  calc
    -oneStepLyapunovConstant criticalP / (lo : ℝ) =
        -(oneStepLyapunovConstant criticalP / (lo : ℝ)) := by ring
    _ ≤ -(oneStepLyapunovConstant criticalP *
        (∑ n ∈ Finset.Ico (lo + 1) (hi + 1), 1 / (n : ℝ) ^ 2)) :=
      neg_le_neg hmul
    _ = -oneStepLyapunovConstant criticalP *
        (∑ n ∈ Finset.Ico (lo + 1) (hi + 1), 1 / (n : ℝ) ^ 2) := by ring
    _ ≤ dilationBlockH h lo hi := hraw

end

end GDLowerBound.FourBlock
