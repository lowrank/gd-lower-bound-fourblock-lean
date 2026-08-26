import GDLowerBound.FourBlock.ScheduleBlockIdentity

/-! # From exact finite sums to dilation-log block variables -/

namespace GDLowerBound.FourBlock

open scoped BigOperators
open GDLowerBound.Schedule GDLowerBound.RankAnalysis

noncomputable section

/-- A single right-endpoint rectangle lies below the logarithmic integral. -/
theorem one_div_succ_le_log_succ_div {n : ℕ} (hn : 1 ≤ n) :
    1 / ((n + 1 : ℕ) : ℝ) ≤
      Real.log (((n + 1 : ℕ) : ℝ) / (n : ℝ)) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hn10 : (0 : ℝ) < (n + 1 : ℕ) := by positivity
  have hlog := Real.log_le_sub_one_of_pos (div_pos hn0 hn10)
  have hratio :
      (n : ℝ) / ((n + 1 : ℕ) : ℝ) - 1 =
        -(1 / ((n + 1 : ℕ) : ℝ)) := by
    field_simp [hn10.ne']
    norm_num
  have hinvlog :
      -Real.log ((n : ℝ) / ((n + 1 : ℕ) : ℝ)) =
        Real.log (((n + 1 : ℕ) : ℝ) / (n : ℝ)) := by
    rw [Real.log_div hn0.ne' hn10.ne', Real.log_div hn10.ne' hn0.ne']
    ring
  rw [hratio] at hlog
  rw [← hinvlog]
  linarith

/-- The exact harmonic block sum is at most its dilation logarithm. -/
theorem harmonicBlock_le_log_ratio
    {lo hi : ℕ} (hlo : 1 ≤ lo) (hlohi : lo ≤ hi) :
    ∑ n ∈ Finset.Ico (lo + 1) (hi + 1), 1 / (n : ℝ) ≤
      Real.log ((hi : ℝ) / (lo : ℝ)) := by
  induction hi, hlohi using Nat.le_induction with
  | base => simp [show (lo : ℝ) ≠ 0 by positivity]
  | succ hi hlohi ih =>
      rw [Finset.sum_Ico_succ_top (by omega)]
      have hstep := one_div_succ_le_log_succ_div
        (n := hi) (by omega : 1 ≤ hi)
      have hlo0 : (lo : ℝ) ≠ 0 := by positivity
      have hhi0 : (hi : ℝ) ≠ 0 := by exact_mod_cast (by omega : hi ≠ 0)
      have hnext0 : ((hi + 1 : ℕ) : ℝ) ≠ 0 := by positivity
      have hlogs :
          Real.log ((hi : ℝ) / (lo : ℝ)) +
              Real.log (((hi + 1 : ℕ) : ℝ) / (hi : ℝ)) =
            Real.log (((hi + 1 : ℕ) : ℝ) / (lo : ℝ)) := by
        rw [Real.log_div hhi0 hlo0, Real.log_div hnext0 hhi0,
          Real.log_div hnext0 hlo0]
        ring
      rw [← hlogs]
      exact add_le_add ih hstep

/-- The paper's dilation-log version of the block variable. -/
def dilationBlockH {T : ℕ} (h : StepSchedule T) (lo hi : ℕ) : ℝ :=
  betaLower * Real.log ((hi : ℝ) / (lo : ℝ)) -
    Real.log (unresolvedMass h lo / unresolvedMass h hi) +
    betaLower * endpointDefect h lo

theorem scheduleBlockH_le_dilationBlockH
    {T : ℕ} {h : StepSchedule T} (hh : IsNonnegativeSchedule h)
    {lo hi : ℕ} (hlo : 1 ≤ lo) (hlohi : lo ≤ hi)
    (hhir : hi ≤ longCount h) :
    scheduleBlockH h lo hi ≤ dilationBlockH h lo hi := by
  rw [scheduleBlockH_eq hh hlohi hhir]
  unfold dilationBlockH
  have hsum := harmonicBlock_le_log_ratio hlo hlohi
  have hbeta := mul_le_mul_of_nonneg_left hsum betaLower_pos.le
  linarith

/-- Consequently the exact drift estimate gives a lower bound for the
dilation-log block variable used by the local analytic certificate. -/
theorem dilationBlockH_lower
    {T Q : ℕ} (hQ : (criticalTheta)⁻¹ < (Q : ℝ))
    {h : StepSchedule T} (hh : IsNonnegativeSchedule h)
    {lo hi : ℕ} (hQlo : Q ≤ lo) (hlo : 1 ≤ lo)
    (hlohi : lo ≤ hi) (hhir : hi ≤ longCount h)
    (hcut : CutoffConditions criticalP h lo (longCount h)) :
    dilationBlockH h lo hi ≥
      -oneStepLyapunovConstant criticalP *
        ∑ n ∈ Finset.Ico (lo + 1) (hi + 1), 1 / (n : ℝ) ^ 2 := by
  exact (scheduleBlockH_lower hQ hh hQlo hlohi hhir hcut).trans
    (scheduleBlockH_le_dilationBlockH hh hlo hlohi hhir)

end

end GDLowerBound.FourBlock
