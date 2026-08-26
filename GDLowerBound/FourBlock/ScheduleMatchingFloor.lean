import GDLowerBound.FourBlock.ScheduleMatchingTransfer

/-!
# Log-score interface to the robust matching floor

The global large-matching branch naturally controls an outside-in logarithmic
score.  These lemmas isolate the exact finite inequality that this branch must
supply in order to invoke the matching-tolerant local certificate.
-/

namespace GDLowerBound.FourBlock

open GDLowerBound.Schedule GDLowerBound.RankAnalysis

noncomputable section

theorem scheduleActualMatching_ge_half_floor_of_logScore
    {T m : ℕ} {h : StepSchedule T} (hh : IsNonnegativeSchedule h)
    (hm : 0 < m) (hq : 2 * (m + m) ≤ longCount h)
    (hscore : -(m : ℝ) / 1000000 ≤
      outsideInLogScore (m + m) (scheduleFourBlockWeights h hq)) :
    (-1 / 2000000 : ℝ) ≤
      fourBlockMatching
        (fourBlockZ (scheduleFourBlockWeights h hq))
        (fourBlockA (scheduleFourBlockWeights h hq))
        (fourBlockR (scheduleFourBlockWeights h hq))
        (fourBlockS (scheduleFourBlockWeights h hq)) := by
  have hj := scheduleOutsideInLogScore_le_fourBlock hh hm hq
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hscaled := div_le_div_of_nonneg_right hscore
    (by positivity : (0 : ℝ) ≤ 2 * m)
  calc
    (-1 / 2000000 : ℝ) =
        (-(m : ℝ) / 1000000) / (2 * m) := by
      field_simp [hmR.ne']
      ring
    _ ≤ outsideInLogScore (m + m) (scheduleFourBlockWeights h hq) /
        (2 * m) := hscaled
    _ ≤ _ := hj

theorem scheduleIdealMatching_ge_floor_of_logScore
    {T m : ℕ} {h : StepSchedule T} (hh : IsNonnegativeSchedule h)
    (hm : 2000 ≤ m) (hq : 2 * (m + m) ≤ longCount h)
    (hzlo : (centralThetaLowerQ : ℝ) ≤ zetaState h (2 * (m + m)))
    (hord : OrderedFourBlocks (schedulePrefixA h m)
      (schedulePrefixR h m) (schedulePrefixS h m))
    (hrlo : (1 / 20 : ℝ) ≤ schedulePrefixR h m)
    (hscore : -(m : ℝ) / 1000000 ≤
      outsideInLogScore (m + m) (scheduleFourBlockWeights h hq)) :
    (centralMatchingFloorQ : ℝ) ≤
      fourBlockMatching (zetaState h (2 * (m + m)))
        (schedulePrefixA h m) (schedulePrefixR h m) (schedulePrefixS h m) := by
  have hm0 : 0 < m := by omega
  exact scheduleIdealMatching_ge_floor hh hm0 hq hzlo hord hrlo
    (scheduleActualMatching_ge_half_floor_of_logScore hh hm0 hq hscore)
    (scheduleMatchingError_le_half_floor hm)

end

end GDLowerBound.FourBlock
