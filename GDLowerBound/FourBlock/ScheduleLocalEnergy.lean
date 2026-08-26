import GDLowerBound.FourBlock.ScheduleBlockRatioSum
import GDLowerBound.FourBlock.LocalGapTheorem

/-! # Schedule-level realization of the certified local energy -/

namespace GDLowerBound.FourBlock

open GDLowerBound.Schedule GDLowerBound.RankAnalysis

noncomputable section

def scheduleDilationEnergy {T : ℕ} (h : StepSchedule T) (m : ℕ) : ℝ :=
  weightedScheduleEnergy
    (zetaState h (2 * m)) (relativeMassIncrement h (2 * m))
    (zetaState h (3 * m)) (relativeMassIncrement h (3 * m))
    (zetaState h (4 * m)) (relativeMassIncrement h (4 * m))
    (dilationBlockH h (2 * m) (3 * m))
    (dilationBlockH h (3 * m) (4 * m))

/-- The schedule energy is exactly the certified split energy, apart from
replacing the fourth endpoint envelope by its original endpoint cost. -/
theorem scheduleDilationEnergy_eq_localEnergy
    {T m : ℕ} {h : StepSchedule T} (hh : IsNonnegativeSchedule h)
    (hm : 0 < m) (hq : 4 * m ≤ longCount h) :
    scheduleDilationEnergy h m =
      fourBlockLocalEnergy
          (zetaState h (2 * m)) (relativeMassIncrement h (2 * m))
          (zetaState h (3 * m)) (relativeMassIncrement h (3 * m))
          (schedulePrefixS h m * zetaState h (4 * m) / tailR30)
          (zetaState h (4 * m)) (schedulePrefixR h m) +
        endpointCost centralC4Q centralD4Q
          (zetaState h (4 * m)) (relativeMassIncrement h (4 * m)) -
        centralEndpoint (zetaState h (4 * m)) := by
  unfold scheduleDilationEnergy
  apply weightedScheduleEnergy_eq_localEnergy
  · exact dilationBlockH_two_three_add_three_four_eq hh hm hq
  · exact dilationBlockH_three_four_eq hh hm hq

theorem scheduleLocalEnergy_le_dilationEnergy
    {T m : ℕ} {h : StepSchedule T} (hh : IsNonnegativeSchedule h)
    (hm : 0 < m) (hq : 4 * m ≤ longCount h)
    (hz4 : criticalTheta ≤ zetaState h (4 * m))
    (hz4hi : zetaState h (4 * m) ≤ (119 / 250 : ℝ))
    (hv4 : 0 ≤ relativeMassIncrement h (4 * m)) :
    fourBlockLocalEnergy
        (zetaState h (2 * m)) (relativeMassIncrement h (2 * m))
        (zetaState h (3 * m)) (relativeMassIncrement h (3 * m))
        (schedulePrefixS h m * zetaState h (4 * m) / tailR30)
        (zetaState h (4 * m)) (schedulePrefixR h m) ≤
      scheduleDilationEnergy h m := by
  rw [scheduleDilationEnergy_eq_localEnergy hh hm hq]
  have hend := centralEndpoint_le_endpointCost hz4 hz4hi hv4
  linarith

/-- Nonnegativity of the third dilation defect gives exactly the nonlinear
state constraint used by the side certificate. -/
theorem qState_le_tailCoordinate_of_dilationBlockH_nonneg
    {T m : ℕ} {h : StepSchedule T} (hh : IsNonnegativeSchedule h)
    (hm : 0 < m) (hq : 4 * m ≤ longCount h)
    (hdefect : 0 ≤ dilationBlockH h (3 * m) (4 * m)) :
    qState (zetaState h (3 * m)) (relativeMassIncrement h (3 * m)) ≤
      schedulePrefixS h m * zetaState h (4 * m) / tailR30 := by
  have hz3 := zetaState_pos_of_rank hh (q := 3 * m) (by omega) (by omega)
  have hz4 := zetaState_pos_of_rank hh (q := 4 * m) (by omega) hq
  have hs := schedulePrefixS_pos (h := h) hm hq
  have hr30 : 0 < tailR30 := by
    unfold tailR30
    exact Real.rpow_pos_of_pos (by norm_num) _
  have hR : 0 < schedulePrefixS h m * zetaState h (4 * m) / tailR30 :=
    div_pos (mul_pos hs hz4) hr30
  have hidentity := dilationBlockH_three_four_eq hh hm hq
  have hlogq := log_qState (z := zetaState h (3 * m))
    (v := relativeMassIncrement h (3 * m)) hz3
  have hlog :
      Real.log (qState (zetaState h (3 * m))
          (relativeMassIncrement h (3 * m))) ≤
        Real.log (schedulePrefixS h m * zetaState h (4 * m) / tailR30) := by
    rw [hlogq]
    linarith
  have hexp := Real.exp_le_exp.mpr hlog
  rw [Real.exp_log (qState_pos hz3), Real.exp_log hR] at hexp
  exact hexp

end

end GDLowerBound.FourBlock
