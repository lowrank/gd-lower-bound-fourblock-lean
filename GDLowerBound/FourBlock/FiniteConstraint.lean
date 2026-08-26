import GDLowerBound.FourBlock.ReciprocalSquareError

/-! # Explicit finite-rank relaxation of the nonlinear side constraint -/

namespace GDLowerBound.FourBlock

open GDLowerBound.Schedule GDLowerBound.RankAnalysis

noncomputable section

theorem qState_le_tailCoordinate_mul_exp_of_defect
    {T m : ℕ} {h : StepSchedule T} (hh : IsNonnegativeSchedule h)
    (hm : 0 < m) (hq : 4 * m ≤ longCount h) {eps : ℝ}
    (hdefect : -eps ≤ dilationBlockH h (3 * m) (4 * m)) :
    qState (zetaState h (3 * m)) (relativeMassIncrement h (3 * m)) ≤
      (schedulePrefixS h m * zetaState h (4 * m) / tailR30) *
        Real.exp eps := by
  have hz3 := zetaState_pos_of_rank hh (q := 3 * m) (by omega) (by omega)
  have hz4 := zetaState_pos_of_rank hh (q := 4 * m) (by omega) hq
  have hs := schedulePrefixS_pos (h := h) hm hq
  have hr30 : 0 < tailR30 := by
    unfold tailR30
    exact Real.rpow_pos_of_pos (by norm_num) _
  let R := schedulePrefixS h m * zetaState h (4 * m) / tailR30
  have hR : 0 < R := div_pos (mul_pos hs hz4) hr30
  have hidentity := dilationBlockH_three_four_eq hh hm hq
  have hlogq := log_qState
    (z := zetaState h (3 * m))
    (v := relativeMassIncrement h (3 * m)) hz3
  have hlog :
      Real.log (qState (zetaState h (3 * m))
          (relativeMassIncrement h (3 * m))) ≤
        Real.log (R * Real.exp eps) := by
    rw [hlogq, Real.log_mul hR.ne' (Real.exp_pos eps).ne', Real.log_exp]
    dsimp only [R]
    linarith
  have hexp := Real.exp_le_exp.mpr hlog
  rw [Real.exp_log (qState_pos hz3),
    Real.exp_log (mul_pos hR (Real.exp_pos eps))] at hexp
  exact hexp

/-- The exact cutoff drift gives the relaxed side constraint with the fully
explicit exponent `C/(3m)`. -/
theorem schedule_qState_le_tailCoordinate_mul_exp_error
    {T Q m : ℕ} (hQ : (criticalTheta)⁻¹ < (Q : ℝ))
    {h : StepSchedule T} (hh : IsNonnegativeSchedule h)
    (hm : 0 < m) (hQ3m : Q ≤ 3 * m)
    (hq : 4 * m ≤ longCount h)
    (hcut : CutoffConditions criticalP h (3 * m) (longCount h)) :
    qState (zetaState h (3 * m)) (relativeMassIncrement h (3 * m)) ≤
      (schedulePrefixS h m * zetaState h (4 * m) / tailR30) *
        Real.exp (oneStepLyapunovConstant criticalP / (3 * m : ℕ)) := by
  have hdefect := dilationBlockH_lower_inv hQ hh hQ3m
    (by omega : 1 ≤ 3 * m) (by omega : 3 * m ≤ 4 * m) hq hcut
  apply qState_le_tailCoordinate_mul_exp_of_defect hh hm hq
  simpa only [neg_div] using hdefect

end

end GDLowerBound.FourBlock
