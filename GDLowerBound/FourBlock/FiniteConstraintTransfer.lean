import GDLowerBound.FourBlock.FiniteConstraint
import GDLowerBound.FourBlock.ScheduleMatchingDomination

/-!
# Transferring the finite drift into the certified local energy

The reciprocal-square error over the third block telescopes from `3m` to
`4m`.  Consequently its exact four-block loss is `C/(12m)`, rather than the
coarser `C/(3m)`.  This file records both the sharpened nonlinear constraint
and the corresponding additive change in the local logarithmic energy.
-/

namespace GDLowerBound.FourBlock

open GDLowerBound.Schedule GDLowerBound.RankAnalysis

noncomputable section

/-- Taking logarithms transfers a multiplicative `exp eps` relaxation into
an additive `eps` relaxation of the nonlinear state constraint. -/
theorem log_qState_le_log_tail_add_error {z v R eps : ℝ}
    (hz : 0 < z) (hR : 0 < R)
    (hq : qState z v ≤ R * Real.exp eps) :
    Real.log z - betaLower * v * (z - criticalTheta) ≤
      Real.log R + eps := by
  have hlog := Real.log_le_log (qState_pos hz) hq
  rw [log_qState hz, Real.log_mul hR.ne' (Real.exp_pos eps).ne',
    Real.log_exp] at hlog
  exact hlog

/-- Inflating the tail coordinate by `exp eps` adds exactly
`centralAlphaQ * eps` to the local energy. -/
theorem fourBlockLocalEnergy_mul_exp {z₂ v₂ z₃ v₃ R z r eps : ℝ}
    (hR : 0 < R) :
    fourBlockLocalEnergy z₂ v₂ z₃ v₃ (R * Real.exp eps) z r =
      fourBlockLocalEnergy z₂ v₂ z₃ v₃ R z r +
        (centralAlphaQ : ℝ) * eps := by
  unfold fourBlockLocalEnergy q3Contribution
  rw [Real.log_mul hR.ne' (Real.exp_pos eps).ne', Real.log_exp]
  ring

/-- The third-block defect has the sharp telescoping loss `C/(12m)`. -/
theorem scheduleDilationBlockH_three_four_lower_sharp
    {T Q m : ℕ} (hQ : (criticalTheta)⁻¹ < (Q : ℝ))
    {h : StepSchedule T} (hh : IsNonnegativeSchedule h)
    (hm : 0 < m) (hQ3m : Q ≤ 3 * m)
    (hq : 4 * m ≤ longCount h)
    (hcut : CutoffConditions criticalP h (3 * m) (longCount h)) :
    dilationBlockH h (3 * m) (4 * m) ≥
      -oneStepLyapunovConstant criticalP / (12 * m : ℕ) := by
  have hraw := dilationBlockH_lower_telescope hQ hh hQ3m
    (by omega : 1 ≤ 3 * m) (by omega : 3 * m ≤ 4 * m) hq hcut
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have harith :
      (1 / ((3 * m : ℕ) : ℝ) - 1 / ((4 * m : ℕ) : ℝ)) =
        1 / ((12 * m : ℕ) : ℝ) := by
    push_cast
    field_simp
    ring
  rw [harith] at hraw
  calc
    -oneStepLyapunovConstant criticalP / ((12 * m : ℕ) : ℝ) =
        -oneStepLyapunovConstant criticalP *
          (1 / ((12 * m : ℕ) : ℝ)) := by ring
    _ ≤ dilationBlockH h (3 * m) (4 * m) := hraw

/-- Sharp finite-rank relaxation of the schedule side constraint. -/
theorem schedule_qState_le_tailCoordinate_mul_exp_sharp_error
    {T Q m : ℕ} (hQ : (criticalTheta)⁻¹ < (Q : ℝ))
    {h : StepSchedule T} (hh : IsNonnegativeSchedule h)
    (hm : 0 < m) (hQ3m : Q ≤ 3 * m)
    (hq : 4 * m ≤ longCount h)
    (hcut : CutoffConditions criticalP h (3 * m) (longCount h)) :
    qState (zetaState h (3 * m)) (relativeMassIncrement h (3 * m)) ≤
      (schedulePrefixS h m * zetaState h (4 * m) / tailR30) *
        Real.exp (oneStepLyapunovConstant criticalP / (12 * m : ℕ)) := by
  apply qState_le_tailCoordinate_mul_exp_of_defect hh hm hq
  simpa only [neg_div] using
    scheduleDilationBlockH_three_four_lower_sharp hQ hh hm hQ3m hq hcut

/-- The same inflation changes the schedule-level local energy by only its
explicit logarithmic price. -/
theorem scheduleInflatedLocalEnergy_le_dilationEnergy_add
    {T m : ℕ} {h : StepSchedule T} (hh : IsNonnegativeSchedule h)
    (hm : 0 < m) (hq : 4 * m ≤ longCount h)
    (hz4 : criticalTheta ≤ zetaState h (4 * m))
    (hz4hi : zetaState h (4 * m) ≤ (119 / 250 : ℝ))
    (hv4 : 0 ≤ relativeMassIncrement h (4 * m)) {eps : ℝ} :
    fourBlockLocalEnergy
        (zetaState h (2 * m)) (relativeMassIncrement h (2 * m))
        (zetaState h (3 * m)) (relativeMassIncrement h (3 * m))
        ((schedulePrefixS h m * zetaState h (4 * m) / tailR30) *
          Real.exp eps)
        (zetaState h (4 * m)) (schedulePrefixR h m) ≤
      scheduleDilationEnergy h m + (centralAlphaQ : ℝ) * eps := by
  have hs := schedulePrefixS_pos (h := h) hm hq
  have hz4pos := zetaState_pos_of_rank hh (q := 4 * m) (by omega) hq
  have hr30 : 0 < tailR30 := by
    unfold tailR30
    exact Real.rpow_pos_of_pos (by norm_num) _
  have hR : 0 < schedulePrefixS h m * zetaState h (4 * m) / tailR30 :=
    div_pos (mul_pos hs hz4pos) hr30
  rw [fourBlockLocalEnergy_mul_exp hR]
  have hbase := scheduleLocalEnergy_le_dilationEnergy
    hh hm hq hz4 hz4hi hv4
  linarith

/-- Combined schedule interface: the exact finite-drift hypotheses give both
the inflated nonlinear constraint and its explicit energy cost. -/
theorem scheduleSharpConstraintAndEnergy
    {T Q m : ℕ} (hQ : (criticalTheta)⁻¹ < (Q : ℝ))
    {h : StepSchedule T} (hh : IsNonnegativeSchedule h)
    (hm : 0 < m) (hQ3m : Q ≤ 3 * m)
    (hq : 4 * m ≤ longCount h)
    (hcut : CutoffConditions criticalP h (3 * m) (longCount h))
    (hz4 : criticalTheta ≤ zetaState h (4 * m))
    (hz4hi : zetaState h (4 * m) ≤ (119 / 250 : ℝ))
    (hv4 : 0 ≤ relativeMassIncrement h (4 * m)) :
    qState (zetaState h (3 * m)) (relativeMassIncrement h (3 * m)) ≤
        (schedulePrefixS h m * zetaState h (4 * m) / tailR30) *
          Real.exp (oneStepLyapunovConstant criticalP / (12 * m : ℕ)) ∧
      fourBlockLocalEnergy
          (zetaState h (2 * m)) (relativeMassIncrement h (2 * m))
          (zetaState h (3 * m)) (relativeMassIncrement h (3 * m))
          ((schedulePrefixS h m * zetaState h (4 * m) / tailR30) *
            Real.exp (oneStepLyapunovConstant criticalP / (12 * m : ℕ)))
          (zetaState h (4 * m)) (schedulePrefixR h m) ≤
        scheduleDilationEnergy h m +
          (centralAlphaQ : ℝ) *
            (oneStepLyapunovConstant criticalP / (12 * m : ℕ)) := by
  constructor
  · exact schedule_qState_le_tailCoordinate_mul_exp_sharp_error
      hQ hh hm hQ3m hq hcut
  · exact scheduleInflatedLocalEnergy_le_dilationEnergy_add
      hh hm hq hz4 hz4hi hv4

end

end GDLowerBound.FourBlock
