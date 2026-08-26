import GDLowerBound.FourBlock.ScheduleBlockRatios

/-! # The combined `2m`-to-`4m` block-ratio identity -/

namespace GDLowerBound.FourBlock

open GDLowerBound.Schedule GDLowerBound.RankAnalysis

noncomputable section

theorem dilationBlockH_two_three_add_three_four_eq
    {T m : ℕ} {h : StepSchedule T} (hh : IsNonnegativeSchedule h)
    (hm : 0 < m) (hq : 4 * m ≤ longCount h) :
    dilationBlockH h (2 * m) (3 * m) +
        dilationBlockH h (3 * m) (4 * m) =
      betaLower *
          (relativeMassIncrement h (2 * m) *
              (zetaState h (2 * m) - criticalTheta) +
            relativeMassIncrement h (3 * m) *
              (zetaState h (3 * m) - criticalTheta)) +
        Real.log (schedulePrefixR h m / tailR20) +
        Real.log (zetaState h (4 * m)) -
        Real.log (zetaState h (2 * m)) := by
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  have hz2 := zetaState_pos_of_rank hh (q := 2 * m) (by omega) (by omega)
  have hz4 := zetaState_pos_of_rank hh (q := 4 * m) (by omega) hq
  have hr := schedulePrefixR_pos (h := h) hm hq
  have hD2 := unresolvedMass_pos hh (2 * m)
  have hD3 := unresolvedMass_pos hh (3 * m)
  have hD4 := unresolvedMass_pos hh (4 * m)
  have hr20 : 0 < tailR20 := by
    unfold tailR20
    exact Real.rpow_pos_of_pos (by norm_num) _
  have hdilation23 :
      (((3 * m : ℕ) : ℝ) / ((2 * m : ℕ) : ℝ)) = 3 / 2 := by
    norm_num [Nat.cast_mul]
    field_simp [hmR]
  have hdilation34 :
      (((4 * m : ℕ) : ℝ) / ((3 * m : ℕ) : ℝ)) = 4 / 3 := by
    norm_num [Nat.cast_mul]
    field_simp [hmR]
  have hlogDilation :
      Real.log (3 / 2 : ℝ) + Real.log (4 / 3 : ℝ) = Real.log 2 := by
    rw [Real.log_div (by norm_num : (3 : ℝ) ≠ 0)
        (by norm_num : (2 : ℝ) ≠ 0),
      Real.log_div (by norm_num : (4 : ℝ) ≠ 0)
        (by norm_num : (3 : ℝ) ≠ 0)]
    rw [show (4 : ℝ) = (2 : ℝ) ^ 2 by norm_num, Real.log_pow]
    ring
  have hlogMass :
      Real.log (unresolvedMass h (2 * m) / unresolvedMass h (3 * m)) +
          Real.log (unresolvedMass h (3 * m) / unresolvedMass h (4 * m)) =
        Real.log (unresolvedMass h (2 * m) / unresolvedMass h (4 * m)) := by
    rw [Real.log_div hD2.ne' hD3.ne', Real.log_div hD3.ne' hD4.ne',
      Real.log_div hD2.ne' hD4.ne']
    ring
  have hlogHalf : Real.log (1 / 2 : ℝ) = -Real.log 2 := by
    rw [Real.log_div (by norm_num : (1 : ℝ) ≠ 0)
      (by norm_num : (2 : ℝ) ≠ 0), Real.log_one]
    ring
  unfold dilationBlockH endpointDefect
  rw [hdilation23, hdilation34]
  have hrearrange :
      betaLower * Real.log (3 / 2 : ℝ) -
              Real.log (unresolvedMass h (2 * m) / unresolvedMass h (3 * m)) +
            betaLower *
              (relativeMassIncrement h (2 * m) *
                (zetaState h (2 * m) - criticalTheta)) +
          (betaLower * Real.log (4 / 3 : ℝ) -
              Real.log (unresolvedMass h (3 * m) / unresolvedMass h (4 * m)) +
            betaLower *
              (relativeMassIncrement h (3 * m) *
                (zetaState h (3 * m) - criticalTheta))) =
        betaLower *
            (relativeMassIncrement h (2 * m) *
                (zetaState h (2 * m) - criticalTheta) +
              relativeMassIncrement h (3 * m) *
                (zetaState h (3 * m) - criticalTheta)) +
          betaLower *
            (Real.log (3 / 2 : ℝ) + Real.log (4 / 3 : ℝ)) -
          (Real.log (unresolvedMass h (2 * m) / unresolvedMass h (3 * m)) +
            Real.log (unresolvedMass h (3 * m) / unresolvedMass h (4 * m))) := by
    ring
  rw [hrearrange, hlogDilation, hlogMass,
    unresolvedMass_two_four_ratio hh hm hq]
  rw [Real.log_div
      (mul_pos (by positivity : (0 : ℝ) < (1 / 2 : ℝ) ^ 2)
        (div_pos hz2 hz4)).ne' hr.ne',
    Real.log_mul (by positivity : (1 / 2 : ℝ) ^ 2 ≠ 0)
      (div_pos hz2 hz4).ne',
    Real.log_pow, Real.log_div hz2.ne' hz4.ne',
    Real.log_div hr.ne' hr20.ne']
  unfold tailR20
  rw [Real.log_rpow (by norm_num : (0 : ℝ) < 1 / 2), hlogHalf]
  ring

end

end GDLowerBound.FourBlock
