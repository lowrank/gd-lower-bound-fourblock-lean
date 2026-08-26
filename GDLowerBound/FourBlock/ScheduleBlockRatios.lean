import GDLowerBound.FourBlock.ScheduleCoordinates

/-! # The two exact four-block ratio identities -/

namespace GDLowerBound.FourBlock

open GDLowerBound.Schedule GDLowerBound.RankAnalysis

noncomputable section

theorem zetaState_pos_of_rank
    {T q : ℕ} {h : StepSchedule T} (hh : IsNonnegativeSchedule h)
    (hq0 : 1 ≤ q) (hqr : q ≤ longCount h) :
    0 < zetaState h q := by
  unfold zetaState
  have hqR : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  positivity [unresolvedMass_pos hh q,
    reciprocalPrefix_pos_of_rank (h := h) hq0 hqr]

/-- Exact identity for the `3m`-to-`4m` dilation defect. -/
theorem dilationBlockH_three_four_eq
    {T m : ℕ} {h : StepSchedule T} (hh : IsNonnegativeSchedule h)
    (hm : 0 < m) (hq : 4 * m ≤ longCount h) :
    dilationBlockH h (3 * m) (4 * m) =
      betaLower * relativeMassIncrement h (3 * m) *
          (zetaState h (3 * m) - criticalTheta) +
        Real.log (schedulePrefixS h m * zetaState h (4 * m) / tailR30) -
        Real.log (zetaState h (3 * m)) := by
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  have hz3 := zetaState_pos_of_rank hh (q := 3 * m) (by omega) (by omega)
  have hz4 := zetaState_pos_of_rank hh (q := 4 * m) (by omega) hq
  have hs := schedulePrefixS_pos (h := h) hm hq
  have hr30 : 0 < tailR30 := by
    unfold tailR30
    exact Real.rpow_pos_of_pos (by norm_num) _
  have hdilation :
      (((4 * m : ℕ) : ℝ) / ((3 * m : ℕ) : ℝ)) = 4 / 3 := by
    norm_num [Nat.cast_mul]
    field_simp [hmR]
  have hlogInverse : Real.log (4 / 3 : ℝ) = -Real.log (3 / 4 : ℝ) := by
    rw [Real.log_div (by norm_num : (4 : ℝ) ≠ 0)
        (by norm_num : (3 : ℝ) ≠ 0),
      Real.log_div (by norm_num : (3 : ℝ) ≠ 0)
        (by norm_num : (4 : ℝ) ≠ 0)]
    ring
  unfold dilationBlockH endpointDefect
  rw [hdilation, unresolvedMass_three_four_ratio hh hm hq]
  rw [Real.log_div
      (mul_pos (by positivity : (0 : ℝ) < (3 / 4 : ℝ) ^ 2)
        (div_pos hz3 hz4)).ne' hs.ne',
    Real.log_mul (by positivity : (3 / 4 : ℝ) ^ 2 ≠ 0)
      (div_pos hz3 hz4).ne',
    Real.log_pow, Real.log_div hz3.ne' hz4.ne',
    Real.log_div (mul_pos hs hz4).ne' hr30.ne',
    Real.log_mul hs.ne' hz4.ne']
  unfold tailR30
  rw [Real.log_rpow (by norm_num : (0 : ℝ) < 3 / 4), hlogInverse]
  ring

end

end GDLowerBound.FourBlock
