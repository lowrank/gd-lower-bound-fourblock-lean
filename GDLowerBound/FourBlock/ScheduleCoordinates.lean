import GDLowerBound.FourBlock.ScheduleEnergy

/-! # Exact reciprocal-prefix coordinates at ranks `2m,3m,4m` -/

namespace GDLowerBound.FourBlock

open scoped BigOperators
open GDLowerBound.Schedule GDLowerBound.RankAnalysis

noncomputable section

def schedulePrefixR {T : ℕ} (h : StepSchedule T) (m : ℕ) : ℝ :=
  reciprocalPrefix h (2 * m) / reciprocalPrefix h (4 * m)

def schedulePrefixS {T : ℕ} (h : StepSchedule T) (m : ℕ) : ℝ :=
  reciprocalPrefix h (3 * m) / reciprocalPrefix h (4 * m)

theorem reciprocalPrefix_pos_of_rank
    {T q : ℕ} {h : StepSchedule T} (hq0 : 1 ≤ q)
    (hqr : q ≤ longCount h) :
    0 < reciprocalPrefix h q := by
  unfold reciprocalPrefix
  apply Finset.sum_pos
  · intro i hi
    have hiq : i < q := Finset.mem_range.mp hi
    exact inv_pos.mpr (rankedExcessOne_pos h (q := i + 1)
      (by omega) (by omega))
  · exact ⟨0, Finset.mem_range.mpr (by omega)⟩

theorem schedulePrefixR_pos
    {T m : ℕ} {h : StepSchedule T} (hm : 0 < m)
    (hq : 4 * m ≤ longCount h) :
    0 < schedulePrefixR h m := by
  unfold schedulePrefixR
  exact div_pos
    (reciprocalPrefix_pos_of_rank (by omega) (by omega))
    (reciprocalPrefix_pos_of_rank (by omega) hq)

theorem schedulePrefixS_pos
    {T m : ℕ} {h : StepSchedule T} (hm : 0 < m)
    (hq : 4 * m ≤ longCount h) :
    0 < schedulePrefixS h m := by
  unfold schedulePrefixS
  exact div_pos
    (reciprocalPrefix_pos_of_rank (by omega) (by omega))
    (reciprocalPrefix_pos_of_rank (by omega) hq)

/-- Exact `2m`-to-`4m` mass ratio in reciprocal-prefix coordinates. -/
theorem unresolvedMass_two_four_ratio
    {T m : ℕ} {h : StepSchedule T} (hh : IsNonnegativeSchedule h)
    (hm : 0 < m) (hq : 4 * m ≤ longCount h) :
    unresolvedMass h (2 * m) / unresolvedMass h (4 * m) =
      (1 / 2 : ℝ) ^ 2 *
        (zetaState h (2 * m) / zetaState h (4 * m)) /
          schedulePrefixR h m := by
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  have hD2 := (unresolvedMass_pos hh (2 * m)).ne'
  have hD4 := (unresolvedMass_pos hh (4 * m)).ne'
  have hP2 := (reciprocalPrefix_pos_of_rank
    (h := h) (q := 2 * m) (by omega) (by omega)).ne'
  have hP4 := (reciprocalPrefix_pos_of_rank
    (h := h) (q := 4 * m) (by omega) hq).ne'
  unfold schedulePrefixR zetaState
  norm_num [Nat.cast_mul]
  field_simp [hm0, hD2, hD4, hP2, hP4]
  ring

/-- Exact `3m`-to-`4m` mass ratio in reciprocal-prefix coordinates. -/
theorem unresolvedMass_three_four_ratio
    {T m : ℕ} {h : StepSchedule T} (hh : IsNonnegativeSchedule h)
    (hm : 0 < m) (hq : 4 * m ≤ longCount h) :
    unresolvedMass h (3 * m) / unresolvedMass h (4 * m) =
      (3 / 4 : ℝ) ^ 2 *
        (zetaState h (3 * m) / zetaState h (4 * m)) /
          schedulePrefixS h m := by
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  have hD3 := (unresolvedMass_pos hh (3 * m)).ne'
  have hD4 := (unresolvedMass_pos hh (4 * m)).ne'
  have hP3 := (reciprocalPrefix_pos_of_rank
    (h := h) (q := 3 * m) (by omega) (by omega)).ne'
  have hP4 := (reciprocalPrefix_pos_of_rank
    (h := h) (q := 4 * m) (by omega) hq).ne'
  unfold schedulePrefixS zetaState
  norm_num [Nat.cast_mul]
  field_simp [hm0, hD3, hD4, hP3, hP4]
  ring

end

end GDLowerBound.FourBlock
