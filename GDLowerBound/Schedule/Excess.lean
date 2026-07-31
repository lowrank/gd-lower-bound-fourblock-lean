import GDLowerBound.Optimization.GradientDescent
import Mathlib.Algebra.Order.BigOperators.Group.Finset

namespace GDLowerBound.Schedule

open scoped BigOperators

/-- A finite predetermined schedule. -/
abbrev StepSchedule (T : ℕ) := Fin T → ℝ

/-- The part of a normalized step that exceeds one. -/
def excess {T : ℕ} (h : StepSchedule T) (t : Fin T) : ℝ :=
  max (h t - 1) 0

/-- The part of a normalized step capped at one. -/
def capped {T : ℕ} (h : StepSchedule T) (t : Fin T) : ℝ :=
  min (h t) 1

/-- One plus the total capped schedule mass. -/
def cappedMass {T : ℕ} (h : StepSchedule T) : ℝ :=
  1 + ∑ t, capped h t

/-- Time indices carrying a strictly positive excess. -/
noncomputable def longTimes {T : ℕ} (h : StepSchedule T) : Finset (Fin T) :=
  Finset.univ.filter fun t => 1 < h t

/-- Number of steps carrying a positive excess. -/
noncomputable def longCount {T : ℕ} (h : StepSchedule T) : ℕ :=
  (longTimes h).card

theorem excess_nonneg {T : ℕ} (h : StepSchedule T) (t : Fin T) :
    0 ≤ excess h t :=
  le_max_right _ _

theorem excess_pos_iff {T : ℕ} (h : StepSchedule T) (t : Fin T) :
    0 < excess h t ↔ 1 < h t := by
  simp [excess]

theorem mem_longTimes_iff {T : ℕ} (h : StepSchedule T) (t : Fin T) :
    t ∈ longTimes h ↔ 1 < h t := by
  simp [longTimes]

theorem capped_nonneg {T : ℕ} {h : StepSchedule T}
    (hh : IsNonnegativeSchedule h) (t : Fin T) :
    0 ≤ capped h t := by
  exact le_min (hh t) zero_le_one

theorem capped_le_one {T : ℕ} (h : StepSchedule T) (t : Fin T) :
    capped h t ≤ 1 :=
  min_le_right _ _

theorem step_decomposition {T : ℕ} (h : StepSchedule T) (t : Fin T) :
    capped h t + excess h t = h t := by
  by_cases ht : h t ≤ 1
  · simp [capped, excess, ht, sub_nonpos.mpr ht]
  · have h1 : 1 ≤ h t := le_of_not_ge ht
    simp [capped, excess, h1, sub_nonneg.mpr h1]

theorem cappedMass_pos {T : ℕ} {h : StepSchedule T}
    (hh : IsNonnegativeSchedule h) :
    0 < cappedMass h := by
  have hs : 0 ≤ ∑ t, capped h t :=
    Finset.sum_nonneg fun t _ => capped_nonneg hh t
  unfold cappedMass
  linarith

theorem cappedMass_le_horizon {T : ℕ} (h : StepSchedule T) :
    cappedMass h ≤ T + 1 := by
  calc
    cappedMass h = 1 + ∑ t, capped h t := rfl
    _ ≤ 1 + ∑ _t : Fin T, (1 : ℝ) := by
      gcongr with t
      exact capped_le_one h t
    _ = T + 1 := by norm_num [add_comm]

theorem longCount_le_horizon {T : ℕ} (h : StepSchedule T) :
    longCount h ≤ T := by
  simpa [longCount] using (longTimes h).card_le_univ

theorem total_mass_decomposition {T : ℕ} (h : StepSchedule T) :
    1 + ∑ t, h t = cappedMass h + ∑ t, excess h t := by
  calc
    1 + ∑ t, h t = 1 + ∑ t, (capped h t + excess h t) := by
      congr 1
      apply Finset.sum_congr rfl
      intro t _
      exact (step_decomposition h t).symm
    _ = cappedMass h + ∑ t, excess h t := by
      rw [Finset.sum_add_distrib]
      simp [cappedMass, add_assoc]

end GDLowerBound.Schedule
