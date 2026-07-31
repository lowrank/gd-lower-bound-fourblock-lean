import GDLowerBound.FunctionalReduction
import GDLowerBound.RankAnalysis.Horizon

namespace GDLowerBound.RankAnalysis

open scoped Real
open Schedule

/-- The schedule-independent normalized estimate proved by the rank scan,
before replacing `B` and `r` by the horizon. -/
def NormalizedScheduleFloor (p c : ℝ) : Prop :=
  ∀ (T : ℕ), ∀ h : StepSchedule T, IsNonnegativeSchedule h →
    c / (cappedMass h *
      Real.rpow ((longCount h : ℝ) + 1) (p - 1)) ≤
      lowerBoundFunctional h

/-- The normalized rank estimate implies the horizon-rate functional floor.
The output constant is halved because geometric attainment identifies the
functional with twice the objective gap. -/
theorem functionalFloor_of_normalizedScheduleFloor
    {p c : ℝ} (hp : 1 ≤ p) (hc : 0 ≤ c)
    (hfloor : NormalizedScheduleFloor p c) :
    FunctionalFloor p (c / 2) := by
  intro T _hT h hh
  have hrate := scheduleFloor_to_horizon hp hc hh (hfloor T h hh)
  have hconstant : 2 * (c / 2) = c := by ring
  rw [hconstant]
  exact hrate

/-- The remaining analytic target after all geometric and scaling reductions.
It is exactly Proposition `prop:normalized-floor` with the theorem's exponent
range and positive constant made explicit. -/
def NormalizedFloorTheorem : Prop :=
  ∀ p : ℝ, pStar < p → p < 2 →
    ∃ c : ℝ, 0 < c ∧ NormalizedScheduleFloor p c

/-- Once normalized rank analysis and functional attainment are available,
the exact main statement follows. -/
theorem mainStatement_of_normalizedFloor
    (hattain : FunctionalAttainment)
    (hnormalized : NormalizedFloorTheorem) : mainStatement := by
  intro p hp hp_two
  obtain ⟨c, hc, hfloor⟩ := hnormalized p hp hp_two
  refine ⟨c / 2, by positivity, ?_⟩
  apply mainClaim_of_functional hattain
  exact functionalFloor_of_normalizedScheduleFloor
    (le_of_lt (one_lt_pStar.trans hp)) hc.le hfloor

end GDLowerBound.RankAnalysis
