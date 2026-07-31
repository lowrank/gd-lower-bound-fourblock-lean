import GDLowerBound.MainReduction
import GDLowerBound.Schedule.Functional

namespace GDLowerBound

open scoped Real

/-- Abstract interface supplied by the geometric construction: the schedule
functional is attained, up to the factor two in the objective gap, by a
unit-radius normalized GD instance. -/
def FunctionalAttainment : Prop :=
  ∀ (T : ℕ), ∀ h : Schedule.StepSchedule T,
    IsNonnegativeSchedule h →
    ∃ d : ℕ, 1 ≤ d ∧ d ≤ T + 1 ∧
      ∃ F : SmoothConvexFn (EuclideanSpace ℝ (Fin d)) 1,
      ∃ x : Fin (T + 1) → EuclideanSpace ℝ (Fin d),
        IsGDTrajectory F.grad h x ∧
        ‖x 0 - F.minimizer‖ = 1 ∧
        2 * (F (x (Fin.last T)) - F F.minimizer) =
          Schedule.lowerBoundFunctional h

/-- A horizon-rate lower bound stated directly for the schedule functional.
The factor two matches `FunctionalAttainment`. -/
def FunctionalFloor (p c : ℝ) : Prop :=
  ∀ (T : ℕ), 1 ≤ T →
  ∀ h : Schedule.StepSchedule T, IsNonnegativeSchedule h →
    2 * c * Real.rpow ((T : ℝ) + 1) (-p) ≤
      Schedule.lowerBoundFunctional h

/-- Functional attainment and a functional floor together imply the
normalized lower-bound claim. -/
theorem normalizedClaim_of_functional
    {p c : ℝ} (hattain : FunctionalAttainment)
    (hfloor : FunctionalFloor p c) : NormalizedClaim p c := by
  intro T hT h hh
  obtain ⟨d, hd₀, hdT, F, x, htraj, hdist, hvalue⟩ :=
    hattain T h hh
  refine ⟨d, hd₀, hdT, F, x, htraj, hdist, ?_⟩
  have hlower := hfloor T hT h hh
  linarith

/-- End-to-end reduction after the normalized schedule analysis and
geometric construction have been supplied. -/
theorem mainClaim_of_functional {p c : ℝ}
    (hattain : FunctionalAttainment) (hfloor : FunctionalFloor p c) :
    MainClaim p c :=
  normalizedClaim_to_mainClaim
    (normalizedClaim_of_functional hattain hfloor)

end GDLowerBound
