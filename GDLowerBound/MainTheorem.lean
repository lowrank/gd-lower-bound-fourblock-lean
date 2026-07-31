import GDLowerBound.Basic
import GDLowerBound.Optimization.GradientDescent
import Mathlib.Analysis.InnerProductSpace.PiL2

namespace GDLowerBound

open scoped Real

/-- The finite-horizon conclusion for a fixed exponent and constant. -/
def MainClaim (p c : ℝ) : Prop :=
  ∀ (T : ℕ), 1 ≤ T →
  ∀ (L R : ℝ), 0 < L → 0 < R →
  ∀ η : Fin T → ℝ, IsNonnegativeSchedule η →
    ∃ d : ℕ, 1 ≤ d ∧ d ≤ T + 1 ∧
      ∃ F : SmoothConvexFn (EuclideanSpace ℝ (Fin d)) L,
      ∃ x : Fin (T + 1) → EuclideanSpace ℝ (Fin d),
        IsGDTrajectory F.grad η x ∧
        ‖x 0 - F.minimizer‖ = R ∧
        F (x (Fin.last T)) - F F.minimizer ≥
          c * L * R ^ 2 * Real.rpow (T + 1 : ℝ) (-p)

/-- Exact formal specification of `thm:main` from the manuscript. -/
def mainStatement : Prop :=
  ∀ p : ℝ, pStar < p → p < 2 →
    ∃ c : ℝ, 0 < c ∧ MainClaim p c

end GDLowerBound
