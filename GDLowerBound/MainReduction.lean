import GDLowerBound.MainTheorem
import GDLowerBound.Scaling

namespace GDLowerBound

open scoped Real

/-- Unit-smooth, unit-radius form of the finite-horizon lower-bound claim.
This is the interface between the schedule analysis/geometric realization
and the final scaling argument. -/
def NormalizedClaim (p c : ℝ) : Prop :=
  ∀ (T : ℕ), 1 ≤ T →
  ∀ h : Fin T → ℝ, IsNonnegativeSchedule h →
    ∃ d : ℕ, 1 ≤ d ∧ d ≤ T + 1 ∧
      ∃ F : SmoothConvexFn (EuclideanSpace ℝ (Fin d)) 1,
      ∃ x : Fin (T + 1) → EuclideanSpace ℝ (Fin d),
        IsGDTrajectory F.grad h x ∧
        ‖x 0 - F.minimizer‖ = 1 ∧
        F (x (Fin.last T)) - F F.minimizer ≥
          c * Real.rpow ((T : ℝ) + 1) (-p)

/-- Restoring `L` and `R` turns a normalized witness into the exact witness
required by `MainClaim`, without changing its dimension. -/
theorem normalizedClaim_to_mainClaim {p c : ℝ}
    (hnormalized : NormalizedClaim p c) : MainClaim p c := by
  intro T hT L R hL hR eta heta
  let h : Fin T → ℝ := fun t ↦ L * eta t
  have hh : IsNonnegativeSchedule h := by
    intro t
    exact mul_nonneg hL.le (heta t)
  obtain ⟨d, hd₀, hdT, F, xbar, htraj, hdist, hgap⟩ :=
    hnormalized T hT h hh
  let f : SmoothConvexFn (EuclideanSpace ℝ (Fin d)) L :=
    F.scale L R hL hR
  let x : Fin (T + 1) → EuclideanSpace ℝ (Fin d) := fun t ↦ R • xbar t
  refine ⟨d, hd₀, hdT, f, x, ?_, ?_, ?_⟩
  · exact scale_gd_trajectory F L R hL hR eta xbar htraj
  · change ‖R • xbar 0 - (F.scale L R hL hR).minimizer‖ = R
    rw [SmoothConvexFn.scale_minimizer]
    rw [SmoothConvexFn.scale_distance R hR]
    rw [hdist, mul_one]
  · change F.scale L R hL hR (R • xbar (Fin.last T)) -
        F.scale L R hL hR (F.scale L R hL hR).minimizer ≥
      c * L * R ^ 2 * Real.rpow ((T : ℝ) + 1) (-p)
    rw [SmoothConvexFn.scale_minimizer]
    rw [SmoothConvexFn.scale_gap]
    have hscale : 0 ≤ L * R ^ 2 := by positivity
    calc
      L * R ^ 2 * (F (xbar (Fin.last T)) - F F.minimizer) ≥
          L * R ^ 2 *
            (c * Real.rpow ((T : ℝ) + 1) (-p)) :=
        mul_le_mul_of_nonneg_left hgap hscale
      _ = c * L * R ^ 2 * Real.rpow ((T : ℝ) + 1) (-p) := by ring

end GDLowerBound
