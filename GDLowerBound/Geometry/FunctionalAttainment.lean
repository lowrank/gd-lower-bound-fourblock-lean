import GDLowerBound.FunctionalReduction
import GDLowerBound.Geometry.GeometricRealization

namespace GDLowerBound

open Schedule

/-- Corollary `cor:functional-attainment`: a maximizing chronological chain
is realized by a normalized smooth convex objective in at most `T+1`
dimensions. -/
theorem functionalAttainment : FunctionalAttainment := by
  intro T h hh
  obtain ⟨c, hc⟩ := exists_maximizingChain h
  obtain ⟨F, x, hmin, hx, htraj, hvalue⟩ :=
    GeometricRealization.chainValueRealization c hh
  refine ⟨c.length + 1, by omega,
    GeometricRealization.block_dimension_le_horizon c,
    F, x, htraj, ?_, ?_⟩
  · rw [hmin, sub_zero]
    exact hx
  · rw [hmin, hvalue, hc]
    ring

end GDLowerBound
