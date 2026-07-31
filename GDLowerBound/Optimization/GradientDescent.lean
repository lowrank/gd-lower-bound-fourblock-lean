import GDLowerBound.Optimization.SmoothConvex

namespace GDLowerBound

/-- A nonnegative predetermined schedule of length `T`. -/
def IsNonnegativeSchedule {T : ℕ} (η : Fin T → ℝ) : Prop :=
  ∀ t, 0 ≤ η t

/-- The graph of `T` gradient-descent updates. -/
def IsGDTrajectory
    {E : Type*} [NormedAddCommGroup E] [SMul ℝ E]
    {T : ℕ} (grad : E → E) (η : Fin T → ℝ)
    (x : Fin (T + 1) → E) : Prop :=
  ∀ t : Fin T,
    x t.succ = x t.castSucc - η t • grad (x t.castSucc)

end GDLowerBound
