import GDLowerBound.Optimization.GradientDescent
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.InnerProductSpace.Dual

namespace GDLowerBound

open scoped InnerProductSpace

namespace SmoothConvexFn

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Spatial scaling map used to restore the initial radius. -/
def spatialScale (a : ℝ) : E →L[ℝ] E :=
  a • ContinuousLinearMap.id ℝ E

@[simp]
theorem spatialScale_apply (a : ℝ) (x : E) : spatialScale a x = a • x := by
  rfl

section Complete

variable [CompleteSpace E]

theorem toDual_comp_spatialScale (a : ℝ) (g : E) :
    ((InnerProductSpace.toDual ℝ E) g).comp (spatialScale a) =
      (InnerProductSpace.toDual ℝ E) (a • g) := by
  ext x
  simp [spatialScale, InnerProductSpace.toDual_apply_apply]

/-- Restore smoothness `L` and radius `R` by
`f(x)=L R² F(x/R)`. -/
noncomputable def scale (F : SmoothConvexFn E 1) (L R : ℝ)
    (hL : 0 < L) (hR : 0 < R) : SmoothConvexFn E L where
  toFun x := L * R ^ 2 * F (R⁻¹ • x)
  grad x := (L * R) • F.grad (R⁻¹ • x)
  convex := by
    refine ⟨convex_univ, ?_⟩
    intro x _ y _ a b ha hb hab
    have hconv := F.convex.2
      (x := R⁻¹ • x) (y := R⁻¹ • y)
      (Set.mem_univ _) (Set.mem_univ _) ha hb hab
    have hscale : 0 ≤ L * R ^ 2 := by positivity
    have hinput : R⁻¹ • (a • x + b • y) =
        a • (R⁻¹ • x) + b • (R⁻¹ • y) := by
      module
    change L * R ^ 2 * F (R⁻¹ • (a • x + b • y)) ≤
      a • (L * R ^ 2 * F (R⁻¹ • x)) +
        b • (L * R ^ 2 * F (R⁻¹ • y))
    rw [hinput]
    calc
      L * R ^ 2 * F (a • (R⁻¹ • x) + b • (R⁻¹ • y)) ≤
          L * R ^ 2 * (a • F (R⁻¹ • x) + b • F (R⁻¹ • y)) :=
        mul_le_mul_of_nonneg_left hconv hscale
      _ = a • (L * R ^ 2 * F (R⁻¹ • x)) +
          b • (L * R ^ 2 * F (R⁻¹ • y)) := by
        simp only [smul_eq_mul]
        ring
  hasGradient := by
    intro x
    have hinner := (F.hasGradient (R⁻¹ • x)).hasFDerivAt
    have hcomp := hinner.comp x (spatialScale R⁻¹).hasFDerivAt
    have hscaled := hcomp.const_smul (L * R ^ 2)
    change HasFDerivAt
      (fun z : E ↦ L * R ^ 2 * F (R⁻¹ • z))
      (((L * R ^ 2) • (InnerProductSpace.toDual ℝ E)
        (F.grad (R⁻¹ • x))).comp (spatialScale R⁻¹)) x at hscaled
    have hderiv :
        (((L * R ^ 2) • (InnerProductSpace.toDual ℝ E)
          (F.grad (R⁻¹ • x))).comp (spatialScale R⁻¹)) =
        (InnerProductSpace.toDual ℝ E)
          ((L * R) • F.grad (R⁻¹ • x)) := by
      ext z
      change (L * R ^ 2) * ⟪F.grad (R⁻¹ • x), R⁻¹ • z⟫_ℝ =
        ⟪(L * R) • F.grad (R⁻¹ • x), z⟫_ℝ
      rw [inner_smul_right, inner_smul_left]
      field_simp [hR.ne']
      simp
      ring
    rw [hasGradientAt_iff_hasFDerivAt]
    rw [← hderiv]
    exact hscaled
  grad_lipschitz := by
    intro x y
    have hbase := F.grad_lipschitz (R⁻¹ • x) (R⁻¹ • y)
    have hLR : 0 ≤ L * R := by positivity
    calc
      ‖(L * R) • F.grad (R⁻¹ • x) -
          (L * R) • F.grad (R⁻¹ • y)‖ =
          (L * R) * ‖F.grad (R⁻¹ • x) - F.grad (R⁻¹ • y)‖ := by
        rw [← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_nonneg hLR]
      _ ≤ (L * R) * ‖R⁻¹ • x - R⁻¹ • y‖ := by
        have : ‖F.grad (R⁻¹ • x) - F.grad (R⁻¹ • y)‖ ≤
            ‖R⁻¹ • x - R⁻¹ • y‖ := by simpa using hbase
        exact mul_le_mul_of_nonneg_left this hLR
      _ = L * ‖x - y‖ := by
        rw [← smul_sub, norm_smul, Real.norm_eq_abs,
          abs_of_pos (inv_pos.mpr hR)]
        field_simp [hR.ne']
  minimizer := R • F.minimizer
  minimizes := by
    intro x
    have hmin := F.minimizes (R⁻¹ • x)
    have hscale : 0 ≤ L * R ^ 2 := by positivity
    have := mul_le_mul_of_nonneg_left hmin hscale
    simpa [smul_smul, hR.ne'] using this

@[simp]
theorem scale_apply (F : SmoothConvexFn E 1) (L R : ℝ)
    (hL : 0 < L) (hR : 0 < R) (x : E) :
    F.scale L R hL hR x = L * R ^ 2 * F (R⁻¹ • x) := rfl

@[simp]
theorem scale_grad (F : SmoothConvexFn E 1) (L R : ℝ)
    (hL : 0 < L) (hR : 0 < R) (x : E) :
    (F.scale L R hL hR).grad x = (L * R) • F.grad (R⁻¹ • x) := rfl

@[simp]
theorem scale_minimizer (F : SmoothConvexFn E 1) (L R : ℝ)
    (hL : 0 < L) (hR : 0 < R) :
    (F.scale L R hL hR).minimizer = R • F.minimizer := rfl

theorem scale_gap (F : SmoothConvexFn E 1) (L R : ℝ)
    (hL : 0 < L) (hR : 0 < R) (x y : E) :
    F.scale L R hL hR (R • x) - F.scale L R hL hR (R • y) =
      L * R ^ 2 * (F x - F y) := by
  simp [smul_smul, hR.ne']
  ring

end Complete

theorem scale_distance (R : ℝ) (hR : 0 < R) (x y : E) :
    ‖R • x - R • y‖ = R * ‖x - y‖ := by
  rw [← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_pos hR]

end SmoothConvexFn

/-- Scaling a normalized GD trajectory yields the trajectory for the
original step sizes. -/
theorem scale_gd_trajectory
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] {T : ℕ}
    (F : SmoothConvexFn E 1) (L R : ℝ) (hL : 0 < L) (hR : 0 < R)
    (eta : Fin T → ℝ) (xbar : Fin (T + 1) → E)
    (htraj : IsGDTrajectory F.grad (λ t ↦ L * eta t) xbar) :
    IsGDTrajectory (F.scale L R hL hR).grad eta (λ t ↦ R • xbar t) := by
  intro t
  change R • xbar t.succ =
    R • xbar t.castSucc - eta t •
      (F.scale L R hL hR).grad (R • xbar t.castSucc)
  rw [htraj t]
  simp only [SmoothConvexFn.scale_grad]
  have hcancel : R⁻¹ • (R • xbar t.castSucc) = xbar t.castSucc := by
    simp [smul_smul, hR.ne']
  rw [hcancel]
  module

end GDLowerBound
