import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Convex.Basic

namespace GDLowerBound

/-- A differentiable convex objective together with its explicitly identified
gradient and a chosen minimizer.  Keeping the gradient as data makes the GD
recursion independent of implementation details of `gradient`. -/
structure SmoothConvexFn
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E]
    (L : ℝ) where
  toFun : E → ℝ
  grad : E → E
  convex : ConvexOn ℝ Set.univ toFun
  hasGradient : ∀ x, HasGradientAt toFun (grad x) x
  grad_lipschitz : ∀ x y, ‖grad x - grad y‖ ≤ L * ‖x - y‖
  minimizer : E
  minimizes : ∀ x, toFun minimizer ≤ toFun x

namespace SmoothConvexFn

instance
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E]
    {L : ℝ} : CoeFun (SmoothConvexFn E L) (fun _ => E → ℝ) :=
  ⟨SmoothConvexFn.toFun⟩

theorem minimizer_mem_argmin
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E]
    {L : ℝ} (F : SmoothConvexFn E L) :
    ∀ x, F F.minimizer ≤ F x :=
  F.minimizes

end SmoothConvexFn

end GDLowerBound
