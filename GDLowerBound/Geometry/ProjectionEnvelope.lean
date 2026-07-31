import GDLowerBound.Geometry.ConvexProjection
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Convex.Function
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Tactic

/-!
# Projection envelope

For a nonempty complete convex set `K`, this file formalizes the dual representation

`F x = max (g ∈ K) (⟨g, x⟩ - ‖g‖² / 2)`.

The chosen maximizer is the metric projection of `x` onto `K`.  This is the form of the
Moreau envelope of the support function used in the geometric realization proof.
-/

open scoped InnerProductSpace
open Set Filter Topology

namespace GDLowerBound

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The affine-in-`x` quadratic support expression. -/
noncomputable def quadraticSupport (g x : E) : ℝ := ⟪g, x⟫_ℝ - ‖g‖ ^ 2 / 2

/-- The projection envelope, defined using its unique maximizing point. -/
noncomputable def projectionEnvelope (K : Set E) (hne : K.Nonempty)
    (hcomplete : IsComplete K) (hconvex : Convex ℝ K) (x : E) : ℝ :=
  quadraticSupport (convexProj K hne hcomplete hconvex x) x

theorem quadraticSupport_add (g x h : E) :
    quadraticSupport g (x + h) = quadraticSupport g x + ⟪g, h⟫_ℝ := by
  simp only [quadraticSupport, inner_add_right]
  ring

theorem quadraticSupport_combo (g x y : E) {a b : ℝ} (hab : a + b = 1) :
    quadraticSupport g (a • x + b • y) =
      a * quadraticSupport g x + b * quadraticSupport g y := by
  simp only [quadraticSupport, inner_add_right, inner_smul_right]
  linear_combination (‖g‖ ^ 2 / 2) * hab

/-- Every point of `K` gives a lower support value than the projection.  Thus the projection
really realizes the maximum in the dual formula. -/
theorem quadraticSupport_le_projectionEnvelope (K : Set E) (hne : K.Nonempty)
    (hcomplete : IsComplete K) (hconvex : Convex ℝ K) (x g : E) (hg : g ∈ K) :
    quadraticSupport g x ≤ projectionEnvelope K hne hcomplete hconvex x := by
  let p := convexProj K hne hcomplete hconvex x
  let d := g - p
  have hvi := convexProj_vi K hne hcomplete hconvex x g hg
  change ⟪x - p, d⟫_ℝ ≤ 0 at hvi
  change ⟪g, x⟫_ℝ - ‖g‖ ^ 2 / 2 ≤ ⟪p, x⟫_ℝ - ‖p‖ ^ 2 / 2
  rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq]
  rw [show g = p + d by simp [d]]
  simp only [inner_add_left, inner_add_right]
  have hdx : ⟪d, x⟫_ℝ = ⟪x, d⟫_ℝ := real_inner_comm _ _
  have hdp : ⟪d, p⟫_ℝ = ⟪p, d⟫_ℝ := real_inner_comm _ _
  rw [hdx, hdp]
  simp only [inner_sub_left] at hvi
  have hd : 0 ≤ ⟪d, d⟫_ℝ := real_inner_self_nonneg
  linarith

/-- The projection envelope is convex, as follows directly from its pointwise-maximum
representation. -/
theorem projectionEnvelope_convex (K : Set E) (hne : K.Nonempty)
    (hcomplete : IsComplete K) (hconvex : Convex ℝ K) :
    ConvexOn ℝ Set.univ (projectionEnvelope K hne hcomplete hconvex) := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb hab
  let z := a • x + b • y
  let p := convexProj K hne hcomplete hconvex z
  have hp_mem : p ∈ K := convexProj_mem K hne hcomplete hconvex z
  have hx := quadraticSupport_le_projectionEnvelope K hne hcomplete hconvex x p hp_mem
  have hy := quadraticSupport_le_projectionEnvelope K hne hcomplete hconvex y p hp_mem
  change projectionEnvelope K hne hcomplete hconvex z ≤
    a • projectionEnvelope K hne hcomplete hconvex x +
      b • projectionEnvelope K hne hcomplete hconvex y
  change quadraticSupport p z ≤
    a • projectionEnvelope K hne hcomplete hconvex x +
      b • projectionEnvelope K hne hcomplete hconvex y
  rw [quadraticSupport_combo p x y hab]
  simp only [smul_eq_mul]
  exact add_le_add (mul_le_mul_of_nonneg_left hx ha)
    (mul_le_mul_of_nonneg_left hy hb)

/-- Completing the square gives the projection-distance value formula. -/
theorem projectionEnvelope_eq_norm_sub_proj (K : Set E) (hne : K.Nonempty)
    (hcomplete : IsComplete K) (hconvex : Convex ℝ K) (x : E) :
    projectionEnvelope K hne hcomplete hconvex x =
      ‖x‖ ^ 2 / 2 - ‖x - convexProj K hne hcomplete hconvex x‖ ^ 2 / 2 := by
  let p := convexProj K hne hcomplete hconvex x
  change ⟪p, x⟫_ℝ - ‖p‖ ^ 2 / 2 = ‖x‖ ^ 2 / 2 - ‖x - p‖ ^ 2 / 2
  rw [@norm_sub_sq ℝ]
  have hcomm : ⟪x, p⟫_ℝ = ⟪p, x⟫_ℝ := real_inner_comm _ _
  rw [hcomm]
  simp only [RCLike.re_to_real]
  ring

theorem norm_sub_convexProj_eq_infDist (K : Set E) (hne : K.Nonempty)
    (hcomplete : IsComplete K) (hconvex : Convex ℝ K) (x : E) :
    ‖x - convexProj K hne hcomplete hconvex x‖ = Metric.infDist x K := by
  rw [convexProj_norm_eq_iInf]
  rw [Metric.infDist_eq_iInf]
  congr 1
  funext y
  rw [dist_eq_norm]

/-- The explicit value formula from the Moreau-envelope projection lemma. -/
theorem projectionEnvelope_value (K : Set E) (hne : K.Nonempty)
    (hcomplete : IsComplete K) (hconvex : Convex ℝ K) (x : E) :
    projectionEnvelope K hne hcomplete hconvex x =
      ‖x‖ ^ 2 / 2 - Metric.infDist x K ^ 2 / 2 := by
  rw [projectionEnvelope_eq_norm_sub_proj]
  rw [norm_sub_convexProj_eq_infDist]

/-- Lower half of the two-sided increment estimate used to identify the gradient. -/
theorem inner_convexProj_le_projectionEnvelope_increment (K : Set E)
    (hne : K.Nonempty) (hcomplete : IsComplete K) (hconvex : Convex ℝ K)
    (x h : E) :
    ⟪convexProj K hne hcomplete hconvex x, h⟫_ℝ ≤
      projectionEnvelope K hne hcomplete hconvex (x + h) -
        projectionEnvelope K hne hcomplete hconvex x := by
  let p := convexProj K hne hcomplete hconvex x
  have hp_mem : p ∈ K := convexProj_mem K hne hcomplete hconvex x
  have hmax := quadraticSupport_le_projectionEnvelope K hne hcomplete hconvex
    (x + h) p hp_mem
  change ⟪p, h⟫_ℝ ≤ projectionEnvelope K hne hcomplete hconvex (x + h) -
    quadraticSupport p x
  rw [le_sub_iff_add_le]
  rw [add_comm, ← quadraticSupport_add]
  exact hmax

/-- Upper half of the two-sided increment estimate used to identify the gradient. -/
theorem projectionEnvelope_increment_le_inner_convexProj (K : Set E)
    (hne : K.Nonempty) (hcomplete : IsComplete K) (hconvex : Convex ℝ K)
    (x h : E) :
    projectionEnvelope K hne hcomplete hconvex (x + h) -
        projectionEnvelope K hne hcomplete hconvex x ≤
      ⟪convexProj K hne hcomplete hconvex (x + h), h⟫_ℝ := by
  let q := convexProj K hne hcomplete hconvex (x + h)
  have hq_mem : q ∈ K := convexProj_mem K hne hcomplete hconvex (x + h)
  have hmax := quadraticSupport_le_projectionEnvelope K hne hcomplete hconvex x q hq_mem
  change quadraticSupport q (x + h) - projectionEnvelope K hne hcomplete hconvex x ≤
    ⟪q, h⟫_ℝ
  rw [quadraticSupport_add]
  exact sub_le_iff_le_add.mpr (by simpa [add_comm] using hmax)

theorem projectionEnvelope_remainder_nonneg (K : Set E) (hne : K.Nonempty)
    (hcomplete : IsComplete K) (hconvex : Convex ℝ K) (x h : E) :
    0 ≤ projectionEnvelope K hne hcomplete hconvex (x + h) -
      projectionEnvelope K hne hcomplete hconvex x -
        ⟪convexProj K hne hcomplete hconvex x, h⟫_ℝ := by
  linarith [inner_convexProj_le_projectionEnvelope_increment K hne hcomplete hconvex x h]

/-- The first-order remainder is quadratically small. -/
theorem projectionEnvelope_remainder_le_sq (K : Set E) (hne : K.Nonempty)
    (hcomplete : IsComplete K) (hconvex : Convex ℝ K) (x h : E) :
    projectionEnvelope K hne hcomplete hconvex (x + h) -
        projectionEnvelope K hne hcomplete hconvex x -
          ⟪convexProj K hne hcomplete hconvex x, h⟫_ℝ ≤
      ‖h‖ * ‖h‖ := by
  let p := convexProj K hne hcomplete hconvex x
  let q := convexProj K hne hcomplete hconvex (x + h)
  have hu := projectionEnvelope_increment_le_inner_convexProj K hne hcomplete hconvex x h
  have hinner : ⟪q - p, h⟫_ℝ ≤ ‖q - p‖ * ‖h‖ := real_inner_le_norm _ _
  have hproj := convexProj_nonexpansive K hne hcomplete hconvex (x + h) x
  have hnorm : ‖q - p‖ ≤ ‖h‖ := by
    simpa [p, q] using hproj
  change projectionEnvelope K hne hcomplete hconvex (x + h) -
      projectionEnvelope K hne hcomplete hconvex x - ⟪p, h⟫_ℝ ≤ ‖h‖ * ‖h‖
  calc
    _ ≤ ⟪q - p, h⟫_ℝ := by
      simp only [inner_sub_left]
      linarith
    _ ≤ ‖q - p‖ * ‖h‖ := hinner
    _ ≤ ‖h‖ * ‖h‖ := mul_le_mul_of_nonneg_right hnorm (norm_nonneg h)

theorem norm_projectionEnvelope_remainder_le_sq (K : Set E) (hne : K.Nonempty)
    (hcomplete : IsComplete K) (hconvex : Convex ℝ K) (x h : E) :
    ‖projectionEnvelope K hne hcomplete hconvex (x + h) -
        projectionEnvelope K hne hcomplete hconvex x -
          ⟪convexProj K hne hcomplete hconvex x, h⟫_ℝ‖ ≤
      ‖h‖ * ‖h‖ := by
  rw [Real.norm_eq_abs,
    abs_of_nonneg (projectionEnvelope_remainder_nonneg K hne hcomplete hconvex x h)]
  exact projectionEnvelope_remainder_le_sq K hne hcomplete hconvex x h

section Complete

variable [CompleteSpace E]

/-- The projection is the Fréchet gradient of the envelope. -/
theorem hasGradientAt_projectionEnvelope (K : Set E) (hne : K.Nonempty)
    (hcomplete : IsComplete K) (hconvex : Convex ℝ K) (x : E) :
    HasGradientAt (projectionEnvelope K hne hcomplete hconvex)
      (convexProj K hne hcomplete hconvex x) x := by
  rw [hasGradientAt_iff_isLittleO_nhds_zero]
  apply Asymptotics.IsLittleO.of_bound
  intro c hc
  rw [Metric.eventually_nhds_iff]
  refine ⟨c, hc, ?_⟩
  intro h hh
  have hnorm : ‖h‖ < c := by simpa only [dist_zero_right] using hh
  calc
    ‖projectionEnvelope K hne hcomplete hconvex (x + h) -
        projectionEnvelope K hne hcomplete hconvex x -
          ⟪convexProj K hne hcomplete hconvex x, h⟫_ℝ‖ ≤
        ‖h‖ * ‖h‖ :=
      norm_projectionEnvelope_remainder_le_sq K hne hcomplete hconvex x h
    _ ≤ c * ‖h‖ :=
      mul_le_mul_of_nonneg_right (le_of_lt hnorm) (norm_nonneg h)

theorem gradient_projectionEnvelope (K : Set E) (hne : K.Nonempty)
    (hcomplete : IsComplete K) (hconvex : Convex ℝ K) (x : E) :
    gradient (projectionEnvelope K hne hcomplete hconvex) x =
      convexProj K hne hcomplete hconvex x :=
  (hasGradientAt_projectionEnvelope K hne hcomplete hconvex x).gradient

/-- The envelope has a `1`-Lipschitz gradient. -/
theorem gradient_projectionEnvelope_lipschitz (K : Set E) (hne : K.Nonempty)
    (hcomplete : IsComplete K) (hconvex : Convex ℝ K) :
    LipschitzWith 1 (gradient (projectionEnvelope K hne hcomplete hconvex)) := by
  have hfun : gradient (projectionEnvelope K hne hcomplete hconvex) =
      convexProj K hne hcomplete hconvex := by
    funext x
    exact gradient_projectionEnvelope K hne hcomplete hconvex x
  rw [hfun]
  exact convexProj_lipschitz K hne hcomplete hconvex

end Complete

/-- If `0 ∈ K`, its projection is itself. -/
theorem convexProj_zero (K : Set E) (hne : K.Nonempty) (hcomplete : IsComplete K)
    (hconvex : Convex ℝ K) (hzero : 0 ∈ K) :
    convexProj K hne hcomplete hconvex 0 = 0 := by
  symm
  apply eq_convexProj_of_mem_of_vi K hne hcomplete hconvex 0 0 hzero
  intro z hz
  simp

theorem projectionEnvelope_zero (K : Set E) (hne : K.Nonempty)
    (hcomplete : IsComplete K) (hconvex : Convex ℝ K) (hzero : 0 ∈ K) :
    projectionEnvelope K hne hcomplete hconvex 0 = 0 := by
  simp [projectionEnvelope, convexProj_zero K hne hcomplete hconvex hzero,
    quadraticSupport]

theorem projectionEnvelope_nonneg (K : Set E) (hne : K.Nonempty)
    (hcomplete : IsComplete K) (hconvex : Convex ℝ K) (hzero : 0 ∈ K)
    (x : E) : 0 ≤ projectionEnvelope K hne hcomplete hconvex x := by
  have hmax := quadraticSupport_le_projectionEnvelope K hne hcomplete hconvex x 0 hzero
  simpa [quadraticSupport] using hmax

/-- When the convex set contains the origin, the envelope has value zero and is globally
minimized there. -/
theorem projectionEnvelope_isMinOn_zero (K : Set E) (hne : K.Nonempty)
    (hcomplete : IsComplete K) (hconvex : Convex ℝ K) (hzero : 0 ∈ K) :
    IsMinOn (projectionEnvelope K hne hcomplete hconvex) Set.univ 0 := by
  rw [isMinOn_univ_iff]
  intro x
  rw [projectionEnvelope_zero K hne hcomplete hconvex hzero]
  exact projectionEnvelope_nonneg K hne hcomplete hconvex hzero x

end GDLowerBound
