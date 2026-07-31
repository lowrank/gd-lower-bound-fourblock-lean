import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Tactic

/-!
# Projection onto a complete convex set

Mathlib proves the Hilbert projection theorem for a nonempty complete convex set, but it does
not bundle the minimizer as a map.  This file makes that noncomputable choice and records the
variational inequality, uniqueness, and nonexpansiveness needed by the realization argument.
-/

open scoped InnerProductSpace
open Set

namespace GDLowerBound

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The metric projection onto a nonempty complete convex subset of a real inner product
space. -/
noncomputable def convexProj (K : Set E) (hne : K.Nonempty) (hcomplete : IsComplete K)
    (hconvex : Convex ℝ K) (x : E) : E :=
  Classical.choose (exists_norm_eq_iInf_of_complete_convex hne hcomplete hconvex x)

theorem convexProj_mem (K : Set E) (hne : K.Nonempty) (hcomplete : IsComplete K)
    (hconvex : Convex ℝ K) (x : E) : convexProj K hne hcomplete hconvex x ∈ K :=
  (Classical.choose_spec
    (exists_norm_eq_iInf_of_complete_convex hne hcomplete hconvex x)).1

theorem convexProj_norm_eq_iInf (K : Set E) (hne : K.Nonempty) (hcomplete : IsComplete K)
    (hconvex : Convex ℝ K) (x : E) :
    ‖x - convexProj K hne hcomplete hconvex x‖ = ⨅ w : K, ‖x - w‖ :=
  (Classical.choose_spec
    (exists_norm_eq_iInf_of_complete_convex hne hcomplete hconvex x)).2

/-- The variational inequality characterizing the projection. -/
theorem convexProj_vi (K : Set E) (hne : K.Nonempty) (hcomplete : IsComplete K)
    (hconvex : Convex ℝ K) (x : E) :
    ∀ z ∈ K, ⟪x - convexProj K hne hcomplete hconvex x,
      z - convexProj K hne hcomplete hconvex x⟫_ℝ ≤ 0 := by
  rw [← norm_eq_iInf_iff_real_inner_le_zero hconvex
    (convexProj_mem K hne hcomplete hconvex x)]
  exact convexProj_norm_eq_iInf K hne hcomplete hconvex x

/-- Any point of the set satisfying the projection variational inequality is the chosen
projection. -/
theorem eq_convexProj_of_mem_of_vi (K : Set E) (hne : K.Nonempty)
    (hcomplete : IsComplete K) (hconvex : Convex ℝ K) (x p : E)
    (hp_mem : p ∈ K) (hp_vi : ∀ z ∈ K, ⟪x - p, z - p⟫_ℝ ≤ 0) :
    p = convexProj K hne hcomplete hconvex x := by
  let q := convexProj K hne hcomplete hconvex x
  have hq_mem : q ∈ K := convexProj_mem K hne hcomplete hconvex x
  have hq_vi : ∀ z ∈ K, ⟪x - q, z - q⟫_ℝ ≤ 0 :=
    convexProj_vi K hne hcomplete hconvex x
  have hpq := hp_vi q hq_mem
  have hqp := hq_vi p hp_mem
  have hinner : ⟪p - q, p - q⟫_ℝ ≤ 0 := by
    have hid : ⟪p - q, p - q⟫_ℝ =
        ⟪x - p, q - p⟫_ℝ + ⟪x - q, p - q⟫_ℝ := by
      rw [show x - q = (x - p) + (p - q) by abel]
      rw [show q - p = -(p - q) by abel]
      simp only [inner_add_left, inner_neg_right]
      ring
    rw [hid]
    linarith
  have hzero : ⟪p - q, p - q⟫_ℝ = 0 :=
    le_antisymm hinner real_inner_self_nonneg
  have : p - q = 0 := inner_self_eq_zero.mp hzero
  exact sub_eq_zero.mp this

/-- Metric projections are firmly nonexpansive.  This is the quantitative form of the two
projection variational inequalities. -/
theorem convexProj_firmly_nonexpansive (K : Set E) (hne : K.Nonempty)
    (hcomplete : IsComplete K) (hconvex : Convex ℝ K) (x y : E) :
    ‖convexProj K hne hcomplete hconvex x - convexProj K hne hcomplete hconvex y‖ ^ 2 ≤
      ⟪convexProj K hne hcomplete hconvex x - convexProj K hne hcomplete hconvex y,
        x - y⟫_ℝ := by
  let p := convexProj K hne hcomplete hconvex x
  let q := convexProj K hne hcomplete hconvex y
  let d := p - q
  have hp_mem : p ∈ K := convexProj_mem K hne hcomplete hconvex x
  have hq_mem : q ∈ K := convexProj_mem K hne hcomplete hconvex y
  have hx := convexProj_vi K hne hcomplete hconvex x q hq_mem
  have hy := convexProj_vi K hne hcomplete hconvex y p hp_mem
  have hx' : 0 ≤ ⟪x - p, d⟫_ℝ := by
    rw [show q - p = -d by simp [d]] at hx
    simpa only [inner_neg_right, neg_nonpos] using hx
  have hy' : 0 ≤ ⟪q - y, d⟫_ℝ := by
    rw [show p - q = d by rfl] at hy
    rw [show q - y = -(y - q) by abel]
    simpa only [inner_neg_left, neg_nonneg] using hy
  change ‖d‖ ^ 2 ≤ ⟪d, x - y⟫_ℝ
  rw [← real_inner_self_eq_norm_sq]
  calc
    ⟪d, d⟫_ℝ ≤ ⟪x - p, d⟫_ℝ + ⟪d, d⟫_ℝ + ⟪q - y, d⟫_ℝ := by linarith
    _ = ⟪(x - p) + d + (q - y), d⟫_ℝ := by simp only [inner_add_left]
    _ = ⟪x - y, d⟫_ℝ := by congr 1; simp [d]
    _ = ⟪d, x - y⟫_ℝ := real_inner_comm _ _

/-- Metric projections onto complete convex sets do not increase distances. -/
theorem convexProj_nonexpansive (K : Set E) (hne : K.Nonempty)
    (hcomplete : IsComplete K) (hconvex : Convex ℝ K) (x y : E) :
    ‖convexProj K hne hcomplete hconvex x - convexProj K hne hcomplete hconvex y‖ ≤
      ‖x - y‖ := by
  let d := convexProj K hne hcomplete hconvex x - convexProj K hne hcomplete hconvex y
  have hfirm := convexProj_firmly_nonexpansive K hne hcomplete hconvex x y
  have hinner : ⟪d, x - y⟫_ℝ ≤ ‖d‖ * ‖x - y‖ := real_inner_le_norm _ _
  have hsq : ‖d‖ * ‖d‖ ≤ ‖d‖ * ‖x - y‖ := by
    calc
      ‖d‖ * ‖d‖ = ‖d‖ ^ 2 := by ring
      _ ≤ ⟪d, x - y⟫_ℝ := hfirm
      _ ≤ ‖d‖ * ‖x - y‖ := hinner
  change ‖d‖ ≤ ‖x - y‖
  by_cases hd : ‖d‖ = 0
  · rw [hd]
    exact norm_nonneg _
  · exact le_of_mul_le_mul_left hsq
      (lt_of_le_of_ne (norm_nonneg d) (Ne.symm hd))

/-- The projection is a `1`-Lipschitz map. -/
theorem convexProj_lipschitz (K : Set E) (hne : K.Nonempty)
    (hcomplete : IsComplete K) (hconvex : Convex ℝ K) :
    LipschitzWith 1 (convexProj K hne hcomplete hconvex) := by
  apply LipschitzWith.mk_one
  intro x y
  simpa only [dist_eq_norm] using
    convexProj_nonexpansive K hne hcomplete hconvex x y

end GDLowerBound
