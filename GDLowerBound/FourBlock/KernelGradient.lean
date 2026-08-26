import GDLowerBound.FourBlock.KernelConcavity

/-! # Exact gradients and supporting planes for the logarithmic kernel -/

namespace GDLowerBound.FourBlock

noncomputable section

def edgeParameterLineSlope (u v du dv : ℝ) : ℝ :=
  (v ^ 2 * du + u ^ 2 * dv) / (2 * (u + v) ^ 2)

def kernelGradU (u v : ℝ) : ℝ :=
  1 / (u + v) + logEnvelopeSlope (edgeParameter u v) *
    v ^ 2 / (2 * (u + v) ^ 2)

def kernelGradV (u v : ℝ) : ℝ :=
  1 / (u + v) + logEnvelopeSlope (edgeParameter u v) *
    u ^ 2 / (2 * (u + v) ^ 2)

theorem hasDerivAt_edgeParameter_line
    {u v du dv : ℝ} (hsum : 0 < u + v) :
    HasDerivAt
      (fun t : ℝ ↦ edgeParameter (u + t * du) (v + t * dv))
      (edgeParameterLineSlope u v du dv) 0 := by
  have hu : HasDerivAt (fun t : ℝ ↦ u + t * du) du 0 := by
    simpa only [one_mul] using
      ((hasDerivAt_id' (0 : ℝ)).mul_const du).const_add u
  have hv : HasDerivAt (fun t : ℝ ↦ v + t * dv) dv 0 := by
    simpa only [one_mul] using
      ((hasDerivAt_id' (0 : ℝ)).mul_const dv).const_add v
  have hnum := hu.mul hv
  have hden := (hu.add hv).const_mul 2
  have hden0 : 2 * (u + v) ≠ 0 := by positivity
  have hden0' : (2 * ((fun t : ℝ ↦ u + t * du) +
      fun t : ℝ ↦ v + t * dv) 0) ≠ 0 := by
    simpa using hden0
  have hraw := hnum.div hden hden0'
  have hraw' : HasDerivAt
      (fun t : ℝ ↦ edgeParameter (u + t * du) (v + t * dv))
      (((du * v + u * dv) * (2 * (u + v)) -
          (u * v) * (2 * (du + dv))) / (2 * (u + v)) ^ 2) 0 := by
    unfold edgeParameter
    change HasDerivAt
      (((fun t : ℝ ↦ u + t * du) * fun t : ℝ ↦ v + t * dv) /
        fun y : ℝ ↦ 2 * (((fun t : ℝ ↦ u + t * du) +
          fun t : ℝ ↦ v + t * dv) y))
      (((du * v + u * dv) * (2 * (u + v)) -
          (u * v) * (2 * (du + dv))) / (2 * (u + v)) ^ 2) 0
    apply hraw.congr_deriv
    simp only [Pi.add_apply, Pi.mul_apply, zero_mul, add_zero]
  apply hraw'.congr_deriv
  unfold edgeParameterLineSlope
  field_simp [hsum.ne']
  ring

theorem hasDerivAt_pairLogKernelClosed_line
    {u v du dv : ℝ} (hu : 0 < u) (hv : 0 < v) :
    HasDerivAt
      (fun t : ℝ ↦ pairLogKernelClosed (u + t * du, v + t * dv))
      (kernelGradU u v * du + kernelGradV u v * dv) 0 := by
  have hsum : 0 < u + v := by linarith
  have hlineU : HasDerivAt (fun t : ℝ ↦ u + t * du) du 0 := by
    simpa only [one_mul] using
      ((hasDerivAt_id' (0 : ℝ)).mul_const du).const_add u
  have hlineV : HasDerivAt (fun t : ℝ ↦ v + t * dv) dv 0 := by
    simpa only [one_mul] using
      ((hasDerivAt_id' (0 : ℝ)).mul_const dv).const_add v
  have hhalf : HasDerivAt
      (fun t : ℝ ↦ ((u + t * du) + (v + t * dv)) / 2)
      ((du + dv) / 2) 0 := by
    change HasDerivAt
      (fun t : ℝ ↦ ((fun y : ℝ ↦ u + y * du) +
        fun y : ℝ ↦ v + y * dv) t / 2) ((du + dv) / 2) 0
    exact (hlineU.add hlineV).div_const 2
  have hhalf0 : (u + v) / 2 ≠ 0 := by positivity
  have hhalf0' : ((fun t : ℝ ↦ ((u + t * du) + (v + t * dv)) / 2) 0) ≠ 0 := by
    simpa using hhalf0
  have hlogHalf := hhalf.log hhalf0'
  have hb : 0 ≤ edgeParameter u v := edgeParameter_nonneg hu.le hv.le
  have hparam := hasDerivAt_edgeParameter_line (du := du) (dv := dv) hsum
  have hb0 : 0 ≤ edgeParameter (u + 0 * du) (v + 0 * dv) := by simpa using hb
  have hlogEnvRaw := (hasDerivAt_logEnvelope hb0).comp 0 hparam
  have hlogEnv : HasDerivAt
      (fun t : ℝ ↦ logEnvelope (edgeParameter (u + t * du) (v + t * dv)))
      (logEnvelopeSlope (edgeParameter u v) * edgeParameterLineSlope u v du dv) 0 := by
    change HasDerivAt
      (logEnvelope ∘ fun t : ℝ ↦ edgeParameter (u + t * du) (v + t * dv))
      (logEnvelopeSlope (edgeParameter u v) * edgeParameterLineSlope u v du dv) 0
    simpa only [zero_mul, add_zero] using hlogEnvRaw
  have hraw := hlogHalf.add hlogEnv
  have hraw' : HasDerivAt
      (fun t : ℝ ↦ pairLogKernelClosed (u + t * du, v + t * dv))
      (((du + dv) / 2) / ((u + v) / 2) +
        logEnvelopeSlope (edgeParameter u v) * edgeParameterLineSlope u v du dv) 0 := by
    unfold pairLogKernelClosed pairEdgeParameter
    change HasDerivAt
      ((fun t : ℝ ↦ Real.log (((u + t * du) + (v + t * dv)) / 2)) +
        fun t : ℝ ↦ logEnvelope (edgeParameter (u + t * du) (v + t * dv)))
      (((du + dv) / 2) / ((u + v) / 2) +
        logEnvelopeSlope (edgeParameter u v) * edgeParameterLineSlope u v du dv) 0
    simpa only [zero_mul, add_zero] using hraw
  apply hraw'.congr_deriv
  unfold kernelGradU kernelGradV edgeParameterLineSlope
  field_simp [hsum.ne']
  ring

def pairSegment (p₀ p : ℝ × ℝ) (t : ℝ) : ℝ × ℝ :=
  p₀ + t • (p - p₀)

theorem pairSegment_mem {p₀ p : ℝ × ℝ}
    (hp₀ : p₀ ∈ positiveQuadrant) (hp : p ∈ positiveQuadrant)
    {t : ℝ} (ht : t ∈ Set.Icc 0 1) : pairSegment p₀ p t ∈ positiveQuadrant := by
  have hone : 0 ≤ 1 - t := sub_nonneg.mpr ht.2
  have hsum : (1 - t) + t = 1 := by ring
  have hconv := positiveQuadrant_convex hp₀ hp hone ht.1 hsum
  convert hconv using 1
  unfold pairSegment
  ext <;> simp [smul_eq_mul] <;> ring

theorem pairLogKernelClosed_segment_concave {p₀ p : ℝ × ℝ}
    (hp₀ : p₀ ∈ positiveQuadrant) (hp : p ∈ positiveQuadrant) :
    ConcaveOn ℝ (Set.Icc 0 1)
      (fun t ↦ pairLogKernelClosed (pairSegment p₀ p t)) := by
  refine ⟨convex_Icc 0 1, ?_⟩
  intro x hx y hy a b ha hb hab
  have hxmem := pairSegment_mem hp₀ hp hx
  have hymem := pairSegment_mem hp₀ hp hy
  have hconc := pairLogKernelClosed_concave.2 hxmem hymem ha hb hab
  calc
    a * pairLogKernelClosed (pairSegment p₀ p x) +
        b * pairLogKernelClosed (pairSegment p₀ p y) ≤
        pairLogKernelClosed
          (a • pairSegment p₀ p x + b • pairSegment p₀ p y) := by
      simpa only [smul_eq_mul] using hconc
    _ = pairLogKernelClosed (pairSegment p₀ p (a * x + b * y)) := by
      congr 1
      unfold pairSegment
      ext <;> simp [smul_eq_mul]
      · linear_combination p₀.1 * hab
      · linear_combination p₀.2 * hab

theorem pairLogKernelClosed_le_support
    {u₀ v₀ u v : ℝ}
    (hu₀ : 0 < u₀) (hv₀ : 0 < v₀) (hu : 0 < u) (hv : 0 < v) :
    pairLogKernelClosed (u, v) ≤ pairLogKernelClosed (u₀, v₀) +
      kernelGradU u₀ v₀ * (u - u₀) + kernelGradV u₀ v₀ * (v - v₀) := by
  let p₀ : ℝ × ℝ := (u₀, v₀)
  let p : ℝ × ℝ := (u, v)
  let g : ℝ → ℝ := fun t ↦ pairLogKernelClosed (pairSegment p₀ p t)
  have hp₀ : p₀ ∈ positiveQuadrant := ⟨hu₀, hv₀⟩
  have hp : p ∈ positiveQuadrant := ⟨hu, hv⟩
  have hconc := pairLogKernelClosed_segment_concave hp₀ hp
  have hderiv : HasDerivAt g
      (kernelGradU u₀ v₀ * (u - u₀) +
        kernelGradV u₀ v₀ * (v - v₀)) 0 := by
    dsimp only [g, p₀, p, pairSegment]
    convert hasDerivAt_pairLogKernelClosed_line hu₀ hv₀ using 1 <;>
      simp [smul_eq_mul]
  have hslope := hconc.slope_le_of_hasDerivAt
    (Set.left_mem_Icc.mpr (by norm_num : (0 : ℝ) ≤ 1))
    (Set.right_mem_Icc.mpr (by norm_num : (0 : ℝ) ≤ 1))
    (by norm_num : (0 : ℝ) < 1) hderiv
  dsimp only [g, p₀, p, pairSegment] at hslope
  have hend : (u₀, v₀) + ((u, v) - (u₀, v₀)) = (u, v) := by
    ext <;> simp
  unfold slope at hslope
  norm_num [hend] at hslope
  linarith

end

end GDLowerBound.FourBlock
