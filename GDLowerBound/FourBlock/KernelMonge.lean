import GDLowerBound.FourBlock.KernelGradient
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# The outside-in (Monge) property of the exact envelope kernel

The chronological matching reduction needs more than joint concavity: it
needs decreasing differences.  We prove this from an exact formula for the
mixed derivative of the logarithmic kernel.
-/

namespace GDLowerBound.FourBlock

noncomputable section

def edgeParameterRightSlope (u v : ℝ) : ℝ :=
  u ^ 2 / (2 * (u + v) ^ 2)

def kernelRatio (u v : ℝ) : ℝ :=
  v ^ 2 / (2 * (u + v) ^ 2)

def kernelRatioRightSlope (u v : ℝ) : ℝ :=
  u * v / (u + v) ^ 3

def kernelCrossRaw (u v : ℝ) : ℝ :=
  -1 / (u + v) ^ 2 +
    (2 * deltaDeriv (edgeParameter u v) *
        (1 - delta (edgeParameter u v)) * edgeParameterRightSlope u v) *
      kernelRatio u v +
    logEnvelopeSlope (edgeParameter u v) * kernelRatioRightSlope u v

theorem hasDerivAt_edgeParameter_right {u v : ℝ} (hsum : 0 < u + v) :
    HasDerivAt (edgeParameter u) (edgeParameterRightSlope u v) v := by
  have hnum : HasDerivAt (fun y : ℝ ↦ u * y) u v := by
    simpa only [mul_one, mul_comm] using
      (hasDerivAt_id' v).mul_const u
  have hsumDeriv : HasDerivAt (fun y : ℝ ↦ u + y) 1 v :=
    (hasDerivAt_id' v).const_add u
  have hden := hsumDeriv.const_mul 2
  have hden0 : 2 * (u + v) ≠ 0 := by positivity
  have hraw := hnum.div hden hden0
  unfold edgeParameter edgeParameterRightSlope
  apply hraw.congr_deriv
  field_simp [hsum.ne']
  ring

theorem hasDerivAt_kernelRatio_right {u v : ℝ} (hsum : 0 < u + v) :
    HasDerivAt (kernelRatio u) (kernelRatioRightSlope u v) v := by
  have hnum := (hasDerivAt_id' v).pow 2
  have hsumDeriv : HasDerivAt (fun y : ℝ ↦ u + y) 1 v :=
    (hasDerivAt_id' v).const_add u
  have hden := (hsumDeriv.pow 2).const_mul 2
  have hden0 : 2 * (u + v) ^ 2 ≠ 0 := by positivity
  have hraw := hnum.div hden hden0
  have hfun : (fun y : ℝ ↦ y ^ 2 / (2 * (u + y) ^ 2)) =ᶠ[nhds v]
      (((fun x : ℝ ↦ x) ^ 2) / fun y : ℝ ↦ 2 * ((fun y : ℝ ↦ u + y) ^ 2) y) := by
    filter_upwards [] with y
    simp only [Pi.pow_apply, Pi.div_apply]
  have hraw' := hraw.congr_of_eventuallyEq hfun
  unfold kernelRatio kernelRatioRightSlope
  apply hraw'.congr_deriv
  simp only [Pi.pow_apply]
  field_simp [hsum.ne']
  ring

theorem hasDerivAt_kernelGradU_right
    {u v : ℝ} (hu : 0 < u) (hv : 0 < v) :
    HasDerivAt (kernelGradU u) (kernelCrossRaw u v) v := by
  have hsum : 0 < u + v := by linarith
  have hsumDeriv : HasDerivAt (fun y : ℝ ↦ u + y) 1 v :=
    (hasDerivAt_id' v).const_add u
  have hsum0 : u + v ≠ 0 := hsum.ne'
  have hinvRaw := (hasDerivAt_const v (1 : ℝ)).div hsumDeriv hsum0
  have hinv : HasDerivAt (fun y : ℝ ↦ 1 / (u + y))
      (-1 / (u + v) ^ 2) v := by
    change HasDerivAt
      ((fun _y : ℝ ↦ (1 : ℝ)) / fun y : ℝ ↦ u + y)
      (-1 / (u + v) ^ 2) v
    simpa only [zero_mul, one_mul, zero_sub] using hinvRaw
  have hb : 0 ≤ edgeParameter u v := edgeParameter_nonneg hu.le hv.le
  have hparam := hasDerivAt_edgeParameter_right hsum
  have hslope := (hasDerivAt_logEnvelopeSlope (edgeParameter u v)).comp v hparam
  have hratio := hasDerivAt_kernelRatio_right hsum
  have hproduct := hslope.mul hratio
  have htotal := hinv.add hproduct
  have hfun : (fun y : ℝ ↦ kernelGradU u y) =ᶠ[nhds v]
      ((fun y : ℝ ↦ 1 / (u + y)) +
        (logEnvelopeSlope ∘ edgeParameter u) * kernelRatio u) := by
    filter_upwards [] with y
    simp only [kernelGradU, kernelRatio, Function.comp_apply,
      Pi.add_apply, Pi.mul_apply]
    ring
  apply (htotal.congr_of_eventuallyEq hfun).congr_deriv
  unfold kernelCrossRaw edgeParameterRightSlope kernelRatio
    kernelRatioRightSlope
  simp only [Function.comp_apply]
  ring

private theorem crossScalarIdentity
    {b d dp : ℝ} (hb : 0 ≤ b) (hd : 0 < d) (hd1 : d ≤ 1)
    (hstat : b * (d * (2 - d)) = 1 - d)
    (himp : dp * (1 + 2 * b * (1 - d)) = -(d * (2 - d))) :
    -1 + 2 * dp * (1 - d) * b ^ 2 + 2 * b * (d * (2 - d)) =
      -d ^ 2 / (1 + (1 - d) ^ 2) := by
  have htwo : 0 < 2 - d := by linarith
  have hL : 0 < d * (2 - d) := mul_pos hd htwo
  have hbFormula : b = (1 - d) / (d * (2 - d)) := by
    rw [eq_div_iff hL.ne']
    exact hstat
  have hOne : 0 ≤ 1 - d := sub_nonneg.mpr hd1
  have hprod : 0 ≤ 2 * b * (1 - d) := by positivity
  have hA : 0 < 1 + 2 * b * (1 - d) := by linarith
  have hdpFormula : dp = -(d * (2 - d)) / (1 + 2 * b * (1 - d)) := by
    rw [eq_div_iff hA.ne']
    exact himp
  rw [hdpFormula, hbFormula]
  field_simp [hd.ne', (by linarith : (2 - d) ≠ 0)]
  ring

theorem kernelCrossRaw_eq {u v : ℝ} (hu : 0 < u) (hv : 0 < v) :
    kernelCrossRaw u v =
      -(delta (edgeParameter u v)) ^ 2 /
        ((u + v) ^ 2 *
          (1 + (1 - delta (edgeParameter u v)) ^ 2)) := by
  let S : ℝ := u + v
  let b : ℝ := edgeParameter u v
  let d : ℝ := delta b
  have hS : 0 < S := by dsimp only [S]; linarith
  have hb : 0 ≤ b := by
    dsimp only [b]
    exact edgeParameter_nonneg hu.le hv.le
  have hd : 0 < d := by dsimp only [d]; exact delta_pos hb
  have hd1 : d ≤ 1 := by dsimp only [d]; exact delta_le_one hb
  have hstat : b * (d * (2 - d)) = 1 - d := by
    dsimp only [d]
    simpa only [mul_assoc] using delta_stationary hb
  have himp : deltaDeriv b * (1 + 2 * b * (1 - d)) = -(d * (2 - d)) := by
    dsimp only [d]
    simpa only [neg_mul] using deltaDeriv_stationary hb
  have hnormalized :
      kernelCrossRaw u v * S ^ 2 =
        -1 + 2 * deltaDeriv b * (1 - d) * b ^ 2 +
          2 * b * (d * (2 - d)) := by
    dsimp only [kernelCrossRaw, edgeParameterRightSlope, kernelRatio,
      kernelRatioRightSlope, logEnvelopeSlope, S, b, d]
    unfold edgeParameter
    field_simp [hS.ne']
  have hscalar := crossScalarIdentity hb hd hd1 hstat himp
  rw [hscalar] at hnormalized
  dsimp only [S, b, d] at hnormalized ⊢
  apply (mul_left_cancel₀ (pow_ne_zero 2 hS.ne'))
  calc
    (u + v) ^ 2 * kernelCrossRaw u v =
        kernelCrossRaw u v * (u + v) ^ 2 := by ring
    _ = -delta (edgeParameter u v) ^ 2 /
        (1 + (1 - delta (edgeParameter u v)) ^ 2) := hnormalized
    _ = (u + v) ^ 2 *
        (-delta (edgeParameter u v) ^ 2 /
          ((u + v) ^ 2 *
            (1 + (1 - delta (edgeParameter u v)) ^ 2))) := by
      field_simp [hS.ne']

theorem kernelCrossRaw_nonpos {u v : ℝ} (hu : 0 < u) (hv : 0 < v) :
    kernelCrossRaw u v ≤ 0 := by
  rw [kernelCrossRaw_eq hu hv]
  have hb : 0 ≤ edgeParameter u v := edgeParameter_nonneg hu.le hv.le
  have hd := delta_pos hb
  have hsum : 0 < u + v := by linarith
  exact div_nonpos_of_nonpos_of_nonneg
    (neg_nonpos.mpr (sq_nonneg _)) (by positivity)

end

end GDLowerBound.FourBlock
