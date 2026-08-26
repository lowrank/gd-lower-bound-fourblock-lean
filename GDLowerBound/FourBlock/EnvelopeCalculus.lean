import GDLowerBound.FourBlock.Envelope
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-! # Calculus and concavity of the exact envelope -/

namespace GDLowerBound.FourBlock

noncomputable section

def sqrtSlope (b : ℝ) : ℝ :=
  (4 * (2 * b)) / (2 * Real.sqrt (4 * b ^ 2 + 1))

def deltaDenominatorSlope (b : ℝ) : ℝ := 2 + sqrtSlope b

def deltaDeriv (b : ℝ) : ℝ :=
  (0 * (2 * b + 1 + Real.sqrt (4 * b ^ 2 + 1)) -
      2 * deltaDenominatorSlope b) /
    (2 * b + 1 + Real.sqrt (4 * b ^ 2 + 1)) ^ 2

def logEnvelope (b : ℝ) : ℝ :=
  Real.log (2 / delta b - 1) + delta b - 1

theorem logEnvelope_eq_log_envelope {b : ℝ} (hb : 0 ≤ b) :
    logEnvelope b = Real.log (envelope b) := by
  have hd := delta_pos hb
  have hd1 := delta_le_one hb
  have hf : 0 < 2 / delta b - 1 := by
    rw [sub_pos, lt_div_iff₀ hd]
    linarith
  unfold logEnvelope envelope
  rw [Real.log_mul hf.ne' (Real.exp_pos _).ne', Real.log_exp]
  ring

theorem hasDerivAt_delta (b : ℝ) : HasDerivAt delta (deltaDeriv b) b := by
  have hs : 4 * b ^ 2 + 1 ≠ 0 := by positivity
  have hinner : HasDerivAt (fun x : ℝ ↦ 4 * x ^ 2 + 1) (4 * (2 * b)) b := by
    simpa [pow_two] using
      (((hasDerivAt_id b).pow 2).const_mul 4).add_const 1
  have hsqrt : HasDerivAt (fun x : ℝ ↦ Real.sqrt (4 * x ^ 2 + 1))
      (sqrtSlope b) b := by
    simpa only [sqrtSlope] using hinner.sqrt hs
  have hlinear : HasDerivAt (fun x : ℝ ↦ 2 * x + 1) 2 b := by
    simpa using ((hasDerivAt_id b).const_mul 2).add_const 1
  have hden : HasDerivAt
      (fun x : ℝ ↦ 2 * x + 1 + Real.sqrt (4 * x ^ 2 + 1))
      (deltaDenominatorSlope b) b := by
    unfold deltaDenominatorSlope
    change HasDerivAt
      ((fun x : ℝ ↦ 2 * x + 1) + fun x : ℝ ↦ Real.sqrt (4 * x ^ 2 + 1))
      (2 + sqrtSlope b) b
    exact hlinear.add hsqrt
  have hden0 : 2 * b + 1 + Real.sqrt (4 * b ^ 2 + 1) ≠ 0 := by
    have hs0 := Real.sqrt_nonneg (4 * b ^ 2 + 1)
    by_cases hb : 0 ≤ b
    · positivity
    · have hb' : b < 0 := lt_of_not_ge hb
      have hsquare := Real.sq_sqrt (by positivity : 0 ≤ 4 * b ^ 2 + 1)
      have hsabs : -2 * b < Real.sqrt (4 * b ^ 2 + 1) := by
        nlinarith [sq_nonneg (Real.sqrt (4 * b ^ 2 + 1) + 2 * b)]
      linarith
  have hquot := (hasDerivAt_const b (2 : ℝ)).div hden hden0
  unfold delta deltaDeriv
  change HasDerivAt
    ((fun _x : ℝ ↦ (2 : ℝ)) /
      fun x : ℝ ↦ 2 * x + 1 + Real.sqrt (4 * x ^ 2 + 1))
    ((0 * (2 * b + 1 + Real.sqrt (4 * b ^ 2 + 1)) -
        2 * deltaDenominatorSlope b) /
      (2 * b + 1 + Real.sqrt (4 * b ^ 2 + 1)) ^ 2) b
  exact hquot

theorem sqrtSlope_nonneg {b : ℝ} (hb : 0 ≤ b) : 0 ≤ sqrtSlope b := by
  unfold sqrtSlope
  positivity

theorem deltaDeriv_nonpos {b : ℝ} (hb : 0 ≤ b) : deltaDeriv b ≤ 0 := by
  have hslope : 0 ≤ deltaDenominatorSlope b := by
    unfold deltaDenominatorSlope
    positivity [sqrtSlope_nonneg hb]
  unfold deltaDeriv
  apply div_nonpos_of_nonpos_of_nonneg
  · nlinarith
  · positivity

theorem deltaDeriv_stationary {b : ℝ} (hb : 0 ≤ b) :
    deltaDeriv b * (1 + 2 * b * (1 - delta b)) =
      -delta b * (2 - delta b) := by
  unfold deltaDeriv deltaDenominatorSlope sqrtSlope delta
  have hs := sqrt_discriminant_pos b
  have hden := delta_denominator_pos hb
  have hsq := Real.sq_sqrt (by positivity : 0 ≤ 4 * b ^ 2 + 1)
  have hsqrtarg : Real.sqrt (b ^ 2 * 4 + 1) =
      Real.sqrt (4 * b ^ 2 + 1) := by
    congr 1
    ring
  field_simp [hs.ne', hden.ne']
  rw [hsqrtarg]
  linear_combination 4 * (2 * b + Real.sqrt (4 * b ^ 2 + 1)) * hsq

theorem hasDerivAt_logEnvelope {b : ℝ} (hb : 0 ≤ b) :
    HasDerivAt logEnvelope (logEnvelopeSlope b) b := by
  have hd := delta_pos hb
  have hd1 := delta_le_one hb
  have hf : 0 < 2 / delta b - 1 := by
    rw [sub_pos, lt_div_iff₀ hd]
    linarith
  have hdelta := hasDerivAt_delta b
  have hfactorRaw := ((hasDerivAt_const b (2 : ℝ)).div hdelta hd.ne').sub_const 1
  have hfactor : HasDerivAt (fun x : ℝ ↦ 2 / delta x - 1)
      ((0 * delta b - 2 * deltaDeriv b) / delta b ^ 2) b := by
    simpa only [Pi.div_apply] using hfactorRaw
  have hlog := hfactor.log hf.ne'
  have hraw := (hlog.add hdelta).sub_const 1
  have hraw' : HasDerivAt logEnvelope
      ((0 * delta b - 2 * deltaDeriv b) / delta b ^ 2 /
          (2 / delta b - 1) + deltaDeriv b) b := by
    unfold logEnvelope
    change HasDerivAt
      (fun x : ℝ ↦ ((fun y : ℝ ↦ Real.log (2 / delta y - 1)) + delta) x - 1)
      ((0 * delta b - 2 * deltaDeriv b) / delta b ^ 2 /
        (2 / delta b - 1) + deltaDeriv b) b
    exact hraw
  apply hraw'.congr_deriv
  unfold logEnvelopeSlope
  have himp := deltaDeriv_stationary hb
  have hstat := delta_stationary hb
  have htwo : 0 < 2 - delta b := by linarith
  have hdenid :
      (1 + 2 * b * (1 - delta b)) * (delta b * (2 - delta b)) =
        2 - delta b * (2 - delta b) := by
    calc
      (1 + 2 * b * (1 - delta b)) * (delta b * (2 - delta b)) =
          delta b * (2 - delta b) +
            2 * (1 - delta b) * (b * delta b * (2 - delta b)) := by ring
      _ = delta b * (2 - delta b) + 2 * (1 - delta b) ^ 2 := by
        rw [hstat]
        ring
      _ = 2 - delta b * (2 - delta b) := by ring
  have hm :
      deltaDeriv b * (2 - delta b * (2 - delta b)) =
        -(delta b * (2 - delta b)) ^ 2 := by
    calc
      deltaDeriv b * (2 - delta b * (2 - delta b)) =
          deltaDeriv b *
            ((1 + 2 * b * (1 - delta b)) * (delta b * (2 - delta b))) := by rw [hdenid]
      _ = (deltaDeriv b * (1 + 2 * b * (1 - delta b))) *
            (delta b * (2 - delta b)) := by ring
      _ = (-delta b * (2 - delta b)) * (delta b * (2 - delta b)) := by rw [himp]
      _ = -(delta b * (2 - delta b)) ^ 2 := by ring
  field_simp [hd.ne', htwo.ne', hf.ne']
  nlinarith [hm]

theorem hasDerivAt_logEnvelopeSlope (b : ℝ) :
    HasDerivAt logEnvelopeSlope (2 * deltaDeriv b * (1 - delta b)) b := by
  have hraw := (hasDerivAt_delta b).mul
    ((hasDerivAt_const b (2 : ℝ)).sub (hasDerivAt_delta b))
  have hraw' : HasDerivAt logEnvelopeSlope
      (deltaDeriv b * (2 - delta b) + delta b * (0 - deltaDeriv b)) b := by
    unfold logEnvelopeSlope
    change HasDerivAt (delta * ((fun _x : ℝ ↦ (2 : ℝ)) - delta))
      (deltaDeriv b * (2 - delta b) + delta b * (0 - deltaDeriv b)) b
    exact hraw
  apply hraw'.congr_deriv
  ring

theorem logEnvelopeSlope_deriv_nonpos {b : ℝ} (hb : 0 ≤ b) :
    2 * deltaDeriv b * (1 - delta b) ≤ 0 := by
  have hd' := deltaDeriv_nonpos hb
  have hd1 := delta_le_one hb
  nlinarith

theorem logEnvelope_concave : ConcaveOn ℝ (Set.Ici 0) logEnvelope := by
  apply concaveOn_of_hasDerivWithinAt2_nonpos (convex_Ici 0)
  · intro b hb
    exact (hasDerivAt_logEnvelope hb).continuousAt.continuousWithinAt
  · intro b hb
    exact (hasDerivAt_logEnvelope (interior_subset hb)).hasDerivWithinAt
  · intro b _
    exact (hasDerivAt_logEnvelopeSlope b).hasDerivWithinAt
  · intro b hb
    exact logEnvelopeSlope_deriv_nonpos (interior_subset hb)

theorem logEnvelope_monotoneOn : MonotoneOn logEnvelope (Set.Ici 0) := by
  apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici 0)
  · intro b hb
    exact (hasDerivAt_logEnvelope hb).continuousAt.continuousWithinAt
  · intro b hb
    exact (hasDerivAt_logEnvelope (interior_subset hb)).hasDerivWithinAt
  · intro b hb
    exact logEnvelopeSlope_nonneg (interior_subset hb)

end

end GDLowerBound.FourBlock
