import GDLowerBound.FourBlock.Constants
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Exact equalization envelope

The certificate evaluates the closed forms below; it never asks an untrusted
program to optimize a real function.
-/

namespace GDLowerBound.FourBlock

noncomputable section

/-- Rationalized stationary parameter for the exact equalization envelope. -/
def delta (b : ℝ) : ℝ :=
  2 / (2 * b + 1 + Real.sqrt (4 * b ^ 2 + 1))

/-- Closed form of `max_{x>0} x(1+bx) exp(1-x)`. -/
def envelope (b : ℝ) : ℝ :=
  (2 / delta b - 1) * Real.exp (delta b - 1)

/-- The exact logarithmic edge kernel. -/
def logKernel (u v : ℝ) : ℝ :=
  Real.log ((u + v) / 2) +
    Real.log (envelope (u * v / (2 * (u + v))))

theorem sqrt_discriminant_pos (b : ℝ) :
    0 < Real.sqrt (4 * b ^ 2 + 1) := by
  positivity

theorem delta_denominator_pos {b : ℝ} (hb : 0 ≤ b) :
    0 < 2 * b + 1 + Real.sqrt (4 * b ^ 2 + 1) := by
  positivity

theorem delta_pos {b : ℝ} (hb : 0 ≤ b) : 0 < delta b := by
  unfold delta
  positivity [delta_denominator_pos hb]

theorem one_le_sqrt_discriminant (b : ℝ) :
    1 ≤ Real.sqrt (4 * b ^ 2 + 1) := by
  have harg : 0 ≤ 4 * b ^ 2 + 1 := by positivity
  have hs := Real.sq_sqrt harg
  have hs0 := Real.sqrt_nonneg (4 * b ^ 2 + 1)
  nlinarith [sq_nonneg b]

theorem delta_le_one {b : ℝ} (hb : 0 ≤ b) : delta b ≤ 1 := by
  have hden := delta_denominator_pos hb
  rw [delta, div_le_one hden]
  nlinarith [one_le_sqrt_discriminant b]

/-- The rationalized formula satisfies the stationary quadratic exactly. -/
theorem delta_stationary {b : ℝ} (hb : 0 ≤ b) :
    b * delta b * (2 - delta b) = 1 - delta b := by
  let s : ℝ := Real.sqrt (4 * b ^ 2 + 1)
  have hs2 : s ^ 2 = 4 * b ^ 2 + 1 := by
    dsimp only [s]
    rw [Real.sq_sqrt]
    positivity
  have hden : 0 < 2 * b + 1 + s := by
    dsimp only [s]
    exact delta_denominator_pos hb
  unfold delta
  dsimp only [s] at hs2 hden ⊢
  field_simp [hden.ne']
  ring_nf at hs2 ⊢
  nlinarith [hs2]

theorem envelope_pos {b : ℝ} (hb : 0 ≤ b) : 0 < envelope b := by
  have hd := delta_pos hb
  have hd1 := delta_le_one hb
  have hfactor : 0 < 2 / delta b - 1 := by
    rw [sub_pos, lt_div_iff₀ hd]
    nlinarith
  unfold envelope
  positivity

theorem logKernel_comm (u v : ℝ) : logKernel u v = logKernel v u := by
  unfold logKernel
  rw [add_comm u v, mul_comm u v]

/-- Derivative value of the logarithmic envelope at its stationary point. -/
def logEnvelopeSlope (b : ℝ) : ℝ := delta b * (2 - delta b)

theorem logEnvelopeSlope_nonneg {b : ℝ} (hb : 0 ≤ b) :
    0 ≤ logEnvelopeSlope b := by
  have hd0 := (delta_pos hb).le
  have hd1 := delta_le_one hb
  unfold logEnvelopeSlope
  exact mul_nonneg hd0 (by linarith)

end

end GDLowerBound.FourBlock
