import GDLowerBound.FourBlock.Envelope

/-! # Exact one-variable equalization -/

namespace GDLowerBound.FourBlock

noncomputable section

/-- The positive maximizer corresponding to `delta`. -/
def maximizer (b : ℝ) : ℝ := 2 - delta b

theorem one_le_maximizer {b : ℝ} (hb : 0 ≤ b) : 1 ≤ maximizer b := by
  unfold maximizer
  linarith [delta_le_one hb]

theorem maximizer_pos {b : ℝ} (hb : 0 ≤ b) : 0 < maximizer b :=
  zero_lt_one.trans_le (one_le_maximizer hb)

theorem maximizer_stationary {b : ℝ} (hb : 0 ≤ b) :
    1 / maximizer b + b / (1 + b * maximizer b) = 1 := by
  have hx := maximizer_pos hb
  have hlin : 0 < 1 + b * maximizer b := by positivity
  have hstat := delta_stationary hb
  unfold maximizer at hx hlin hstat ⊢
  field_simp [hx.ne', hlin.ne']
  nlinarith

theorem envelope_eq_maximizer_value {b : ℝ} (hb : 0 ≤ b) :
    envelope b = maximizer b * (1 + b * maximizer b) *
      Real.exp (1 - maximizer b) := by
  have hd := delta_pos hb
  have hstat := delta_stationary hb
  have hfactor :
      maximizer b * (1 + b * maximizer b) = 2 / delta b - 1 := by
    unfold maximizer
    field_simp [hd.ne']
    nlinarith
  unfold envelope
  rw [hfactor]
  have hexponent : delta b - 1 = 1 - maximizer b := by
    unfold maximizer
    ring
  rw [hexponent]

/-- Exact one-variable equalization. -/
theorem equalization_le_envelope {b x : ℝ} (hb : 0 ≤ b) (hx : 0 < x) :
    x * (1 + b * x) * Real.exp (1 - x) ≤ envelope b := by
  let xstar := maximizer b
  let r₁ := x / xstar
  let r₂ := (1 + b * x) / (1 + b * xstar)
  have hxs : 0 < xstar := maximizer_pos hb
  have hlinx : 0 < 1 + b * x := by positivity
  have hlins : 0 < 1 + b * xstar := by positivity
  have hr₁ : 0 < r₁ := div_pos hx hxs
  have hr₂ : 0 < r₂ := div_pos hlinx hlins
  have h₁ : r₁ ≤ Real.exp (r₁ - 1) := by
    linarith [Real.add_one_le_exp (r₁ - 1)]
  have h₂ : r₂ ≤ Real.exp (r₂ - 1) := by
    linarith [Real.add_one_le_exp (r₂ - 1)]
  have hprod : r₁ * r₂ ≤ Real.exp (x - xstar) := by
    have hmul := mul_le_mul h₁ h₂ hr₂.le (Real.exp_pos _).le
    rw [← Real.exp_add] at hmul
    have hstationary := maximizer_stationary hb
    have hsum : (r₁ - 1) + (r₂ - 1) = x - xstar := by
      calc
        (r₁ - 1) + (r₂ - 1) =
            (x - xstar) *
              (1 / xstar + b / (1 + b * xstar)) := by
          dsimp only [r₁, r₂]
          field_simp [hxs.ne', hlins.ne']
          ring
        _ = x - xstar := by rw [hstationary, mul_one]
    rwa [hsum] at hmul
  rw [envelope_eq_maximizer_value hb]
  have hscale : 0 < xstar * (1 + b * xstar) * Real.exp (1 - x) := by
    positivity
  have hratio :
      x * (1 + b * x) * Real.exp (1 - x) =
        (r₁ * r₂) * (xstar * (1 + b * xstar) * Real.exp (1 - x)) := by
    dsimp only [r₁, r₂]
    field_simp [hxs.ne', hlins.ne']
  rw [hratio]
  calc
    (r₁ * r₂) * (xstar * (1 + b * xstar) * Real.exp (1 - x)) ≤
        Real.exp (x - xstar) *
          (xstar * (1 + b * xstar) * Real.exp (1 - x)) :=
      mul_le_mul_of_nonneg_right hprod hscale.le
    _ = xstar * (1 + b * xstar) * Real.exp (1 - xstar) := by
      calc
        Real.exp (x - xstar) *
              (xstar * (1 + b * xstar) * Real.exp (1 - x)) =
            xstar * (1 + b * xstar) *
              (Real.exp (x - xstar) * Real.exp (1 - x)) := by ring
        _ = xstar * (1 + b * xstar) * Real.exp (1 - xstar) := by
          rw [← Real.exp_add]
          congr 1
          ring

end

end GDLowerBound.FourBlock
