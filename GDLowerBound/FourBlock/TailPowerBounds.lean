import GDLowerBound.FourBlock.TailCertificate
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! # Coarse exact power bounds used by the practical tail certificate -/

namespace GDLowerBound.FourBlock

noncomputable section

def tailR20 : ℝ := (1 / 2 : ℝ) ^ (betaLower + 2)
def tailR30 : ℝ := (3 / 4 : ℝ) ^ (betaLower + 2)

theorem tailR20_lt_upper : tailR20 < (tailR20UpperQ : ℝ) := by
  have hexp : (11 / 4 : ℝ) < betaLower + 2 := by
    norm_num [betaLower]
  have hmono : (1 / 2 : ℝ) ^ (betaLower + 2) <
      (1 / 2 : ℝ) ^ (11 / 4 : ℝ) :=
    Real.rpow_lt_rpow_of_exponent_gt (by norm_num) (by norm_num) hexp
  let x : ℝ := (1 / 2 : ℝ) ^ (11 / 4 : ℝ)
  have hx0 : 0 ≤ x := Real.rpow_nonneg (by norm_num) _
  have hx4 : x ^ (4 : ℕ) = (1 / 2 : ℝ) ^ (11 : ℕ) := by
    dsimp only [x]
    rw [← Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (11 / 4 : ℝ) 4]
    norm_num [Real.rpow_natCast]
  have hx : x < (3 / 20 : ℝ) := by
    by_contra hnot
    have hle : (3 / 20 : ℝ) ≤ x := le_of_not_gt hnot
    have hp : (3 / 20 : ℝ) ^ (4 : ℕ) ≤ x ^ (4 : ℕ) := by
      gcongr
    rw [hx4] at hp
    norm_num at hp
  have hx' : (1 / 2 : Real) ^ (11 / 4 : Real) <
      (tailR20UpperQ : Real) := by
    simpa [x, tailR20UpperQ] using hx
  unfold tailR20
  exact hmono.trans hx'

theorem tailR30Lower_lt : (tailR30LowerQ : ℝ) < tailR30 := by
  have hexp : betaLower + 2 < (23 / 8 : ℝ) := by
    norm_num [betaLower]
  have hmono : (3 / 4 : ℝ) ^ (23 / 8 : ℝ) <
      (3 / 4 : ℝ) ^ (betaLower + 2) :=
    Real.rpow_lt_rpow_of_exponent_gt (by norm_num) (by norm_num) hexp
  let x : ℝ := (3 / 4 : ℝ) ^ (23 / 8 : ℝ)
  have hx0 : 0 ≤ x := Real.rpow_nonneg (by norm_num) _
  have hx8 : x ^ (8 : ℕ) = (3 / 4 : ℝ) ^ (23 : ℕ) := by
    dsimp only [x]
    rw [← Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 3 / 4)
      (23 / 8 : ℝ) 8]
    norm_num [Real.rpow_natCast]
  have hx : (109 / 250 : ℝ) < x := by
    by_contra hnot
    have hle : x ≤ (109 / 250 : ℝ) := le_of_not_gt hnot
    have hp : x ^ (8 : ℕ) ≤ (109 / 250 : ℝ) ^ (8 : ℕ) := by
      gcongr
    rw [hx8] at hp
    norm_num at hp
  simpa [tailR30LowerQ, tailR30] using hx.trans hmono

end

end GDLowerBound.FourBlock
