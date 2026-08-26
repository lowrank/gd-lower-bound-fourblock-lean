import GDLowerBound.FourBlock.RankedPathWeights

/-! # Invariance of normalized four-block coordinates under scaling -/

namespace GDLowerBound.FourBlock

open scoped BigOperators

noncomputable section

theorem quarterSumOne_scale {m : ℕ} (c : ℝ)
    (w : Fin (2 * (m + m)) → ℝ) :
    quarterSumOne (fun i ↦ c * w i) = c * quarterSumOne w := by
  unfold quarterSumOne outsideQuarterOne
  simp only [← Finset.mul_sum]

theorem quarterSumTwo_scale {m : ℕ} (c : ℝ)
    (w : Fin (2 * (m + m)) → ℝ) :
    quarterSumTwo (fun i ↦ c * w i) = c * quarterSumTwo w := by
  unfold quarterSumTwo outsideQuarterTwo
  simp only [← Finset.mul_sum]

theorem quarterSumThree_scale {m : ℕ} (c : ℝ)
    (w : Fin (2 * (m + m)) → ℝ) :
    quarterSumThree (fun i ↦ c * w i) = c * quarterSumThree w := by
  unfold quarterSumThree outsideQuarterThree
  simp only [← Finset.mul_sum]

theorem quarterSumFour_scale {m : ℕ} (c : ℝ)
    (w : Fin (2 * (m + m)) → ℝ) :
    quarterSumFour (fun i ↦ c * w i) = c * quarterSumFour w := by
  unfold quarterSumFour outsideQuarterFour
  simp only [← Finset.mul_sum]

theorem fourBlockTotal_scale {m : ℕ} (c : ℝ)
    (w : Fin (2 * (m + m)) → ℝ) :
    fourBlockTotal (fun i ↦ c * w i) = c * fourBlockTotal w := by
  rw [fourBlockTotal_eq_sum, fourBlockTotal_eq_sum]
  simp only [← Finset.mul_sum]

theorem fourBlockA_scale {m : ℕ} {c : ℝ} (hc : c ≠ 0)
    (w : Fin (2 * (m + m)) → ℝ) :
    fourBlockA (fun i ↦ c * w i) = fourBlockA w := by
  unfold fourBlockA
  rw [quarterSumOne_scale, fourBlockTotal_scale]
  field_simp [hc]

theorem fourBlockR_scale {m : ℕ} {c : ℝ} (hc : c ≠ 0)
    (w : Fin (2 * (m + m)) → ℝ) :
    fourBlockR (fun i ↦ c * w i) = fourBlockR w := by
  unfold fourBlockR
  rw [quarterSumOne_scale, quarterSumTwo_scale, fourBlockTotal_scale]
  field_simp [hc]

theorem fourBlockS_scale {m : ℕ} {c : ℝ} (hc : c ≠ 0)
    (w : Fin (2 * (m + m)) → ℝ) :
    fourBlockS (fun i ↦ c * w i) = fourBlockS w := by
  unfold fourBlockS
  rw [quarterSumOne_scale, quarterSumTwo_scale, quarterSumThree_scale,
    fourBlockTotal_scale]
  field_simp [hc]

end

end GDLowerBound.FourBlock
