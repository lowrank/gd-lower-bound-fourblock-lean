import GDLowerBound.FourBlock.RobustLocalGap
import GDLowerBound.FourBlock.FiniteConstraintTransfer

/-!
# Finite rank threshold for the robust local certificate

The sharp defect exponent C/(12m) tends to zero.  An elementary geometric
upper bound for the exponential gives the exact rational cutoff required by
the robust side certificates.  The reduced local gap still strictly exceeds
the certified global budget.
-/

namespace GDLowerBound.FourBlock

open GDLowerBound.RankAnalysis

noncomputable section

theorem exists_exp_sharpFiniteError_threshold :
    ∃ M : ℕ, ∀ m : ℕ, M ≤ m →
      Real.exp (oneStepLyapunovConstant criticalP / (12 * m : ℕ)) ≤
        (8201 / 8200 : ℝ) := by
  let C := oneStepLyapunovConstant criticalP
  have hC : 0 < C := zero_lt_one.trans_le
    (oneStepLyapunovConstant_ge_one criticalP)
  let A := C * 8201 / 12
  have hA : 0 < A := by
    dsimp only [A]
    positivity
  obtain ⟨M, hM⟩ := exists_nat_gt A
  refine ⟨M, ?_⟩
  intro m hmm
  have hMpos : 0 < M := by
    have hMR : (0 : ℝ) < M := hA.trans hM
    exact_mod_cast hMR
  have hmpos : 0 < m := hMpos.trans_le hmm
  have hmR : (0 : ℝ) < m := by exact_mod_cast hmpos
  have hmmR : (M : ℝ) ≤ m := by exact_mod_cast hmm
  have hAm : A < (m : ℝ) := hM.trans_le hmmR
  have hcross : C * 8201 < 12 * (m : ℝ) := by
    dsimp only [A] at hAm
    nlinarith
  let x := C / ((12 * m : ℕ) : ℝ)
  have hx0 : 0 ≤ x := by
    dsimp only [x]
    positivity
  have hxcap : x < (1 / 8201 : ℝ) := by
    dsimp only [x]
    push_cast
    apply (div_lt_div_iff₀ (by positivity : (0 : ℝ) < 12 * m)
      (by norm_num : (0 : ℝ) < 8201)).2
    nlinarith
  have hxlt1 : x < 1 := hxcap.trans (by norm_num)
  calc
    Real.exp (oneStepLyapunovConstant criticalP / (12 * m : ℕ)) =
        Real.exp x := by rfl
    _ ≤ 1 / (1 - x) :=
      Real.exp_bound_div_one_sub_of_interval hx0 hxlt1
    _ ≤ (8201 / 8200 : ℝ) := by
      apply (div_le_iff₀ (sub_pos.mpr hxlt1)).2
      nlinarith

theorem global_budget_lt_robustLocalGap :
    globalCoefficientUpper * (betaUpper - massExponent) < robustLocalGap := by
  have hK := globalCoefficient_lt
  have hd : 0 < betaUpper - massExponent := by
    norm_num [betaUpper, massExponent]
  calc
    globalCoefficientUpper * (betaUpper - massExponent) <
        (89257 / 100000 : ℝ) * (betaUpper - massExponent) :=
      mul_lt_mul_of_pos_right hK hd
    _ < robustLocalGap := by
      norm_num [betaUpper, massExponent, robustLocalGap]

end

end GDLowerBound.FourBlock
