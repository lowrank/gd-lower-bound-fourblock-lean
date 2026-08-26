import GDLowerBound.FourBlock.FiniteConstraintTransfer
import GDLowerBound.FourBlock.GlobalCertificate

/-!
# Eventual absorption of the finite drift error

The global certificate has a strict rational margin.  This module verifies
that the sharp third-block energy price tends to zero strongly enough to fit
inside that margin beyond one fixed rank threshold.
-/

namespace GDLowerBound.FourBlock

open GDLowerBound.RankAnalysis

noncomputable section

def finiteDriftEnergyError (m : ℕ) : ℝ :=
  (centralAlphaQ : ℝ) * oneStepLyapunovConstant criticalP / (12 * m : ℕ)

theorem finiteDriftEnergyError_nonneg (m : ℕ) :
    0 ≤ finiteDriftEnergyError m := by
  unfold finiteDriftEnergyError
  have ha : (0 : ℝ) ≤ centralAlphaQ := by norm_num [centralAlphaQ]
  have hC : 0 ≤ oneStepLyapunovConstant criticalP :=
    zero_le_one.trans (oneStepLyapunovConstant_ge_one criticalP)
  exact div_nonneg (mul_nonneg ha hC) (by positivity)

/-- The strict global numerical margin eventually absorbs the exact finite
third-block price.  No numerical approximation of `C` is needed. -/
theorem exists_finiteDrift_absorption_threshold :
    ∃ M : ℕ, ∀ m : ℕ, M ≤ m →
      globalCoefficientUpper * (betaUpper - massExponent) +
          finiteDriftEnergyError m < localGap := by
  let δ := localGap -
    globalCoefficientUpper * (betaUpper - massExponent)
  have hδ : 0 < δ := by
    dsimp only [δ]
    linarith [global_budget_lt_localGap]
  let A := (centralAlphaQ : ℝ) *
    oneStepLyapunovConstant criticalP / 12
  have hA : 0 ≤ A := by
    dsimp only [A]
    have ha : (0 : ℝ) ≤ centralAlphaQ := by norm_num [centralAlphaQ]
    have hC : 0 ≤ oneStepLyapunovConstant criticalP :=
      zero_le_one.trans (oneStepLyapunovConstant_ge_one criticalP)
    exact div_nonneg (mul_nonneg ha hC) (by norm_num)
  obtain ⟨M, hM⟩ := exists_nat_gt (A / δ)
  refine ⟨M, ?_⟩
  intro m hmm
  have hratio0 : 0 ≤ A / δ := div_nonneg hA hδ.le
  have hMpos : 0 < M := by
    have hMR : (0 : ℝ) < M := hratio0.trans_lt hM
    exact_mod_cast hMR
  have hmpos : 0 < m := hMpos.trans_le hmm
  have hmR : (0 : ℝ) < m := by exact_mod_cast hmpos
  have hmmR : (M : ℝ) ≤ m := by exact_mod_cast hmm
  have hAm : A / δ < (m : ℝ) := hM.trans_le hmmR
  have hA_lt : A < (m : ℝ) * δ := (div_lt_iff₀ hδ).mp hAm
  have herror : finiteDriftEnergyError m < δ := by
    have hdiv : A / (m : ℝ) < δ := by
      apply (div_lt_iff₀ hmR).2
      nlinarith
    have heq : finiteDriftEnergyError m = A / (m : ℝ) := by
      dsimp only [finiteDriftEnergyError, A]
      push_cast
      field_simp
    rwa [heq]
  dsimp only [δ] at herror
  linarith

end

end GDLowerBound.FourBlock
