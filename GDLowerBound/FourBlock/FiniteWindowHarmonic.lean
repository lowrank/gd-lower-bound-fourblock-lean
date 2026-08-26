import GDLowerBound.FourBlock.FiniteWindowRigidityErrors
import GDLowerBound.FourBlock.RationalBounds

/-!
# Harmonic mass of finite averaging windows

The strict error margin is obtained from multiplicatively long windows.  The
lemmas below expose the logarithmic growth of the exact finite harmonic
weight and give a convenient dyadic lower bound with a rational certificate
for `log 2`.
-/

namespace GDLowerBound.FourBlock

open scoped BigOperators

noncomputable section

theorem averagingHarmonicWeight_eq_adjacent (M N : ℕ) :
    averagingHarmonicWeight M N = adjacentHarmonicWeight M N := by
  rfl

theorem averagingHarmonicWeight_le_log_ratio
    {M N : ℕ} (hM : 1 ≤ M) (hMN : M ≤ N) :
    averagingHarmonicWeight M N ≤
      Real.log ((N : ℝ) / (M : ℝ)) := by
  unfold averagingHarmonicWeight
  exact harmonicBlock_le_log_ratio hM hMN

/-- Integral comparison in the direction needed to make the normalized
finite errors small. -/
theorem log_ratio_sub_inv_le_averagingHarmonicWeight
    {M N : ℕ} (hM : 1 ≤ M) (hMN : M ≤ N) :
    Real.log ((N : ℝ) / (M : ℝ)) - 1 / (M : ℝ) ≤
      averagingHarmonicWeight M N := by
  have hlog := log_ratio_le_adjacentHarmonic_add_inv hM hMN
  rw [← averagingHarmonicWeight_eq_adjacent] at hlog
  linarith

def logTwoLowerCert : LogBoundCert where
  y := 2
  n := 2
  lower := 2 / 3
  upper := 1

theorem two_thirds_le_log_two : (2 / 3 : ℝ) ≤ Real.log 2 := by
  simpa [logTwoLowerCert] using
    (LogBoundCert.sound (c := logTwoLowerCert) (by native_decide)).1

/-- A dyadic window of depth `R` has harmonic mass at least
`(2/3) R - 1/M`.  No finite sum is evaluated in this certificate. -/
theorem dyadic_averagingHarmonicWeight_lower
    {M R : ℕ} (hM : 1 ≤ M) :
    (2 / 3 : ℝ) * (R : ℝ) - 1 / (M : ℝ) ≤
      averagingHarmonicWeight M ((2 ^ R) * M) := by
  have hMN : M ≤ (2 ^ R) * M := by
    have hp : 1 ≤ 2 ^ R := one_le_pow₀ (by omega)
    nlinarith
  have hbase := log_ratio_sub_inv_le_averagingHarmonicWeight hM hMN
  have hM0 : (M : ℝ) ≠ 0 := by positivity
  have hratio :
      ((((2 ^ R) * M : ℕ) : ℝ) / (M : ℝ)) = (2 : ℝ) ^ R := by
    push_cast
    field_simp [hM0]
  rw [hratio, Real.log_pow] at hbase
  have hR0 : (0 : ℝ) ≤ R := by positivity
  have hlog := mul_le_mul_of_nonneg_left two_thirds_le_log_two hR0
  linarith

/-- The exact harmonic mass can be made larger than any prescribed real
number by increasing only the dyadic depth. -/
theorem exists_dyadicDepth_harmonicWeight_gt (A : ℝ) :
    ∃ R : ℕ, ∀ M : ℕ, 1 ≤ M →
      A < averagingHarmonicWeight M ((2 ^ R) * M) := by
  obtain ⟨R, hR⟩ := exists_nat_gt ((3 / 2 : ℝ) * (A + 1))
  refine ⟨R, ?_⟩
  intro M hM
  have hlower := dyadic_averagingHarmonicWeight_lower (R := R) hM
  have hMR : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hMpos : (0 : ℝ) < M := lt_of_lt_of_le zero_lt_one hMR
  have hinv : 1 / (M : ℝ) ≤ 1 := by
    exact (div_le_one hMpos).2 hMR
  nlinarith

end

end GDLowerBound.FourBlock
