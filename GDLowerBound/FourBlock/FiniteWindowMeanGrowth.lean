import GDLowerBound.FourBlock.FiniteWindowHarmonic

/-!
# Endpoint mass growth implies the effective window-growth hypothesis

This module rewrites the abstract growth hypothesis of the normalized
composition as a linear finite-sum condition.  The exact unresolved-mass
product then supplies that condition from a lower bound on one endpoint mass
ratio.
-/

namespace GDLowerBound.FourBlock

open scoped BigOperators
open GDLowerBound.Schedule GDLowerBound.RankAnalysis

noncomputable section

theorem massExponent_le_effectiveMeanGrowth_iff
    {T : ℕ} (h : StepSchedule T) (M N : ℕ) :
    massExponent ≤ effectiveMeanGrowth h M N ↔
      normalizedCommonMeanDeficit h M N ≤ betaLower - massExponent := by
  have hgap : 0 ≤ betaLower - massExponent :=
    sub_nonneg.mpr massExponent_lt_betaLower.le
  unfold effectiveMeanGrowth effectiveMeanDeficit
  constructor
  · intro hgrowth
    have hmax : max (normalizedCommonMeanDeficit h M N) 0 ≤
        betaLower - massExponent := by
      linarith
    exact (le_max_left _ _).trans hmax
  · intro hdeficit
    have hmax : max (normalizedCommonMeanDeficit h M N) 0 ≤
        betaLower - massExponent := max_le hdeficit hgap
    linarith

theorem normalizedCommonMeanDeficit_eq_growthSum
    {T : ℕ} (h : StepSchedule T) (M N : ℕ) :
    normalizedCommonMeanDeficit h M N =
      (betaLower * adjacentHarmonicWeight (2 * M) (4 * N) -
          ∑ n ∈ Finset.Ico (2 * M + 1) (4 * N + 1),
            relativeMassIncrement h n / (n : ℝ)) /
        averagingHarmonicWeight M N := by
  unfold normalizedCommonMeanDeficit commonMeanDeficitSum
  congr 1
  unfold adjacentHarmonicWeight
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro n _
  ring

/-- Linear finite-sum form of the mean-growth requirement. -/
theorem massExponent_le_effectiveMeanGrowth_of_sum
    {T : ℕ} {h : StepSchedule T} {M N : ℕ}
    (hM : 1 ≤ M) (hMN : M < N)
    (hsum :
      betaLower * adjacentHarmonicWeight (2 * M) (4 * N) -
          (betaLower - massExponent) * averagingHarmonicWeight M N ≤
        ∑ n ∈ Finset.Ico (2 * M + 1) (4 * N + 1),
          relativeMassIncrement h n / (n : ℝ)) :
    massExponent ≤ effectiveMeanGrowth h M N := by
  rw [massExponent_le_effectiveMeanGrowth_iff,
    normalizedCommonMeanDeficit_eq_growthSum]
  have hH := averagingHarmonicWeight_pos hM hMN
  apply (div_le_iff₀ hH).2
  linarith

/-- The logarithm of an unresolved-mass ratio is bounded by the corresponding
weighted sum of relative mass increments. -/
theorem log_unresolvedMass_ratio_le_commonGrowthSum
    {T : ℕ} {h : StepSchedule T} (hh : IsNonnegativeSchedule h)
    {M N : ℕ} (hM : 1 ≤ M) (hMN : M ≤ N)
    (h4N : 4 * N ≤ longCount h) :
    Real.log (unresolvedMass h (2 * M) / unresolvedMass h (4 * N)) ≤
      ∑ n ∈ Finset.Ico (2 * M + 1) (4 * N + 1),
        relativeMassIncrement h n / (n : ℝ) := by
  rw [← sum_log_mass_increment_eq_log_ratio hh
    (by omega : 2 * M ≤ 4 * N) h4N]
  apply Finset.sum_le_sum
  intro n hn
  have hnIco := Finset.mem_Ico.mp hn
  have hn0 : (0 : ℝ) < n := by
    exact_mod_cast (show 0 < n by omega)
  have hv := relativeMassIncrement_pos hh
    (q := n) (by omega : 1 ≤ n) (by omega : n ≤ longCount h)
  have hpositive :
      0 < 1 + relativeMassIncrement h n / (n : ℝ) := by positivity
  have hlog := Real.log_le_sub_one_of_pos hpositive
  have hid :
      1 + relativeMassIncrement h n / (n : ℝ) - 1 =
        relativeMassIncrement h n / (n : ℝ) := by ring
  rwa [hid] at hlog

/-- Endpoint-mass version of the growth hypothesis used by the finite-window
good-scale theorem. -/
theorem massExponent_le_effectiveMeanGrowth_of_log_ratio
    {T : ℕ} {h : StepSchedule T} (hh : IsNonnegativeSchedule h)
    {M N : ℕ} (hM : 1 ≤ M) (hMN : M < N)
    (h4N : 4 * N ≤ longCount h)
    (hratio :
      betaLower * adjacentHarmonicWeight (2 * M) (4 * N) -
          (betaLower - massExponent) * averagingHarmonicWeight M N ≤
        Real.log (unresolvedMass h (2 * M) /
          unresolvedMass h (4 * N))) :
    massExponent ≤ effectiveMeanGrowth h M N := by
  apply massExponent_le_effectiveMeanGrowth_of_sum hM hMN
  exact hratio.trans
    (log_unresolvedMass_ratio_le_commonGrowthSum hh hM hMN.le h4N)

end

end GDLowerBound.FourBlock
