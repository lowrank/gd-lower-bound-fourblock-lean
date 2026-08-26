import GDLowerBound.FourBlock.FiniteWindowEndpointGoodScale
import GDLowerBound.FourBlock.FiniteWindowDyadicError

/-!
# Exact dyadic endpoint-growth threshold

The rational estimate `2 / 3 ≤ log 2` is sufficient for making finite-window
errors small, but is too lossy in the coefficient of a long global window.
This module retains the exact `log 2` in the endpoint-growth hypothesis.  The
only finite correction is one reciprocal starting-rank term.
-/

namespace GDLowerBound.FourBlock

open GDLowerBound.Schedule GDLowerBound.RankAnalysis

noncomputable section

/-- Exact-log version of the lower harmonic estimate on a dyadic window. -/
theorem dyadic_averagingHarmonicWeight_lower_logTwo
    {M R : ℕ} (hM : 1 ≤ M) :
    (R : ℝ) * Real.log 2 - 1 / (M : ℝ) ≤
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
  simpa [mul_comm] using hbase

/-- The shifted harmonic block has exactly one additional dyadic logarithmic
unit, before the harmless integral-comparison inequality. -/
theorem shiftedDyadicAdjacentHarmonicWeight_le_logTwo
    {M R : ℕ} (hM : 1 ≤ M) :
    adjacentHarmonicWeight (2 * M) (4 * ((2 ^ R) * M)) ≤
      ((R : ℝ) + 1) * Real.log 2 := by
  have hlo : 1 ≤ 2 * M := by omega
  have hlohi : 2 * M ≤ 4 * ((2 ^ R) * M) := by
    have hp : 1 ≤ 2 ^ R := one_le_pow₀ (by omega)
    nlinarith
  have hlog := harmonicBlock_le_log_ratio hlo hlohi
  have hM0 : (M : ℝ) ≠ 0 := by positivity
  have hratio :
      (((4 * ((2 ^ R) * M) : ℕ) : ℝ) / ((2 * M : ℕ) : ℝ)) =
        (2 : ℝ) ^ (R + 1) := by
    push_cast
    rw [pow_succ]
    field_simp [hM0]
    ring
  unfold adjacentHarmonicWeight
  rw [hratio, Real.log_pow] at hlog
  norm_num at hlog ⊢
  simpa [mul_add, add_mul, mul_comm, mul_left_comm, mul_assoc] using hlog

/-- Exact upper bound for the endpoint logarithmic growth needed by the
finite-window theorem.  Its coefficient of the dyadic depth is precisely
`massExponent`, rather than the larger coefficient produced by replacing
`log 2` with `2/3`. -/
theorem dyadicEndpointGrowthThreshold_le
    {M R : ℕ} (hM : 1 ≤ M) :
    betaLower *
          adjacentHarmonicWeight (2 * M) (4 * ((2 ^ R) * M)) -
        (betaLower - massExponent) *
          averagingHarmonicWeight M ((2 ^ R) * M) ≤
      massExponent * (R : ℝ) * Real.log 2 +
        betaLower * Real.log 2 +
        (betaLower - massExponent) / (M : ℝ) := by
  have hshift := shiftedDyadicAdjacentHarmonicWeight_le_logTwo
    (R := R) hM
  have havg := dyadic_averagingHarmonicWeight_lower_logTwo
    (R := R) hM
  have hb : 0 ≤ betaLower := betaLower_pos.le
  have hgap : 0 ≤ betaLower - massExponent :=
    sub_nonneg.mpr massExponent_lt_betaLower.le
  have hshift' := mul_le_mul_of_nonneg_left hshift hb
  have havg' := mul_le_mul_of_nonneg_left havg hgap
  calc
    betaLower *
          adjacentHarmonicWeight (2 * M) (4 * ((2 ^ R) * M)) -
        (betaLower - massExponent) *
          averagingHarmonicWeight M ((2 ^ R) * M)
        ≤ betaLower * (((R : ℝ) + 1) * Real.log 2) -
            (betaLower - massExponent) *
              ((R : ℝ) * Real.log 2 - 1 / (M : ℝ)) := by linarith
    _ = massExponent * (R : ℝ) * Real.log 2 +
          betaLower * Real.log 2 +
          (betaLower - massExponent) / (M : ℝ) := by ring

/-- A directly checkable exact-log endpoint ratio implies the abstract
finite-window mean-growth hypothesis. -/
theorem massExponent_le_effectiveMeanGrowth_of_dyadic_log_ratio
    {T : ℕ} {h : StepSchedule T} (hh : IsNonnegativeSchedule h)
    {M R : ℕ} (hM : 1 ≤ M) (hR : 1 ≤ R)
    (h4N : 4 * ((2 ^ R) * M) ≤ longCount h)
    (hratio :
      massExponent * (R : ℝ) * Real.log 2 +
          betaLower * Real.log 2 +
          (betaLower - massExponent) / (M : ℝ) ≤
        Real.log (unresolvedMass h (2 * M) /
          unresolvedMass h (4 * ((2 ^ R) * M)))) :
    massExponent ≤ effectiveMeanGrowth h M ((2 ^ R) * M) := by
  have hMN : M < (2 ^ R) * M := by
    have hp : 2 ^ 1 ≤ 2 ^ R :=
      Nat.pow_le_pow_right (by omega : 0 < 2) hR
    norm_num at hp
    have hmpos : 0 < M := by omega
    nlinarith
  apply massExponent_le_effectiveMeanGrowth_of_log_ratio hh hM hMN h4N
  exact (dyadicEndpointGrowthThreshold_le (R := R) hM).trans hratio


/-- Unconditional form of the finite-window mechanism.  A valid dyadic
window either produces the desired functional rank, or its endpoint mass
ratio is strictly smaller than the exact exponential growth threshold. -/
theorem finiteWindowDyadic_functional_or_massRatio_lt
    {T Q : ℕ} (hQ : criticalTheta⁻¹ < (Q : ℝ))
    {h : StepSchedule T} (hh : IsNonnegativeSchedule h)
    {M R : ℕ} (hM : 2000 ≤ M) (hR : 1 ≤ R)
    (hQ2M : Q ≤ 2 * M)
    (h4N : 4 * ((2 ^ R) * M) ≤ longCount h)
    (hcut : CutoffConditions criticalP h (2 * M) (longCount h))
    (hexp : ∀ m : ℕ, M ≤ m →
      Real.exp (oneStepLyapunovConstant criticalP / (12 * m : ℕ)) ≤
        (8201 / 8200 : ℝ))
    (hwindow :
      fourBlockWindowError M ((2 ^ R) * M) < fourBlockFiniteMargin) :
    (∃ m ∈ Finset.Ico (M + 1) ((2 ^ R) * M + 1),
        (4 : ℝ)⁻¹ / unresolvedMass h (4 * m) <
          lowerBoundFunctional h) ∨
      unresolvedMass h (2 * M) /
          unresolvedMass h (4 * ((2 ^ R) * M)) <
        Real.exp
          (massExponent * (R : ℝ) * Real.log 2 +
            betaLower * Real.log 2 +
            (betaLower - massExponent) / (M : ℝ)) := by
  let E := massExponent * (R : ℝ) * Real.log 2 +
    betaLower * Real.log 2 +
    (betaLower - massExponent) / (M : ℝ)
  by_cases hgrowth : E ≤
      Real.log (unresolvedMass h (2 * M) /
        unresolvedMass h (4 * ((2 ^ R) * M)))
  · left
    have hMN : M < (2 ^ R) * M := by
      have hp : 2 ^ 1 ≤ 2 ^ R :=
        Nat.pow_le_pow_right (by omega : 0 < 2) hR
      norm_num at hp
      have hmpos : 0 < M := by omega
      nlinarith
    have hmean := massExponent_le_effectiveMeanGrowth_of_dyadic_log_ratio
      hh (by omega : 1 ≤ M) hR h4N (by simpa only [E] using hgrowth)
    exact finiteWindow_forces_small_scale hQ hh hM hMN hQ2M h4N hcut
      hexp hmean hwindow
  · right
    have hlog :
        Real.log (unresolvedMass h (2 * M) /
            unresolvedMass h (4 * ((2 ^ R) * M))) < E :=
      lt_of_not_ge hgrowth
    have hratioPos :
        0 < unresolvedMass h (2 * M) /
          unresolvedMass h (4 * ((2 ^ R) * M)) :=
      div_pos (unresolvedMass_pos hh _) (unresolvedMass_pos hh _)
    calc
      unresolvedMass h (2 * M) /
            unresolvedMass h (4 * ((2 ^ R) * M)) =
          Real.exp
            (Real.log (unresolvedMass h (2 * M) /
              unresolvedMass h (4 * ((2 ^ R) * M)))) := by
        rw [Real.exp_log hratioPos]
      _ < Real.exp E := Real.exp_lt_exp.mpr hlog
      _ = Real.exp
          (massExponent * (R : ℝ) * Real.log 2 +
            betaLower * Real.log 2 +
            (betaLower - massExponent) / (M : ℝ)) := rfl

end

end GDLowerBound.FourBlock
