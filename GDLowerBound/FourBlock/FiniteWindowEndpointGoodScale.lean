import GDLowerBound.FourBlock.FiniteWindowGoodScale
import GDLowerBound.FourBlock.FiniteWindowMeanGrowth

/-!
# Endpoint-mass finite-window interface

The sharper local conclusion now follows from two schedule-independent window
requirements (rank threshold and finite error) plus one explicit endpoint
unresolved-mass inequality.
-/

namespace GDLowerBound.FourBlock

open GDLowerBound.Schedule GDLowerBound.RankAnalysis

noncomputable section

theorem finiteWindowEndpointGrowth_forces_small_scale
    {T Q : ℕ} (hQ : criticalTheta⁻¹ < (Q : ℝ))
    {h : StepSchedule T} (hh : IsNonnegativeSchedule h)
    {M N : ℕ} (hM : 2000 ≤ M) (hMN : M < N)
    (hQ2M : Q ≤ 2 * M) (h4N : 4 * N ≤ longCount h)
    (hcut : CutoffConditions criticalP h (2 * M) (longCount h))
    (hexp : ∀ m : ℕ, M ≤ m →
      Real.exp (oneStepLyapunovConstant criticalP / (12 * m : ℕ)) ≤
        (8201 / 8200 : ℝ))
    (hwindow : fourBlockWindowError M N < fourBlockFiniteMargin)
    (hratio :
      betaLower * adjacentHarmonicWeight (2 * M) (4 * N) -
          (betaLower - massExponent) * averagingHarmonicWeight M N ≤
        Real.log (unresolvedMass h (2 * M) /
          unresolvedMass h (4 * N))) :
    ∃ m ∈ Finset.Ico (M + 1) (N + 1),
      (4 : ℝ)⁻¹ / unresolvedMass h (4 * m) < lowerBoundFunctional h := by
  have hgrowth := massExponent_le_effectiveMeanGrowth_of_log_ratio hh
    (by omega : 1 ≤ M) hMN h4N hratio
  exact finiteWindow_forces_small_scale hQ hh hM hMN hQ2M h4N hcut
    hexp hgrowth hwindow

end

end GDLowerBound.FourBlock
