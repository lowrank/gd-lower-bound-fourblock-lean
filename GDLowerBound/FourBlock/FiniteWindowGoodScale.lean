import GDLowerBound.FourBlock.AveragedGoodScale
import GDLowerBound.FourBlock.FiniteWindowRigidityErrors

/-!
# Good-scale extraction from a schedule-independent window certificate

This is the public finite-window interface for the sharper route.  The only
remaining error check depends on `M` and `N`, not on the schedule.
-/

namespace GDLowerBound.FourBlock

open GDLowerBound.Schedule GDLowerBound.RankAnalysis

noncomputable section

theorem finiteWindow_forces_small_scale
    {T Q : ℕ} (hQ : criticalTheta⁻¹ < (Q : ℝ))
    {h : StepSchedule T} (hh : IsNonnegativeSchedule h)
    {M N : ℕ} (hM : 2000 ≤ M) (hMN : M < N)
    (hQ2M : Q ≤ 2 * M) (h4N : 4 * N ≤ longCount h)
    (hcut : CutoffConditions criticalP h (2 * M) (longCount h))
    (hexp : ∀ m : ℕ, M ≤ m →
      Real.exp (oneStepLyapunovConstant criticalP / (12 * m : ℕ)) ≤
        (8201 / 8200 : ℝ))
    (hgrowth : massExponent ≤ effectiveMeanGrowth h M N)
    (hwindow : fourBlockWindowError M N < fourBlockFiniteMargin) :
    ∃ m ∈ Finset.Ico (M + 1) (N + 1),
      (4 : ℝ)⁻¹ / unresolvedMass h (4 * m) < lowerBoundFunctional h := by
  have hbudget := normalizedErrorBudget_le_window hQ hh
    (by omega : 1 ≤ M) hMN hQ2M h4N hcut
  exact normalizedAveraging_forces_small_scale hQ hh hM hMN hQ2M h4N
    hcut hexp hgrowth (hbudget.trans_lt hwindow)

end

end GDLowerBound.FourBlock
