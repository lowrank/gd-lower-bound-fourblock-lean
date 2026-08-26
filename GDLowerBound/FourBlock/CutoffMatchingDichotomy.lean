import GDLowerBound.FourBlock.ExactMatchingScoreDichotomy
import GDLowerBound.FourBlock.IdealPrefixCoordinates

/-!
# Coupling the Ma--Chen cutoff interval to exact four-block matching

This is the first global-composition interface.  Membership of `4m` in the
existing Ma--Chen cutoff interval supplies the critical-state lower bound;
the reciprocal-prefix construction supplies the ordered four-block domain;
the uniform exact-score theorem then leaves only the genuine `r ≥ 0.05`
case condition exposed.
-/

namespace GDLowerBound.FourBlock

open GDLowerBound.Schedule GDLowerBound.RankAnalysis

noncomputable section

theorem exactMatchingScoreDichotomy_of_cutoff
    {T lo m : ℕ} {h : StepSchedule T} (hh : IsNonnegativeSchedule h)
    (hm : 2000 ≤ m) (hlo : lo ≤ 4 * m)
    (hq : 4 * m ≤ longCount h)
    (hcut : CutoffConditions criticalP h lo (longCount h))
    (hrlo : (1 / 20 : ℝ) ≤ schedulePrefixR h m) :
    (4 : ℝ)⁻¹ / unresolvedMass h (4 * m) < lowerBoundFunctional h ∨
      (centralMatchingFloorQ : ℝ) ≤
        fourBlockMatching (zetaState h (4 * m))
          (schedulePrefixA h m) (schedulePrefixR h m)
          (schedulePrefixS h m) := by
  have hm0 : 0 < m := by omega
  have hq' : 2 * (m + m) ≤ longCount h := by omega
  have hstate := (hcut (4 * m) (Finset.mem_Icc.mpr ⟨hlo, hq⟩)).1
  have hzcrit : criticalTheta < zetaState h (2 * (m + m)) := by
    simpa only [criticalTheta, show 2 * (m + m) = 4 * m by omega] using hstate
  have htheta : (centralThetaLowerQ : ℝ) < criticalTheta := by
    rw [criticalTheta_eq]
    norm_num [centralThetaLowerQ, betaLower]
  have hzlo : (centralThetaLowerQ : ℝ) ≤
      zetaState h (2 * (m + m)) := (htheta.trans hzcrit).le
  have hord := schedulePrefix_ordered (h := h) hm0 hq
  have hdich := exactMatchingScoreDichotomy hh hm hq' hzlo hord hrlo
  simpa only [show 2 * (m + m) = 4 * m by omega] using hdich

end

end GDLowerBound.FourBlock
