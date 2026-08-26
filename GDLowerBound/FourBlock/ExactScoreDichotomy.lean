import GDLowerBound.FourBlock.ExactScoreSmallBranch

/-!
# Closed exact-score dichotomy at a four-block rank

This module packages the two exact-score branches into the interface needed
by the eventual global averaging argument.  No outside-in score hypothesis
is exposed: a small score directly contributes to the schedule functional,
while a non-small score supplies both the critical-state lower bound and the
ideal four-block matching floor.
-/

namespace GDLowerBound.FourBlock

open GDLowerBound.Schedule GDLowerBound.RankAnalysis

noncomputable section

/-- At every admissible rank `4m` with `m ≥ 2000`, either the top-chain
already gives the stated functional lower bound, or the same rank satisfies
the state and exact-matching hypotheses used by the local certificate. -/
theorem exactScoreDichotomy
    {T m : ℕ} {h : StepSchedule T} (hh : IsNonnegativeSchedule h)
    (hm : 2000 ≤ m) (hq : 2 * (m + m) ≤ longCount h)
    (hord : OrderedFourBlocks (schedulePrefixA h m)
      (schedulePrefixR h m) (schedulePrefixS h m))
    (hrlo : (1 / 20 : ℝ) ≤ schedulePrefixR h m) :
    (4 * unresolvedMass h (2 * (m + m)) *
        Real.exp ((4 * m : ℕ) * exactScoreCutoff))⁻¹ <
        lowerBoundFunctional h ∨
      (criticalTheta < zetaState h (2 * (m + m)) ∧
        (centralMatchingFloorQ : ℝ) ≤
          fourBlockMatching (zetaState h (2 * (m + m)))
            (schedulePrefixA h m) (schedulePrefixR h m)
            (schedulePrefixS h m)) := by
  by_cases hsmall : SmallExactScoreRank h m
  · exact Or.inl (functional_lower_of_smallExactScore hh hm hq hsmall)
  · exact Or.inr ⟨
      criticalTheta_lt_zeta_of_not_smallExactScore hh hm hq hsmall,
      scheduleIdealMatching_ge_floor_of_not_smallExactScore
        hh hm hq hord hrlo hsmall⟩

end

end GDLowerBound.FourBlock
