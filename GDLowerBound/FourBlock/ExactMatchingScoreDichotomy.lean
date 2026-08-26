import GDLowerBound.FourBlock.ExactScoreSmallBranch

/-!
# Uniform exact-score dichotomy for the matching floor

The positive scalar cutoff in `ExactScoreCutoff` is useful for detecting the
critical state, but its small branch carries an exponential factor depending
on the rank.  For the normalized-floor argument the useful split is instead
at the negative normalized score `-1/2000000`.  Then the small branch gives a
uniform `1 / (4 D_{4m})` functional contribution, while failure of the small
branch is exactly the score floor needed by the matching-transfer theorem.
-/

namespace GDLowerBound.FourBlock

open GDLowerBound.Schedule GDLowerBound.RankAnalysis

noncomputable section

def matchingScoreCutoff : ℝ := -(1 / 2000000)

def SmallExactMatchingScoreRank {T : ℕ} (h : StepSchedule T) (m : ℕ) : Prop :=
  ∃ hq : 2 * (m + m) ≤ longCount h,
    outsideInLogScore (m + m) (scheduleFourBlockWeights h hq) /
        (2 * m) < matchingScoreCutoff

theorem smallExactMatchingScoreRank_iff {T m : ℕ} {h : StepSchedule T}
    (hq : 2 * (m + m) ≤ longCount h) :
    SmallExactMatchingScoreRank h m ↔
      outsideInLogScore (m + m) (scheduleFourBlockWeights h hq) /
        (2 * m) < matchingScoreCutoff := by
  constructor
  · rintro ⟨hq', hs⟩
    simpa only [Subsingleton.elim hq' hq] using hs
  · exact fun hs ↦ ⟨hq, hs⟩

/-- Failure of the uniform small-score branch is precisely the raw score
floor used by `scheduleIdealMatching_ge_floor_of_logScore`. -/
theorem outsideInLogScore_ge_matching_floor_of_not_small
    {T m : ℕ} {h : StepSchedule T} (hm : 0 < m)
    (hq : 2 * (m + m) ≤ longCount h)
    (hlarge : ¬ SmallExactMatchingScoreRank h m) :
    -(m : ℝ) / 1000000 ≤
      outsideInLogScore (m + m) (scheduleFourBlockWeights h hq) := by
  have hmR : (0 : ℝ) < 2 * m := by positivity
  have hnorm : matchingScoreCutoff ≤
      outsideInLogScore (m + m) (scheduleFourBlockWeights h hq) /
        (2 * m) := by
    rw [← not_lt]
    intro hs
    exact hlarge ((smallExactMatchingScoreRank_iff hq).2 hs)
  have hmul := mul_le_mul_of_nonneg_right hnorm hmR.le
  have hcancel :
      outsideInLogScore (m + m) (scheduleFourBlockWeights h hq) /
          (2 * m) * (2 * m) =
        outsideInLogScore (m + m) (scheduleFourBlockWeights h hq) := by
    field_simp [hmR.ne']
  rw [hcancel] at hmul
  norm_num [matchingScoreCutoff, div_eq_mul_inv] at hmul ⊢
  linarith

/-- A negative exact normalized score gives a rank-uniform functional
contribution: the exponential factor in the exact top-chain estimate is at
most one. -/
theorem quarter_div_unresolvedMass_lt_functional_of_smallMatchingScore
    {T m : ℕ} {h : StepSchedule T} (hh : IsNonnegativeSchedule h)
    (hm : 0 < m) (hq : 2 * (m + m) ≤ longCount h)
    (hsmall : SmallExactMatchingScoreRank h m) :
    (4 : ℝ)⁻¹ / unresolvedMass h (2 * (m + m)) <
      lowerBoundFunctional h := by
  have hs := (smallExactMatchingScoreRank_iff hq).1 hsmall
  have hmR : (0 : ℝ) < 2 * m := by positivity
  have hraw' := (div_lt_iff₀ hmR).1 hs
  have hraw :
      outsideInLogScore (m + m) (scheduleFourBlockWeights h hq) <
        (2 * m : ℕ) * matchingScoreCutoff := by
    simpa only [Nat.cast_mul, Nat.cast_ofNat, mul_comm] using hraw'
  have hchain := topChain_value_lower_of_outsideInLogScore_lt
    hh hm hq hraw
  let D := unresolvedMass h (2 * (m + m))
  let c := (2 * m : ℕ) * matchingScoreCutoff
  have hD : 0 < D := unresolvedMass_pos hh _
  have hc : c < 0 := by
    dsimp only [c, matchingScoreCutoff]
    have hmR' : (0 : ℝ) < (2 * m : ℕ) := by positivity
    exact mul_neg_of_pos_of_neg hmR' (by norm_num)
  have hexp : Real.exp (2 * c) ≤ 1 := by
    exact Real.exp_le_one_iff.mpr (by linarith)
  have hden : 4 * D * Real.exp (2 * c) ≤ 4 * D := by
    nlinarith [Real.exp_pos (2 * c)]
  have hinv : (4 * D)⁻¹ ≤ (4 * D * Real.exp (2 * c))⁻¹ := by
    exact (inv_le_inv₀ (by positivity : 0 < 4 * D)
      (by positivity : 0 < 4 * D * Real.exp (2 * c))).2 hden
  have hquarter : (4 : ℝ)⁻¹ / D = (4 * D)⁻¹ := by
    field_simp [hD.ne']
  rw [hquarter]
  exact hinv.trans_lt (hchain.trans_le
    (chainValue_le_functional h (topChain h (2 * (m + m)))))

/-- Uniform exact-score alternative at rank `4m`.  The critical-state lower
bound is deliberately supplied by the surrounding Ma--Chen cutoff interval;
this theorem closes only the independent score/matching split. -/
theorem exactMatchingScoreDichotomy
    {T m : ℕ} {h : StepSchedule T} (hh : IsNonnegativeSchedule h)
    (hm : 2000 ≤ m) (hq : 2 * (m + m) ≤ longCount h)
    (hzlo : (centralThetaLowerQ : ℝ) ≤
      zetaState h (2 * (m + m)))
    (hord : OrderedFourBlocks (schedulePrefixA h m)
      (schedulePrefixR h m) (schedulePrefixS h m))
    (hrlo : (1 / 20 : ℝ) ≤ schedulePrefixR h m) :
    (4 : ℝ)⁻¹ / unresolvedMass h (2 * (m + m)) <
        lowerBoundFunctional h ∨
      (centralMatchingFloorQ : ℝ) ≤
        fourBlockMatching (zetaState h (2 * (m + m)))
          (schedulePrefixA h m) (schedulePrefixR h m)
          (schedulePrefixS h m) := by
  have hm0 : 0 < m := by omega
  by_cases hsmall : SmallExactMatchingScoreRank h m
  · exact Or.inl
      (quarter_div_unresolvedMass_lt_functional_of_smallMatchingScore
        hh hm0 hq hsmall)
  · have hscore := outsideInLogScore_ge_matching_floor_of_not_small
      hm0 hq hsmall
    exact Or.inr (scheduleIdealMatching_ge_floor_of_logScore
      hh hm hq hzlo hord hrlo hscore)

end

end GDLowerBound.FourBlock
