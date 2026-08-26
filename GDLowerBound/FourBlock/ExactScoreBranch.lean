import GDLowerBound.FourBlock.ExactScoreCutoff
import GDLowerBound.FourBlock.ScheduleMatchingFloor

/-!
# The exact small-score / large-score rank alternative

At a four-block rank `4m`, the small branch is expressed directly in terms
of the normalized outside-in logarithmic score.  Failure of this branch
forces the critical-state lower bound and, simultaneously, the matching
floor required by the robust local certificate.
-/

namespace GDLowerBound.FourBlock

open GDLowerBound.Schedule GDLowerBound.RankAnalysis

noncomputable section

def exactScoreCutoff : ℝ := 1 / 10000000

/-- A proof-independent predicate for the exact small-score alternative at
the four-block rank `4m`. -/
def SmallExactScoreRank {T : ℕ} (h : StepSchedule T) (m : ℕ) : Prop :=
  ∃ hq : 2 * (m + m) ≤ longCount h,
    outsideInLogScore (m + m) (scheduleFourBlockWeights h hq) /
        (2 * m) < exactScoreCutoff

theorem smallExactScoreRank_iff {T m : ℕ} {h : StepSchedule T}
    (hq : 2 * (m + m) ≤ longCount h) :
    SmallExactScoreRank h m ↔
      outsideInLogScore (m + m) (scheduleFourBlockWeights h hq) /
        (2 * m) < exactScoreCutoff := by
  constructor
  · rintro ⟨hq', hs⟩
    simpa only [Subsingleton.elim hq' hq] using hs
  · exact fun hs ↦ ⟨hq, hs⟩

theorem exactScoreCutoff_le_of_not_small
    {T m : ℕ} {h : StepSchedule T}
    (hq : 2 * (m + m) ≤ longCount h)
    (hlarge : ¬ SmallExactScoreRank h m) :
    exactScoreCutoff ≤
      outsideInLogScore (m + m) (scheduleFourBlockWeights h hq) /
        (2 * m) := by
  rw [← not_lt]
  intro hsmall
  exact hlarge ((smallExactScoreRank_iff hq).2 hsmall)

/-- The exact scalar cutoff turns failure of the small-score alternative
into the strict critical-state inequality needed by the Lyapunov drift. -/
theorem criticalTheta_lt_zeta_of_not_smallExactScore
    {T m : ℕ} {h : StepSchedule T} (hh : IsNonnegativeSchedule h)
    (hm : 2000 ≤ m) (hq : 2 * (m + m) ≤ longCount h)
    (hlarge : ¬ SmallExactScoreRank h m) :
    criticalTheta < zetaState h (2 * (m + m)) := by
  by_contra hnot
  have hzeta : zetaState h (2 * (m + m)) ≤ criticalTheta :=
    le_of_not_gt hnot
  have hsmall := scheduleOutsideInLogScore_average_lt_cutoff_of_zeta_le
    hh hm hq hzeta
  apply hlarge
  refine (smallExactScoreRank_iff hq).2 ?_
  simpa only [exactScoreCutoff] using hsmall

theorem outsideInLogScore_nonneg_of_not_smallExactScore
    {T m : ℕ} {h : StepSchedule T}
    (hm : 2000 ≤ m) (hq : 2 * (m + m) ≤ longCount h)
    (hlarge : ¬ SmallExactScoreRank h m) :
    0 ≤ outsideInLogScore (m + m) (scheduleFourBlockWeights h hq) := by
  have hm0 : 0 < m := by omega
  have hmR : (0 : ℝ) < 2 * m := by positivity
  have hnorm := exactScoreCutoff_le_of_not_small hq hlarge
  have hcut : (0 : ℝ) < exactScoreCutoff := by
    norm_num [exactScoreCutoff]
  have hpos : 0 <
      outsideInLogScore (m + m) (scheduleFourBlockWeights h hq) /
        (2 * m) := hcut.trans_le hnorm
  have hmul := mul_pos hpos hmR
  have hcancel :
      outsideInLogScore (m + m) (scheduleFourBlockWeights h hq) /
          (2 * m) * (2 * m) =
        outsideInLogScore (m + m) (scheduleFourBlockWeights h hq) := by
    field_simp [hmR.ne']
  rw [hcancel] at hmul
  exact hmul.le

/-- The former free score hypothesis is now a consequence of the exact
large-score branch. -/
theorem scheduleIdealMatching_ge_floor_of_not_smallExactScore
    {T m : ℕ} {h : StepSchedule T} (hh : IsNonnegativeSchedule h)
    (hm : 2000 ≤ m) (hq : 2 * (m + m) ≤ longCount h)
    (hord : OrderedFourBlocks (schedulePrefixA h m)
      (schedulePrefixR h m) (schedulePrefixS h m))
    (hrlo : (1 / 20 : ℝ) ≤ schedulePrefixR h m)
    (hlarge : ¬ SmallExactScoreRank h m) :
    (centralMatchingFloorQ : ℝ) ≤
      fourBlockMatching (zetaState h (2 * (m + m)))
        (schedulePrefixA h m) (schedulePrefixR h m)
        (schedulePrefixS h m) := by
  have hzeta := criticalTheta_lt_zeta_of_not_smallExactScore
    hh hm hq hlarge
  have hzlo : (centralThetaLowerQ : ℝ) ≤
      zetaState h (2 * (m + m)) := by
    have hcritical : (centralThetaLowerQ : ℝ) < criticalTheta := by
      rw [criticalTheta_eq]
      norm_num [centralThetaLowerQ, betaLower]
    exact hcritical.trans hzeta |>.le
  have hscore0 := outsideInLogScore_nonneg_of_not_smallExactScore
    hm hq hlarge
  have hscore : -(m : ℝ) / 1000000 ≤
      outsideInLogScore (m + m) (scheduleFourBlockWeights h hq) := by
    have hmnonneg : (0 : ℝ) ≤ m := by positivity
    exact (div_nonpos_of_nonpos_of_nonneg (by linarith) (by norm_num)).trans hscore0
  exact scheduleIdealMatching_ge_floor_of_logScore hh hm hq hzlo hord hrlo hscore

end

end GDLowerBound.FourBlock
