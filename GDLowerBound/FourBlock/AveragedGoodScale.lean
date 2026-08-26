import GDLowerBound.FourBlock.NormalizedAveragingComposition

/-!
# A good scale forced by normalized averaging

The pointwise four-block theorem gives, at every sampled scale, either the
desired small-functional branch or an energy strictly above the robust local
gap.  The normalized global estimate makes the latter alternative impossible
at every scale simultaneously.  This file records that strict weighted-
average contradiction.
-/

namespace GDLowerBound.FourBlock

open scoped BigOperators
open GDLowerBound.Schedule GDLowerBound.RankAnalysis

noncomputable section

/-- The normalized four-block estimate forces at least one sampled scale onto
the small-functional branch of `schedulePointwiseDichotomy`. -/
theorem normalizedAveraging_forces_small_scale
    {T Q : ℕ} (hQ : criticalTheta⁻¹ < (Q : ℝ))
    {h : StepSchedule T} (hh : IsNonnegativeSchedule h)
    {M N : ℕ} (hM : 2000 ≤ M) (hMN : M < N)
    (hQ2M : Q ≤ 2 * M) (h4N : 4 * N ≤ longCount h)
    (hcut : CutoffConditions criticalP h (2 * M) (longCount h))
    (hexp : ∀ m : ℕ, M ≤ m →
      Real.exp (oneStepLyapunovConstant criticalP / (12 * m : ℕ)) ≤
        (8201 / 8200 : ℝ))
    (hgrowth : massExponent ≤ effectiveMeanGrowth h M N)
    (herrors :
      squareWeightSum * normalizedJointRigidityError h M N +
          defectSlackCoefficient * normalizedDefectRigidityError h M N +
          normalizedScheduleAveragingError M N < fourBlockFiniteMargin) :
    ∃ m ∈ Finset.Ico (M + 1) (N + 1),
      (4 : ℝ)⁻¹ / unresolvedMass h (4 * m) < lowerBoundFunctional h := by
  have hH : 0 < averagingHarmonicWeight M N :=
    averagingHarmonicWeight_pos (by omega) hMN
  have havg := normalizedAveragedScheduleEnergy_lt_robustLocalGap
    hQ hh (by omega : 8 ≤ M) hMN hQ2M h4N hcut hgrowth herrors
  by_contra hsmall
  push Not at hsmall
  have hlarge : ∀ m ∈ Finset.Ico (M + 1) (N + 1),
      robustLocalGap < scheduleDilationEnergy h m + scheduleControlError m := by
    intro m hm
    have hmIco := Finset.mem_Ico.mp hm
    have hMm : M ≤ m := by omega
    have hmN : m ≤ N := by omega
    have hpoint := schedulePointwiseDichotomy hQ hh
      (by omega : 2000 ≤ m)
      (by omega : Q ≤ 2 * m)
      (by omega : 2 * M ≤ 2 * m)
      (by omega : 4 * m ≤ longCount h)
      hcut (hexp m hMm)
    exact hpoint.resolve_left (not_lt_of_ge (hsmall m hm))
  have hwindow : (Finset.Ico (M + 1) (N + 1)).Nonempty := by
    refine ⟨M + 1, Finset.mem_Ico.mpr ⟨le_rfl, ?_⟩⟩
    omega
  have hsum :
      (∑ m ∈ Finset.Ico (M + 1) (N + 1),
          robustLocalGap / (m : ℝ)) <
        ∑ m ∈ Finset.Ico (M + 1) (N + 1),
          (scheduleDilationEnergy h m + scheduleControlError m) / (m : ℝ) := by
    apply Finset.sum_lt_sum_of_nonempty hwindow
    intro m hm
    have hmIco := Finset.mem_Ico.mp hm
    have hmpos : (0 : ℝ) < m := by
      exact_mod_cast (show 0 < m by omega)
    exact div_lt_div_of_pos_right (hlarge m hm) hmpos
  have hleft :
      (∑ m ∈ Finset.Ico (M + 1) (N + 1),
          robustLocalGap / (m : ℝ)) =
        robustLocalGap * averagingHarmonicWeight M N := by
    unfold averagingHarmonicWeight
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro m _
    ring
  rw [hleft] at hsum
  have hsumDiv := div_lt_div_of_pos_right hsum hH
  have hgapAverage :
      robustLocalGap <
        (∑ m ∈ Finset.Ico (M + 1) (N + 1),
          (scheduleDilationEnergy h m + scheduleControlError m) / (m : ℝ)) /
            averagingHarmonicWeight M N := by
    simpa [hH.ne'] using hsumDiv
  exact lt_asymm havg hgapAverage

end

end GDLowerBound.FourBlock
