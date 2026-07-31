import GDLowerBound.RankAnalysis.Adjacent

namespace GDLowerBound.RankAnalysis

open scoped BigOperators
open Schedule

noncomputable section

/-- The one-based ranked excess sequence is antitone throughout its valid
range, not just at adjacent ranks. -/
theorem rankedExcessOne_antitone {T : ℕ} (h : StepSchedule T)
    {a b : ℕ} (ha : 1 ≤ a) (hab : a ≤ b) (hb : b ≤ longCount h) :
    rankedExcessOne h b ≤ rankedExcessOne h a := by
  have har : a ≤ longCount h := hab.trans hb
  rw [rankedExcessOne_eq_rankedExcessAt h ha har]
  rw [rankedExcessOne_eq_rankedExcessAt h (ha.trans hab) hb]
  apply rankedExcessAt_antitone h
  simp only [Fin.mk_le_mk]
  omega

/-- The smallest selected excess times the reciprocal prefix is at most the
number of selected ranks. -/
theorem rankedExcess_mul_reciprocalPrefix_le {T : ℕ}
    (h : StepSchedule T) {q : ℕ} (hqr : q ≤ longCount h) :
    rankedExcessOne h q * reciprocalPrefix h q ≤ (q : ℝ) := by
  unfold reciprocalPrefix
  rw [Finset.mul_sum]
  calc
    ∑ i ∈ Finset.range q,
        rankedExcessOne h q * (rankedExcessOne h (i + 1))⁻¹ ≤
        ∑ _i ∈ Finset.range q, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro i hi
      have hiq : i + 1 ≤ q := by
        exact Finset.mem_range.mp hi
      have hai : 0 < rankedExcessOne h (i + 1) :=
        rankedExcessOne_pos h (by omega) (hiq.trans hqr)
      have hmono : rankedExcessOne h q ≤ rankedExcessOne h (i + 1) :=
        rankedExcessOne_antitone h (by omega) hiq hqr
      rw [← div_eq_mul_inv]
      exact (div_le_one hai).2 hmono
    _ = (q : ℝ) := by simp

/-- Equation `eq:zeta-density-bound`: the matching-density state and the
relative mass increment have product at most one. -/
theorem zeta_mul_relativeMassIncrement_le_one
    {T : ℕ} {h : StepSchedule T} (hh : IsNonnegativeSchedule h)
    {q : ℕ} (hq₀ : 1 ≤ q) (hqr : q ≤ longCount h) :
    zetaState h q * relativeMassIncrement h q ≤ 1 := by
  have hD : 0 < unresolvedMass h q := unresolvedMass_pos hh q
  have hqR : 0 < (q : ℝ) := by exact_mod_cast (by omega : 0 < q)
  have hsum := rankedExcess_mul_reciprocalPrefix_le h hqr
  have hidentity :
      zetaState h q * relativeMassIncrement h q =
        (rankedExcessOne h q * reciprocalPrefix h q) / (q : ℝ) := by
    unfold zetaState relativeMassIncrement
    field_simp [hD.ne', hqR.ne']
  rw [hidentity]
  exact (div_le_one hqR).2 hsum

end
end GDLowerBound.RankAnalysis
