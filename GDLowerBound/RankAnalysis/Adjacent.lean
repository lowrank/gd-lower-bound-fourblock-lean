import GDLowerBound.Schedule.TailMass
import GDLowerBound.RankAnalysis.Lyapunov

namespace GDLowerBound
namespace RankAnalysis

open scoped BigOperators
open Schedule

noncomputable section

/-- The ranked excess `a_q`, with the manuscript's one-based indexing.
Outside the available positive ranks this totalized definition is zero. -/
def rankedExcessOne {T : ℕ} (h : StepSchedule T) (q : ℕ) : ℝ :=
  (rankedExcesses h).getD (q - 1) 0

/-- The adjacent unresolved-mass ratio `D_(q-1) / D_q`. -/
def massRatio {T : ℕ} (h : StepSchedule T) (q : ℕ) : ℝ :=
  unresolvedMass h (q - 1) / unresolvedMass h q

/-- The relative mass increment `ν_q = q a_q / D_q`. -/
def relativeMassIncrement {T : ℕ} (h : StepSchedule T) (q : ℕ) : ℝ :=
  (q : ℝ) * rankedExcessOne h q / unresolvedMass h q

/-- The reciprocal prefix `∑_{s=1}^q 1/a_s`. -/
def reciprocalPrefix {T : ℕ} (h : StepSchedule T) (q : ℕ) : ℝ :=
  ∑ i ∈ Finset.range q, (rankedExcessOne h (i + 1))⁻¹

/-- The matching-density state
`zeta_q = D_q / q^2 * ∑_{s=1}^q 1/a_s`. -/
def zetaState {T : ℕ} (h : StepSchedule T) (q : ℕ) : ℝ :=
  unresolvedMass h q / (q : ℝ) ^ 2 * reciprocalPrefix h q

private lemma rank_sub_lt_longCount {T : ℕ} {h : StepSchedule T}
    {q : ℕ} (hq0 : 1 ≤ q) (hqr : q ≤ longCount h) :
    q - 1 < longCount h := by
  omega

/-- Within the valid one-based range, `rankedExcessOne` agrees with the
existing zero-based finite-rank accessor. -/
theorem rankedExcessOne_eq_rankedExcessAt {T : ℕ} (h : StepSchedule T)
    {q : ℕ} (hq0 : 1 ≤ q) (hqr : q ≤ longCount h) :
    rankedExcessOne h q =
      rankedExcessAt h ⟨q - 1, rank_sub_lt_longCount hq0 hqr⟩ := by
  have hi : q - 1 < (rankedExcesses h).length := by
    simpa only [rankedExcesses_length] using
      (rank_sub_lt_longCount (h := h) hq0 hqr)
  simpa [rankedExcessOne, rankedExcessAt] using
    (List.getD_eq_get
      (l := rankedExcesses h) (d := (0 : ℝ)) ⟨q - 1, hi⟩)

theorem rankedExcessOne_pos {T : ℕ} (h : StepSchedule T)
    {q : ℕ} (hq0 : 1 ≤ q) (hqr : q ≤ longCount h) :
    0 < rankedExcessOne h q := by
  rw [rankedExcessOne_eq_rankedExcessAt h hq0 hqr]
  exact Schedule.rankedExcessAt_pos h _

theorem rankedExcessOne_antitone_adjacent {T : ℕ} (h : StepSchedule T)
    {q : ℕ} (hq0 : 1 ≤ q) (hqr : q < longCount h) :
    rankedExcessOne h (q + 1) ≤ rankedExcessOne h q := by
  have hq_le : q ≤ longCount h := Nat.le_of_lt hqr
  have hq1_le : q + 1 ≤ longCount h := by omega
  rw [rankedExcessOne_eq_rankedExcessAt h hq0 hq_le]
  rw [rankedExcessOne_eq_rankedExcessAt h (by omega) hq1_le]
  apply rankedExcessAt_antitone h
  simp only [Fin.mk_le_mk]
  omega

/-- Removing rank `q` gives `D_(q-1) = a_q + D_q`. -/
theorem unresolvedMass_rank_recurrence {T : ℕ} (h : StepSchedule T)
    {q : ℕ} (hq0 : 1 ≤ q) (hqr : q ≤ longCount h) :
    unresolvedMass h (q - 1) =
      rankedExcessOne h q + unresolvedMass h q := by
  have hi := rank_sub_lt_longCount (h := h) hq0 hqr
  have hrec := unresolvedMass_recurrence h hi
  rw [rankedExcessOne_eq_rankedExcessAt h hq0 hqr]
  simpa only [Nat.sub_add_cancel hq0] using hrec

theorem relativeMassIncrement_pos {T : ℕ} {h : StepSchedule T}
    (hh : IsNonnegativeSchedule h) {q : ℕ}
    (hq0 : 1 ≤ q) (hqr : q ≤ longCount h) :
    0 < relativeMassIncrement h q := by
  unfold relativeMassIncrement
  positivity [rankedExcessOne_pos h hq0 hqr, unresolvedMass_pos hh q]

/-- Dividing `ν_q` by its positive rank recovers `a_q / D_q`. -/
theorem relativeMassIncrement_div_rank {T : ℕ} (h : StepSchedule T)
    {q : ℕ} (hq0 : 1 ≤ q) :
    relativeMassIncrement h q / (q : ℝ) =
      rankedExcessOne h q / unresolvedMass h q := by
  have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (by omega : 0 < q))
  unfold relativeMassIncrement
  field_simp [hqR]

/-- Equation `eq:one-rank-mass-ratio`. -/
theorem oneRankMassRatio {T : ℕ} {h : StepSchedule T}
    (hh : IsNonnegativeSchedule h) {q : ℕ}
    (hq0 : 1 ≤ q) (hqr : q ≤ longCount h) :
    massRatio h q =
      1 + relativeMassIncrement h q / (q : ℝ) := by
  unfold massRatio
  rw [relativeMassIncrement_div_rank h hq0]
  rw [unresolvedMass_rank_recurrence h hq0 hqr]
  have hD0 := unresolvedMass_pos hh q
  field_simp [ne_of_gt hD0]
  ring

private lemma prod_adjacent_div
    {f : ℕ → ℝ}
    (hf : ∀ i, f i ≠ 0)
    {k r : ℕ} (hkr : k ≤ r) :
    f k / f r =
      ∏ s ∈ Finset.Ico (k + 1) (r + 1), f (s - 1) / f s := by
  induction r, hkr using Nat.le_induction with
  | base => simp [hf]
  | succ r hkr ih =>
      rw [Finset.prod_Ico_succ_top (by omega)]
      rw [← ih]
      simp only [Nat.add_sub_cancel]
      field_simp [hf]

/-- Equation `eq:mass-product`, including the empty product when `k = r`. -/
theorem massProduct {T : ℕ} {h : StepSchedule T}
    (hh : IsNonnegativeSchedule h) {k : ℕ}
    (hkr : k ≤ longCount h) :
    unresolvedMass h k / cappedMass h =
      ∏ s ∈ Finset.Ico (k + 1) (longCount h + 1),
        (1 + relativeMassIncrement h s / (s : ℝ)) := by
  rw [← unresolvedMass_longCount h]
  calc
    unresolvedMass h k / unresolvedMass h (longCount h) =
        ∏ s ∈ Finset.Ico (k + 1) (longCount h + 1),
          unresolvedMass h (s - 1) / unresolvedMass h s :=
      prod_adjacent_div (fun i ↦ (unresolvedMass_pos hh i).ne') hkr
    _ = ∏ s ∈ Finset.Ico (k + 1) (longCount h + 1),
          (1 + relativeMassIncrement h s / (s : ℝ)) := by
      apply Finset.prod_congr rfl
      intro s hs
      have hsIco := Finset.mem_Ico.mp hs
      simpa only [massRatio] using
        oneRankMassRatio hh (q := s) (by omega) (by omega)

/-- Equation `eq:mass-increment-transition`. -/
theorem massIncrementTransition {T : ℕ} {h : StepSchedule T}
    (hh : IsNonnegativeSchedule h) {q : ℕ}
    (hq0 : 1 ≤ q) (hqr : q < longCount h) :
    relativeMassIncrement h q / (q : ℝ) *
        (1 + relativeMassIncrement h (q + 1) / (q + 1 : ℕ)) ≥
      relativeMassIncrement h (q + 1) / (q + 1 : ℕ) := by
  have hq_le : q ≤ longCount h := Nat.le_of_lt hqr
  have hq1_le : q + 1 ≤ longCount h := by omega
  rw [relativeMassIncrement_div_rank h hq0]
  rw [relativeMassIncrement_div_rank h (q := q + 1) (by omega)]
  have hDq0 := unresolvedMass_pos hh q
  have hDq10 := unresolvedMass_pos hh (q + 1)
  have hrec := unresolvedMass_rank_recurrence h (q := q + 1) (by omega) hq1_le
  have hrec' :
      unresolvedMass h q =
        rankedExcessOne h (q + 1) + unresolvedMass h (q + 1) := by
    simpa using hrec
  have hmono := rankedExcessOne_antitone_adjacent h hq0 hqr
  have hratio :
      1 + rankedExcessOne h (q + 1) / unresolvedMass h (q + 1) =
        unresolvedMass h q / unresolvedMass h (q + 1) := by
    rw [hrec']
    field_simp [ne_of_gt hDq10]
    ring
  rw [hratio]
  have hcollapse :
      rankedExcessOne h q / unresolvedMass h q *
          (unresolvedMass h q / unresolvedMass h (q + 1)) =
        rankedExcessOne h q / unresolvedMass h (q + 1) := by
    field_simp [ne_of_gt hDq0, ne_of_gt hDq10]
  rw [hcollapse]
  exact div_le_div_of_nonneg_right hmono hDq10.le

private lemma transition_implies_bound
    {Q u v : ℝ}
    (hQ0 : 0 < Q)
    (htransition : u / Q * (1 + v / (Q + 1)) ≥ v / (Q + 1))
    (hsmall : u < Q) :
    v ≤ (Q + 1) * u / (Q - u) := by
  have hQ10 : 0 < Q + 1 := by linarith
  have hden0 : 0 < Q * (Q + 1) := mul_pos hQ0 hQ10
  have hnormalize :
      u / Q * (1 + v / (Q + 1)) - v / (Q + 1) =
        ((Q + 1) * u - v * (Q - u)) / (Q * (Q + 1)) := by
    field_simp [ne_of_gt hQ0, ne_of_gt hQ10]
    ring
  have hdiff :
      0 ≤ u / Q * (1 + v / (Q + 1)) - v / (Q + 1) :=
    sub_nonneg.mpr htransition
  rw [hnormalize] at hdiff
  have hnumerator := (le_div_iff₀ hden0).mp hdiff
  apply (le_div_iff₀ (sub_pos.mpr hsmall)).2
  nlinarith

/-- Equation `eq:mass-increment-bound`. -/
theorem massIncrementBound {T : ℕ} {h : StepSchedule T}
    (hh : IsNonnegativeSchedule h) {q : ℕ}
    (hq0 : 1 ≤ q) (hqr : q < longCount h)
    (hsmall : relativeMassIncrement h q < (q : ℝ)) :
    relativeMassIncrement h (q + 1) ≤
      ((q : ℝ) + 1) * relativeMassIncrement h q /
        ((q : ℝ) - relativeMassIncrement h q) := by
  apply transition_implies_bound (Q := (q : ℝ))
  · exact_mod_cast (by omega : 0 < q)
  · simpa only [Nat.cast_add, Nat.cast_one] using
      massIncrementTransition hh hq0 hqr
  · exact hsmall

@[simp]
theorem reciprocalPrefix_zero {T : ℕ} (h : StepSchedule T) :
    reciprocalPrefix h 0 = 0 := by
  simp [reciprocalPrefix]

/-- Adding one rank adds the reciprocal of exactly the new ranked excess. -/
theorem reciprocalPrefix_succ {T : ℕ} (h : StepSchedule T) (q : ℕ) :
    reciprocalPrefix h (q + 1) =
      reciprocalPrefix h q + (rankedExcessOne h (q + 1))⁻¹ := by
  simp [reciprocalPrefix, Finset.sum_range_succ]

/-- Equation `eq:zeta-recursion`. -/
theorem zetaRecursion {T : ℕ} {h : StepSchedule T}
    (hh : IsNonnegativeSchedule h) {q : ℕ}
    (hq0 : 1 ≤ q) (hqr : q < longCount h) :
    zetaState h (q + 1) =
      (q : ℝ) ^ 2 * zetaState h q /
          (((q : ℝ) + 1) *
            ((q : ℝ) + 1 + relativeMassIncrement h (q + 1))) +
        1 / (relativeMassIncrement h (q + 1) * ((q : ℝ) + 1)) := by
  have hq_le : q ≤ longCount h := Nat.le_of_lt hqr
  have hq1_le : q + 1 ≤ longCount h := by omega
  have hqR0 : 0 < (q : ℝ) := by exact_mod_cast (by omega : 0 < q)
  have hq1R0 : 0 < (q : ℝ) + 1 := by linarith
  have hDq0 := unresolvedMass_pos hh q
  have hDq10 := unresolvedMass_pos hh (q + 1)
  have ha0 := rankedExcessOne_pos h (q := q + 1) (by omega) hq1_le
  have hnu0 := relativeMassIncrement_pos hh (q := q + 1) (by omega) hq1_le
  have hsum0 :
      0 < (q : ℝ) + 1 + relativeMassIncrement h (q + 1) := by
    linarith
  have hrec := unresolvedMass_rank_recurrence h (q := q + 1) (by omega) hq1_le
  have hrec' :
      unresolvedMass h q =
        rankedExcessOne h (q + 1) + unresolvedMass h (q + 1) := by
    simpa using hrec
  unfold zetaState
  rw [reciprocalPrefix_succ]
  unfold relativeMassIncrement
  simp only [Nat.cast_add, Nat.cast_one]
  rw [hrec']
  field_simp [ne_of_gt hqR0, ne_of_gt hq1R0, ne_of_gt hDq0,
    ne_of_gt hDq10, ne_of_gt ha0, ne_of_gt hnu0, ne_of_gt hsum0]
  ring

end
end RankAnalysis
end GDLowerBound
