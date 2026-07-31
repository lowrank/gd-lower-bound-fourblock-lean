import GDLowerBound.Schedule.Ranking

namespace GDLowerBound.Schedule

open scoped BigOperators

/-- Time carrying the `q`-th largest positive excess (zero-based index). -/
noncomputable def rankedTimeAt {T : ℕ} (h : StepSchedule T)
    (q : Fin (longCount h)) : Fin T :=
  (rankedTimes h).get
    ⟨q, by simpa only [rankedTimes_length] using q.isLt⟩

/-- The `q`-th largest positive excess (zero-based index). -/
noncomputable def rankedExcessAt {T : ℕ} (h : StepSchedule T)
    (q : Fin (longCount h)) : ℝ :=
  (rankedExcesses h).get
    ⟨q, by simpa only [rankedExcesses_length] using q.isLt⟩

theorem rankedTimeAt_mem {T : ℕ} (h : StepSchedule T)
    (q : Fin (longCount h)) : rankedTimeAt h q ∈ rankedTimes h := by
  exact List.get_mem _ _

theorem rankedTimeAt_mem_longTimes {T : ℕ} (h : StepSchedule T)
    (q : Fin (longCount h)) : rankedTimeAt h q ∈ longTimes h := by
  exact (mem_rankedTimes_iff h _).mp (rankedTimeAt_mem h q)

theorem rankedExcessAt_eq {T : ℕ} (h : StepSchedule T)
    (q : Fin (longCount h)) :
    rankedExcessAt h q = excess h (rankedTimeAt h q) := by
  simp [rankedExcessAt, rankedTimeAt, rankedExcesses]

theorem rankedExcessAt_pos {T : ℕ} (h : StepSchedule T)
    (q : Fin (longCount h)) : 0 < rankedExcessAt h q := by
  rw [rankedExcessAt_eq, excess_pos_iff]
  exact (mem_longTimes_iff h _).mp (rankedTimeAt_mem_longTimes h q)

/-- The ranked excess sequence is antitone in its finite rank. -/
theorem rankedExcessAt_antitone {T : ℕ} (h : StepSchedule T) :
    Antitone (rankedExcessAt h) := by
  intro i j hij
  unfold rankedExcessAt
  apply (rankedExcesses_pairwise_ge h).rel_get_of_le
  exact hij

/-- The unresolved mass `D_q`: capped mass plus the excesses below rank `q`.
The definition accepts every natural `q`; after the last rank it is simply
the capped mass. -/
noncomputable def unresolvedMass {T : ℕ} (h : StepSchedule T) (q : ℕ) : ℝ :=
  cappedMass h + (rankedExcesses h |>.drop q).sum

theorem rankedExcesses_drop_sum_nonneg {T : ℕ} (h : StepSchedule T)
    (q : ℕ) : 0 ≤ (rankedExcesses h |>.drop q).sum := by
  apply List.sum_nonneg
  intro a ha
  exact (rankedExcesses_pos h (List.mem_of_mem_drop ha)).le

theorem unresolvedMass_pos {T : ℕ} {h : StepSchedule T}
    (hh : IsNonnegativeSchedule h) (q : ℕ) : 0 < unresolvedMass h q := by
  have hB := cappedMass_pos hh
  have htail := rankedExcesses_drop_sum_nonneg h q
  unfold unresolvedMass
  linarith

theorem unresolvedMass_nonneg {T : ℕ} {h : StepSchedule T}
    (hh : IsNonnegativeSchedule h) (q : ℕ) : 0 ≤ unresolvedMass h q :=
  (unresolvedMass_pos hh q).le

@[simp]
theorem unresolvedMass_zero {T : ℕ} (h : StepSchedule T) :
    unresolvedMass h 0 = cappedMass h + (rankedExcesses h).sum := by
  simp [unresolvedMass]

theorem unresolvedMass_zero_eq_total {T : ℕ} (h : StepSchedule T) :
    unresolvedMass h 0 = 1 + ∑ t, h t := by
  rw [unresolvedMass_zero, rankedExcesses_sum]
  exact (total_mass_decomposition h).symm

@[simp]
theorem unresolvedMass_longCount {T : ℕ} (h : StepSchedule T) :
    unresolvedMass h (longCount h) = cappedMass h := by
  have hlen : longCount h = (rankedExcesses h).length :=
    (rankedExcesses_length h).symm
  rw [unresolvedMass, hlen, List.drop_length]
  simp

theorem unresolvedMass_eq_cappedMass_of_longCount_le {T : ℕ}
    (h : StepSchedule T) {q : ℕ} (hq : longCount h ≤ q) :
    unresolvedMass h q = cappedMass h := by
  simp [unresolvedMass, List.drop_eq_nil_of_le, rankedExcesses_length, hq]

/-- Removing one unresolved rank removes exactly that ranked excess. -/
theorem unresolvedMass_recurrence {T : ℕ} (h : StepSchedule T)
    {q : ℕ} (hq : q < longCount h) :
    unresolvedMass h q =
      rankedExcessAt h ⟨q, hq⟩ + unresolvedMass h (q + 1) := by
  have hq' : q < (rankedExcesses h).length := by
    simpa only [rankedExcesses_length] using hq
  have hdrop :
      (rankedExcesses h)[q] :: (rankedExcesses h).drop (q + 1) =
        (rankedExcesses h).drop q :=
    List.cons_getElem_drop_succ
  have hget :
      rankedExcessAt h ⟨q, hq⟩ = (rankedExcesses h)[q] := by
    simp [rankedExcessAt]
  rw [hget]
  unfold unresolvedMass
  rw [← hdrop]
  simp only [List.sum_cons]
  ring

theorem unresolvedMass_succ_le {T : ℕ} (h : StepSchedule T) (q : ℕ) :
    unresolvedMass h (q + 1) ≤ unresolvedMass h q := by
  by_cases hq : q < longCount h
  · rw [unresolvedMass_recurrence h hq]
    exact le_add_of_nonneg_left (rankedExcessAt_pos h ⟨q, hq⟩).le
  · have hqr : longCount h ≤ q := Nat.le_of_not_gt hq
    rw [unresolvedMass_eq_cappedMass_of_longCount_le h hqr]
    rw [unresolvedMass_eq_cappedMass_of_longCount_le h (hqr.trans (Nat.le_add_right q 1))]

/-- The unresolved mass is antitone in the cutoff. -/
theorem unresolvedMass_antitone {T : ℕ} (h : StepSchedule T) :
    Antitone (unresolvedMass h) := by
  exact antitone_nat_of_succ_le (unresolvedMass_succ_le h)

theorem cappedMass_le_unresolvedMass {T : ℕ} (h : StepSchedule T) (q : ℕ) :
    cappedMass h ≤ unresolvedMass h q := by
  unfold unresolvedMass
  exact le_add_of_nonneg_right (rankedExcesses_drop_sum_nonneg h q)

end GDLowerBound.Schedule
