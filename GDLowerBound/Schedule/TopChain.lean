import GDLowerBound.Schedule.Chain
import GDLowerBound.Schedule.TailMass

namespace GDLowerBound.Schedule

open scoped BigOperators

/-- Set of times carrying the first `q` ranked excesses. -/
noncomputable def topTimes {T : ℕ} (h : StepSchedule T) (q : ℕ) :
    Finset (Fin T) :=
  ((rankedTimes h).take q).toFinset

theorem mem_topTimes_iff {T : ℕ} (h : StepSchedule T) (q : ℕ)
    (t : Fin T) :
    t ∈ topTimes h q ↔ t ∈ (rankedTimes h).take q := by
  simp [topTimes]

theorem topTimes_subset_longTimes {T : ℕ} (h : StepSchedule T) (q : ℕ) :
    topTimes h q ⊆ longTimes h := by
  intro t ht
  have ht' : t ∈ (rankedTimes h).take q := (mem_topTimes_iff h q t).mp ht
  exact (mem_rankedTimes_iff h t).mp (List.mem_of_mem_take ht')

theorem topTimes_card {T : ℕ} (h : StepSchedule T) (q : ℕ) :
    (topTimes h q).card = min q (longCount h) := by
  calc
    (topTimes h q).card = ((rankedTimes h).take q).length := by
      exact List.toFinset_card_of_nodup (rankedTimes_nodup h).take
    _ = min q (longCount h) := by simp [rankedTimes_length]

theorem topTimes_card_of_le {T : ℕ} (h : StepSchedule T) {q : ℕ}
    (hq : q ≤ longCount h) : (topTimes h q).card = q := by
  rw [topTimes_card, min_eq_left hq]

/-- The top `q` excesses, placed back in chronological order by `Chain`.
For `q` beyond the available ranks this simply selects every long time. -/
noncomputable def topChain {T : ℕ} (h : StepSchedule T) (q : ℕ) : Chain h where
  times := topTimes h q
  sub_longTimes := topTimes_subset_longTimes h q

@[simp]
theorem topChain_times {T : ℕ} (h : StepSchedule T) (q : ℕ) :
    (topChain h q).times = topTimes h q := rfl

@[simp]
theorem topChain_length {T : ℕ} (h : StepSchedule T) (q : ℕ) :
    (topChain h q).length = min q (longCount h) := by
  exact topTimes_card h q

theorem topChain_length_of_le {T : ℕ} (h : StepSchedule T) {q : ℕ}
    (hq : q ≤ longCount h) : (topChain h q).length = q := by
  rw [topChain_length, min_eq_left hq]

@[simp]
theorem topChain_zero {T : ℕ} (h : StepSchedule T) :
    topChain h 0 = Chain.empty h := by
  apply Chain.ext
  simp [topChain, topTimes, Chain.empty]

theorem sum_topTimes {T : ℕ} (h : StepSchedule T) (q : ℕ)
    (f : Fin T → ℝ) :
    ∑ t ∈ topTimes h q, f t = ((rankedTimes h).take q |>.map f).sum := by
  classical
  symm
  exact sum_map_eq_sum_toFinset_of_nodup _ (rankedTimes_nodup h).take _

theorem sum_topTimes_excess {T : ℕ} (h : StepSchedule T) (q : ℕ) :
    ∑ t ∈ topTimes h q, excess h t =
      ((rankedExcesses h).take q).sum := by
  rw [sum_topTimes]
  simp [rankedExcesses]

theorem rankedExcesses_sum_take_add_drop {T : ℕ} (h : StepSchedule T)
    (q : ℕ) :
    ((rankedExcesses h).take q).sum +
        ((rankedExcesses h).drop q).sum =
      (rankedExcesses h).sum := by
  rw [← List.sum_append, List.take_append_drop]

/-- `D_q` is the total normalized schedule mass after removing the selected
top-`q` excesses. -/
theorem unresolvedMass_add_selected {T : ℕ} (h : StepSchedule T) (q : ℕ) :
    unresolvedMass h q + ∑ t ∈ topTimes h q, excess h t =
      1 + ∑ t, h t := by
  rw [sum_topTimes_excess, unresolvedMass]
  calc
    cappedMass h + ((rankedExcesses h).drop q).sum +
          ((rankedExcesses h).take q).sum =
        cappedMass h +
          (((rankedExcesses h).take q).sum +
            ((rankedExcesses h).drop q).sum) := by ring
    _ = cappedMass h + (rankedExcesses h).sum := by
      rw [rankedExcesses_sum_take_add_drop]
    _ = cappedMass h + ∑ t, excess h t := by rw [rankedExcesses_sum]
    _ = 1 + ∑ t, h t := (total_mass_decomposition h).symm

/-- The chronological gap masses of the top-`q` chain add up to `D_q`.
This is the first identity in the manuscript's mass decomposition. -/
theorem topChain_sum_gapMass {T : ℕ} (h : StepSchedule T) {q : ℕ}
    (hq : q ≤ longCount h) :
    ∑ i ∈ Finset.range (q + 1), (topChain h q).gapMass i =
      unresolvedMass h q := by
  let c := topChain h q
  have hlen : c.length = q := topChain_length_of_le h hq
  change ∑ i ∈ Finset.range (q + 1), c.gapMass i = unresolvedMass h q
  have hres := unresolvedMass_add_selected h q
  change unresolvedMass h q + ∑ t ∈ c.times, excess h t =
    1 + ∑ t, h t at hres
  have hpartition := c.sum_times_add_sum_gaps h
  have hselected := c.sum_times_steps
  have hgap := c.sum_gapMass
  have hall := c.sum_allGapTimes h
  rw [hlen] at hselected hpartition hgap
  rw [hlen] at hall
  norm_num [Nat.cast_add, Nat.cast_one] at hgap
  linarith

theorem topChain_mass_decomposition {T : ℕ} (h : StepSchedule T) {q : ℕ}
    (hq : q ≤ longCount h) :
    (∑ i ∈ Finset.range q, (topChain h q).gapMass i) +
        (topChain h q).gapMass q = unresolvedMass h q := by
  rw [← topChain_sum_gapMass h hq]
  simp [Finset.sum_range_succ]

theorem terminalScale_eq_two_gapMass_sub_one {T : ℕ} {h : StepSchedule T}
    (c : Chain h) :
    c.terminalScale = 2 * c.gapMass c.length - 1 := by
  simp only [Chain.terminalScale, Chain.gapMass]
  ring

theorem topChain_terminalScale {T : ℕ} (h : StepSchedule T) {q : ℕ}
    (hq : q ≤ longCount h) :
    (topChain h q).terminalScale =
      2 * (topChain h q).gapMass q - 1 := by
  rw [terminalScale_eq_two_gapMass_sub_one]
  rw [topChain_length_of_le h hq]

theorem topChain_initial_gap_sum_le {T : ℕ} {h : StepSchedule T}
    (hh : IsNonnegativeSchedule h) {q : ℕ} (hq : q ≤ longCount h) :
    ∑ i ∈ Finset.range q, (topChain h q).gapMass i ≤
      unresolvedMass h q - 1 := by
  have hV : 1 ≤ (topChain h q).gapMass q := by
    have := (topChain h q).gapMass_pos hh q
    unfold Chain.gapMass at this ⊢
    have hs : 0 ≤ ∑ t ∈ (topChain h q).gapTimes q, h t := by
      exact Finset.sum_nonneg fun t _ ↦ hh t
    linarith
  have hmass := topChain_mass_decomposition h hq
  linarith

end GDLowerBound.Schedule
