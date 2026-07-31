import GDLowerBound.Schedule.Excess
import Mathlib.Data.Finset.Sort

namespace GDLowerBound.Schedule

open scoped BigOperators

/-- A chronological chain is a finite selection of steps with positive excess.

The selection is stored as a finset.  Its chronological ordering is derived
canonically, so no separate proof that a list is strictly increasing is needed.
-/
structure Chain {T : ℕ} (h : StepSchedule T) where
  times : Finset (Fin T)
  sub_longTimes : times ⊆ longTimes h

namespace Chain

variable {T : ℕ} {h : StepSchedule T}

@[ext]
theorem ext {c d : Chain h} (htimes : c.times = d.times) : c = d := by
  cases c
  cases d
  simp_all

/-- The empty chain, which is a genuine candidate in the lower-bound
functional. -/
def empty (h : StepSchedule T) : Chain h where
  times := ∅
  sub_longTimes := by simp

/-- Number of selected transition times. -/
def length (c : Chain h) : ℕ := c.times.card

/-- The selected times in increasing temporal order. -/
def chronological (c : Chain h) : List (Fin T) := c.times.sort

@[simp]
theorem length_empty : (empty h).length = 0 := by
  simp [length, empty]

@[simp]
theorem chronological_empty : (empty h).chronological = [] := by
  simp [chronological, empty]

@[simp]
theorem chronological_length (c : Chain h) :
    c.chronological.length = c.length := by
  simp [chronological, length]

@[simp]
theorem chronological_nodup (c : Chain h) : c.chronological.Nodup := by
  exact Finset.sort_nodup _ _

theorem chronological_pairwise (c : Chain h) :
    c.chronological.Pairwise (· < ·) := by
  simpa only [chronological] using (Finset.sortedLT_sort c.times).pairwise

@[simp]
theorem mem_chronological_iff (c : Chain h) (t : Fin T) :
    t ∈ c.chronological ↔ t ∈ c.times := by
  simpa only [chronological] using (Finset.mem_sort (· ≤ ·) : t ∈ c.times.sort ↔ t ∈ c.times)

theorem mem_longTimes_of_mem (c : Chain h) {t : Fin T}
    (ht : t ∈ c.times) : t ∈ longTimes h :=
  c.sub_longTimes ht

theorem excess_pos_of_mem (c : Chain h) {t : Fin T}
    (ht : t ∈ c.times) : 0 < excess h t := by
  rw [excess_pos_iff]
  exact (mem_longTimes_iff h t).mp (c.mem_longTimes_of_mem ht)

theorem length_le_longCount (c : Chain h) : c.length ≤ longCount h := by
  exact Finset.card_le_card c.sub_longTimes

theorem length_le_horizon (c : Chain h) : c.length ≤ T := by
  exact c.length_le_longCount.trans (longCount_le_horizon h)

/-- The transition time at a given chain position. -/
def selected (c : Chain h) (i : Fin c.length) : Fin T :=
  c.chronological.get
    ⟨i, by simpa only [chronological_length] using i.isLt⟩

theorem selected_mem (c : Chain h) (i : Fin c.length) :
    c.selected i ∈ c.times := by
  rw [← mem_chronological_iff]
  exact List.get_mem _ _

theorem selected_excess_pos (c : Chain h) (i : Fin c.length) :
    0 < excess h (c.selected i) :=
  c.excess_pos_of_mem (c.selected_mem i)

theorem selected_strictMono (c : Chain h) : StrictMono c.selected := by
  intro i j hij
  exact c.chronological_pairwise.rel_get_of_lt hij

theorem selected_injective (c : Chain h) : Function.Injective c.selected :=
  c.selected_strictMono.injective

/-- Schedule indices in gap `i`.  Selected transition times are omitted;
`i` counts the selected times strictly before the schedule index.  This
definition also handles empty gaps and the terminal gap uniformly. -/
noncomputable def gapTimes (c : Chain h) (i : ℕ) : Finset (Fin T) :=
  Finset.univ.filter fun t ↦
    t ∉ c.times ∧ (c.times.filter fun s ↦ s < t).card = i

theorem mem_gapTimes_iff (c : Chain h) (i : ℕ) (t : Fin T) :
    t ∈ c.gapTimes i ↔
      t ∉ c.times ∧ (c.times.filter fun s ↦ s < t).card = i := by
  simp [gapTimes]

theorem gapTimes_disjoint (c : Chain h) {i j : ℕ} (hij : i ≠ j) :
    Disjoint (c.gapTimes i) (c.gapTimes j) := by
  rw [Finset.disjoint_left]
  intro t hti htj
  have hi := (c.mem_gapTimes_iff i t).mp hti
  have hj := (c.mem_gapTimes_iff j t).mp htj
  exact hij (hi.2.symm.trans hj.2)

/-- A gap with an index larger than the chain length is empty. -/
theorem gapTimes_eq_empty_of_length_lt (c : Chain h) {i : ℕ}
    (hi : c.length < i) : c.gapTimes i = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro t ht
  have hit := (c.mem_gapTimes_iff i t).mp ht
  have hcard : (c.times.filter fun s ↦ s < t).card ≤ c.length := by
    simpa only [length] using
      (Finset.card_le_card (Finset.filter_subset (fun s ↦ s < t) c.times))
  omega

/-- Every unselected time belongs to exactly the gap indexed by the number
of selected times that precede it. -/
theorem mem_canonical_gap (c : Chain h) {t : Fin T} (ht : t ∉ c.times) :
    t ∈ c.gapTimes ((c.times.filter fun s ↦ s < t).card) := by
  simp [gapTimes, ht]

/-- Union of all genuine gaps, from the initial gap through the terminal
gap. -/
noncomputable def allGapTimes (c : Chain h) : Finset (Fin T) :=
  (Finset.range (c.length + 1)).biUnion c.gapTimes

theorem mem_allGapTimes_iff (c : Chain h) (t : Fin T) :
    t ∈ c.allGapTimes ↔ t ∉ c.times := by
  constructor
  · intro ht
    obtain ⟨i, hi, hit⟩ := Finset.mem_biUnion.mp ht
    exact (c.mem_gapTimes_iff i t).mp hit |>.1
  · intro ht
    let i := (c.times.filter fun s ↦ s < t).card
    have hi_le : i ≤ c.length := by
      simpa only [i, length] using
        (Finset.card_le_card (Finset.filter_subset (fun s ↦ s < t) c.times))
    apply Finset.mem_biUnion.mpr
    exact ⟨i, Finset.mem_range.mpr (Nat.lt_succ_of_le hi_le), c.mem_canonical_gap ht⟩

theorem allGapTimes_eq_sdiff (c : Chain h) :
    c.allGapTimes = Finset.univ \ c.times := by
  ext t
  simp only [mem_allGapTimes_iff, Finset.mem_sdiff, Finset.mem_univ, true_and]

theorem times_disjoint_allGapTimes (c : Chain h) :
    Disjoint c.times c.allGapTimes := by
  rw [Finset.disjoint_left]
  intro t ht hgap
  exact (c.mem_allGapTimes_iff t).mp hgap ht

theorem times_union_allGapTimes (c : Chain h) :
    c.times ∪ c.allGapTimes = Finset.univ := by
  rw [allGapTimes_eq_sdiff, Finset.union_sdiff_of_subset]
  exact Finset.subset_univ _

theorem gapTimes_pairwiseDisjoint (c : Chain h) :
    Set.PairwiseDisjoint (↑(Finset.range (c.length + 1))) c.gapTimes := by
  intro i hi j hj hij
  exact c.gapTimes_disjoint hij

theorem sum_allGapTimes (c : Chain h) (f : Fin T → ℝ) :
    ∑ t ∈ c.allGapTimes, f t =
      ∑ i ∈ Finset.range (c.length + 1), ∑ t ∈ c.gapTimes i, f t := by
  unfold allGapTimes
  exact Finset.sum_biUnion c.gapTimes_pairwiseDisjoint

theorem sum_times_add_sum_gaps (c : Chain h) (f : Fin T → ℝ) :
    (∑ t ∈ c.times, f t) +
        ∑ i ∈ Finset.range (c.length + 1), ∑ t ∈ c.gapTimes i, f t =
      ∑ t, f t := by
  rw [← c.sum_allGapTimes f]
  rw [← Finset.sum_union c.times_disjoint_allGapTimes]
  rw [c.times_union_allGapTimes]

theorem step_eq_one_add_excess_of_mem (c : Chain h) {t : Fin T}
    (ht : t ∈ c.times) : h t = 1 + excess h t := by
  have hlong : 1 < h t :=
    (mem_longTimes_iff h t).mp (c.mem_longTimes_of_mem ht)
  simp [excess, max_eq_left (sub_nonneg.mpr hlong.le)]

theorem sum_times_steps (c : Chain h) :
    ∑ t ∈ c.times, h t =
      (c.length : ℝ) + ∑ t ∈ c.times, excess h t := by
  calc
    ∑ t ∈ c.times, h t =
        ∑ t ∈ c.times, (1 + excess h t) := by
      apply Finset.sum_congr rfl
      intro t ht
      exact c.step_eq_one_add_excess_of_mem ht
    _ = (c.length : ℝ) + ∑ t ∈ c.times, excess h t := by
      simp [length, Finset.sum_add_distrib]

/-- Mass in a chronological gap, including the unit offset used in the
manuscript's `U_i` and terminal `V`. -/
noncomputable def gapMass (c : Chain h) (i : ℕ) : ℝ :=
  1 + ∑ t ∈ c.gapTimes i, h t

/-- Scale of the final block. -/
noncomputable def terminalScale (c : Chain h) : ℝ :=
  1 + 2 * ∑ t ∈ c.gapTimes c.length, h t

theorem sum_gapMass (c : Chain h) :
    ∑ i ∈ Finset.range (c.length + 1), c.gapMass i =
      (c.length + 1 : ℕ) + ∑ t ∈ c.allGapTimes, h t := by
  calc
    ∑ i ∈ Finset.range (c.length + 1), c.gapMass i =
        ∑ i ∈ Finset.range (c.length + 1),
          (1 + ∑ t ∈ c.gapTimes i, h t) := by
      rfl
    _ = (∑ _i ∈ Finset.range (c.length + 1), (1 : ℝ)) +
          ∑ i ∈ Finset.range (c.length + 1),
            ∑ t ∈ c.gapTimes i, h t := by
      rw [Finset.sum_add_distrib]
    _ = (c.length + 1 : ℕ) + ∑ t ∈ c.allGapTimes, h t := by
      rw [← c.sum_allGapTimes h]
      simp

/-- The manuscript's preceding-gap mass `U_i`. -/
noncomputable def precedingMass (c : Chain h) (i : Fin c.length) : ℝ :=
  c.gapMass i

/-- The manuscript's nonterminal block scale `H_i=U_i+y_{t_{i+1}}`.
Indices are zero-based here. -/
noncomputable def nonterminalScale (c : Chain h) (i : Fin c.length) : ℝ :=
  c.precedingMass i + excess h (c.selected i)

/-- Scale of any block, including the terminal block at index `length`. -/
noncomputable def blockScale (c : Chain h) (i : Fin (c.length + 1)) : ℝ :=
  if hi : i < c.length then
    c.nonterminalScale ⟨i, hi⟩
  else
    c.terminalScale

/-- Largest admissible squared amplitude for a transition. -/
noncomputable def localBound (c : Chain h) (i : Fin c.length) : ℝ :=
  excess h (c.selected i) * c.blockScale i.succ /
    (c.precedingMass i *
      (c.blockScale i.castSucc + c.blockScale i.succ))

theorem gapMass_pos (c : Chain h) (hh : IsNonnegativeSchedule h) (i : ℕ) :
    0 < c.gapMass i := by
  have hs : 0 ≤ ∑ t ∈ c.gapTimes i, h t := by
    exact Finset.sum_nonneg fun t _ ↦ hh t
  simp only [gapMass]
  linarith

theorem terminalScale_pos (c : Chain h) (hh : IsNonnegativeSchedule h) :
    0 < c.terminalScale := by
  have hs : 0 ≤ ∑ t ∈ c.gapTimes c.length, h t := by
    exact Finset.sum_nonneg fun t _ ↦ hh t
  simp only [terminalScale]
  linarith

theorem precedingMass_pos (c : Chain h) (hh : IsNonnegativeSchedule h)
    (i : Fin c.length) : 0 < c.precedingMass i := by
  exact c.gapMass_pos hh i

theorem nonterminalScale_pos (c : Chain h) (hh : IsNonnegativeSchedule h)
    (i : Fin c.length) : 0 < c.nonterminalScale i := by
  unfold nonterminalScale
  have hU := c.precedingMass_pos hh i
  have hy := c.selected_excess_pos i
  linarith

@[simp]
theorem blockScale_castSucc (c : Chain h) (i : Fin c.length) :
    c.blockScale i.castSucc = c.nonterminalScale i := by
  simp [blockScale, i.isLt]

@[simp]
theorem blockScale_last (c : Chain h) :
    c.blockScale (Fin.last c.length) = c.terminalScale := by
  simp [blockScale]

theorem blockScale_pos (c : Chain h) (hh : IsNonnegativeSchedule h)
    (i : Fin (c.length + 1)) : 0 < c.blockScale i := by
  unfold blockScale
  split_ifs with hi
  · exact c.nonterminalScale_pos hh ⟨i, hi⟩
  · exact c.terminalScale_pos hh

theorem localBound_pos (c : Chain h) (hh : IsNonnegativeSchedule h)
    (i : Fin c.length) : 0 < c.localBound i := by
  have hy := c.selected_excess_pos i
  have hnext := c.blockScale_pos hh i.succ
  have hU := c.precedingMass_pos hh i
  have hcur := c.blockScale_pos hh i.castSucc
  unfold localBound
  positivity

@[simp]
theorem gapTimes_empty_zero : (empty h).gapTimes 0 = Finset.univ := by
  ext t
  simp [gapTimes, empty]

@[simp]
theorem terminalScale_empty :
    (empty h).terminalScale = 1 + 2 * ∑ t, h t := by
  simp [terminalScale]

end Chain

end GDLowerBound.Schedule
