import GDLowerBound.Schedule.Excess
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Prod.Lex

namespace GDLowerBound.Schedule

open scoped BigOperators

/-- A key that orders positive-excess times by decreasing excess, with the
time index as a deterministic tie breaker. -/
abbrev RankKey (T : ℕ) := OrderDual ℝ ×ₗ Fin T

/-- Key of a schedule time in the size ranking. -/
def rankKey {T : ℕ} (h : StepSchedule T) (t : Fin T) : RankKey T :=
  toLex (OrderDual.toDual (excess h t), t)

theorem rankKey_injective {T : ℕ} (h : StepSchedule T) :
    Function.Injective (rankKey h) := by
  intro s t hst
  have := congrArg (fun k : RankKey T ↦ (ofLex k).2) hst
  simpa only [rankKey, ofLex_toLex] using this

/-- The keys of all positive-excess times. -/
noncomputable def rankedKeys {T : ℕ} (h : StepSchedule T) :
    Finset (RankKey T) :=
  (longTimes h).image (rankKey h)

/-- All positive-excess times ordered by decreasing excess and then by
increasing time.  This makes the manuscript's arbitrary tie breaking
explicit and reproducible. -/
noncomputable def rankedTimes {T : ℕ} (h : StepSchedule T) : List (Fin T) :=
  (rankedKeys h).sort.map fun k ↦ (ofLex k).2

/-- The ranked excess values `a₁,…,aᵣ`. -/
noncomputable def rankedExcesses {T : ℕ} (h : StepSchedule T) : List ℝ :=
  (rankedTimes h).map (excess h)

@[simp]
theorem rankedKeys_card {T : ℕ} (h : StepSchedule T) :
    (rankedKeys h).card = longCount h := by
  simp only [rankedKeys, longCount]
  exact Finset.card_image_of_injective _ (rankKey_injective h)

@[simp]
theorem rankedTimes_length {T : ℕ} (h : StepSchedule T) :
    (rankedTimes h).length = longCount h := by
  simp [rankedTimes]

@[simp]
theorem rankedExcesses_length {T : ℕ} (h : StepSchedule T) :
    (rankedExcesses h).length = longCount h := by
  simp [rankedExcesses]

@[simp]
theorem mem_rankedTimes_iff {T : ℕ} (h : StepSchedule T) (t : Fin T) :
    t ∈ rankedTimes h ↔ t ∈ longTimes h := by
  constructor
  · intro ht
    simp only [rankedTimes, List.mem_map] at ht
    obtain ⟨k, hk, hkt⟩ := ht
    have hk' : k ∈ rankedKeys h := (Finset.mem_sort (· ≤ ·)).mp hk
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hk'
    have : s = t := by simpa only [rankKey, ofLex_toLex] using hkt
    simpa only [this] using hs
  · intro ht
    have hk : rankKey h t ∈ rankedKeys h := by
      exact Finset.mem_image.mpr ⟨t, ht, rfl⟩
    have hks : rankKey h t ∈ (rankedKeys h).sort :=
      (Finset.mem_sort (· ≤ ·)).mpr hk
    exact List.mem_map.mpr ⟨rankKey h t, hks, by simp [rankKey]⟩

theorem rankedTimes_nodup {T : ℕ} (h : StepSchedule T) :
    (rankedTimes h).Nodup := by
  apply List.Nodup.map_on _ (Finset.sort_nodup (rankedKeys h) (· ≤ ·))
  intro k hk l hl hkl
  have hk' : k ∈ rankedKeys h := (Finset.mem_sort (· ≤ ·)).mp hk
  have hl' : l ∈ rankedKeys h := (Finset.mem_sort (· ≤ ·)).mp hl
  obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hk'
  obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hl'
  have hst : s = t := by simpa only [rankKey, ofLex_toLex] using hkl
  simp [hst]

@[simp]
theorem rankedTimes_toFinset {T : ℕ} (h : StepSchedule T) :
    (rankedTimes h).toFinset = longTimes h := by
  ext t
  simp only [List.mem_toFinset, mem_rankedTimes_iff]

theorem sum_map_eq_sum_toFinset_of_nodup {A : Type*} [DecidableEq A]
    (l : List A) (hl : l.Nodup) (f : A → ℝ) :
    (l.map f).sum = ∑ a ∈ l.toFinset, f a := by
  induction l with
  | nil => simp
  | cons a l ih =>
      obtain ⟨ha, hl⟩ := List.nodup_cons.mp hl
      simp [ha, ih hl]

theorem rankedExcesses_sum_longTimes {T : ℕ} (h : StepSchedule T) :
    (rankedExcesses h).sum = ∑ t ∈ longTimes h, excess h t := by
  classical
  calc
    (rankedExcesses h).sum = ((rankedTimes h).map (excess h)).sum := rfl
    _ = ∑ t ∈ (rankedTimes h).toFinset, excess h t :=
      sum_map_eq_sum_toFinset_of_nodup _ (rankedTimes_nodup h) _
    _ = ∑ t ∈ longTimes h, excess h t := by rw [rankedTimes_toFinset]

theorem excess_eq_zero_of_not_mem_longTimes {T : ℕ} (h : StepSchedule T)
    {t : Fin T} (ht : t ∉ longTimes h) : excess h t = 0 := by
  have hnpos : ¬ 0 < excess h t := by
    intro hpos
    exact ht ((mem_longTimes_iff h t).mpr ((excess_pos_iff h t).mp hpos))
  exact le_antisymm (le_of_not_gt hnpos) (excess_nonneg h t)

theorem rankedExcesses_sum {T : ℕ} (h : StepSchedule T) :
    (rankedExcesses h).sum = ∑ t, excess h t := by
  classical
  calc
    (rankedExcesses h).sum = ∑ t ∈ longTimes h, excess h t :=
      rankedExcesses_sum_longTimes h
    _ = ∑ t ∈ Finset.univ, excess h t := by
      apply Finset.sum_subset (Finset.subset_univ _)
      intro t _ ht
      exact excess_eq_zero_of_not_mem_longTimes h ht
    _ = ∑ t, excess h t := rfl

theorem excess_pos_of_mem_rankedTimes {T : ℕ} (h : StepSchedule T)
    {t : Fin T} (ht : t ∈ rankedTimes h) : 0 < excess h t := by
  rw [excess_pos_iff]
  exact (mem_longTimes_iff h t).mp ((mem_rankedTimes_iff h t).mp ht)

/-- Ranked excesses are nonincreasing. -/
theorem rankedExcesses_pairwise_ge {T : ℕ} (h : StepSchedule T) :
    (rankedExcesses h).Pairwise (· ≥ ·) := by
  unfold rankedExcesses rankedTimes
  rw [List.pairwise_map, List.pairwise_map]
  refine (Finset.pairwise_sort (rankedKeys h) (· ≤ ·)).imp_of_mem ?_
  intro k l hk hl hkl
  have hk' : k ∈ rankedKeys h := (Finset.mem_sort (· ≤ ·)).mp hk
  have hl' : l ∈ rankedKeys h := (Finset.mem_sort (· ≤ ·)).mp hl
  obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hk'
  obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hl'
  have hfirst := Prod.Lex.monotone_fst (rankKey h s) (rankKey h t) hkl
  exact (OrderDual.toDual_le_toDual.mp hfirst)

/-- Every value in the ranked excess list is positive. -/
theorem rankedExcesses_pos {T : ℕ} (h : StepSchedule T)
    {a : ℝ} (ha : a ∈ rankedExcesses h) : 0 < a := by
  obtain ⟨t, ht, rfl⟩ := List.mem_map.mp ha
  exact excess_pos_of_mem_rankedTimes h ht

end GDLowerBound.Schedule
