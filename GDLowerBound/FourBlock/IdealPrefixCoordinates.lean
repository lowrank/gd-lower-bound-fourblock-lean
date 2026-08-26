import GDLowerBound.FourBlock.IdealBlockCoordinates

/-!
# Exact prefix coordinates of the ideal reciprocal four-block tuple

The four consecutive blocks of the monotone reciprocal-rank tuple have
cumulative masses exactly equal to the reciprocal prefixes at ranks
`m`, `2m`, and `3m`.  Consequently the normalized abstract coordinates
used by the local certificate are the genuine schedule prefix ratios.
-/

namespace GDLowerBound.FourBlock

open scoped BigOperators
open GDLowerBound.Schedule GDLowerBound.RankAnalysis

noncomputable section

theorem idealQuarterSumOne_eq_reciprocalPrefix
    {T m : ℕ} (h : StepSchedule T) :
    quarterSumOne (idealReciprocalWeights h m) =
      reciprocalPrefix h m := by
  rw [quarterSumOne_eq_flatten]
  unfold idealReciprocalWeights reciprocalPrefix
  convert
    (Fin.sum_univ_eq_sum_range
      (fun i : ℕ ↦ (rankedExcessOne h (i + 1))⁻¹) m)
    using 1 <;> simp [fourBlockFlatten_val]

theorem idealQuarterSumTwo_eq_segment
    {T m : ℕ} (h : StepSchedule T) :
    quarterSumTwo (idealReciprocalWeights h m) =
      ∑ i ∈ Finset.range m, (rankedExcessOne h (m + i + 1))⁻¹ := by
  rw [quarterSumTwo_eq_flatten]
  unfold idealReciprocalWeights
  convert
    (Fin.sum_univ_eq_sum_range
      (fun i : ℕ ↦ (rankedExcessOne h (m + i + 1))⁻¹) m)
    using 1 <;> simp [fourBlockFlatten_val]

theorem idealQuarterSumThree_eq_segment
    {T m : ℕ} (h : StepSchedule T) :
    quarterSumThree (idealReciprocalWeights h m) =
      ∑ i ∈ Finset.range m,
        (rankedExcessOne h (2 * m + i + 1))⁻¹ := by
  rw [quarterSumThree_eq_flatten]
  unfold idealReciprocalWeights
  convert
    (Fin.sum_univ_eq_sum_range
      (fun i : ℕ ↦ (rankedExcessOne h (2 * m + i + 1))⁻¹) m)
    using 1 <;> simp [fourBlockFlatten_val]

theorem idealFirstTwo_eq_reciprocalPrefix
    {T m : ℕ} (h : StepSchedule T) :
    quarterSumOne (idealReciprocalWeights h m) +
        quarterSumTwo (idealReciprocalWeights h m) =
      reciprocalPrefix h (2 * m) := by
  rw [idealQuarterSumOne_eq_reciprocalPrefix,
    idealQuarterSumTwo_eq_segment]
  unfold reciprocalPrefix
  rw [show 2 * m = m + m by omega, Finset.sum_range_add]

theorem idealFirstThree_eq_reciprocalPrefix
    {T m : ℕ} (h : StepSchedule T) :
    quarterSumOne (idealReciprocalWeights h m) +
        quarterSumTwo (idealReciprocalWeights h m) +
        quarterSumThree (idealReciprocalWeights h m) =
      reciprocalPrefix h (3 * m) := by
  rw [idealFirstTwo_eq_reciprocalPrefix,
    idealQuarterSumThree_eq_segment]
  unfold reciprocalPrefix
  rw [show 3 * m = 2 * m + m by omega, Finset.sum_range_add]

theorem idealFourBlockA_eq_schedulePrefixA
    {T m : ℕ} (h : StepSchedule T) :
    fourBlockA (idealReciprocalWeights h m) = schedulePrefixA h m := by
  unfold fourBlockA schedulePrefixA
  rw [idealQuarterSumOne_eq_reciprocalPrefix,
    idealFourBlockTotal_eq_reciprocalPrefix]

theorem idealFourBlockR_eq_schedulePrefixR
    {T m : ℕ} (h : StepSchedule T) :
    fourBlockR (idealReciprocalWeights h m) = schedulePrefixR h m := by
  unfold fourBlockR schedulePrefixR
  rw [idealFirstTwo_eq_reciprocalPrefix,
    idealFourBlockTotal_eq_reciprocalPrefix]

theorem idealFourBlockS_eq_schedulePrefixS
    {T m : ℕ} (h : StepSchedule T) :
    fourBlockS (idealReciprocalWeights h m) = schedulePrefixS h m := by
  unfold fourBlockS schedulePrefixS
  rw [idealFirstThree_eq_reciprocalPrefix,
    idealFourBlockTotal_eq_reciprocalPrefix]

/-- The genuine reciprocal-prefix ratios lie in the ordered four-block
domain required by the local interval certificates. -/
theorem schedulePrefix_ordered
    {T m : ℕ} {h : StepSchedule T} (hm : 0 < m)
    (hq : 4 * m ≤ longCount h) :
    OrderedFourBlocks (schedulePrefixA h m)
      (schedulePrefixR h m) (schedulePrefixS h m) := by
  rw [← idealFourBlockA_eq_schedulePrefixA,
    ← idealFourBlockR_eq_schedulePrefixR,
    ← idealFourBlockS_eq_schedulePrefixS]
  apply idealFourBlock_ordered hm
  omega

end

end GDLowerBound.FourBlock
