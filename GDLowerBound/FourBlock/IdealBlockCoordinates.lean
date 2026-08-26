import GDLowerBound.FourBlock.ScheduleScaleSandwich

/-! # Ordered four-block coordinates of the genuine reciprocal prefix -/

namespace GDLowerBound.FourBlock

open scoped BigOperators
open GDLowerBound.Schedule GDLowerBound.RankAnalysis

noncomputable section

def schedulePrefixA {T : ℕ} (h : StepSchedule T) (m : ℕ) : ℝ :=
  reciprocalPrefix h m / reciprocalPrefix h (4 * m)

def idealReciprocalWeights {T : ℕ} (h : StepSchedule T) (m : ℕ) :
    Fin (2 * (m + m)) → ℝ := fun i ↦
  (rankedExcessOne h (i.val + 1))⁻¹

theorem idealReciprocalWeights_pos
    {T m : ℕ} {h : StepSchedule T} (hm : 0 < m)
    (hq : 2 * (m + m) ≤ longCount h) :
    ∀ i, 0 < idealReciprocalWeights h m i := by
  intro i
  unfold idealReciprocalWeights
  exact inv_pos.mpr (rankedExcessOne_pos h (by omega) (by omega))

theorem idealReciprocalWeights_monotone
    {T m : ℕ} {h : StepSchedule T} (hm : 0 < m)
    (hq : 2 * (m + m) ≤ longCount h) :
    Monotone (idealReciprocalWeights h m) := by
  intro i j hij
  have hi := rankedExcessOne_pos h (q := i.val + 1) (by omega) (by omega)
  have hj := rankedExcessOne_pos h (q := j.val + 1) (by omega) (by omega)
  have hanti := rankedExcessOne_antitone h
    (a := i.val + 1) (b := j.val + 1) (by omega) (by omega) (by omega)
  unfold idealReciprocalWeights
  exact (inv_le_inv₀ hi hj).2 hanti

theorem idealFourBlock_ordered
    {T m : ℕ} {h : StepSchedule T} (hm : 0 < m)
    (hq : 2 * (m + m) ≤ longCount h) :
    OrderedFourBlocks
      (fourBlockA (idealReciprocalWeights h m))
      (fourBlockR (idealReciprocalWeights h m))
      (fourBlockS (idealReciprocalWeights h m)) := by
  exact orderedFourBlocks_of_sortedWeights hm
    (idealReciprocalWeights_pos hm hq)
    (idealReciprocalWeights_monotone hm hq)

theorem idealFourBlockTotal_eq_reciprocalPrefix
    {T m : ℕ} (h : StepSchedule T) :
    fourBlockTotal (idealReciprocalWeights h m) =
      reciprocalPrefix h (4 * m) := by
  rw [fourBlockTotal_eq_sum]
  unfold idealReciprocalWeights reciprocalPrefix
  have hcard : 2 * (m + m) = 4 * m := by omega
  rw [hcard]
  exact Fin.sum_univ_eq_sum_range
    (fun i : ℕ ↦ (rankedExcessOne h (i + 1))⁻¹) (4 * m)

end

end GDLowerBound.FourBlock
