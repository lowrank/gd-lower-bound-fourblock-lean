import GDLowerBound.FourBlock.ScheduleFourBlock
import GDLowerBound.FourBlock.FiniteConstraint

/-! # Two-sided control of the finite four-block matching scale -/

namespace GDLowerBound.FourBlock

open scoped BigOperators
open GDLowerBound.Schedule GDLowerBound.RankAnalysis GDLowerBound.Matching

noncomputable section

/-- Dropping the smallest sorted entry loses no more mass than dropping the
distinguished last entry. -/
theorem castSucc_sum_le_sortedNearTail_sum
    {k : ℕ} (hk : 0 < k) (v : Fin (2 * k + 1) → ℝ) :
    (∑ i : Fin (2 * k), v i.castSucc) ≤
      ∑ i : Fin (2 * k), sortedNearTail v i := by
  have hmono := sortedWeight_monotone v
  let j : Fin (2 * k + 1) := (Tuple.sort v).symm (Fin.last (2 * k))
  have hzeroj : (0 : Fin (2 * k + 1)) ≤ j := Fin.zero_le j
  have hmin : sortedWeight v 0 ≤ v (Fin.last (2 * k)) := by
    calc
      sortedWeight v 0 ≤ sortedWeight v j := hmono hzeroj
      _ = v (Fin.last (2 * k)) := by
        simp [sortedWeight, j]
  have hsorted := Fin.sum_univ_succ (sortedWeight v)
  have horiginal := Fin.sum_univ_castSucc v
  have hsum := sortedWeight_sum v
  have htail :
      (∑ i : Fin (2 * k), sortedNearTail v i) =
        ∑ i : Fin (2 * k), sortedWeight v i.succ := by
    rfl
  rw [hsum] at hsorted
  rw [htail]
  linarith

/-- The selected four-block total is at least the total of the genuine
reciprocal weights. -/
theorem topPathOriginalTotal_le_fourBlockTotal
    {T m : ℕ} {h : StepSchedule T} (hm : 0 < m)
    (hq : 2 * (m + m) ≤ longCount h) :
    2 * (2 * (m + m) : ℕ) * zetaState h (2 * (m + m)) ≤
      fourBlockTotal (scheduleFourBlockWeights h hq) := by
  let v := topPathWeight h (2 * (m + m)) hq
  have hlower := castSucc_sum_le_sortedNearTail_sum
    (k := m + m) (by omega) v
  have htotal := topPathWeight_sum (h := h) (q := 2 * (m + m)) (by omega) hq
  have hlast := topPathWeight_last h hq
  have hsplit := Fin.sum_univ_castSucc v
  have horiginal :
      (∑ i : Fin (2 * (m + m)), v i.castSucc) =
        2 * (2 * (m + m) : ℕ) * zetaState h (2 * (m + m)) := by
    dsimp only [v] at hsplit ⊢
    rw [htotal, hlast] at hsplit
    linarith
  rw [fourBlockTotal_eq_sum, scheduleFourBlockWeights, ← horiginal]
  exact hlower

theorem zeta_le_scheduleFourBlockZ
    {T m : ℕ} {h : StepSchedule T} (hm : 0 < m)
    (hq : 2 * (m + m) ≤ longCount h) :
    zetaState h (2 * (m + m)) ≤ fourBlockZ (scheduleFourBlockWeights h hq) := by
  have htotal := topPathOriginalTotal_le_fourBlockTotal (h := h) hm hq
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  unfold fourBlockZ
  rw [le_div_iff₀ (by positivity : (0 : ℝ) < 8 * m)]
  norm_num [Nat.cast_mul] at htotal ⊢
  linarith

/-- Exact scale sandwich; the correction is `O(m⁻²)` after normalization. -/
theorem scheduleFourBlockZ_sandwich
    {T m : ℕ} {h : StepSchedule T} (hh : IsNonnegativeSchedule h)
    (hm : 0 < m) (hq : 2 * (m + m) ≤ longCount h) :
    zetaState h (2 * (m + m)) ≤ fourBlockZ (scheduleFourBlockWeights h hq) ∧
      fourBlockZ (scheduleFourBlockWeights h hq) ≤
        zetaState h (2 * (m + m)) +
          1 / ((8 * (m : ℝ)) * ((2 * (m + m) : ℕ) - 1)) := by
  constructor
  · exact zeta_le_scheduleFourBlockZ hm hq
  · convert scheduleFourBlockZ_le_zeta_add_aux hh hm hq using 1 <;>
      norm_num [Nat.cast_mul, Nat.cast_add]

end

end GDLowerBound.FourBlock
