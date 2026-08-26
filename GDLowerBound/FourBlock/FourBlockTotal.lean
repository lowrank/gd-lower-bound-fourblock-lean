import GDLowerBound.FourBlock.FourBlockCoordinates
import GDLowerBound.Matching.ScalarBound
import Mathlib.Data.Fin.Rev

/-!
# Total mass of the four sorted blocks

The four oriented quarter sums are a permutation of all `4m` selected
weights.  This file proves that identity and bounds the selected total by the
known total mass of the augmented endpoint path.
-/

namespace GDLowerBound.FourBlock

open scoped BigOperators
open GDLowerBound.Schedule GDLowerBound.RankAnalysis GDLowerBound.Matching

noncomputable section

def fourBlockFlatten (m : ℕ) :
    Fin 4 × Fin m ≃ Fin (2 * (m + m)) :=
  finProdFinEquiv.trans
    (Fin.castOrderIso (by omega : 4 * m = 2 * (m + m))).toEquiv

@[simp]
theorem fourBlockFlatten_val (m : ℕ) (j : Fin 4) (i : Fin m) :
    (fourBlockFlatten m (j, i)).val = j.val * m + i.val := by
  simp [fourBlockFlatten, finProdFinEquiv, Nat.mul_comm, Nat.add_comm]

theorem quarterSumOne_eq_flatten {m : ℕ}
    (w : Fin (2 * (m + m)) → ℝ) :
    quarterSumOne w = ∑ i : Fin m, w (fourBlockFlatten m (0, i)) := by
  apply Finset.sum_congr rfl
  intro i hi
  apply congrArg w
  apply Fin.ext
  simp [quarterSumOne, outsideQuarterOne]

theorem quarterSumTwo_eq_flatten {m : ℕ}
    (w : Fin (2 * (m + m)) → ℝ) :
    quarterSumTwo w = ∑ i : Fin m, w (fourBlockFlatten m (1, i)) := by
  apply Finset.sum_congr rfl
  intro i hi
  apply congrArg w
  apply Fin.ext
  simp [quarterSumTwo, outsideQuarterTwo]

theorem quarterSumThree_eq_flatten {m : ℕ}
    (w : Fin (2 * (m + m)) → ℝ) :
    quarterSumThree w = ∑ i : Fin m, w (fourBlockFlatten m (2, i)) := by
  calc
    quarterSumThree w =
        ∑ i : Fin m, w (fourBlockFlatten m (2, Fin.revPerm i)) := by
      apply Finset.sum_congr rfl
      intro i hi
      apply congrArg w
      apply Fin.ext
      simp [quarterSumThree, outsideQuarterThree, Fin.revPerm_apply, Fin.rev]
      omega
    _ = ∑ i : Fin m, w (fourBlockFlatten m (2, i)) :=
      Equiv.sum_comp Fin.revPerm (fun i : Fin m ↦
        w (fourBlockFlatten m (2, i)))

theorem quarterSumFour_eq_flatten {m : ℕ}
    (w : Fin (2 * (m + m)) → ℝ) :
    quarterSumFour w = ∑ i : Fin m, w (fourBlockFlatten m (3, i)) := by
  calc
    quarterSumFour w =
        ∑ i : Fin m, w (fourBlockFlatten m (3, Fin.revPerm i)) := by
      apply Finset.sum_congr rfl
      intro i hi
      apply congrArg w
      apply Fin.ext
      simp [quarterSumFour, outsideQuarterFour, Fin.revPerm_apply, Fin.rev]
      omega
    _ = ∑ i : Fin m, w (fourBlockFlatten m (3, i)) :=
      Equiv.sum_comp Fin.revPerm (fun i : Fin m ↦
        w (fourBlockFlatten m (3, i)))

theorem fourBlockTotal_eq_sum {m : ℕ}
    (w : Fin (2 * (m + m)) → ℝ) :
    fourBlockTotal w = ∑ i, w i := by
  rw [fourBlockTotal, quarterSumOne_eq_flatten,
    quarterSumTwo_eq_flatten, quarterSumThree_eq_flatten,
    quarterSumFour_eq_flatten]
  have hsum := (fourBlockFlatten m).sum_comp w
  rw [Fintype.sum_prod_type, Fin.sum_univ_four] at hsum
  exact hsum

theorem sortedWeight_sum {n : ℕ} (v : Fin n → ℝ) :
    (∑ i, sortedWeight v i) = ∑ i, v i := by
  exact Equiv.sum_comp (Tuple.sort v) v

theorem sortedNearTail_sum_le {k : ℕ} (v : Fin (2 * k + 1) → ℝ)
    (hv : ∀ i, 0 ≤ v i) :
    (∑ i, sortedNearTail v i) ≤ ∑ i, v i := by
  have hsplit := Fin.sum_univ_succ (sortedWeight v)
  have hzero : 0 ≤ sortedWeight v 0 := hv _
  have htail :
      (∑ i : Fin (2 * k), sortedNearTail v i) =
        ∑ i : Fin (2 * k), sortedWeight v i.succ := by
    apply Finset.sum_congr rfl
    intro i hi
    rfl
  rw [sortedWeight_sum] at hsplit
  rw [htail]
  linarith

theorem fourBlockTotal_sortedNearTail_le_topPathTotal
    {T m : ℕ} {h : StepSchedule T} (hh : IsNonnegativeSchedule h)
    (hm : 0 < m) (hq : 2 * (m + m) ≤ longCount h) :
    fourBlockTotal
        (sortedNearTail (topPathWeight h (2 * (m + m)) hq)) ≤
      2 * (2 * (m + m) : ℝ) * zetaState h (2 * (m + m)) +
        1 / ((2 * (m + m) : ℝ) - 1) := by
  have hq2 : 2 ≤ 2 * (m + m) := by omega
  have hv : ∀ i, 0 ≤ topPathWeight h (2 * (m + m)) hq i :=
    fun i ↦ (topPathWeight_pos hh hq2 hq i).le
  have htail := sortedNearTail_sum_le
    (topPathWeight h (2 * (m + m)) hq) hv
  have htotal := topPathWeight_sum (h := h) hq2 hq
  have hfour := fourBlockTotal_eq_sum
    (sortedNearTail (topPathWeight h (2 * (m + m)) hq))
  norm_num [Nat.cast_mul, Nat.cast_add] at htotal ⊢
  calc
    fourBlockTotal (sortedNearTail (topPathWeight h (2 * (m + m)) hq)) =
        ∑ i, sortedNearTail (topPathWeight h (2 * (m + m)) hq) i := hfour
    _ ≤ ∑ i, topPathWeight h (2 * (m + m)) hq i := htail
    _ = 2 * (2 * (↑m + ↑m)) * zetaState h (2 * (m + m)) +
        (2 * (↑m + ↑m) - 1)⁻¹ := htotal

end

end GDLowerBound.FourBlock
