import GDLowerBound.FourBlock.IdealPrefixCoordinates

/-!
# Interlacing after inserting one auxiliary weight

If one entry is appended to a finite tuple, then the sorted tuple with its
smallest entry removed dominates the sorted original tuple pointwise.  This
is the exact order-statistic fact needed to control the auxiliary endpoint
vertex without assuming where it lies in the sorted order.
-/

namespace GDLowerBound.FourBlock

open scoped BigOperators

noncomputable section

theorem filter_card_comp_perm {n : ℕ} (v : Fin n → ℝ)
    (σ : Equiv.Perm (Fin n)) (c : ℝ) :
    (Finset.univ.filter (fun i ↦ v (σ i) ≤ c)).card =
      (Finset.univ.filter (fun i ↦ v i ≤ c)).card := by
  simp_rw [Finset.card_filter]
  simpa only [Finset.sum_filter, Finset.sum_const_zero, add_zero] using
    (Equiv.sum_comp σ (fun i ↦ if v i ≤ c then 1 else 0))

theorem filter_card_castSucc_add_last {n : ℕ}
    (v : Fin (n + 1) → ℝ) (c : ℝ) :
    (Finset.univ.filter (fun i ↦ v i ≤ c)).card =
      (Finset.univ.filter (fun i : Fin n ↦ v i.castSucc ≤ c)).card +
        if v (Fin.last n) ≤ c then 1 else 0 := by
  simp_rw [Finset.card_filter]
  simpa only [Finset.sum_filter, Finset.sum_const_zero, add_zero] using
    (Fin.sum_univ_castSucc (fun i ↦ if v i ≤ c then 1 else 0))

/-- Order-statistic interlacing under insertion of one arbitrary entry. -/
theorem sortedWeight_castSucc_le_sortedWeight_succ {n : ℕ}
    (v : Fin (n + 1) → ℝ) (i : Fin n) :
    sortedWeight (fun j : Fin n ↦ v j.castSucc) i ≤
      sortedWeight v i.succ := by
  let x : Fin n → ℝ := sortedWeight (fun j : Fin n ↦ v j.castSucc)
  let y : Fin (n + 1) → ℝ := sortedWeight v
  let j : Fin (n + 1) := ⟨i.val + 1, by omega⟩
  let c : ℝ := y j
  have hy : Monotone y := sortedWeight_monotone v
  have hx : Monotone x := sortedWeight_monotone _
  have hyv : j.val <
      (Finset.univ.filter (fun k ↦ y k ≤ c)).card :=
    (Tuple.lt_card_le_iff_apply_le_of_monotone hy).2 le_rfl
  have hpermV :
      (Finset.univ.filter (fun k ↦ y k ≤ c)).card =
        (Finset.univ.filter (fun k ↦ v k ≤ c)).card := by
    exact filter_card_comp_perm v (Tuple.sort v) c
  have hsplit := filter_card_castSucc_add_last v c
  have hpermX :
      (Finset.univ.filter (fun k ↦ x k ≤ c)).card =
        (Finset.univ.filter
          (fun k : Fin n ↦ v k.castSucc ≤ c)).card := by
    exact filter_card_comp_perm
      (fun k : Fin n ↦ v k.castSucc) (Tuple.sort _) c
  have hcount : i.val <
      (Finset.univ.filter (fun k ↦ x k ≤ c)).card := by
    dsimp only [j] at hyv
    rw [hpermV, hsplit] at hyv
    rw [hpermX]
    have hlast : (if v (Fin.last n) ≤ c then 1 else 0) ≤ 1 := by
      split_ifs <;> omega
    omega
  have hxi : x i ≤ c :=
    (Tuple.lt_card_le_iff_apply_le_of_monotone hx).1 hcount
  exact hxi

/-- For an even tuple, the near tail used by the matching construction
dominates the sorted tuple of genuine (non-auxiliary) entries pointwise. -/
theorem sortedWeight_castSucc_le_sortedNearTail {k : ℕ}
    (v : Fin (2 * k + 1) → ℝ) (i : Fin (2 * k)) :
    sortedWeight (fun j : Fin (2 * k) ↦ v j.castSucc) i ≤
      sortedNearTail v i := by
  exact sortedWeight_castSucc_le_sortedWeight_succ v i

end

end GDLowerBound.FourBlock
