import GDLowerBound.FourBlock.NearPerfectMatching

/-!
# Sorting and the exact near-perfect matching envelope

This module removes the last dependence on the original label order.  The
sorted tuple is supplied by Mathlib's permutation-valued tuple sorter.
-/

namespace GDLowerBound.FourBlock

open scoped BigOperators
open GDLowerBound.Matching

noncomputable section

def sortedWeight {n : ℕ} (v : Fin n → ℝ) : Fin n → ℝ :=
  v ∘ Tuple.sort v

theorem sortedWeight_monotone {n : ℕ} (v : Fin n → ℝ) :
    Monotone (sortedWeight v) := by
  exact Tuple.monotone_sort v

theorem sortedWeight_pos {n : ℕ} {v : Fin n → ℝ} (hv : ∀ i, 0 < v i) :
    ∀ i, 0 < sortedWeight v i := by
  intro i
  exact hv _

def sortedNearTail {k : ℕ} (v : Fin (2 * k + 1) → ℝ) : Fin (2 * k) → ℝ :=
  tailWeight (sortedWeight v)

/-- Any labelled near-perfect matching is dominated by the outside-in
matching of the largest `2*k` sorted weights. -/
theorem edgeMatchingProduct_le_sortedNearOutsideIn {k : ℕ}
    (v : Fin (2 * k + 1) → ℝ) (hv : ∀ i, 0 < v i)
    (M : LabeledMatching (Fin (2 * k + 1)) k) :
    edgeMatchingProduct v M ≤ outsideInProduct k (sortedNearTail v) := by
  let σ : Equiv.Perm (Fin (2 * k + 1)) := Tuple.sort v
  let ws : Fin (2 * k + 1) → ℝ := sortedWeight v
  let M' : LabeledMatching (Fin (2 * k + 1)) k := M.relabel σ.symm
  have heq : edgeMatchingProduct v M = edgeMatchingProduct ws M' := by
    have hrel := edgeMatchingProduct_relabel σ.symm ws M
    symm
    simpa only [ws, sortedWeight, σ, Function.comp_apply,
      Equiv.apply_symm_apply] using hrel
  rw [heq]
  exact edgeMatchingProduct_le_nearOutsideIn ws (sortedWeight_pos hv)
    (sortedWeight_monotone v) M'

theorem Pedge_le_sortedNearOutsideIn {k : ℕ}
    (v : Fin (2 * k + 1) → ℝ) (hv : ∀ i, 0 < v i) :
    Pedge v k ≤ outsideInProduct k (sortedNearTail v) := by
  have hcard : 2 * k ≤ Fintype.card (Fin (2 * k + 1)) := by
    simp
  obtain ⟨M, hM⟩ := exists_edgeMatchingProduct_eq_Pedge v
    ((labeledMatching_nonempty_iff k).2 hcard)
  rw [← hM]
  exact edgeMatchingProduct_le_sortedNearOutsideIn v hv M

@[simp]
theorem kPlus_even (k : ℕ) : kPlus (2 * k) = k := by
  simp only [kPlus]
  omega

@[simp]
theorem kMinus_even (k : ℕ) : kMinus (2 * k) = k := by
  simp only [kMinus]
  omega

/-- For an even augmented path, both parity matchings have the same size and
are bounded by the same sorted outside-in product. -/
theorem edgeMatchingEnvelope_even_le_sortedOutsideIn_sq {k : ℕ}
    (v : Fin (2 * k + 1) → ℝ) (hv : ∀ i, 0 < v i) :
    edgeMatchingEnvelope v ≤ outsideInProduct k (sortedNearTail v) ^ 2 := by
  have hP := Pedge_le_sortedNearOutsideIn v hv
  have hP0 : 0 ≤ Pedge v k := by
    apply Pedge_nonneg (fun i ↦ (hv i).le)
    rw [labeledMatching_nonempty_iff]
    simp
  have hout0 : 0 ≤ outsideInProduct k (sortedNearTail v) := by
    apply Finset.prod_nonneg
    intro i _
    exact (edgeKernel_pos (tailWeight_pos (sortedWeight_pos hv) _)
      (tailWeight_pos (sortedWeight_pos hv) _)).le
  unfold edgeMatchingEnvelope
  simp only [kPlus_even, kMinus_even, pow_two]
  exact mul_le_mul hP hP hP0 hout0

end

end GDLowerBound.FourBlock
