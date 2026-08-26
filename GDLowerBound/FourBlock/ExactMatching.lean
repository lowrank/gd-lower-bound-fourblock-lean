import GDLowerBound.FourBlock.ExactAugmentedPath

/-!
# Finite matchings for the exact envelope kernel

This is the order-free matching layer for `edgeKernel`.  It deliberately uses
the same labelled-matching type and parity matchings as Ma--Chen's `psi`
argument, but maximizes the sharper exact kernel instead.
-/

namespace GDLowerBound.FourBlock

open scoped BigOperators
open GDLowerBound.Matching

noncomputable section

def edgeMatchingProduct {α : Type*} {k : ℕ} (w : α → ℝ)
    (M : LabeledMatching α k) : ℝ :=
  ∏ i, edgeKernel (w (M.left i)) (w (M.right i))

@[simp]
theorem edgeMatchingProduct_zero {α : Type*} (w : α → ℝ)
    (M : LabeledMatching α 0) : edgeMatchingProduct w M = 1 := by
  simp [edgeMatchingProduct]

def edgeMatchingValues [Fintype α] (w : α → ℝ) (k : ℕ) : Finset ℝ :=
  Finset.univ.image (fun M : LabeledMatching α k ↦ edgeMatchingProduct w M)

noncomputable def Pedge [Fintype α] (w : α → ℝ) (k : ℕ) : ℝ :=
  if h : (edgeMatchingValues w k).Nonempty then
    (edgeMatchingValues w k).max' h
  else 0

theorem edgeMatchingValues_nonempty [Fintype α] (w : α → ℝ) {k : ℕ}
    (M : LabeledMatching α k) : (edgeMatchingValues w k).Nonempty := by
  exact ⟨edgeMatchingProduct w M,
    Finset.mem_image.mpr ⟨M, Finset.mem_univ _, rfl⟩⟩

theorem edgeMatchingProduct_le_Pedge [Fintype α] (w : α → ℝ) {k : ℕ}
    (M : LabeledMatching α k) : edgeMatchingProduct w M ≤ Pedge w k := by
  classical
  let hne := edgeMatchingValues_nonempty w M
  rw [Pedge, dif_pos hne]
  exact Finset.le_max' _ _
    (Finset.mem_image.mpr ⟨M, Finset.mem_univ _, rfl⟩)

theorem exists_edgeMatchingProduct_eq_Pedge [Fintype α] (w : α → ℝ) {k : ℕ}
    (hne : Nonempty (LabeledMatching α k)) :
    ∃ M : LabeledMatching α k, edgeMatchingProduct w M = Pedge w k := by
  classical
  let M₀ := Classical.choice hne
  let hs := edgeMatchingValues_nonempty w M₀
  rw [Pedge, dif_pos hs]
  have hmem := Finset.max'_mem (edgeMatchingValues w k) hs
  rcases Finset.mem_image.mp hmem with ⟨M, _, hM⟩
  exact ⟨M, hM⟩

theorem edgeMatchingProduct_nonneg {α : Type*} {k : ℕ} {w : α → ℝ}
    (hw : ∀ a, 0 ≤ w a) (M : LabeledMatching α k) :
    0 ≤ edgeMatchingProduct w M := by
  apply Finset.prod_nonneg
  intro i _
  by_cases hzero : w (M.left i) + w (M.right i) = 0
  · have hleft : w (M.left i) = 0 := by
      have := hw (M.left i)
      have := hw (M.right i)
      linarith
    have hright : w (M.right i) = 0 := by
      have := hw (M.left i)
      have := hw (M.right i)
      linarith
    simp [edgeKernel, hleft, hright]
  · have hsum : 0 < w (M.left i) + w (M.right i) :=
      lt_of_le_of_ne (add_nonneg (hw _) (hw _)) (Ne.symm hzero)
    have hb : 0 ≤ edgeParameter (w (M.left i)) (w (M.right i)) :=
      edgeParameter_nonneg (hw (M.left i)) (hw (M.right i))
    unfold edgeKernel
    exact mul_nonneg (by linarith) (envelope_pos hb).le

theorem Pedge_nonneg [Fintype α] {w : α → ℝ} {k : ℕ}
    (hw : ∀ a, 0 ≤ w a) (hne : Nonempty (LabeledMatching α k)) :
    0 ≤ Pedge w k := by
  obtain ⟨M, hM⟩ := exists_edgeMatchingProduct_eq_Pedge w hne
  rw [← hM]
  exact edgeMatchingProduct_nonneg hw M

/-- Product of the two parity matchings, using the exact envelope kernel. -/
def edgeParityProduct {q : ℕ} (v : Fin (q + 1) → ℝ) : ℝ :=
  edgeMatchingProduct v (evenEdgeMatching q) *
    edgeMatchingProduct v (oddEdgeMatching q)

/-- Order-free product of the two exact matching maxima. -/
def edgeMatchingEnvelope {q : ℕ} (v : Fin (q + 1) → ℝ) : ℝ :=
  Pedge v (kPlus q) * Pedge v (kMinus q)

/-- Alternating edges partition the augmented path for the exact kernel too. -/
theorem edgeParityProduct_eq_chronological {q : ℕ}
    (v : Fin (q + 1) → ℝ) :
    edgeParityProduct v = chronologicalEdgeKernelProduct v := by
  let f : Fin q → ℝ := fun i ↦ edgeKernel (v i.castSucc) (v i.succ)
  calc
    edgeParityProduct v =
        ∏ z : Fin (kPlus q) ⊕ Fin (kMinus q),
          f (edgeParityEquiv q z) := by
      rw [Fintype.prod_sum_type]
      apply congrArg₂ (fun x y : ℝ ↦ x * y)
      · apply Finset.prod_congr rfl
        intro i _
        simp only [edgeMatchingProduct, f, edgeParityEquiv_apply,
          edgeParityMap]
        apply congrArg₂ edgeKernel
        · apply congrArg v
          apply Fin.ext
          simp
        · apply congrArg v
          apply Fin.ext
          simp
      · apply Finset.prod_congr rfl
        intro i _
        simp only [edgeMatchingProduct, f, edgeParityEquiv_apply,
          edgeParityMap]
        apply congrArg₂ edgeKernel
        · apply congrArg v
          apply Fin.ext
          simp
        · apply congrArg v
          apply Fin.ext
          simp
    _ = ∏ i : Fin q, f i := (edgeParityEquiv q).prod_comp f
    _ = chronologicalEdgeKernelProduct v := rfl

theorem edgeParityProduct_le_matchingEnvelope {q : ℕ}
    (v : Fin (q + 1) → ℝ) (hv : ∀ i, 0 ≤ v i) :
    edgeParityProduct v ≤ edgeMatchingEnvelope v := by
  have hcard : 2 * kPlus q ≤ Fintype.card (Fin (q + 1)) := by
    simpa using two_kPlus_le q
  have hplus : 0 ≤ Pedge v (kPlus q) :=
    Pedge_nonneg hv ((labeledMatching_nonempty_iff (kPlus q)).2 hcard)
  exact mul_le_mul
    (edgeMatchingProduct_le_Pedge v (evenEdgeMatching q))
    (edgeMatchingProduct_le_Pedge v (oddEdgeMatching q))
    (edgeMatchingProduct_nonneg hv (oddEdgeMatching q)) hplus

theorem chronologicalEdgeKernelProduct_le_matchingEnvelope {q : ℕ}
    (v : Fin (q + 1) → ℝ) (hv : ∀ i, 0 ≤ v i) :
    chronologicalEdgeKernelProduct v ≤ edgeMatchingEnvelope v := by
  rw [← edgeParityProduct_eq_chronological]
  exact edgeParityProduct_le_matchingEnvelope v hv

end

end GDLowerBound.FourBlock
