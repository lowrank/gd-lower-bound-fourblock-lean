import GDLowerBound.FourBlock.ExactEndpoint

/-!
# Exact envelope bound on the augmented chronological path

The internal exact-envelope estimate still carries one terminal quadratic
factor.  This file identifies that factor with the auxiliary endpoint used by
Ma--Chen and bounds its `psi` edge by twice the exact envelope edge kernel.
Consequently every edge of the augmented path is governed by the same kernel,
with no limiting argument and no hidden error term.
-/

namespace GDLowerBound.FourBlock

open scoped BigOperators
open GDLowerBound.Schedule GDLowerBound.RankAnalysis GDLowerBound.Matching

noncomputable section

/-- Product of the exact envelope kernel over all edges of an augmented path. -/
def chronologicalEdgeKernelProduct {q : ℕ} (v : Fin (q + 1) → ℝ) : ℝ :=
  ∏ i : Fin q, edgeKernel (v i.castSucc) (v i.succ)

theorem edgeKernel_pos {u v : ℝ} (hu : 0 < u) (hv : 0 < v) :
    0 < edgeKernel u v := by
  unfold edgeKernel
  positivity [envelope_pos (edgeParameter_nonneg hu.le hv.le)]

/-- The terminal multiplier is exactly a `psi` edge to the auxiliary vertex. -/
theorem topPath_terminalFactor_eq_psi
    {T n : ℕ} {h : StepSchedule T} (hn : 0 < n)
    (hq : n + 1 ≤ longCount h) :
    (1 + 2 * unresolvedMass h (n + 1) *
        (chronologicalExcess h (n + 1) hq (Fin.last n))⁻¹) *
        (unresolvedMass h (n + 1) / (n + 1)) =
      (2 * unresolvedMass h (n + 1) * n / (n + 1)) *
        psi
          (topPathWeight h (n + 1) hq (Fin.last n).castSucc)
          (topPathWeight h (n + 1) hq (Fin.last n).succ) := by
  let D : ℝ := unresolvedMass h (n + 1)
  let xi : Fin (n + 1) → ℝ := fun i ↦
    (chronologicalExcess h (n + 1) hq i)⁻¹
  have hv := topPathWeight_castSucc h (by omega : 0 < n + 1) hq (Fin.last n)
  have haux : (Fin.last n).succ = Fin.last (n + 1) := Fin.succ_last n
  have hvlast :
      topPathWeight h (n + 1) hq (Fin.last (n + 1)) = 1 / (n : ℝ) := by
    simpa using topPathWeight_last h hq
  rw [hv, haux, hvlast]
  dsimp only [D, xi, psi]
  have hnreal : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hqreal : (n + 1 : ℝ) ≠ 0 := by positivity
  field_simp [hnreal, hqreal]
  norm_num [Nat.cast_add, Nat.cast_one]
  ring

/-- The exact finite endpoint estimate, now expressed by one uniform envelope
kernel on every edge of the augmented chronological path. -/
theorem topChain_reciprocalProduct_le_exactAugmentedPath
    {T n : ℕ} {h : StepSchedule T} (hh : IsNonnegativeSchedule h)
    (hn : 0 < n) (hq : n + 1 ≤ longCount h) :
    (topChain h (n + 1)).terminalScale *
        ∏ i : Fin (n + 1),
          (chronologicalLocalBound h (n + 1) hq i)⁻¹ ≤
      (4 * unresolvedMass h (n + 1) * n / (n + 1)) *
        chronologicalEdgeKernelProduct (topPathWeight h (n + 1) hq) := by
  let v : Fin (n + 2) → ℝ := topPathWeight h (n + 1) hq
  let D : ℝ := unresolvedMass h (n + 1)
  let xi : Fin (n + 1) → ℝ := fun i ↦
    (chronologicalExcess h (n + 1) hq i)⁻¹
  let I : ℝ := ∏ i : Fin n,
    edgeKernel (v i.castSucc.castSucc) (v i.succ.castSucc)
  let E : ℝ := edgeKernel (v (Fin.last n).castSucc) (v (Fin.last n).succ)
  have hbase := topChain_reciprocalProduct_le_exactInternalPath hh hn hq
  have hvpos : ∀ i, 0 < v i := fun i ↦
    topPathWeight_pos hh (by omega : 2 ≤ n + 1) hq i
  have hI : 0 ≤ I := by
    apply Finset.prod_nonneg
    intro i _
    exact (edgeKernel_pos (hvpos _) (hvpos _)).le
  have hpsi :
      psi (v (Fin.last n).castSucc) (v (Fin.last n).succ) ≤ 2 * E :=
    psi_le_two_edgeKernel (hvpos _) (hvpos _)
  have hcoeff : 0 ≤ 2 * D * n / (n + 1) := by
    have hD : 0 < D := unresolvedMass_pos hh (n + 1)
    positivity
  have hterminal := mul_le_mul_of_nonneg_left hpsi hcoeff
  have hid := topPath_terminalFactor_eq_psi (h := h) hn hq
  have hterminal' :
      (1 + 2 * D * xi (Fin.last n)) * (D / (n + 1)) ≤
        (4 * D * n / (n + 1)) * E := by
    calc
      (1 + 2 * D * xi (Fin.last n)) * (D / (n + 1)) =
          (2 * D * n / (n + 1)) *
            psi (v (Fin.last n).castSucc) (v (Fin.last n).succ) := by
        simpa only [D, xi, v] using hid
      _ ≤ (2 * D * n / (n + 1)) * (2 * E) := hterminal
      _ = (4 * D * n / (n + 1)) * E := by ring
  have hmul := mul_le_mul_of_nonneg_right hterminal' hI
  calc
    (topChain h (n + 1)).terminalScale *
          ∏ i : Fin (n + 1),
            (chronologicalLocalBound h (n + 1) hq i)⁻¹ ≤
        (1 + 2 * D * xi (Fin.last n)) * (D / (n + 1)) * I := by
      simpa only [D, xi, v, I, mul_assoc] using hbase
    _ ≤ (4 * D * n / (n + 1)) * E * I := by
      simpa only [mul_assoc] using hmul
    _ = (4 * unresolvedMass h (n + 1) * n / (n + 1)) *
        chronologicalEdgeKernelProduct (topPathWeight h (n + 1) hq) := by
      rw [show chronologicalEdgeKernelProduct v = I * E by
        unfold chronologicalEdgeKernelProduct I E
        rw [Fin.prod_univ_castSucc]
        rfl]
      dsimp only [D, v]
      ring

end

end GDLowerBound.FourBlock
