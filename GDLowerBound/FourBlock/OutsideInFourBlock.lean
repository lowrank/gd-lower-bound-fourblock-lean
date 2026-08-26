import GDLowerBound.FourBlock.SortedEndpoint
import Mathlib.Analysis.Convex.Jensen

/-!
# From the exact outside-in product to four block means

This file contains the finite Jensen step used after the exact matching
theorem.  It is deliberately stated without limits or asymptotic notation.
-/

namespace GDLowerBound.FourBlock

open scoped BigOperators

noncomputable section

/-- The arithmetic mean of a nonempty finite tuple. -/
def finMean {m : ℕ} (u : Fin m → ℝ) : ℝ :=
  (∑ i, u i) / m

/-- Finite Jensen for the exact logarithmic edge kernel. -/
theorem mean_logKernel_le_logKernel_means {m : ℕ} (hm : 0 < m)
    (u v : Fin m → ℝ) (hu : ∀ i, 0 < u i) (hv : ∀ i, 0 < v i) :
    (∑ i, logKernel (u i) (v i)) / m ≤
      logKernel (finMean u) (finMean v) := by
  let p : Fin m → ℝ × ℝ := fun i ↦ (u i, v i)
  let c : Fin m → ℝ := fun _ ↦ ((m : ℝ)⁻¹)
  have hc0 : ∀ i ∈ (Finset.univ : Finset (Fin m)), 0 ≤ c i := by
    intro i hi
    positivity
  have hcsum : ∑ i ∈ (Finset.univ : Finset (Fin m)), c i = 1 := by
    simp [c, hm.ne']
  have hp : ∀ i ∈ (Finset.univ : Finset (Fin m)), p i ∈ positiveQuadrant := by
    intro i hi
    exact ⟨hu i, hv i⟩
  have hJ := pairLogKernelClosed_concave.le_map_sum hc0 hcsum hp
  have hsumU : 0 < ∑ i, u i := by
    apply Finset.sum_pos
    · intro i hi
      exact hu i
    · exact ⟨⟨0, hm⟩, Finset.mem_univ _⟩
  have hsumV : 0 < ∑ i, v i := by
    apply Finset.sum_pos
    · intro i hi
      exact hv i
    · exact ⟨⟨0, hm⟩, Finset.mem_univ _⟩
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hmeanU : 0 < finMean u := by
    exact div_pos hsumU hmR
  have hmeanV : 0 < finMean v := by
    exact div_pos hsumV hmR
  have hpair :
      (∑ i ∈ (Finset.univ : Finset (Fin m)), c i • p i) =
        (finMean u, finMean v) := by
    apply Prod.ext
    · simp only [Prod.fst_sum, Prod.smul_fst, smul_eq_mul]
      simp [finMean, c, p, div_eq_mul_inv, mul_comm, Finset.sum_mul]
    · simp only [Prod.snd_sum, Prod.smul_snd, smul_eq_mul]
      simp [finMean, c, p, div_eq_mul_inv, mul_comm, Finset.sum_mul]
  calc
    (∑ i, logKernel (u i) (v i)) / m =
        ∑ i, c i • pairLogKernelClosed (p i) := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro i hi
      rw [pairLogKernelClosed_eq ⟨hu i, hv i⟩]
      simp [c, p, div_eq_mul_inv, mul_comm]
    _ ≤ pairLogKernelClosed
          (∑ i ∈ (Finset.univ : Finset (Fin m)), c i • p i) := hJ
    _ = pairLogKernelClosed (finMean u, finMean v) := by rw [hpair]
    _ = logKernel (finMean u) (finMean v) :=
      pairLogKernelClosed_eq ⟨hmeanU, hmeanV⟩

end

end GDLowerBound.FourBlock
