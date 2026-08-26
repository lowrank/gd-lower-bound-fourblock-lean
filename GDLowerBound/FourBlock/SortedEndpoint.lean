import GDLowerBound.FourBlock.SortedMatching
import GDLowerBound.FourBlock.ExactAugmentedRank

/-!
# Exact schedule endpoint bound in sorted outside-in form

This composes the exact augmented-path estimate, parity splitting, finite
matching maximization, sorting, and outside-in exchange.  The statement is
fully finite and contains no asymptotic error.
-/

namespace GDLowerBound.FourBlock

open scoped BigOperators
open GDLowerBound.Schedule GDLowerBound.RankAnalysis GDLowerBound.Matching

noncomputable section

theorem chronologicalEdgeKernelProduct_even_le_sortedOutsideIn_sq {k : ℕ}
    (v : Fin (2 * k + 1) → ℝ) (hv : ∀ i, 0 < v i) :
    chronologicalEdgeKernelProduct v ≤
      outsideInProduct k (sortedNearTail v) ^ 2 := by
  calc
    chronologicalEdgeKernelProduct v ≤ edgeMatchingEnvelope v :=
      chronologicalEdgeKernelProduct_le_matchingEnvelope v (fun i ↦ (hv i).le)
    _ ≤ outsideInProduct k (sortedNearTail v) ^ 2 :=
      edgeMatchingEnvelope_even_le_sortedOutsideIn_sq v hv

/-- Exact finite outside-in endpoint bound at every positive even rank. -/
theorem topChain_reciprocalProduct_le_sortedOutsideIn
    {T k : ℕ} {h : StepSchedule T} (hh : IsNonnegativeSchedule h)
    (hk : 0 < k) (hq : 2 * k ≤ longCount h) :
    (topChain h (2 * k)).terminalScale *
        ∏ i : Fin (2 * k),
          (chronologicalLocalBound h (2 * k) hq i)⁻¹ ≤
      (4 * unresolvedMass h (2 * k) * (2 * k - 1) / (2 * k)) *
        outsideInProduct k
          (sortedNearTail (topPathWeight h (2 * k) hq)) ^ 2 := by
  have haug := topChain_reciprocalProduct_le_exactAugmentedPath_rank
    (h := h) hh (by omega : 2 ≤ 2 * k) hq
  have hv : ∀ i, 0 < topPathWeight h (2 * k) hq i :=
    topPathWeight_pos hh (by omega : 2 ≤ 2 * k) hq
  have hpath := chronologicalEdgeKernelProduct_even_le_sortedOutsideIn_sq
    (topPathWeight h (2 * k) hq) hv
  have hcoeff :
      0 ≤ 4 * unresolvedMass h (2 * k) * (2 * k - 1) / (2 * k) := by
    have hD := unresolvedMass_pos hh (2 * k)
    have hkR : (1 : ℝ) ≤ 2 * (k : ℝ) := by
      exact_mod_cast (show 1 ≤ 2 * k by omega)
    have hnR : 0 ≤ 2 * (k : ℝ) - 1 := sub_nonneg.mpr hkR
    have hden : 0 ≤ 2 * (k : ℝ) := by positivity
    exact div_nonneg (mul_nonneg (mul_nonneg (by norm_num) hD.le) hnR) hden
  have hscaled := mul_le_mul_of_nonneg_left hpath hcoeff
  calc
    (topChain h (2 * k)).terminalScale *
          ∏ i : Fin (2 * k),
            (chronologicalLocalBound h (2 * k) hq i)⁻¹ ≤
        (4 * unresolvedMass h (2 * k) * (2 * k - 1) / (2 * k)) *
          chronologicalEdgeKernelProduct (topPathWeight h (2 * k) hq) := by
      norm_num [Nat.cast_mul, Nat.cast_sub (by omega : 1 ≤ 2 * k)] at haug
      simpa only [← Finset.prod_inv_distrib] using haug
    _ ≤ (4 * unresolvedMass h (2 * k) * (2 * k - 1) / (2 * k)) *
        outsideInProduct k
          (sortedNearTail (topPathWeight h (2 * k) hq)) ^ 2 := hscaled

end

end GDLowerBound.FourBlock
