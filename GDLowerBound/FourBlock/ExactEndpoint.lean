import GDLowerBound.FourBlock.ExactPath
import GDLowerBound.Matching.Endpoint

/-!
# Finite exact-envelope endpoint bound

This is the exact-envelope analogue of the product stage in Ma--Chen's
`topChain_reciprocalProduct_le_path`.  Its conclusion retains the single
terminal factor and has no `O(1/q)` term.
-/

namespace GDLowerBound.FourBlock

open scoped BigOperators
open GDLowerBound.Schedule GDLowerBound.RankAnalysis GDLowerBound.Matching

noncomputable section

theorem topChain_reciprocalProduct_le_exactInternalPath
    {T n : ℕ} {h : StepSchedule T} (hh : IsNonnegativeSchedule h)
    (hn : 0 < n) (hq : n + 1 ≤ longCount h) :
    (topChain h (n + 1)).terminalScale *
        ∏ i : Fin (n + 1),
          (chronologicalLocalBound h (n + 1) hq i)⁻¹ ≤
      (1 + 2 * unresolvedMass h (n + 1) *
          (chronologicalExcess h (n + 1) hq (Fin.last n))⁻¹) *
        (unresolvedMass h (n + 1) / (n + 1)) *
        ∏ i : Fin n,
          edgeKernel
            (topPathWeight h (n + 1) hq i.castSucc.castSucc)
            (topPathWeight h (n + 1) hq i.succ.castSucc) := by
  let c : Chain h := topChain h (n + 1)
  let D : ℝ := unresolvedMass h (n + 1)
  let e : Fin (n + 1) → Fin c.length :=
    topChainIndex h (n + 1) hq
  let u : Fin (n + 1) → ℝ :=
    chronologicalPrecedingMass h (n + 1) hq
  let xi : Fin (n + 1) → ℝ := fun i ↦
    (chronologicalExcess h (n + 1) hq i)⁻¹
  let chi : Fin (n + 1) → ℝ :=
    chronologicalLocalBound h (n + 1) hq
  have hlen : c.length = n + 1 := topChain_length_of_le h hq
  have hD : 0 < D := unresolvedMass_pos hh (n + 1)
  have hu (i : Fin (n + 1)) : 0 < u i :=
    chronologicalPrecedingMass_pos hh (n + 1) hq i
  have hxi (i : Fin (n + 1)) : 0 < xi i :=
    inv_pos.mpr (chronologicalExcess_pos h (n + 1) hq i)
  have hmass : ∑ i, u i ≤ D :=
    chronologicalPrecedingMass_sum_le hh hq
  have hinternal (i : Fin n) :
      (chi i.castSucc)⁻¹ ≤
        u i.castSucc *
          (pathA xi i.castSucc + pathB xi i.castSucc * u i.castSucc) := by
    have hi : (e i.castSucc).val + 1 < c.length := by
      change i.val + 1 < c.length
      rw [topChain_length_of_le h hq]
      omega
    have hnext :
        (⟨(e i.castSucc).val + 1, hi⟩ : Fin c.length) = e i.succ := by
      apply Fin.ext
      simp [e]
    have hlocal := localBound_inv_le_next c hh (e i.castSucc) hi
    rw [hnext] at hlocal
    have hlocal' :
        (chi i.castSucc)⁻¹ ≤
          u i.castSucc * (xi i.castSucc + xi i.succ) +
            u i.castSucc ^ 2 * (xi i.castSucc * xi i.succ) := by
      simpa only [c, e, u, xi, chi, chronologicalLocalBound,
        chronologicalPrecedingMass, chronologicalExcess] using hlocal
    calc
      (chi i.castSucc)⁻¹ ≤
          u i.castSucc * (xi i.castSucc + xi i.succ) +
            u i.castSucc ^ 2 * (xi i.castSucc * xi i.succ) := hlocal'
      _ = u i.castSucc *
          (pathA xi i.castSucc + pathB xi i.castSucc * u i.castSucc) := by
        simp only [pathA, pathB, Fin.lastCases_castSucc]
        ring
  have hterminal :
      c.terminalScale * (chi (Fin.last n))⁻¹ ≤
        u (Fin.last n) *
          (1 + 2 * D * xi (Fin.last n)) := by
    have hterminalMass := chronologicalLastMass_add_terminal_le hh n hq
    have hlocal := terminal_localBound_inv_le c hh n hlen
      (D := D) (by simpa only [c, e, u, D, topChainIndex,
        chronologicalPrecedingMass] using hterminalMass)
    simpa only [c, e, u, xi, chi, chronologicalLocalBound,
      chronologicalPrecedingMass, chronologicalExcess, topChainIndex] using hlocal
  have hprodInternal :
      (∏ i : Fin n, (chi i.castSucc)⁻¹) ≤
        ∏ i : Fin n,
          u i.castSucc *
            (pathA xi i.castSucc + pathB xi i.castSucc * u i.castSucc) := by
    apply Finset.prod_le_prod
    · intro i _
      exact (inv_pos.mpr
        (chronologicalLocalBound_pos hh (n + 1) hq i.castSucc)).le
    · intro i _
      exact hinternal i
  have hprodNonneg : 0 ≤
      ∏ i : Fin n,
        u i.castSucc *
          (pathA xi i.castSucc + pathB xi i.castSucc * u i.castSucc) := by
    apply Finset.prod_nonneg
    intro i _
    have hA : 0 < pathA xi i.castSucc := by
      simp only [pathA, Fin.lastCases_castSucc]
      exact add_pos (hxi _) (hxi _)
    have hB : 0 ≤ pathB xi i.castSucc := by
      simp only [pathB, Fin.lastCases_castSucc]
      exact mul_nonneg (hxi _).le (hxi _).le
    exact mul_nonneg (hu _).le
      (add_nonneg hA.le (mul_nonneg hB (hu _).le))
  have hterminalNonneg : 0 ≤
      c.terminalScale * (chi (Fin.last n))⁻¹ := by
    exact mul_nonneg (c.terminalScale_pos hh).le
      (inv_nonneg.mpr
        (chronologicalLocalBound_pos hh (n + 1) hq (Fin.last n)).le)
  have hmultiplied := mul_le_mul hprodInternal hterminal
    hterminalNonneg hprodNonneg
  have hlocalProduct :
      c.terminalScale * ∏ i : Fin (n + 1), (chi i)⁻¹ ≤
        (1 + 2 * D * xi (Fin.last n)) *
          ∏ i : Fin (n + 1),
            u i * (pathA xi i + pathB xi i * u i) := by
    calc
      c.terminalScale * ∏ i : Fin (n + 1), (chi i)⁻¹ =
          (∏ i : Fin n, (chi i.castSucc)⁻¹) *
            (c.terminalScale * (chi (Fin.last n))⁻¹) := by
        rw [Fin.prod_univ_castSucc]
        ring
      _ ≤ (∏ i : Fin n,
            u i.castSucc *
              (pathA xi i.castSucc + pathB xi i.castSucc * u i.castSucc)) *
          (u (Fin.last n) * (1 + 2 * D * xi (Fin.last n))) := hmultiplied
      _ = (1 + 2 * D * xi (Fin.last n)) *
          ∏ i : Fin (n + 1),
            u i * (pathA xi i + pathB xi i * u i) := by
        rw [Fin.prod_univ_castSucc]
        simp only [pathA, pathB, Fin.lastCases_last, zero_mul, add_zero]
        ring
  have heq := coupledEqualization_exactPath D hD u xi hu hxi hmass
  have hterminalFactor : 0 ≤ 1 + 2 * D * xi (Fin.last n) := by
    have hprod : 0 ≤ 2 * D * xi (Fin.last n) :=
      mul_nonneg (mul_nonneg (by norm_num) hD.le) (hxi _).le
    linarith
  have hscaled := mul_le_mul_of_nonneg_left heq hterminalFactor
  have hv (i : Fin (n + 1)) :
      scaledPathWeight D xi i = topPathWeight h (n + 1) hq i.castSucc := by
    calc
      scaledPathWeight D xi i =
          2 * D / ((n : ℝ) + 1) * xi i := by
        simp only [scaledPathWeight, Nat.cast_add, Nat.cast_one]
        ring
      _ = topPathWeight h (n + 1) hq i.castSucc := by
        simpa only [D, xi, Nat.cast_add, Nat.cast_one] using
          (topPathWeight_castSucc h (by omega) hq i).symm
  change c.terminalScale * ∏ i : Fin (n + 1), (chi i)⁻¹ ≤ _
  calc
    c.terminalScale * ∏ i : Fin (n + 1), (chi i)⁻¹ ≤
        (1 + 2 * D * xi (Fin.last n)) *
          ∏ i : Fin (n + 1),
            u i * (pathA xi i + pathB xi i * u i) := hlocalProduct
    _ ≤ (1 + 2 * D * xi (Fin.last n)) *
        ((D / (n + 1)) *
          ∏ i : Fin n,
            edgeKernel (scaledPathWeight D xi i.castSucc)
              (scaledPathWeight D xi i.succ)) := hscaled
    _ = (1 + 2 * unresolvedMass h (n + 1) *
          (chronologicalExcess h (n + 1) hq (Fin.last n))⁻¹) *
        (unresolvedMass h (n + 1) / (n + 1)) *
        ∏ i : Fin n,
          edgeKernel
            (topPathWeight h (n + 1) hq i.castSucc.castSucc)
            (topPathWeight h (n + 1) hq i.succ.castSucc) := by
      dsimp only [D, xi]
      simp_rw [← hv]
      ring

end

end GDLowerBound.FourBlock
