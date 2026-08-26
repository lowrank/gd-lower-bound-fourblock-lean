import GDLowerBound.FourBlock.FiniteWindowDyadicUniform
import GDLowerBound.RankAnalysis.Normalized

/-!
# Maximal dyadic windows near a terminal rank

The global scan chooses the largest dyadic endpoint still below the terminal
rank.  Its endpoint is within a factor two of the terminal rank, so ordinary
boundary propagation on the remaining tail costs only a fixed factor.
-/

namespace GDLowerBound.FourBlock

open GDLowerBound.Schedule GDLowerBound.RankAnalysis

noncomputable section

/-- A maximal admissible dyadic depth has its four-block endpoint below `r`
and within a factor two of `r`. -/
theorem exists_maximalDyadicDepth
    {M r R₀ : ℕ} (hM : 1 ≤ M)
    (hbase : 4 * ((2 ^ R₀) * M) ≤ r) :
    ∃ R : ℕ, R₀ ≤ R ∧
      4 * ((2 ^ R) * M) ≤ r ∧ r < 8 * ((2 ^ R) * M) := by
  classical
  let depths : Finset ℕ :=
    (Finset.range (r + 1)).filter
      (fun R ↦ 4 * ((2 ^ R) * M) ≤ r)
  have hR₀r : R₀ < r + 1 := by
    have hRpow : R₀ < 2 ^ R₀ := R₀.lt_two_pow_self
    have hpowBlock : 2 ^ R₀ ≤ 4 * ((2 ^ R₀) * M) := by
      have hp : 0 < 2 ^ R₀ := pow_pos (by omega : 0 < 2) R₀
      nlinarith
    omega
  have hR₀mem : R₀ ∈ depths := by
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hR₀r, hbase⟩
  have hnonempty : depths.Nonempty := ⟨R₀, hR₀mem⟩
  let R := depths.max' hnonempty
  have hRmem : R ∈ depths := depths.max'_mem hnonempty
  have hRdata := Finset.mem_filter.mp hRmem
  refine ⟨R, depths.le_max' R₀ hR₀mem, hRdata.2, ?_⟩
  by_contra hnot
  have hnextBound : 4 * ((2 ^ (R + 1)) * M) ≤ r := by
    have hrewrite :
        4 * ((2 ^ (R + 1)) * M) = 8 * ((2 ^ R) * M) := by
      simp only [pow_succ]
      ring
    rw [hrewrite]
    omega
  have hnextRange : R + 1 < r + 1 := by
    have hnextPow : R + 1 < 2 ^ (R + 1) := (R + 1).lt_two_pow_self
    have hpowBlock : 2 ^ (R + 1) ≤ 4 * ((2 ^ (R + 1)) * M) := by
      have hp : 0 < 2 ^ (R + 1) := pow_pos (by omega : 0 < 2) (R + 1)
      nlinarith
    omega
  have hnextMem : R + 1 ∈ depths := by
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr hnextRange, hnextBound⟩
  have := depths.le_max' (R + 1) hnextMem
  omega

/-- Boundary propagation from a rank lying within a factor two of the
terminal rank.  The rank-dependent power is converted into the fixed loss
`2^(p-1)`. -/
theorem unresolvedMass_le_boundaryConstant_mul_two_rpow
    {T Q k : ℕ} {p : ℝ} {h : StepSchedule T}
    (hp : 1 < p) (hQ2 : 2 ≤ Q)
    (hQtheta : (lyapunovTheta p)⁻¹ < (Q : ℝ))
    (hh : IsNonnegativeSchedule h)
    (hk : 1 ≤ k) (hQk : Q ≤ k) (hkr : k ≤ longCount h)
    (hnear : longCount h < 2 * k)
    (hcut : CutoffConditions p h (k + 1) (longCount h)) :
    unresolvedMass h k ≤
      boundaryPropagationConstant p * cappedMass h *
        ((2 : ℝ) ^ (p - 1)) := by
  have hboundary := boundaryPropagation hp hQ2 hQtheta hh hQk hkr hcut
  have hkR : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hrR : (0 : ℝ) < longCount h := by
    exact hkR.trans_le (by exact_mod_cast hkr)
  have hkpow : 0 < (k : ℝ) ^ (p - 1) := Real.rpow_pos_of_pos hkR _
  have hdiv :
      unresolvedMass h k ≤
        (boundaryPropagationConstant p * cappedMass h *
          ((longCount h : ℝ) ^ (p - 1))) /
            ((k : ℝ) ^ (p - 1)) := by
    exact (le_div_iff₀ hkpow).2 hboundary
  have hratioPos : 0 < (longCount h : ℝ) / (k : ℝ) := div_pos hrR hkR
  have hratio : (longCount h : ℝ) / (k : ℝ) < 2 := by
    apply (div_lt_iff₀ hkR).2
    exact_mod_cast hnear
  have hexponent : 0 ≤ p - 1 := by linarith
  have hrpow :
      ((longCount h : ℝ) / (k : ℝ)) ^ (p - 1) ≤
        (2 : ℝ) ^ (p - 1) :=
    Real.rpow_le_rpow hratioPos.le hratio.le hexponent
  have hKB : 0 ≤ boundaryPropagationConstant p * cappedMass h := by
    have hK := boundaryPropagationConstant_ge_one hp
    positivity [cappedMass_pos hh]
  calc
    unresolvedMass h k ≤
        (boundaryPropagationConstant p * cappedMass h *
          ((longCount h : ℝ) ^ (p - 1))) /
            ((k : ℝ) ^ (p - 1)) := hdiv
    _ = boundaryPropagationConstant p * cappedMass h *
          (((longCount h : ℝ) / (k : ℝ)) ^ (p - 1)) := by
      rw [Real.div_rpow hrR.le hkR.le]
      field_simp [hkpow.ne']
    _ ≤ boundaryPropagationConstant p * cappedMass h *
          ((2 : ℝ) ^ (p - 1)) :=
      mul_le_mul_of_nonneg_left hrpow hKB

end

end GDLowerBound.FourBlock
