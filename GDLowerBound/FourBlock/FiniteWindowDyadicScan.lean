import GDLowerBound.FourBlock.FiniteWindowDyadicShortPropagation

/-!
# One step of the maximal-dyadic global scan

From any rank above the cutoff threshold, either its unresolved mass already
obeys the target `massExponent` bound, or the finite-window theorem produces
a strictly later rank with a direct functional contribution.
-/

namespace GDLowerBound.FourBlock

open GDLowerBound.Schedule GDLowerBound.RankAnalysis

noncomputable section

def UniformFiniteWindowDyadicDichotomy (R₀ M₀ : ℕ) : Prop :=
  3 ≤ R₀ ∧ 2000 ≤ M₀ ∧
    ∀ {T Q : ℕ} (hQ : criticalTheta⁻¹ < (Q : ℝ))
      {h : StepSchedule T}, IsNonnegativeSchedule h →
      ∀ R M : ℕ, R₀ ≤ R → M₀ ≤ M → Q ≤ 2 * M →
        4 * ((2 ^ R) * M) ≤ longCount h →
        CutoffConditions criticalP h (2 * M) (longCount h) →
        ((∃ m ∈ Finset.Ico (M + 1) ((2 ^ R) * M + 1),
            (4 : ℝ)⁻¹ / unresolvedMass h (4 * m) <
              lowerBoundFunctional h) ∨
          unresolvedMass h (2 * M) /
              unresolvedMass h (4 * ((2 ^ R) * M)) <
            Real.exp
              (massExponent * (R : ℝ) * Real.log 2 +
                betaLower * Real.log 2 +
                (betaLower - massExponent) / (M : ℝ)))

theorem exists_uniformFiniteWindowDyadicDichotomy :
    ∃ R₀ M₀ : ℕ, UniformFiniteWindowDyadicDichotomy R₀ M₀ := by
  obtain ⟨R₀, M₀, hR₀, hM₀, hrest⟩ :=
    exists_uniform_finiteWindowDyadic_dichotomy
  exact ⟨R₀, M₀, hR₀, hM₀, hrest⟩

def dyadicScanMassConstant (R₀ M₀ : ℕ) : ℝ :=
  max (dyadicShortMassConstant R₀ M₀)
    (dyadicTerminalMassConstant M₀)

theorem dyadicShortMassConstant_pos
    {R₀ M₀ : ℕ} (hM₀ : 1 ≤ M₀) :
    0 < dyadicShortMassConstant R₀ M₀ := by
  unfold dyadicShortMassConstant dyadicShortFactor
  have hK : 0 < boundaryPropagationConstant criticalP :=
    zero_lt_one.trans_le
      (boundaryPropagationConstant_ge_one one_lt_criticalP)
  have hfactor : (0 : ℝ) < (4 * 2 ^ R₀ * M₀ : ℕ) := by
    exact_mod_cast (by positivity : 0 < 4 * 2 ^ R₀ * M₀)
  positivity

theorem dyadicScanMassConstant_pos
    {R₀ M₀ : ℕ} (hM₀ : 1 ≤ M₀) :
    0 < dyadicScanMassConstant R₀ M₀ := by
  unfold dyadicScanMassConstant
  exact (dyadicShortMassConstant_pos hM₀).trans_le (le_max_left _ _)

/-- One maximal-window scan step. -/
theorem dyadicScanStep
    {R₀ M₀ : ℕ} (huniform : UniformFiniteWindowDyadicDichotomy R₀ M₀)
    {T Q k : ℕ} {h : StepSchedule T}
    (hQ2 : 2 ≤ Q) (hQtheta : criticalTheta⁻¹ < (Q : ℝ))
    (hh : IsNonnegativeSchedule h) (hQk : Q ≤ k)
    (hkr : k ≤ longCount h)
    (hcut : CutoffConditions criticalP h (k + 1) (longCount h)) :
    unresolvedMass h k ≤
        dyadicScanMassConstant R₀ M₀ * cappedMass h *
          (((longCount h : ℝ) + 1) ^ massExponent) ∨
      ∃ q : ℕ, k < q ∧ q ≤ longCount h ∧
        (4 : ℝ)⁻¹ / unresolvedMass h q < lowerBoundFunctional h := by
  obtain ⟨hR₀, hM₀, hwindow⟩ := huniform
  let M := nextDyadicBaseScale M₀ k
  have hM₀one : 1 ≤ M₀ := by omega
  have hMM₀ : M₀ ≤ M := by
    dsimp only [M]
    exact nextDyadicBaseScale_ge_threshold M₀ k
  by_cases hfit : 4 * ((2 ^ R₀) * M) ≤ longCount h
  · obtain ⟨R, hR₀R, hendpoint, hnear⟩ :=
      exists_maximalDyadicDepth (M := M) (R₀ := R₀)
        (by omega : 1 ≤ M) hfit
    have hk2M : k + 1 ≤ 2 * M := by
      dsimp only [M]
      exact rank_lt_twice_nextDyadicBaseScale M₀ k
    have hQ2M : Q ≤ 2 * M := by omega
    have hcutM : CutoffConditions criticalP h (2 * M) (longCount h) := by
      intro q hq
      have hqIcc := Finset.mem_Icc.mp hq
      exact hcut q (Finset.mem_Icc.mpr ⟨by omega, hqIcc.2⟩)
    rcases hwindow hQtheta hh R M hR₀R hMM₀ hQ2M hendpoint hcutM with
      hfunctional | hratio
    · right
      obtain ⟨m, hm, hfun⟩ := hfunctional
      have hmIco := Finset.mem_Ico.mp hm
      refine ⟨4 * m, ?_, ?_, hfun⟩
      · have hkM := rank_lt_twice_nextDyadicBaseScale M₀ k
        dsimp only [M] at hmIco hkM
        nlinarith
      · omega
    · left
      have hterminal := unresolvedMass_lt_dyadicTerminalMassConstant
        hQ2 hQtheta hh hQk (by simpa only [M] using hendpoint)
        (by simpa only [M] using hnear) hcut
        (by simpa only [M] using hratio)
      have hscale :
          0 ≤ cappedMass h *
            (((longCount h : ℝ) + 1) ^ massExponent) := by
        have hB : 0 < cappedMass h := cappedMass_pos hh
        positivity
      have hconst :
          dyadicTerminalMassConstant M₀ ≤
            dyadicScanMassConstant R₀ M₀ := by
        exact le_max_right _ _
      have hscaled := mul_le_mul_of_nonneg_right hconst hscale
      exact hterminal.le.trans (by
        simpa only [mul_assoc] using hscaled)
  · left
    have hshort := unresolvedMass_le_dyadicShortMassConstant
      hQ2 hQtheta hh hQk hM₀one hkr (by simpa only [M] using hfit) hcut
    have hscale :
        0 ≤ cappedMass h *
          (((longCount h : ℝ) + 1) ^ massExponent) := by
      have hB : 0 < cappedMass h := cappedMass_pos hh
      positivity
    have hconst :
        dyadicShortMassConstant R₀ M₀ ≤
          dyadicScanMassConstant R₀ M₀ := le_max_left _ _
    have hscaled := mul_le_mul_of_nonneg_right hconst hscale
    exact hshort.trans (by simpa only [mul_assoc] using hscaled)

end

end GDLowerBound.FourBlock
