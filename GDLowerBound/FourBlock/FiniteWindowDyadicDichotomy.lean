import GDLowerBound.FourBlock.FiniteWindowDyadicGrowthThreshold
import GDLowerBound.FourBlock.FiniteWindowDyadicUniform
import GDLowerBound.FourBlock.FiniteWindowPrefixComparison
import GDLowerBound.FourBlock.RobustFiniteThreshold

/-!
# Uniform unconditional dyadic dichotomy

All analytic and finite-error thresholds are consolidated here.  Beyond two
fixed natural thresholds, every admissible dyadic cutoff window either yields
a functional rank or satisfies the sharp endpoint mass-growth bound.
-/

namespace GDLowerBound.FourBlock

open GDLowerBound.Schedule GDLowerBound.RankAnalysis

noncomputable section

/-- A base scale immediately above a rank `k`, enlarged to a prescribed
uniform threshold. -/
def nextDyadicBaseScale (M₀ k : ℕ) : ℕ :=
  max M₀ (k / 2 + 1)

theorem nextDyadicBaseScale_ge_threshold (M₀ k : ℕ) :
    M₀ ≤ nextDyadicBaseScale M₀ k := by
  exact le_max_left _ _

theorem rank_lt_twice_nextDyadicBaseScale (M₀ k : ℕ) :
    k < 2 * nextDyadicBaseScale M₀ k := by
  unfold nextDyadicBaseScale
  have hhalf : k < 2 * (k / 2 + 1) := by omega
  have hmax : k / 2 + 1 ≤ max M₀ (k / 2 + 1) := le_max_right _ _
  omega

/-- Only a fixed number of ranks is skipped when the cutoff is moved from
`k+1` to the next admissible even starting endpoint. -/
theorem twice_nextDyadicBaseScale_sub_rank_le (M₀ k : ℕ) :
    2 * nextDyadicBaseScale M₀ k - k ≤ 2 * M₀ + 2 := by
  unfold nextDyadicBaseScale
  rcases le_total M₀ (k / 2 + 1) with h | h
  · rw [max_eq_right h]
    omega
  · rw [max_eq_left h]
    omega

/-- Consolidated uniform form of the unconditional dyadic alternative. -/
theorem exists_uniform_finiteWindowDyadic_dichotomy :
    ∃ R₀ M₀ : ℕ, 3 ≤ R₀ ∧ 2000 ≤ M₀ ∧
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
                  (betaLower - massExponent) / (M : ℝ))) := by
  obtain ⟨Rw, Mw, hRw, hMw, hwindow⟩ :=
    exists_uniform_dyadicFourBlockWindow
  obtain ⟨Me, hexp⟩ := exists_exp_sharpFiniteError_threshold
  let M₀ := max 2000 (max Mw Me)
  refine ⟨Rw, M₀, hRw, le_max_left _ _, ?_⟩
  intro T Q hQ h hh R M hRM hMM hQ2M h4N hcut
  have hMwM : Mw ≤ M := by
    exact (le_max_of_le_right (le_max_left Mw Me)).trans hMM
  have hMeM : Me ≤ M := by
    exact (le_max_of_le_right (le_max_right Mw Me)).trans hMM
  have h2000M : 2000 ≤ M := (le_max_left _ _).trans hMM
  have hRone : 1 ≤ R := by omega
  exact finiteWindowDyadic_functional_or_massRatio_lt hQ hh h2000M
    hRone hQ2M h4N hcut (fun m hm ↦ hexp m (hMeM.trans hm))
    (hwindow R M hRM hMwM)

end

end GDLowerBound.FourBlock
