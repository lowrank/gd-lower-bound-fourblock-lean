import GDLowerBound.FourBlock.FiniteWindowDyadicDichotomy

/-!
# Forward mass propagation on a failed dyadic window

The non-functional branch of the uniform dichotomy propagates a mass lower
bound almost to the terminal rank.  Moving the start from `k` to the even
endpoint `2*M` costs only a fixed power of two.
-/

namespace GDLowerBound.FourBlock

open GDLowerBound.Schedule GDLowerBound.RankAnalysis

noncomputable section

/-- Quantitative forward propagation in the mass-ratio branch. -/
theorem unresolvedMass_lt_uniformPrefix_mul_dyadicGrowth_mul_endpoint
    {T Q M₀ k R : ℕ} {p : ℝ} {h : StepSchedule T}
    (hQ : (lyapunovTheta p)⁻¹ < (Q : ℝ))
    (hh : IsNonnegativeSchedule h) (hQk : Q ≤ k)
    (hendpoint :
      4 * ((2 ^ R) * nextDyadicBaseScale M₀ k) ≤ longCount h)
    (hcut : CutoffConditions p h (k + 1) (longCount h))
    (hratio :
      unresolvedMass h (2 * nextDyadicBaseScale M₀ k) /
          unresolvedMass h
            (4 * ((2 ^ R) * nextDyadicBaseScale M₀ k)) <
        Real.exp
          (massExponent * (R : ℝ) * Real.log 2 +
            betaLower * Real.log 2 +
            (betaLower - massExponent) /
              (nextDyadicBaseScale M₀ k : ℝ))) :
    unresolvedMass h k <
      (2 : ℝ) ^ (2 * M₀ + 2) *
        Real.exp
          (massExponent * (R : ℝ) * Real.log 2 +
            betaLower * Real.log 2 +
            (betaLower - massExponent) /
              (nextDyadicBaseScale M₀ k : ℝ)) *
        unresolvedMass h
          (4 * ((2 ^ R) * nextDyadicBaseScale M₀ k)) := by
  let M := nextDyadicBaseScale M₀ k
  let E := massExponent * (R : ℝ) * Real.log 2 +
    betaLower * Real.log 2 +
    (betaLower - massExponent) / (M : ℝ)
  have hk2M : k ≤ 2 * M := by
    dsimp only [M]
    exact (rank_lt_twice_nextDyadicBaseScale M₀ k).le
  have h2Mr : 2 * M ≤ longCount h := by
    dsimp only [M] at hendpoint ⊢
    have hp : 1 ≤ 2 ^ R := one_le_pow₀ (by omega)
    nlinarith
  have hprefix := unresolvedMass_le_two_pow_gap_mul_of_cutoff
    hQ hh hQk hk2M h2Mr hcut
  have hgap : 2 * M - k ≤ 2 * M₀ + 2 := by
    dsimp only [M]
    exact twice_nextDyadicBaseScale_sub_rank_le M₀ k
  have hpow :
      (2 : ℝ) ^ (2 * M - k) ≤ (2 : ℝ) ^ (2 * M₀ + 2) :=
    pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hgap
  have hD2M : 0 ≤ unresolvedMass h (2 * M) :=
    (unresolvedMass_pos hh _).le
  have hprefixUniform :
      unresolvedMass h k ≤
        (2 : ℝ) ^ (2 * M₀ + 2) * unresolvedMass h (2 * M) :=
    hprefix.trans (mul_le_mul_of_nonneg_right hpow hD2M)
  have hendPos := unresolvedMass_pos hh
    (4 * ((2 ^ R) * M))
  have hratio' :
      unresolvedMass h (2 * M) <
        Real.exp E * unresolvedMass h (4 * ((2 ^ R) * M)) := by
    apply (div_lt_iff₀ hendPos).mp
    simpa only [M, E] using hratio
  have hscaled := mul_lt_mul_of_pos_left hratio'
    (by positivity : 0 < (2 : ℝ) ^ (2 * M₀ + 2))
  exact hprefixUniform.trans_lt (by
    simpa only [M, E, mul_assoc] using hscaled)

end

end GDLowerBound.FourBlock
