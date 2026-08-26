import GDLowerBound.FourBlock.ExactScoreBranch
import GDLowerBound.RankAnalysis.BoundedRank

/-!
# Functional lower bound in the exact small-score branch

The exact endpoint theorem bounds the reciprocal top-chain value by the
square of the outside-in product.  Therefore a small normalized logarithmic
score immediately gives a quantitative contribution to the schedule
functional, with only the explicit exponential price `exp(4m * 10^-7)`.
-/

namespace GDLowerBound.FourBlock

open scoped BigOperators
open GDLowerBound.Schedule GDLowerBound.RankAnalysis GDLowerBound.Matching

noncomputable section

theorem topChain_value_lower_of_outsideInLogScore_lt
    {T m : ℕ} {h : StepSchedule T} (hh : IsNonnegativeSchedule h)
    (hm : 0 < m) (hq : 2 * (m + m) ≤ longCount h) {c : ℝ}
    (hscore : outsideInLogScore (m + m) (scheduleFourBlockWeights h hq) < c) :
    (4 * unresolvedMass h (2 * (m + m)) * Real.exp (2 * c))⁻¹ <
      (topChain h (2 * (m + m))).value := by
  let q := 2 * (m + m)
  let w := scheduleFourBlockWeights h hq
  let R := (topChain h q).terminalScale *
    ∏ i : Fin q, (chronologicalLocalBound h q hq i)⁻¹
  let K := 4 * unresolvedMass h q * Real.exp (2 * c)
  have hD : 0 < unresolvedMass h q := unresolvedMass_pos hh q
  have hR : 0 < R := by
    dsimp only [R]
    apply mul_pos ((topChain h q).terminalScale_pos hh)
    apply Finset.prod_pos
    intro i hi
    exact inv_pos.mpr (chronologicalLocalBound_pos hh q hq i)
  have hK : 0 < K := by
    dsimp only [K]
    positivity
  have hend := topChain_reciprocalProduct_le_sortedOutsideIn
    (h := h) hh (k := m + m) (by omega) hq
  have hw : ∀ i, 0 < w i := scheduleFourBlockWeights_pos hh hm hq
  have hout := outsideInProduct_eq_exp_logScore hw
  have hsq : outsideInProduct (m + m) w ^ 2 =
      Real.exp (2 * outsideInLogScore (m + m) w) := by
    rw [hout, ← Real.exp_nat_mul]
    norm_num
  have hexp : Real.exp (2 * outsideInLogScore (m + m) w) <
      Real.exp (2 * c) := by
    apply Real.exp_lt_exp.mpr
    linarith
  have hratio :
      (4 * unresolvedMass h q * (q - 1) / q) <
        4 * unresolvedMass h q := by
    have hqR : (0 : ℝ) < q := by
      dsimp only [q]
      positivity
    have hqOne : (1 : ℝ) ≤ q := by
      exact_mod_cast (show 1 ≤ q by dsimp only [q]; omega)
    norm_num [Nat.cast_sub (show 1 ≤ q by dsimp only [q]; omega)]
    rw [div_lt_iff₀ hqR]
    nlinarith
  have hcoeff0 : 0 ≤ 4 * unresolvedMass h q * (q - 1) / q := by
    have hqR : (0 : ℝ) < q := by
      dsimp only [q]
      positivity
    have hqOne : (1 : ℝ) ≤ q := by
      exact_mod_cast (show 1 ≤ q by dsimp only [q]; omega)
    positivity
  have hout0 : 0 ≤ outsideInProduct (m + m) w ^ 2 := sq_nonneg _
  have hbound : R < K := by
    calc
      R ≤ (4 * unresolvedMass h q * (q - 1) / q) *
          outsideInProduct (m + m) w ^ 2 := by
        dsimp only [R, q, w]
        norm_num [Nat.cast_add] at hend ⊢
        simpa only [scheduleFourBlockWeights, ← Finset.prod_inv_distrib] using hend
      _ = (4 * unresolvedMass h q * (q - 1) / q) *
          Real.exp (2 * outsideInLogScore (m + m) w) := by rw [hsq]
      _ < (4 * unresolvedMass h q) *
          Real.exp (2 * outsideInLogScore (m + m) w) := by
        exact mul_lt_mul_of_pos_right hratio (Real.exp_pos _)
      _ ≤ (4 * unresolvedMass h q) * Real.exp (2 * c) := by
        exact mul_le_mul_of_nonneg_left hexp.le (by positivity)
      _ = K := rfl
  have hinv : K⁻¹ < R⁻¹ := by
    exact (inv_lt_inv₀ hK hR).2 hbound
  change K⁻¹ < (topChain h q).value
  rw [topChain_value_eq_inv_reciprocal h hq]
  simpa only [R] using hinv

/-- A small exact score supplies a functional contribution with exponential
penalty `4m * 10^-7`. -/
theorem functional_lower_of_smallExactScore
    {T m : ℕ} {h : StepSchedule T} (hh : IsNonnegativeSchedule h)
    (hm : 2000 ≤ m) (hq : 2 * (m + m) ≤ longCount h)
    (hsmall : SmallExactScoreRank h m) :
    (4 * unresolvedMass h (2 * (m + m)) *
        Real.exp ((4 * m : ℕ) * exactScoreCutoff))⁻¹ <
      lowerBoundFunctional h := by
  have hm0 : 0 < m := by omega
  have hs := (smallExactScoreRank_iff hq).1 hsmall
  have hraw : outsideInLogScore (m + m) (scheduleFourBlockWeights h hq) <
      (2 * m : ℕ) * exactScoreCutoff := by
    have hmR : (0 : ℝ) < 2 * m := by positivity
    have hraw' := (div_lt_iff₀ hmR).1 hs
    simpa only [Nat.cast_mul, Nat.cast_ofNat, mul_comm] using hraw'
  have hchain := topChain_value_lower_of_outsideInLogScore_lt
    hh hm0 hq hraw
  have hrewrite :
      2 * ((2 * m : ℕ) * exactScoreCutoff) =
        (4 * m : ℕ) * exactScoreCutoff := by
    norm_num [Nat.cast_mul]
    ring
  rw [hrewrite] at hchain
  exact hchain.trans_le (chainValue_le_functional h (topChain h (2 * (m + m))))

end

end GDLowerBound.FourBlock
