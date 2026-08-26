import GDLowerBound.FourBlock.FiniteWindowDyadicTerminalPropagation

/-!
# Short-tail branch for the dyadic scan

If even the minimum admissible dyadic window does not fit, the current rank
is within a fixed factor of the terminal rank.  Ordinary boundary propagation
then has only a fixed cost and is stronger than the target power bound.
-/

namespace GDLowerBound.FourBlock

open GDLowerBound.Schedule GDLowerBound.RankAnalysis

noncomputable section

/-- Boundary propagation when the terminal rank is within an arbitrary fixed
natural factor `A` of the starting rank. -/
theorem unresolvedMass_le_boundaryConstant_mul_factor_rpow
    {T Q k A : ℕ} {p : ℝ} {h : StepSchedule T}
    (hp : 1 < p) (hQ2 : 2 ≤ Q)
    (hQtheta : (lyapunovTheta p)⁻¹ < (Q : ℝ))
    (hh : IsNonnegativeSchedule h)
    (hk : 1 ≤ k) (hQk : Q ≤ k) (hkr : k ≤ longCount h)
    (hA : 1 ≤ A) (hnear : longCount h < A * k)
    (hcut : CutoffConditions p h (k + 1) (longCount h)) :
    unresolvedMass h k ≤
      boundaryPropagationConstant p * cappedMass h *
        ((A : ℝ) ^ (p - 1)) := by
  have hboundary := boundaryPropagation hp hQ2 hQtheta hh hQk hkr hcut
  have hkR : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hrR : (0 : ℝ) < longCount h :=
    hkR.trans_le (by exact_mod_cast hkr)
  have hkpow : 0 < (k : ℝ) ^ (p - 1) :=
    Real.rpow_pos_of_pos hkR _
  have hdiv :
      unresolvedMass h k ≤
        (boundaryPropagationConstant p * cappedMass h *
          ((longCount h : ℝ) ^ (p - 1))) /
            ((k : ℝ) ^ (p - 1)) :=
    (le_div_iff₀ hkpow).2 hboundary
  have hratioPos : 0 < (longCount h : ℝ) / (k : ℝ) :=
    div_pos hrR hkR
  have hratio : (longCount h : ℝ) / (k : ℝ) < A := by
    apply (div_lt_iff₀ hkR).2
    exact_mod_cast hnear
  have hexponent : 0 ≤ p - 1 := by linarith
  have hAr : (0 : ℝ) ≤ A := by positivity
  have hrpow :
      ((longCount h : ℝ) / (k : ℝ)) ^ (p - 1) ≤
        (A : ℝ) ^ (p - 1) :=
    Real.rpow_le_rpow hratioPos.le hratio.le hexponent
  have hKB : 0 ≤ boundaryPropagationConstant p * cappedMass h := by
    have hK : 0 < boundaryPropagationConstant p :=
      zero_lt_one.trans_le (boundaryPropagationConstant_ge_one hp)
    have hB : 0 < cappedMass h := cappedMass_pos hh
    positivity
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
          ((A : ℝ) ^ (p - 1)) :=
      mul_le_mul_of_nonneg_left hrpow hKB

def dyadicShortFactor (R₀ M₀ : ℕ) : ℕ :=
  4 * (2 ^ R₀) * M₀

def dyadicShortMassConstant (R₀ M₀ : ℕ) : ℝ :=
  boundaryPropagationConstant criticalP *
    ((dyadicShortFactor R₀ M₀ : ℕ) : ℝ) ^ betaLower

theorem nextDyadicBaseScale_le_threshold_mul_rank
    {M₀ k : ℕ} (hM₀ : 1 ≤ M₀) (hk : 2 ≤ k) :
    nextDyadicBaseScale M₀ k ≤ M₀ * k := by
  unfold nextDyadicBaseScale
  apply max_le
  · nlinarith
  · have hhalf : k / 2 + 1 ≤ k := by omega
    have hkMk : k ≤ M₀ * k := by nlinarith
    exact hhalf.trans hkMk

/-- Failure of the minimum-window fit condition gives a normalized target
bound with a fixed constant. -/
theorem unresolvedMass_le_dyadicShortMassConstant
    {T Q R₀ M₀ k : ℕ} {h : StepSchedule T}
    (hQ2 : 2 ≤ Q) (hQtheta : criticalTheta⁻¹ < (Q : ℝ))
    (hh : IsNonnegativeSchedule h) (hQk : Q ≤ k)
    (hM₀ : 1 ≤ M₀) (hkr : k ≤ longCount h)
    (hdoesNotFit :
      ¬ 4 * ((2 ^ R₀) * nextDyadicBaseScale M₀ k) ≤ longCount h)
    (hcut : CutoffConditions criticalP h (k + 1) (longCount h)) :
    unresolvedMass h k ≤
      dyadicShortMassConstant R₀ M₀ * cappedMass h *
        (((longCount h : ℝ) + 1) ^ massExponent) := by
  have hk2 : 2 ≤ k := hQ2.trans hQk
  have hMbound := nextDyadicBaseScale_le_threshold_mul_rank hM₀ hk2
  have hnear : longCount h < dyadicShortFactor R₀ M₀ * k := by
    have hfirst :
        longCount h <
          4 * ((2 ^ R₀) * nextDyadicBaseScale M₀ k) :=
      Nat.lt_of_not_ge hdoesNotFit
    have hsecond :
        4 * ((2 ^ R₀) * nextDyadicBaseScale M₀ k) ≤
          dyadicShortFactor R₀ M₀ * k := by
      unfold dyadicShortFactor
      nlinarith
    exact hfirst.trans_le hsecond
  have hA : 1 ≤ dyadicShortFactor R₀ M₀ := by
    unfold dyadicShortFactor
    have hp : 1 ≤ 2 ^ R₀ := one_le_pow₀ (by omega)
    nlinarith
  have hshort := unresolvedMass_le_boundaryConstant_mul_factor_rpow
    one_lt_criticalP hQ2 hQtheta hh (by omega : 1 ≤ k) hQk hkr
    hA hnear hcut
  rw [criticalP_sub_one] at hshort
  have hrpow :
      (1 : ℝ) ≤ ((longCount h : ℝ) + 1) ^ massExponent :=
    Real.one_le_rpow (by norm_num) massExponent_pos.le
  have hconstNonneg :
      0 ≤ dyadicShortMassConstant R₀ M₀ * cappedMass h := by
    unfold dyadicShortMassConstant
    have hK : 0 < boundaryPropagationConstant criticalP :=
      zero_lt_one.trans_le
        (boundaryPropagationConstant_ge_one one_lt_criticalP)
    have hB : 0 < cappedMass h := cappedMass_pos hh
    positivity
  calc
    unresolvedMass h k ≤
        boundaryPropagationConstant criticalP * cappedMass h *
          ((dyadicShortFactor R₀ M₀ : ℕ) : ℝ) ^ betaLower := hshort
    _ = dyadicShortMassConstant R₀ M₀ * cappedMass h := by
      unfold dyadicShortMassConstant
      ring
    _ ≤ dyadicShortMassConstant R₀ M₀ * cappedMass h *
          (((longCount h : ℝ) + 1) ^ massExponent) := by
      simpa only [mul_one] using
        mul_le_mul_of_nonneg_left hrpow hconstNonneg

end

end GDLowerBound.FourBlock
