import GDLowerBound.FourBlock.FiniteWindowDyadicPropagation

/-!
# Terminal bound for the non-functional dyadic branch

The exact dyadic exponential has coefficient `massExponent` in the window
depth.  A maximal endpoint converts that depth into the terminal rank, while
the remaining boundary tail costs only a fixed factor.
-/

namespace GDLowerBound.FourBlock

open GDLowerBound.Schedule GDLowerBound.RankAnalysis

noncomputable section

def dyadicGrowthOverhead : ℝ :=
  Real.exp
    (betaLower * Real.log 2 + (betaLower - massExponent))

theorem dyadicGrowthOverhead_pos : 0 < dyadicGrowthOverhead := by
  exact Real.exp_pos _

/-- The exact window-growth exponential is bounded by the target terminal
power and one fixed overhead. -/
theorem dyadicGrowthExp_le_terminalPower
    {M R r : ℕ} (hM : 1 ≤ M)
    (hendpoint : 4 * ((2 ^ R) * M) ≤ r) :
    Real.exp
        (massExponent * (R : ℝ) * Real.log 2 +
          betaLower * Real.log 2 +
          (betaLower - massExponent) / (M : ℝ)) ≤
      dyadicGrowthOverhead *
        (((r : ℝ) + 1) ^ massExponent) := by
  have hpowNat : 2 ^ R ≤ r + 1 := by
    have hMpos : 0 < M := by omega
    have hp : 0 < 2 ^ R := pow_pos (by omega : 0 < 2) R
    nlinarith
  have hpowReal : (2 : ℝ) ^ R ≤ (r : ℝ) + 1 := by
    exact_mod_cast hpowNat
  have hpowPos : 0 < (2 : ℝ) ^ R := by positivity
  have hrPos : 0 < (r : ℝ) + 1 := by positivity
  have hlog := Real.strictMonoOn_log.monotoneOn
    (Set.mem_Ioi.mpr hpowPos) (Set.mem_Ioi.mpr hrPos) hpowReal
  rw [Real.log_pow] at hlog
  have hlogScaled := mul_le_mul_of_nonneg_left hlog massExponent_pos.le
  have hMR : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hMposR : (0 : ℝ) < M := zero_lt_one.trans_le hMR
  have hinv : 1 / (M : ℝ) ≤ 1 := (div_le_one hMposR).2 hMR
  have hgap : 0 ≤ betaLower - massExponent :=
    sub_nonneg.mpr massExponent_lt_betaLower.le
  have hinvScaled := mul_le_mul_of_nonneg_left hinv hgap
  have hexponent :
      massExponent * (R : ℝ) * Real.log 2 +
          betaLower * Real.log 2 +
          (betaLower - massExponent) / (M : ℝ) ≤
        massExponent * Real.log ((r : ℝ) + 1) +
          (betaLower * Real.log 2 +
            (betaLower - massExponent)) := by
    have hdivEq :
        (betaLower - massExponent) / (M : ℝ) =
          (betaLower - massExponent) * (1 / (M : ℝ)) := by ring
    rw [hdivEq]
    linarith
  have hexp := Real.exp_le_exp.mpr hexponent
  calc
    Real.exp
        (massExponent * (R : ℝ) * Real.log 2 +
          betaLower * Real.log 2 +
          (betaLower - massExponent) / (M : ℝ)) ≤
      Real.exp
        (massExponent * Real.log ((r : ℝ) + 1) +
          (betaLower * Real.log 2 +
            (betaLower - massExponent))) := hexp
    _ = dyadicGrowthOverhead *
          (((r : ℝ) + 1) ^ massExponent) := by
      rw [Real.exp_add]
      rw [Real.rpow_def_of_pos hrPos]
      unfold dyadicGrowthOverhead
      ring

/-- Fixed constant multiplying the target terminal power in the
non-functional branch. -/
def dyadicTerminalMassConstant (M₀ : ℕ) : ℝ :=
  (2 : ℝ) ^ (2 * M₀ + 2) * dyadicGrowthOverhead *
    boundaryPropagationConstant criticalP *
    ((2 : ℝ) ^ betaLower)

theorem dyadicTerminalMassConstant_pos (M₀ : ℕ) :
    0 < dyadicTerminalMassConstant M₀ := by
  unfold dyadicTerminalMassConstant
  have hK : 0 < boundaryPropagationConstant criticalP :=
    zero_lt_one.trans_le
      (boundaryPropagationConstant_ge_one one_lt_criticalP)
  positivity [dyadicGrowthOverhead_pos]

/-- A maximal dyadic window on the mass-ratio branch already gives the
target `massExponent` bound at its incoming functional rank. -/
theorem unresolvedMass_lt_dyadicTerminalMassConstant
    {T Q M₀ k R : ℕ} {h : StepSchedule T}
    (hQ2 : 2 ≤ Q) (hQtheta : criticalTheta⁻¹ < (Q : ℝ))
    (hh : IsNonnegativeSchedule h) (hQk : Q ≤ k)
    (hendpoint :
      4 * ((2 ^ R) * nextDyadicBaseScale M₀ k) ≤ longCount h)
    (hnear :
      longCount h < 8 * ((2 ^ R) * nextDyadicBaseScale M₀ k))
    (hcut : CutoffConditions criticalP h (k + 1) (longCount h))
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
      dyadicTerminalMassConstant M₀ * cappedMass h *
        (((longCount h : ℝ) + 1) ^ massExponent) := by
  let M := nextDyadicBaseScale M₀ k
  let e := 4 * ((2 ^ R) * M)
  have hforward :=
    unresolvedMass_lt_uniformPrefix_mul_dyadicGrowth_mul_endpoint
      hQtheta hh hQk hendpoint hcut hratio
  have hke : k + 1 ≤ e := by
    dsimp only [e, M]
    have hkM := rank_lt_twice_nextDyadicBaseScale M₀ k
    have hp : 1 ≤ 2 ^ R := one_le_pow₀ (by omega)
    nlinarith
  have hQe : Q ≤ e := by omega
  have her : e ≤ longCount h := by simpa only [e, M] using hendpoint
  have hcutEnd : CutoffConditions criticalP h (e + 1) (longCount h) := by
    intro q hq
    have hqIcc := Finset.mem_Icc.mp hq
    exact hcut q (Finset.mem_Icc.mpr ⟨by omega, hqIcc.2⟩)
  have hnear' : longCount h < 2 * e := by
    simpa only [e, M, show 2 * (4 * ((2 ^ R) * M)) =
      8 * ((2 ^ R) * M) by ring] using hnear
  have hend := unresolvedMass_le_boundaryConstant_mul_two_rpow
    one_lt_criticalP hQ2 hQtheta hh (by omega : 1 ≤ e) hQe her
    hnear' hcutEnd
  rw [criticalP_sub_one] at hend
  have hMone : 1 ≤ M := by
    dsimp only [M, nextDyadicBaseScale]
    have : 1 ≤ k / 2 + 1 := by omega
    exact this.trans (le_max_right _ _)
  have hgrowth := dyadicGrowthExp_le_terminalPower hMone hendpoint
  have hA : 0 ≤ (2 : ℝ) ^ (2 * M₀ + 2) := by positivity
  have hgrowthScaled := mul_le_mul_of_nonneg_left hgrowth hA
  have hterminalScale :
      (2 : ℝ) ^ (2 * M₀ + 2) *
          Real.exp
            (massExponent * (R : ℝ) * Real.log 2 +
              betaLower * Real.log 2 +
              (betaLower - massExponent) / (M : ℝ)) *
          unresolvedMass h e ≤
        dyadicTerminalMassConstant M₀ * cappedMass h *
          (((longCount h : ℝ) + 1) ^ massExponent) := by
    have hscalarNonneg :
        0 ≤ (2 : ℝ) ^ (2 * M₀ + 2) *
          Real.exp
            (massExponent * (R : ℝ) * Real.log 2 +
              betaLower * Real.log 2 +
              (betaLower - massExponent) / (M : ℝ)) := by positivity
    have hendScaled := mul_le_mul_of_nonneg_left hend hscalarNonneg
    calc
      (2 : ℝ) ^ (2 * M₀ + 2) *
            Real.exp
              (massExponent * (R : ℝ) * Real.log 2 +
                betaLower * Real.log 2 +
                (betaLower - massExponent) / (M : ℝ)) *
            unresolvedMass h e ≤
          (2 : ℝ) ^ (2 * M₀ + 2) *
            Real.exp
              (massExponent * (R : ℝ) * Real.log 2 +
                betaLower * Real.log 2 +
                (betaLower - massExponent) / (M : ℝ)) *
            (boundaryPropagationConstant criticalP * cappedMass h *
              ((2 : ℝ) ^ betaLower)) := by
        simpa only [mul_assoc] using hendScaled
      _ ≤ (2 : ℝ) ^ (2 * M₀ + 2) *
            (dyadicGrowthOverhead *
              (((longCount h : ℝ) + 1) ^ massExponent)) *
            (boundaryPropagationConstant criticalP * cappedMass h *
              ((2 : ℝ) ^ betaLower)) := by
        have hright :
            0 ≤ boundaryPropagationConstant criticalP * cappedMass h *
              ((2 : ℝ) ^ betaLower) := by
          have hKpos : 0 < boundaryPropagationConstant criticalP :=
            zero_lt_one.trans_le
              (boundaryPropagationConstant_ge_one one_lt_criticalP)
          have hBpos : 0 < cappedMass h := cappedMass_pos hh
          positivity
        exact mul_le_mul_of_nonneg_right hgrowthScaled hright
      _ = dyadicTerminalMassConstant M₀ * cappedMass h *
            (((longCount h : ℝ) + 1) ^ massExponent) := by
        unfold dyadicTerminalMassConstant
        ring
  exact hforward.trans_le (by simpa only [M, e] using hterminalScale)

end

end GDLowerBound.FourBlock
