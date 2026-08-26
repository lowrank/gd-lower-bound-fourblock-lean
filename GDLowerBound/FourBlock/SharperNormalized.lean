import GDLowerBound.FourBlock.FiniteWindowDyadicGlobal

/-!
# End-to-end sharper normalized floor

The exact-envelope cutoff starts the maximal-dyadic scan.  The terminating
scan closes the normalized estimate at the exact rational exponent
`exponent = 1 + massExponent = 1.8288`.
-/

namespace GDLowerBound.FourBlock

open scoped Real
open GDLowerBound.Schedule GDLowerBound.RankAnalysis

noncomputable section

def sharperBaseCoefficient : ℝ :=
  min ((4 : ℝ)⁻¹) (boundedRankConstant allRankCutoff)

def sharperNormalizedConstant (R₀ M₀ : ℕ) : ℝ :=
  min sharperBaseCoefficient
    (sharperBaseCoefficient / dyadicScanMassConstant R₀ M₀)

theorem sharperBaseCoefficient_pos : 0 < sharperBaseCoefficient := by
  unfold sharperBaseCoefficient
  exact lt_min (by norm_num)
    (boundedRankConstant_pos (by
      have : 2 ≤ allRankCutoff := allRankCutoff_two
      omega))

theorem sharperNormalizedConstant_pos
    {R₀ M₀ : ℕ} (huniform : UniformFiniteWindowDyadicDichotomy R₀ M₀) :
    0 < sharperNormalizedConstant R₀ M₀ := by
  have hM₀ : 1 ≤ M₀ := by
    have : 2000 ≤ M₀ := huniform.2.1
    omega
  have hC : 0 < dyadicScanMassConstant R₀ M₀ :=
    dyadicScanMassConstant_pos hM₀
  unfold sharperNormalizedConstant
  exact lt_min sharperBaseCoefficient_pos
    (div_pos sharperBaseCoefficient_pos hC)

theorem exponent_sub_one_eq_massExponent :
    exponent - 1 = massExponent := by
  rw [exponent_eq_one_add_massExponent]
  ring

/-- End-to-end normalized floor, conditional only on the uniform thresholds
whose existence has already been proved. -/
theorem sharperNormalizedLowerBound_of_uniform
    {R₀ M₀ : ℕ} (huniform : UniformFiniteWindowDyadicDichotomy R₀ M₀) :
    NormalizedScheduleFloor exponent
      (sharperNormalizedConstant R₀ M₀) := by
  classical
  let Q : ℕ := allRankCutoff
  let a : ℝ := sharperBaseCoefficient
  let c : ℝ := sharperNormalizedConstant R₀ M₀
  have hQ2 : 2 ≤ Q := by simpa only [Q] using allRankCutoff_two
  have hQtheta : criticalTheta⁻¹ < (Q : ℝ) := by
    simpa only [Q] using allRankCutoff_above_criticalTheta
  have ha : 0 < a := by simpa only [a] using sharperBaseCoefficient_pos
  have haQuarter : a ≤ (4 : ℝ)⁻¹ := by
    dsimp only [a, sharperBaseCoefficient]
    exact min_le_left _ _
  have haBounded : a ≤ boundedRankConstant Q := by
    dsimp only [a, sharperBaseCoefficient, Q]
    exact min_le_right _ _
  have hcNonneg : 0 ≤ c := by
    exact (by
      dsimp only [c]
      exact (sharperNormalizedConstant_pos huniform).le)
  have hcScan :
      c ≤ a / dyadicScanMassConstant R₀ M₀ := by
    dsimp only [c, a, sharperNormalizedConstant]
    exact min_le_right _ _
  have hcBase : c ≤ a := by
    dsimp only [c, a, sharperNormalizedConstant]
    exact min_le_left _ _
  intro T h hh
  have hB : 0 < cappedMass h := cappedMass_pos hh
  have hRpow :
      0 < (((longCount h : ℝ) + 1) ^ massExponent) :=
    Real.rpow_pos_of_pos (by positivity) _
  have hden :
      0 < cappedMass h *
        (((longCount h : ℝ) + 1) ^ massExponent) :=
    mul_pos hB hRpow
  let smallRanks : Finset ℕ :=
    (Finset.Icc Q (longCount h)).filter
      (fun q ↦ zetaState h q ≤ criticalTheta)
  have htarget_of_scan {k : ℕ} (hQk : Q ≤ k)
      (hkr : k ≤ longCount h)
      (hcut : CutoffConditions criticalP h (k + 1) (longCount h))
      (hfun : a / unresolvedMass h k ≤ lowerBoundFunctional h) :
      c / (cappedMass h *
          (((longCount h : ℝ) + 1) ^ massExponent)) ≤
        lowerBoundFunctional h := by
    have hscan := dyadicScan_normalizedFunctional huniform hQ2 hQtheta hh
      hQk hkr hcut ha haQuarter hfun
    exact (div_le_div_of_nonneg_right hcScan hden.le).trans hscan
  have hmassExponentTarget :
      c / (cappedMass h *
          (((longCount h : ℝ) + 1) ^ massExponent)) ≤
        lowerBoundFunctional h := by
    by_cases hsmallRanks : smallRanks.Nonempty
    · let k : ℕ := smallRanks.max' hsmallRanks
      have hkMember : k ∈ smallRanks := smallRanks.max'_mem hsmallRanks
      have hkData :
          k ∈ Finset.Icc Q (longCount h) ∧
            zetaState h k ≤ criticalTheta := by
        simpa only [smallRanks, Finset.mem_filter] using hkMember
      have hkIcc := Finset.mem_Icc.mp hkData.1
      have hlargeAbove :
          ∀ q ∈ Finset.Icc (k + 1) (longCount h),
            criticalTheta < zetaState h q := by
        intro q hq
        apply lt_of_not_ge
        intro hqSmall
        have hqIcc := Finset.mem_Icc.mp hq
        have hqFull : q ∈ Finset.Icc Q (longCount h) :=
          Finset.mem_Icc.mpr ⟨by omega, hqIcc.2⟩
        have hqMember : q ∈ smallRanks :=
          Finset.mem_filter.mpr ⟨hqFull, hqSmall⟩
        have hqk : q ≤ k := by
          dsimp only [k]
          exact smallRanks.le_max' q hqMember
        omega
      have hcut :
          CutoffConditions criticalP h (k + 1) (longCount h) :=
        criticalCutoffConditions_of_no_small_state hh (by
          dsimp only [Q] at hkIcc
          omega) hlargeAbove
      have hquarter :
          (4 : ℝ)⁻¹ / unresolvedMass h k ≤ lowerBoundFunctional h :=
        (quarter_div_unresolvedMass_lt_functional_of_zeta_le hh
          (by simpa only [Q] using hkIcc.1) hkIcc.2 hkData.2).le
      have hDk : 0 < unresolvedMass h k := unresolvedMass_pos hh k
      have hfun :
          a / unresolvedMass h k ≤ lowerBoundFunctional h :=
        (div_le_div_of_nonneg_right haQuarter hDk.le).trans hquarter
      exact htarget_of_scan hkIcc.1 hkIcc.2 hcut hfun
    · have hnoSmall :
          ∀ q ∈ Finset.Icc Q (longCount h),
            criticalTheta < zetaState h q := by
        intro q hq
        apply lt_of_not_ge
        intro hqSmall
        apply hsmallRanks
        exact ⟨q, Finset.mem_filter.mpr ⟨hq, hqSmall⟩⟩
      by_cases hrSmall : longCount h < Q
      · have hbounded := boundedRankPrefix_uniform hh hQ2
          (Nat.le_of_lt hrSmall) (le_refl (longCount h))
        have hcBounded : c ≤ boundedRankConstant Q :=
          hcBase.trans haBounded
        have hRone :
            (1 : ℝ) ≤
              ((longCount h : ℝ) + 1) ^ massExponent :=
          Real.one_le_rpow (by norm_num) massExponent_pos.le
        have hBden :
            cappedMass h ≤ cappedMass h *
              (((longCount h : ℝ) + 1) ^ massExponent) := by
          simpa only [mul_one] using
            mul_le_mul_of_nonneg_left hRone hB.le
        have hfirst :
            c / (cappedMass h *
                (((longCount h : ℝ) + 1) ^ massExponent)) ≤
              c / cappedMass h :=
          div_le_div_of_nonneg_left hcNonneg hB hBden
        have hsecond :
            c / cappedMass h ≤
              boundedRankConstant Q / cappedMass h :=
          div_le_div_of_nonneg_right hcBounded hB.le
        have hbounded' :
            boundedRankConstant Q / cappedMass h ≤
              lowerBoundFunctional h := by
          simpa only [unresolvedMass_longCount] using hbounded
        exact hfirst.trans (hsecond.trans hbounded')
      · have hQr : Q ≤ longCount h := Nat.le_of_not_gt hrSmall
        have hlargeAfterQ :
            ∀ q ∈ Finset.Icc (Q + 1) (longCount h),
              criticalTheta < zetaState h q := by
          intro q hq
          have hqIcc := Finset.mem_Icc.mp hq
          exact hnoSmall q
            (Finset.mem_Icc.mpr ⟨by omega, hqIcc.2⟩)
        have hcut :
            CutoffConditions criticalP h (Q + 1) (longCount h) :=
          criticalCutoffConditions_of_no_small_state hh (by
            dsimp only [Q]
            omega) hlargeAfterQ
        have hbounded := boundedRankPrefix_uniform hh hQ2
          (le_refl Q) hQr
        have hDQ : 0 < unresolvedMass h Q := unresolvedMass_pos hh Q
        have hfun :
            a / unresolvedMass h Q ≤ lowerBoundFunctional h :=
          (div_le_div_of_nonneg_right haBounded hDQ.le).trans hbounded
        exact htarget_of_scan (le_refl Q) hQr hcut hfun
  rw [exponent_sub_one_eq_massExponent]
  exact hmassExponentTarget

/-- Fully unconditional normalized floor at the exact rational exponent
`1.8288`. -/
theorem sharperNormalizedLowerBound :
    ∃ c : ℝ, 0 < c ∧ NormalizedScheduleFloor exponent c := by
  obtain ⟨R₀, M₀, huniform⟩ :=
    exists_uniformFiniteWindowDyadicDichotomy
  exact ⟨sharperNormalizedConstant R₀ M₀,
    sharperNormalizedConstant_pos huniform,
    sharperNormalizedLowerBound_of_uniform huniform⟩

/-- The sharper normalized floor persists for every larger exponent. -/
theorem sharperNormalizedLowerBound_of_gt
    {p : ℝ} (hp : exponent < p) :
    ∃ c : ℝ, 0 < c ∧ NormalizedScheduleFloor p c := by
  obtain ⟨c, hc, hfloor⟩ := sharperNormalizedLowerBound
  exact ⟨c, hc,
    normalizedScheduleFloor_mono_exponent hc.le hp.le hfloor⟩

/-- Public end-to-end claim at every exponent above `1.8288`. -/
def SharperMainStatement : Prop :=
  ∀ p : ℝ, exponent < p → p < 2 →
    ∃ c : ℝ, 0 < c ∧ MainClaim p c

theorem sharperMainTheorem : SharperMainStatement := by
  intro p hp _hpTwo
  obtain ⟨c, hc, hfloor⟩ := sharperNormalizedLowerBound_of_gt hp
  refine ⟨c / 2, by positivity, ?_⟩
  apply mainClaim_of_functional functionalAttainment
  exact functionalFloor_of_normalizedScheduleFloor
    (one_lt_exponent.trans hp).le hc.le hfloor

end

end GDLowerBound.FourBlock
