import GDLowerBound.FourBlock.AllRankCutoff
import GDLowerBound.RankAnalysis.Normalized
import GDLowerBound.Geometry.FunctionalAttainment

/-!
# End-to-end exact-envelope lower bound

The exact chronological envelope gives a uniform small-state branch at every
rank above `allRankCutoff`.  Combining that branch with the original finite
cutoff scan and boundary propagation proves a normalized floor at the exact
rational exponent `criticalP = 1 + betaLower`.  This result is independent of
the still sharper four-block fixed-dilation averaging argument.
-/

namespace GDLowerBound.FourBlock

open scoped Real
open GDLowerBound.Schedule GDLowerBound.RankAnalysis

noncomputable section

/-- The explicit positive constant in the exact-envelope normalized floor. -/
def exactEnvelopeFloorConstant : ℝ :=
  min ((4 * boundaryPropagationConstant criticalP)⁻¹)
    (boundedRankConstant allRankCutoff /
      boundaryPropagationConstant criticalP)

theorem allRankCutoff_two : 2 ≤ allRankCutoff := by
  norm_num [allRankCutoff]

theorem allRankCutoff_above_criticalTheta :
    criticalTheta⁻¹ < (allRankCutoff : ℝ) := by
  rw [criticalTheta_eq]
  norm_num [betaLower, allRankCutoff]

theorem exactEnvelopeFloorConstant_pos :
    0 < exactEnvelopeFloorConstant := by
  have hK : 0 < boundaryPropagationConstant criticalP :=
    zero_lt_one.trans_le (boundaryPropagationConstant_ge_one one_lt_criticalP)
  unfold exactEnvelopeFloorConstant
  exact lt_min (by positivity)
    (div_pos (boundedRankConstant_pos (by
      exact allRankCutoff_two.trans' (by omega))) hK)

private theorem scaled_exactEnvelope_estimate
    {c a K B R D F : ℝ}
    (ha : 0 ≤ a) (hK : 0 < K) (hB : 0 < B) (hR : 0 < R)
    (hD : 0 < D) (hc : c ≤ a / K) (hmass : D ≤ K * B * R)
    (hfunctional : a / D ≤ F) :
    c / (B * R) ≤ F := by
  have hBR : 0 < B * R := mul_pos hB hR
  have hfirst : c / (B * R) ≤ (a / K) / (B * R) :=
    div_le_div_of_nonneg_right hc hBR.le
  have hrewrite : (a / K) / (B * R) = a / (K * B * R) := by
    field_simp [hK.ne', hB.ne', hR.ne']
  have hsecond : a / (K * B * R) ≤ a / D :=
    div_le_div_of_nonneg_left ha hD hmass
  exact hfirst.trans ((hrewrite ▸ hsecond).trans hfunctional)

/-- Exact-envelope normalized floor at the rational critical exponent. -/
theorem exactEnvelopeNormalizedLowerBound :
    ∃ c : ℝ, 0 < c ∧ NormalizedScheduleFloor criticalP c := by
  classical
  let Q : ℕ := allRankCutoff
  let c : ℝ := exactEnvelopeFloorConstant
  have hQtwo : 2 ≤ Q := allRankCutoff_two
  have hQtheta : criticalTheta⁻¹ < (Q : ℝ) :=
    allRankCutoff_above_criticalTheta
  have hK : 0 < boundaryPropagationConstant criticalP :=
    zero_lt_one.trans_le (boundaryPropagationConstant_ge_one one_lt_criticalP)
  refine ⟨c, exactEnvelopeFloorConstant_pos, ?_⟩
  intro T h hh
  have hB : 0 < cappedMass h := cappedMass_pos hh
  have hR :
      0 < ((longCount h : ℝ) + 1) ^ (criticalP - 1) :=
    Real.rpow_pos_of_pos (by positivity) _
  let smallRanks : Finset ℕ :=
    (Finset.Icc Q (longCount h)).filter
      (fun q ↦ zetaState h q ≤ criticalTheta)
  by_cases hsmallRanks : smallRanks.Nonempty
  · let k : ℕ := smallRanks.max' hsmallRanks
    have hkMember : k ∈ smallRanks := smallRanks.max'_mem hsmallRanks
    have hkData :
        k ∈ Finset.Icc Q (longCount h) ∧
          zetaState h k ≤ criticalTheta := by
      simpa only [smallRanks, Finset.mem_filter] using hkMember
    have hkIcc := Finset.mem_Icc.mp hkData.1
    have hQk : Q ≤ k := hkIcc.1
    have hkr : k ≤ longCount h := hkIcc.2
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
    have hcutAbove :
        CutoffConditions criticalP h (k + 1) (longCount h) :=
      criticalCutoffConditions_of_no_small_state hh (by
        dsimp only [Q] at hQk
        omega) hlargeAbove
    have hboundary := boundaryPropagation one_lt_criticalP hQtwo hQtheta hh
      hQk hkr hcutAbove
    have hmass := unresolvedMass_le_normalizedMass_of_boundary
      hh one_lt_criticalP (by omega : 1 ≤ k) hboundary
    have hfunctional :
        (4 : ℝ)⁻¹ / unresolvedMass h k ≤
          lowerBoundFunctional h :=
      (quarter_div_unresolvedMass_lt_functional_of_zeta_le hh
        (by simpa only [Q] using hQk) hkr hkData.2).le
    have hcSmall :
        c ≤ (4 : ℝ)⁻¹ / boundaryPropagationConstant criticalP := by
      have hcInv : c ≤ (4 * boundaryPropagationConstant criticalP)⁻¹ := by
        exact min_le_left _ _
      calc
        c ≤ (4 * boundaryPropagationConstant criticalP)⁻¹ := hcInv
        _ = (4 : ℝ)⁻¹ / boundaryPropagationConstant criticalP := by
          field_simp [hK.ne']
    exact scaled_exactEnvelope_estimate
      (a := (4 : ℝ)⁻¹) (K := boundaryPropagationConstant criticalP)
      (B := cappedMass h)
      (R := ((longCount h : ℝ) + 1) ^ (criticalP - 1))
      (D := unresolvedMass h k) (F := lowerBoundFunctional h)
      (by positivity) hK hB hR (unresolvedMass_pos hh k)
      hcSmall hmass hfunctional
  · have hnoSmall :
        ∀ q ∈ Finset.Icc Q (longCount h),
          criticalTheta < zetaState h q := by
      intro q hq
      apply lt_of_not_ge
      intro hqSmall
      apply hsmallRanks
      refine ⟨q, ?_⟩
      exact Finset.mem_filter.mpr ⟨hq, hqSmall⟩
    have hcLarge :
        c ≤ boundedRankConstant Q /
          boundaryPropagationConstant criticalP := by
      exact min_le_right _ _
    by_cases hrSmall : longCount h < Q
    · have hfunctional := boundedRankPrefix_uniform hh hQtwo
        (Nat.le_of_lt hrSmall) (le_refl (longCount h))
      have hKone : 1 ≤ boundaryPropagationConstant criticalP :=
        boundaryPropagationConstant_ge_one one_lt_criticalP
      have hRone :
          (1 : ℝ) ≤ ((longCount h : ℝ) + 1) ^ (criticalP - 1) := by
        exact Real.one_le_rpow (by norm_num)
          (by rw [criticalP_sub_one]; exact betaLower_pos.le)
      have hKB :
          cappedMass h ≤
            boundaryPropagationConstant criticalP * cappedMass h := by
        simpa only [one_mul] using
          mul_le_mul_of_nonneg_right hKone hB.le
      have hKBR :
          boundaryPropagationConstant criticalP * cappedMass h ≤
            boundaryPropagationConstant criticalP * cappedMass h *
              (((longCount h : ℝ) + 1) ^ (criticalP - 1)) := by
        simpa only [mul_one] using
          mul_le_mul_of_nonneg_left hRone
            (mul_nonneg (zero_le_one.trans hKone) hB.le)
      have hmass :
          unresolvedMass h (longCount h) ≤
            boundaryPropagationConstant criticalP * cappedMass h *
              (((longCount h : ℝ) + 1) ^ (criticalP - 1)) := by
        rw [unresolvedMass_longCount]
        exact hKB.trans hKBR
      exact scaled_exactEnvelope_estimate
        (a := boundedRankConstant Q)
        (K := boundaryPropagationConstant criticalP) (B := cappedMass h)
        (R := ((longCount h : ℝ) + 1) ^ (criticalP - 1))
        (D := unresolvedMass h (longCount h))
        (F := lowerBoundFunctional h)
        (boundedRankConstant_pos (by omega)).le hK hB hR
        (unresolvedMass_pos hh (longCount h)) hcLarge hmass hfunctional
    · have hQr : Q ≤ longCount h := Nat.le_of_not_gt hrSmall
      have hlargeAfterQ :
          ∀ q ∈ Finset.Icc (Q + 1) (longCount h),
            criticalTheta < zetaState h q := by
        intro q hq
        have hqIcc := Finset.mem_Icc.mp hq
        exact hnoSmall q (Finset.mem_Icc.mpr ⟨by omega, hqIcc.2⟩)
      have hcutAfterQ :
          CutoffConditions criticalP h (Q + 1) (longCount h) :=
        criticalCutoffConditions_of_no_small_state hh (by
          dsimp only [Q]
          omega) hlargeAfterQ
      have hboundary := boundaryPropagation one_lt_criticalP hQtwo hQtheta hh
        (le_refl Q) hQr hcutAfterQ
      have hmass := unresolvedMass_le_normalizedMass_of_boundary
        hh one_lt_criticalP (by omega : 1 ≤ Q) hboundary
      have hfunctional := boundedRankPrefix_uniform hh hQtwo
        (le_refl Q) hQr
      exact scaled_exactEnvelope_estimate
        (a := boundedRankConstant Q)
        (K := boundaryPropagationConstant criticalP) (B := cappedMass h)
        (R := ((longCount h : ℝ) + 1) ^ (criticalP - 1))
        (D := unresolvedMass h Q) (F := lowerBoundFunctional h)
        (boundedRankConstant_pos (by omega)).le hK hB hR
        (unresolvedMass_pos hh Q) hcLarge hmass hfunctional

/-- A normalized schedule floor remains valid when the target exponent is
increased. -/
theorem normalizedScheduleFloor_mono_exponent
    {p q c : ℝ} (hc : 0 ≤ c) (hpq : p ≤ q)
    (hfloor : NormalizedScheduleFloor p c) :
    NormalizedScheduleFloor q c := by
  intro T h hh
  have hB : 0 < cappedMass h := cappedMass_pos hh
  have hbase : (1 : ℝ) ≤ (longCount h : ℝ) + 1 := by norm_num
  have hpow :
      ((longCount h : ℝ) + 1) ^ (p - 1) ≤
        ((longCount h : ℝ) + 1) ^ (q - 1) :=
    Real.rpow_le_rpow_of_exponent_le hbase (by linarith)
  have hdenP :
      0 < cappedMass h *
        ((longCount h : ℝ) + 1) ^ (p - 1) := by
    exact mul_pos hB (Real.rpow_pos_of_pos (by positivity) _)
  have hden :
      cappedMass h * ((longCount h : ℝ) + 1) ^ (p - 1) ≤
        cappedMass h * ((longCount h : ℝ) + 1) ^ (q - 1) :=
    mul_le_mul_of_nonneg_left hpow hB.le
  exact (div_le_div_of_nonneg_left hc hdenP hden).trans (hfloor T h hh)

/-- Exact-envelope normalized floor for every exponent above `criticalP`. -/
theorem exactEnvelopeNormalizedLowerBound_of_gt
    {p : ℝ} (hp : criticalP < p) :
    ∃ c : ℝ, 0 < c ∧ NormalizedScheduleFloor p c := by
  obtain ⟨c, hc, hfloor⟩ := exactEnvelopeNormalizedLowerBound
  exact ⟨c, hc, normalizedScheduleFloor_mono_exponent hc.le hp.le hfloor⟩

/-- Public end-to-end statement of the rigorous exact-envelope improvement. -/
def ExactEnvelopeMainStatement : Prop :=
  ∀ p : ℝ, criticalP < p → p < 2 →
    ∃ c : ℝ, 0 < c ∧ MainClaim p c

theorem exactEnvelopeMainTheorem : ExactEnvelopeMainStatement := by
  intro p hp _hpTwo
  obtain ⟨c, hc, hfloor⟩ := exactEnvelopeNormalizedLowerBound_of_gt hp
  refine ⟨c / 2, by positivity, ?_⟩
  apply mainClaim_of_functional functionalAttainment
  exact functionalFloor_of_normalizedScheduleFloor
    (one_lt_criticalP.trans hp).le hc.le hfloor

end

end GDLowerBound.FourBlock
