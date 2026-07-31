import GDLowerBound.Matching.ScalarBound
import GDLowerBound.RankAnalysis.BoundedRank
import GDLowerBound.RankAnalysis.Boundary
import GDLowerBound.RankAnalysis.Density
import GDLowerBound.RankAnalysis.FloorReduction
import GDLowerBound.RankAnalysis.Parameters

namespace GDLowerBound
namespace RankAnalysis

open scoped BigOperators Real
open Schedule

noncomputable section

/-- A rank-independent version of the bounded-prefix constant, valid through
rank `Q`. -/
def boundedRankConstant (Q : ℕ) : ℝ :=
  (4 * (Q : ℝ) * 8 ^ (Q - 1))⁻¹

/-- The explicit constant left after the bounded-rank and boundary estimates
are combined. -/
def normalizedFloorConstant (p : ℝ) (Q : ℕ) : ℝ :=
  min ((2 * boundaryPropagationConstant p)⁻¹)
    (boundedRankConstant Q / boundaryPropagationConstant p)

theorem boundedRankConstant_pos {Q : ℕ} (hQ : 1 ≤ Q) :
    0 < boundedRankConstant Q := by
  unfold boundedRankConstant
  positivity

theorem normalizedFloorConstant_pos {p : ℝ} (hp : 1 < p)
    {Q : ℕ} (hQ : 1 ≤ Q) :
    0 < normalizedFloorConstant p Q := by
  have hK : 0 < boundaryPropagationConstant p :=
    zero_lt_one.trans_le (boundaryPropagationConstant_ge_one hp)
  have hcQ : 0 < boundedRankConstant Q := boundedRankConstant_pos hQ
  unfold normalizedFloorConstant
  exact lt_min (by positivity) (div_pos hcQ hK)

/-- Every prefix of rank at most `Q` satisfies the same bounded-rank
estimate.  This is the form used by the finite-rank branch of the scan. -/
theorem boundedRankPrefix_uniform {T Q q : ℕ} {h : StepSchedule T}
    (hh : IsNonnegativeSchedule h) (hQ : 2 ≤ Q)
    (hqQ : q ≤ Q) (hqr : q ≤ longCount h) :
    boundedRankConstant Q / unresolvedMass h q ≤
      lowerBoundFunctional h := by
  have hD : 0 < unresolvedMass h q := unresolvedMass_pos hh q
  have hQpos : 0 < (Q : ℝ) := by exact_mod_cast (by omega : 0 < Q)
  have hQpow : 0 < (8 : ℝ) ^ (Q - 1) := by positivity
  have hCQden : 0 < 4 * (Q : ℝ) * 8 ^ (Q - 1) := by positivity
  have hprefix := boundedRankPrefix hh q hqr
  by_cases hq0 : q = 0
  · rw [if_pos hq0] at hprefix
    subst q
    have hcQhalf : boundedRankConstant Q ≤ (2 : ℝ)⁻¹ := by
      unfold boundedRankConstant
      apply (inv_le_inv₀ hCQden (by norm_num : (0 : ℝ) < 2)).2
      have hQone : (1 : ℝ) ≤ Q := by exact_mod_cast (show 1 ≤ Q by omega)
      have hpowOne : (1 : ℝ) ≤ 8 ^ (Q - 1) := by
        exact one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 8)
      nlinarith
    have hscalar :
        boundedRankConstant Q / unresolvedMass h 0 ≤
          (2 * unresolvedMass h 0)⁻¹ := by
      rw [div_le_iff₀ (unresolvedMass_pos hh 0)]
      have hcollapse :
          (2 * unresolvedMass h 0)⁻¹ * unresolvedMass h 0 =
            (2 : ℝ)⁻¹ := by
        field_simp [(unresolvedMass_pos hh 0).ne']
      rw [hcollapse]
      exact hcQhalf
    exact hscalar.trans hprefix
  · rw [if_neg hq0] at hprefix
    have hqpos : 0 < q := Nat.pos_of_ne_zero hq0
    have hqRpos : 0 < (q : ℝ) := by exact_mod_cast hqpos
    have hpow :
        (8 : ℝ) ^ (q - 1) ≤ 8 ^ (Q - 1) := by
      exact pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 8)
        (Nat.sub_le_sub_right hqQ 1)
    have hfactor :
        4 * (q : ℝ) * 8 ^ (q - 1) ≤
          4 * (Q : ℝ) * 8 ^ (Q - 1) := by
      have hqcast : (q : ℝ) ≤ Q := by exact_mod_cast hqQ
      have hqnonneg : 0 ≤ (q : ℝ) := by positivity
      have hpowNonneg : 0 ≤ (8 : ℝ) ^ (q - 1) := by positivity
      have hQpowNonneg : 0 ≤ (8 : ℝ) ^ (Q - 1) := by positivity
      nlinarith [mul_le_mul hqcast hpow hpowNonneg (Nat.cast_nonneg Q)]
    have hqden : 0 < 4 * (q : ℝ) * 8 ^ (q - 1) := by positivity
    have hcQq :
        boundedRankConstant Q ≤
          (4 * (q : ℝ) * 8 ^ (q - 1))⁻¹ := by
      unfold boundedRankConstant
      exact (inv_le_inv₀ hCQden hqden).2 hfactor
    have hscalar :
        boundedRankConstant Q / unresolvedMass h q ≤
          (4 * unresolvedMass h q * (q : ℝ) * 8 ^ (q - 1))⁻¹ := by
      rw [div_le_iff₀ hD]
      have hcollapse :
          (4 * unresolvedMass h q * (q : ℝ) * 8 ^ (q - 1))⁻¹ *
              unresolvedMass h q =
            (4 * (q : ℝ) * 8 ^ (q - 1))⁻¹ := by
        field_simp [hD.ne', hqRpos.ne']
      rw [hcollapse]
      exact hcQq
    exact hscalar.trans hprefix

/-- Boundary propagation, stripped of the harmless rank power on the left
and enlarged from `r` to `r+1` on the right. -/
theorem unresolvedMass_le_normalizedMass_of_boundary
    {T k : ℕ} {p : ℝ} {h : StepSchedule T}
    (hh : IsNonnegativeSchedule h) (hp : 1 < p) (hk : 1 ≤ k)
    (hboundary :
      unresolvedMass h k * ((k : ℝ) ^ (p - 1)) ≤
        boundaryPropagationConstant p * cappedMass h *
          ((longCount h : ℝ) ^ (p - 1))) :
    unresolvedMass h k ≤
      boundaryPropagationConstant p * cappedMass h *
        (((longCount h : ℝ) + 1) ^ (p - 1)) := by
  have hexponent : 0 ≤ p - 1 := by linarith
  have hkbase : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hkpow : (1 : ℝ) ≤ (k : ℝ) ^ (p - 1) :=
    Real.one_le_rpow hkbase hexponent
  have hDnonneg : 0 ≤ unresolvedMass h k := by
    exact unresolvedMass_nonneg hh k
  have hleft :
      unresolvedMass h k ≤
        unresolvedMass h k * ((k : ℝ) ^ (p - 1)) := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hkpow hDnonneg
  have hrbase : (longCount h : ℝ) ≤ (longCount h : ℝ) + 1 := by
    norm_num
  have hrpow :
      (longCount h : ℝ) ^ (p - 1) ≤
        ((longCount h : ℝ) + 1) ^ (p - 1) :=
    Real.rpow_le_rpow (Nat.cast_nonneg _) hrbase hexponent
  have hKnonneg : 0 ≤ boundaryPropagationConstant p :=
    (boundaryPropagationConstant_ge_one hp).trans' zero_le_one
  have hBnonneg : 0 ≤ cappedMass h := by
    exact (cappedMass_pos hh).le
  calc
    unresolvedMass h k ≤
        unresolvedMass h k * ((k : ℝ) ^ (p - 1)) := hleft
    _ ≤ boundaryPropagationConstant p * cappedMass h *
          ((longCount h : ℝ) ^ (p - 1)) := hboundary
    _ ≤ boundaryPropagationConstant p * cappedMass h *
          (((longCount h : ℝ) + 1) ^ (p - 1)) := by
      exact mul_le_mul_of_nonneg_left hrpow (mul_nonneg hKnonneg hBnonneg)

/-- A proof-independent predicate saying that rank `q` realizes the small
matching-factor alternative. -/
def SmallMatchingRank {T : ℕ} (h : StepSchedule T) (rho : ℝ) (q : ℕ) : Prop :=
  ∃ hq : q ≤ longCount h,
    Matching.normalizedMatchingFactor h q hq < rho

theorem smallMatchingRank_iff {T : ℕ} {h : StepSchedule T} {rho : ℝ}
    {q : ℕ} (hq : q ≤ longCount h) :
    SmallMatchingRank h rho q ↔
      Matching.normalizedMatchingFactor h q hq < rho := by
  constructor
  · rintro ⟨hq', hsmall⟩
    simpa only [Subsingleton.elim hq' hq] using hsmall
  · exact fun hsmall ↦ ⟨hq, hsmall⟩

private theorem scaled_normalized_estimate
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

/-- The matching-factor alternative supplies the four scalar assumptions
needed by boundary propagation at every rank where the small alternative
fails. -/
theorem cutoffConditions_of_no_small_matching
    {T Q lo : ℕ} {p rho : ℝ} {h : StepSchedule T}
    (hh : IsNonnegativeSchedule h) (hp : pStar < p)
    (hQtwo : 2 ≤ Q) (hQlo : Q ≤ lo)
    (hcutoff : cutoffMatchingBound p Q < rho)
    (hnoSmall : ∀ q ∈ Finset.Icc lo (longCount h),
      ¬ SmallMatchingRank h rho q) :
    CutoffConditions p h lo (longCount h) := by
  intro q hq
  have hqIcc := Finset.mem_Icc.mp hq
  have hQq : Q ≤ q := hQlo.trans hqIcc.1
  have hqone : 1 ≤ q := by omega
  have hqrank : q ≤ longCount h := hqIcc.2
  have hlarge :
      rho ≤ Matching.normalizedMatchingFactor h q hqrank := by
    rw [← not_lt]
    intro hsmall
    exact hnoSmall q hq ((smallMatchingRank_iff hqrank).2 hsmall)
  have hzeta : lyapunovTheta p < zetaState h q :=
    Matching.zetaState_gt_of_normalizedMatchingFactor_ge
      hh hp hQtwo hQq hqrank hcutoff hlarge
  have hnu : 0 < relativeMassIncrement h q :=
    relativeMassIncrement_pos hh hqone hqrank
  have hproduct :
      zetaState h q * relativeMassIncrement h q ≤ 1 :=
    zeta_mul_relativeMassIncrement_le_one hh hqone hqrank
  have htheta : 0 < lyapunovTheta p :=
    lyapunovTheta_pos_of_pStar_lt hp
  have hnuUpper :
      relativeMassIncrement h q < (lyapunovTheta p)⁻¹ := by
    rw [inv_eq_one_div]
    apply (lt_div_iff₀ htheta).2
    calc
      relativeMassIncrement h q * lyapunovTheta p =
          lyapunovTheta p * relativeMassIncrement h q := mul_comm _ _
      _ < zetaState h q * relativeMassIncrement h q :=
        mul_lt_mul_of_pos_right hzeta hnu
      _ ≤ 1 := hproduct
  exact ⟨hzeta, hnu, hnuUpper, hproduct⟩

/-- A small normalized matching factor already forces a universal
`1/(2 D_q)` functional contribution because the cutoff lies below one. -/
theorem half_div_unresolvedMass_lt_functional_of_small
    {T q : ℕ} {rho : ℝ} {h : StepSchedule T}
    (hh : IsNonnegativeSchedule h) (hqTwo : 2 ≤ q)
    (hq : q ≤ longCount h) (hrho : 0 < rho) (hrhoOne : rho < 1)
    (hsmall : Matching.normalizedMatchingFactor h q hq < rho) :
    (2 : ℝ)⁻¹ / unresolvedMass h q < lowerBoundFunctional h := by
  have hraw := Matching.functional_lower_of_normalizedMatchingFactor_lt
    hh hqTwo hq hrho hsmall
  have hD : 0 < unresolvedMass h q := unresolvedMass_pos hh q
  have hrhoPow : 0 < rho ^ q := pow_pos hrho q
  have hrhoPowLe : rho ^ q ≤ (1 : ℝ) :=
    pow_le_one₀ hrho.le hrhoOne.le
  have hinvPow : (1 : ℝ) ≤ (rho ^ q)⁻¹ :=
    (one_le_inv₀ hrhoPow).2 hrhoPowLe
  have hrewrite :
      (2 : ℝ)⁻¹ / unresolvedMass h q =
        1 / (2 * unresolvedMass h q) := by
    field_simp [hD.ne']
  have hcompare :
      1 / (2 * unresolvedMass h q) ≤
        (rho ^ q)⁻¹ / (2 * unresolvedMass h q) := by
    exact div_le_div_of_nonneg_right hinvPow
      (mul_pos (by norm_num) hD).le
  rw [hrewrite]
  exact hcompare.trans_lt hraw

/-- The normalized rank lower bound, with an explicit constant depending
only on the exponent. -/
theorem normalizedLowerBound {p : ℝ} (hp : pStar < p) :
    ∃ c : ℝ, 0 < c ∧ NormalizedScheduleFloor p c := by
  classical
  obtain ⟨rho, Q, hrhoCut, hrhoOne, hQtwo, hQtheta, hmatchingCut⟩ :=
    exists_cutoffParameters hp
  have hpOne : 1 < p := one_lt_pStar.trans hp
  have htheta : 0 < lyapunovTheta p :=
    lyapunovTheta_pos_of_pStar_lt hp
  have hrho : 0 < rho := by
    nlinarith [sq_nonneg (lyapunovTheta p)]
  have hK : 0 < boundaryPropagationConstant p :=
    zero_lt_one.trans_le (boundaryPropagationConstant_ge_one hpOne)
  let c : ℝ := normalizedFloorConstant p Q
  refine ⟨c, normalizedFloorConstant_pos hpOne (by omega), ?_⟩
  intro T h hh
  have hB : 0 < cappedMass h := cappedMass_pos hh
  have hR :
      0 < ((longCount h : ℝ) + 1) ^ (p - 1) := by
    exact Real.rpow_pos_of_pos (by positivity) _
  let smallRanks : Finset ℕ :=
    (Finset.Icc Q (longCount h)).filter (SmallMatchingRank h rho)
  by_cases hsmallRanks : smallRanks.Nonempty
  · let k : ℕ := smallRanks.max' hsmallRanks
    have hkMember : k ∈ smallRanks := by
      exact smallRanks.max'_mem hsmallRanks
    have hkData :
        k ∈ Finset.Icc Q (longCount h) ∧ SmallMatchingRank h rho k := by
      simpa only [smallRanks, Finset.mem_filter] using hkMember
    have hkIcc := Finset.mem_Icc.mp hkData.1
    have hQk : Q ≤ k := hkIcc.1
    have hkr : k ≤ longCount h := hkIcc.2
    have hkTwo : 2 ≤ k := hQtwo.trans hQk
    have hkSmall :
        Matching.normalizedMatchingFactor h k hkr < rho :=
      (smallMatchingRank_iff hkr).1 hkData.2
    have hnoAbove :
        ∀ q ∈ Finset.Icc (k + 1) (longCount h),
          ¬ SmallMatchingRank h rho q := by
      intro q hq hqSmall
      have hqIcc := Finset.mem_Icc.mp hq
      have hqFull : q ∈ Finset.Icc Q (longCount h) :=
        Finset.mem_Icc.mpr ⟨by omega, hqIcc.2⟩
      have hqMember : q ∈ smallRanks := by
        exact Finset.mem_filter.mpr ⟨hqFull, hqSmall⟩
      have hqk : q ≤ k := by
        dsimp only [k]
        exact smallRanks.le_max' q hqMember
      omega
    have hcutAbove :
        CutoffConditions p h (k + 1) (longCount h) :=
      cutoffConditions_of_no_small_matching hh hp hQtwo
        (by omega) hmatchingCut hnoAbove
    have hboundary := boundaryPropagation hpOne hQtwo hQtheta hh
      hQk hkr hcutAbove
    have hmass := unresolvedMass_le_normalizedMass_of_boundary
      hh hpOne (by omega : 1 ≤ k) hboundary
    have hfunctional :
        (2 : ℝ)⁻¹ / unresolvedMass h k ≤
          lowerBoundFunctional h :=
      (half_div_unresolvedMass_lt_functional_of_small
        hh hkTwo hkr hrho hrhoOne hkSmall).le
    have hcSmall : c ≤ (2 : ℝ)⁻¹ / boundaryPropagationConstant p := by
      calc
        c ≤ (2 * boundaryPropagationConstant p)⁻¹ := by
          exact min_le_left _ _
        _ = (2 : ℝ)⁻¹ / boundaryPropagationConstant p := by
          field_simp [hK.ne']
    exact scaled_normalized_estimate
      (a := (2 : ℝ)⁻¹) (K := boundaryPropagationConstant p)
      (B := cappedMass h)
      (R := ((longCount h : ℝ) + 1) ^ (p - 1))
      (D := unresolvedMass h k) (F := lowerBoundFunctional h)
      (by positivity) hK hB hR (unresolvedMass_pos hh k)
      hcSmall hmass hfunctional
  · have hnoSmall :
        ∀ q ∈ Finset.Icc Q (longCount h),
          ¬ SmallMatchingRank h rho q := by
      intro q hq hqSmall
      apply hsmallRanks
      refine ⟨q, ?_⟩
      exact Finset.mem_filter.mpr ⟨hq, hqSmall⟩
    have hcLarge :
        c ≤ boundedRankConstant Q / boundaryPropagationConstant p := by
      exact min_le_right _ _
    by_cases hrSmall : longCount h < Q
    · have hfunctional := boundedRankPrefix_uniform hh hQtwo
        (Nat.le_of_lt hrSmall) (le_refl (longCount h))
      have hKone : 1 ≤ boundaryPropagationConstant p :=
        boundaryPropagationConstant_ge_one hpOne
      have hRone :
          (1 : ℝ) ≤ ((longCount h : ℝ) + 1) ^ (p - 1) := by
        exact Real.one_le_rpow (by norm_num) (by linarith)
      have hKB :
          cappedMass h ≤ boundaryPropagationConstant p * cappedMass h := by
        simpa only [one_mul] using
          mul_le_mul_of_nonneg_right hKone hB.le
      have hKBR :
          boundaryPropagationConstant p * cappedMass h ≤
            boundaryPropagationConstant p * cappedMass h *
              (((longCount h : ℝ) + 1) ^ (p - 1)) := by
        simpa only [mul_one] using
          mul_le_mul_of_nonneg_left hRone
            (mul_nonneg (zero_le_one.trans hKone) hB.le)
      have hmass :
          unresolvedMass h (longCount h) ≤
            boundaryPropagationConstant p * cappedMass h *
              (((longCount h : ℝ) + 1) ^ (p - 1)) := by
        rw [unresolvedMass_longCount]
        exact hKB.trans hKBR
      exact scaled_normalized_estimate
        (a := boundedRankConstant Q)
        (K := boundaryPropagationConstant p) (B := cappedMass h)
        (R := ((longCount h : ℝ) + 1) ^ (p - 1))
        (D := unresolvedMass h (longCount h))
        (F := lowerBoundFunctional h)
        (boundedRankConstant_pos (by omega)).le hK hB hR
        (unresolvedMass_pos hh (longCount h)) hcLarge hmass hfunctional
    · have hQr : Q ≤ longCount h := Nat.le_of_not_gt hrSmall
      have hnoAfterQ :
          ∀ q ∈ Finset.Icc (Q + 1) (longCount h),
            ¬ SmallMatchingRank h rho q := by
        intro q hq
        have hqIcc := Finset.mem_Icc.mp hq
        exact hnoSmall q (Finset.mem_Icc.mpr ⟨by omega, hqIcc.2⟩)
      have hcutAfterQ :
          CutoffConditions p h (Q + 1) (longCount h) :=
        cutoffConditions_of_no_small_matching hh hp hQtwo
          (by omega) hmatchingCut hnoAfterQ
      have hboundary := boundaryPropagation hpOne hQtwo hQtheta hh
        (le_refl Q) hQr hcutAfterQ
      have hmass := unresolvedMass_le_normalizedMass_of_boundary
        hh hpOne (by omega : 1 ≤ Q) hboundary
      have hfunctional := boundedRankPrefix_uniform hh hQtwo
        (le_refl Q) hQr
      exact scaled_normalized_estimate
        (a := boundedRankConstant Q)
        (K := boundaryPropagationConstant p) (B := cappedMass h)
        (R := ((longCount h : ℝ) + 1) ^ (p - 1))
        (D := unresolvedMass h Q) (F := lowerBoundFunctional h)
        (boundedRankConstant_pos (by omega)).le hK hB hR
        (unresolvedMass_pos hh Q) hcLarge hmass hfunctional

/-- Proposition `prop:normalized-floor`. -/
theorem normalizedFloorTheorem : NormalizedFloorTheorem := by
  intro p hp _hpTwo
  exact normalizedLowerBound hp

end

end RankAnalysis
end GDLowerBound
