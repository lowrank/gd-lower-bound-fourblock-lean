import GDLowerBound.FourBlock.SmallPrefixScore
import GDLowerBound.FourBlock.FiniteConstraintTransfer
import GDLowerBound.FourBlock.RobustFiniteThreshold
import GDLowerBound.FourBlock.LocalParameterBounds

/-!
# Schedule-level robust four-block dichotomy

This is the pointwise composition interface needed by the global averaging
argument. At a sufficiently large four-block rank in a critical cutoff
interval, either the uniform exact-score branch gives a functional
contribution, or the instantiated robust local certificate gives a strict
lower bound for the schedule control energy.
-/

namespace GDLowerBound.FourBlock

open GDLowerBound.Schedule GDLowerBound.RankAnalysis

noncomputable section

def scheduleControlEnergy {T : ℕ} (h : StepSchedule T) (m : ℕ) : ℝ :=
  max (centralEndpoint (zetaState h (4 * m)))
    (scheduleDilationEnergy h m)

theorem schedulePrefix_strict_domain
    {T m : ℕ} {h : StepSchedule T} (hm : 0 < m)
    (hq : 4 * m ≤ longCount h) :
    0 < schedulePrefixA h m ∧
      0 < schedulePrefixR h m - schedulePrefixA h m ∧
      0 < schedulePrefixS h m - schedulePrefixR h m ∧
      0 < 1 - schedulePrefixS h m := by
  let w := idealReciprocalWeights h m
  have hw : ∀ i, 0 < w i := idealReciprocalWeights_pos hm (by omega)
  have htot : 0 < fourBlockTotal w := fourBlockTotal_pos hm hw
  have h1 : 0 < quarterSumOne w :=
    quarterSum_pos hm (outsideQuarterOne w) (fun i ↦ hw _)
  have h2 : 0 < quarterSumTwo w :=
    quarterSum_pos hm (outsideQuarterTwo w) (fun i ↦ hw _)
  have h3 : 0 < quarterSumThree w :=
    quarterSum_pos hm (outsideQuarterThree w) (fun i ↦ hw _)
  have h4 : 0 < quarterSumFour w :=
    quarterSum_pos hm (outsideQuarterFour w) (fun i ↦ hw _)
  rw [← idealFourBlockA_eq_schedulePrefixA,
    ← idealFourBlockR_eq_schedulePrefixR,
    ← idealFourBlockS_eq_schedulePrefixS]
  unfold fourBlockA fourBlockR fourBlockS
  constructor
  · exact div_pos h1 htot
  constructor
  · have heq : (quarterSumOne w + quarterSumTwo w) / fourBlockTotal w -
        quarterSumOne w / fourBlockTotal w =
        quarterSumTwo w / fourBlockTotal w := by ring
    rw [heq]
    exact div_pos h2 htot
  constructor
  · have heq :
        (quarterSumOne w + quarterSumTwo w + quarterSumThree w) /
              fourBlockTotal w -
            (quarterSumOne w + quarterSumTwo w) / fourBlockTotal w =
          quarterSumThree w / fourBlockTotal w := by ring
    rw [heq]
    exact div_pos h3 htot
  · have hsum :
        fourBlockTotal w = quarterSumOne w + quarterSumTwo w +
          quarterSumThree w + quarterSumFour w := rfl
    have heq : 1 -
          (quarterSumOne w + quarterSumTwo w + quarterSumThree w) /
            fourBlockTotal w =
        quarterSumFour w / fourBlockTotal w := by
      rw [hsum]
      field_simp [htot.ne']
      ring
    rw [heq]
    exact div_pos h4 htot

theorem scheduleRobustLocalDichotomy
    {T Q lo m : ℕ} {h : StepSchedule T}
    (hQ : (criticalTheta)⁻¹ < (Q : ℝ))
    (hh : IsNonnegativeSchedule h)
    (hm : 2000 ≤ m) (hQ2m : Q ≤ 2 * m) (hlo : lo ≤ 2 * m)
    (hq : 4 * m ≤ longCount h)
    (hcut : CutoffConditions criticalP h lo (longCount h))
    (hz2hi : zetaState h (2 * m) ≤ (29 / 10 : ℝ))
    (hz3hi : zetaState h (3 * m) ≤ (121 / 100 : ℝ))
    (hz4hi : zetaState h (4 * m) ≤ (119 / 250 : ℝ))
    (hexp : Real.exp
        (oneStepLyapunovConstant criticalP / (12 * m : ℕ)) ≤
      (8201 / 8200 : ℝ)) :
    (4 : ℝ)⁻¹ / unresolvedMass h (4 * m) < lowerBoundFunctional h ∨
      robustLocalGap < scheduleControlEnergy h m := by
  have hm0 : 0 < m := by omega
  have h2mem : 2 * m ∈ Finset.Icc lo (longCount h) :=
    Finset.mem_Icc.mpr ⟨hlo, by omega⟩
  have h3mem : 3 * m ∈ Finset.Icc lo (longCount h) :=
    Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  have h4mem : 4 * m ∈ Finset.Icc lo (longCount h) :=
    Finset.mem_Icc.mpr ⟨by omega, hq⟩
  obtain ⟨hz2, hv2, _hv2hi, _hd2⟩ := hcut (2 * m) h2mem
  obtain ⟨hz3, hv3, _hv3hi, hd3⟩ := hcut (3 * m) h3mem
  obtain ⟨hz4, hv4, _hv4hi, _hd4⟩ := hcut (4 * m) h4mem
  have hz2' : criticalTheta ≤ zetaState h (2 * m) := hz2.le
  have hz3' : criticalTheta ≤ zetaState h (3 * m) := hz3.le
  have hz4' : criticalTheta ≤ zetaState h (4 * m) := hz4.le
  have hz2lo := certificate_state_lower hz2'
  have hz3lo := certificate_state_lower hz3'
  have hv3z : relativeMassIncrement h (3 * m) ≤
      1 / zetaState h (3 * m) := by
    have hz3pos : 0 < zetaState h (3 * m) := criticalTheta_pos.trans_le hz3'
    rw [le_div_iff₀ hz3pos]
    simpa only [mul_comm] using hd3
  have hv3cap := certificate_velocity_upper hz3' hv3z
  have hord := schedulePrefix_ordered (h := h) hm0 hq
  have hstrict := schedulePrefix_strict_domain (h := h) hm0 hq
  have hdomain := orderedFourBlocks_domain hord
  have hrhi : schedulePrefixR h m ≤ (1 / 2 : ℝ) := hdomain.2.1
  have hshi : schedulePrefixS h m ≤ (3 / 4 : ℝ) := by
    have hs := hdomain.2.2.2.1
    linarith
  have hRdef :
      schedulePrefixS h m * zetaState h (4 * m) / tailR30 =
        schedulePrefixS h m * zetaState h (4 * m) / tailR30 := rfl
  have hs0 := schedulePrefixS_pos (h := h) hm0 hq
  have hz40 := zetaState_pos_of_rank hh (by omega) hq
  have hr30 : 0 < tailR30 := by
    unfold tailR30
    exact Real.rpow_pos_of_pos (by norm_num) _
  have hR0 : 0 <
      schedulePrefixS h m * zetaState h (4 * m) / tailR30 :=
    div_pos (mul_pos hs0 hz40) hr30
  have hRhi :
      schedulePrefixS h m * zetaState h (4 * m) / tailR30 ≤
        (41 / 50 : ℝ) :=
    (tailRatio_upper (r := schedulePrefixR h m) hRdef hz40 hz4hi hs0.le hshi).le
  have hcut3 : CutoffConditions criticalP h (3 * m) (longCount h) := by
    intro q hqmem
    have hqm := Finset.mem_Icc.mp hqmem
    exact hcut q (Finset.mem_Icc.mpr ⟨by omega, hqm.2⟩)
  have hconstraint := schedule_qState_le_tailCoordinate_mul_exp_sharp_error
    hQ hh hm0 (by omega : Q ≤ 3 * m) hq hcut3
  have hlocal := scheduleLocalEnergy_le_dilationEnergy
    hh hm0 hq hz4' hz4hi hv4.le
  have hendpoint : centralEndpoint (zetaState h (4 * m)) ≤
      scheduleControlEnergy h m := le_max_left _ _
  have hlocalControl :
      fourBlockLocalEnergy
          (zetaState h (2 * m)) (relativeMassIncrement h (2 * m))
          (zetaState h (3 * m)) (relativeMassIncrement h (3 * m))
          (schedulePrefixS h m * zetaState h (4 * m) / tailR30)
          (zetaState h (4 * m)) (schedulePrefixR h m) ≤
        scheduleControlEnergy h m :=
    hlocal.trans (le_max_right _ _)
  by_cases hrlo : (1 / 20 : ℝ) ≤ schedulePrefixR h m
  · have hslo : (3 / 40 : ℝ) ≤ schedulePrefixS h m := by
      have hrs := hdomain.2.2.1
      linarith
    rcases exactMatchingScoreDichotomy_of_cutoff hh hm (by omega : lo ≤ 4 * m)
        hq hcut hrlo with hsmall | hmatch
    · exact Or.inl hsmall
    · exact Or.inr (fourBlockRobustLocalGap
        hz2' hz2lo hz2hi hz3' hz3lo hz3hi hv3.le hv3cap hv3z
        hR0 hRhi hconstraint hexp hRdef hz40
        (by
          have ht : (centralThetaLowerQ : ℝ) < criticalTheta := by
            rw [criticalTheta_eq]
            norm_num [centralThetaLowerQ, betaLower]
          exact ht.trans hz4 |>.le)
        (by norm_num [centralZUpperQ] at ⊢; exact hz4hi)
        hstrict.1 hstrict.2.1 hstrict.2.2.1 hstrict.2.2.2 hord hmatch
        hrlo hrhi hslo hshi hendpoint hlocalControl)
  · have hrsmall : schedulePrefixR h m < (1 / 20 : ℝ) :=
      lt_of_not_ge hrlo
    have hq' : 2 * (m + m) ≤ longCount h := by omega
    have hsmallScore := smallExactMatchingScoreRank_of_prefixR_lt
      hh hm hq'
      (by
        have ht : (centralThetaLowerQ : ℝ) < criticalTheta := by
          rw [criticalTheta_eq]
          norm_num [centralThetaLowerQ, betaLower]
        simpa only [show 2 * (m + m) = 4 * m by omega] using
          (ht.trans hz4).le)
      (by simpa only [show 2 * (m + m) = 4 * m by omega] using hz4hi)
      hrsmall
    exact Or.inl (by
      have hfun := quarter_div_unresolvedMass_lt_functional_of_smallMatchingScore
        hh hm0 hq' hsmallScore
      simpa only [show 2 * (m + m) = 4 * m by omega] using hfun)

end

end GDLowerBound.FourBlock
