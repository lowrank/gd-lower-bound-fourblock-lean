import GDLowerBound.FourBlock.ScheduleLocalDichotomy
import GDLowerBound.FourBlock.ReciprocalSquareError

/-!
# Cap-free pointwise schedule theorem

If an endpoint cap fails, that endpoint cost already exceeds the local
target. The two dilation defects can be negative only by an explicit
`O(1/m)` amount. Adding that amount makes the schedule energy dominate all
three endpoint costs; when the caps hold, it also dominates the control
energy used by the robust local theorem.
-/

namespace GDLowerBound.FourBlock

open GDLowerBound.Schedule GDLowerBound.RankAnalysis

noncomputable section

def scheduleControlError (m : ℕ) : ℝ :=
  (centralLambda2Q : ℝ) * oneStepLyapunovConstant criticalP / (2 * m : ℕ) +
    (centralLambda3Q : ℝ) * oneStepLyapunovConstant criticalP / (3 * m : ℕ)

theorem scheduleControlError_nonneg (m : ℕ) :
    0 ≤ scheduleControlError m := by
  unfold scheduleControlError
  have hC : 0 ≤ oneStepLyapunovConstant criticalP :=
    zero_le_one.trans (oneStepLyapunovConstant_ge_one criticalP)
  have hl2 : (0 : ℝ) ≤ centralLambda2Q := by norm_num [centralLambda2Q]
  have hl3 : (0 : ℝ) ≤ centralLambda3Q := by norm_num [centralLambda3Q]
  positivity

theorem endpointCost_nonneg_of_cutoff {c d z v : ℝ}
    (hc : 0 ≤ c) (hd : 0 ≤ d) (hz : criticalTheta ≤ z)
    (hv : 0 ≤ v) :
    0 ≤ endpointCost c d z v := by
  unfold endpointCost
  exact add_nonneg (mul_nonneg hc (sq_nonneg _))
    (mul_nonneg (mul_nonneg hd hv) (sub_nonneg.mpr hz))

/-- The weighted schedule energy plus the exact block-error allowance
dominates the sum of its three nonnegative endpoint costs. -/
theorem scheduleEndpointSum_le_add_error
    {T Q lo m : ℕ} {h : StepSchedule T}
    (hQ : (criticalTheta)⁻¹ < (Q : ℝ))
    (hh : IsNonnegativeSchedule h) (hm : 0 < m)
    (hQ2m : Q ≤ 2 * m) (hlo : lo ≤ 2 * m)
    (hq : 4 * m ≤ longCount h)
    (hcut : CutoffConditions criticalP h lo (longCount h)) :
    endpointCost sideC2Q sideD2Q
          (zetaState h (2 * m)) (relativeMassIncrement h (2 * m)) +
        endpointCost sideC3Q sideD3Q
          (zetaState h (3 * m)) (relativeMassIncrement h (3 * m)) +
        endpointCost centralC4Q centralD4Q
          (zetaState h (4 * m)) (relativeMassIncrement h (4 * m)) ≤
      scheduleDilationEnergy h m + scheduleControlError m := by
  have hcut2 : CutoffConditions criticalP h (2 * m) (longCount h) := by
    intro q hqmem
    have hqm := Finset.mem_Icc.mp hqmem
    exact hcut q (Finset.mem_Icc.mpr ⟨by omega, hqm.2⟩)
  have hcut3 : CutoffConditions criticalP h (3 * m) (longCount h) := by
    intro q hqmem
    have hqm := Finset.mem_Icc.mp hqmem
    exact hcut q (Finset.mem_Icc.mpr ⟨by omega, hqm.2⟩)
  have hh2 := dilationBlockH_lower_inv hQ hh hQ2m (by omega : 1 ≤ 2 * m)
    (by omega : 2 * m ≤ 3 * m) (by omega : 3 * m ≤ longCount h) hcut2
  have hh3 := dilationBlockH_lower_inv hQ hh (by omega : Q ≤ 3 * m)
    (by omega : 1 ≤ 3 * m) (by omega : 3 * m ≤ 4 * m) hq hcut3
  have hl2 : (0 : ℝ) ≤ centralLambda2Q := by norm_num [centralLambda2Q]
  have hl3 : (0 : ℝ) ≤ centralLambda3Q := by norm_num [centralLambda3Q]
  have hh2' := mul_le_mul_of_nonneg_left hh2 hl2
  have hh3' := mul_le_mul_of_nonneg_left hh3 hl3
  unfold scheduleDilationEnergy weightedScheduleEnergy scheduleControlError
  ring_nf at hh2' hh3' ⊢
  linarith

/-- With the fourth endpoint cap, the same allowance dominates the `max`
control energy required by the robust certificate. -/
theorem scheduleControlEnergy_le_add_error_of_cap
    {T Q lo m : ℕ} {h : StepSchedule T}
    (hQ : (criticalTheta)⁻¹ < (Q : ℝ))
    (hh : IsNonnegativeSchedule h) (hm : 0 < m)
    (hQ2m : Q ≤ 2 * m) (hlo : lo ≤ 2 * m)
    (hq : 4 * m ≤ longCount h)
    (hcut : CutoffConditions criticalP h lo (longCount h))
    (hz4hi : zetaState h (4 * m) ≤ (119 / 250 : ℝ)) :
    scheduleControlEnergy h m ≤
      scheduleDilationEnergy h m + scheduleControlError m := by
  have h2mem : 2 * m ∈ Finset.Icc lo (longCount h) :=
    Finset.mem_Icc.mpr ⟨hlo, by omega⟩
  have h3mem : 3 * m ∈ Finset.Icc lo (longCount h) :=
    Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  have h4mem : 4 * m ∈ Finset.Icc lo (longCount h) :=
    Finset.mem_Icc.mpr ⟨by omega, hq⟩
  obtain ⟨hz2, hv2, _hv2hi, _hd2⟩ := hcut (2 * m) h2mem
  obtain ⟨hz3, hv3, _hv3hi, _hd3⟩ := hcut (3 * m) h3mem
  obtain ⟨hz4, hv4, _hv4hi, _hd4⟩ := hcut (4 * m) h4mem
  have hsum := scheduleEndpointSum_le_add_error hQ hh hm hQ2m hlo hq hcut
  have he2 : 0 ≤ endpointCost sideC2Q sideD2Q
      (zetaState h (2 * m)) (relativeMassIncrement h (2 * m)) :=
    endpointCost_nonneg_of_cutoff (by norm_num [sideC2Q])
      (by norm_num [sideD2Q]) hz2.le hv2.le
  have he3 : 0 ≤ endpointCost sideC3Q sideD3Q
      (zetaState h (3 * m)) (relativeMassIncrement h (3 * m)) :=
    endpointCost_nonneg_of_cutoff (by norm_num [sideC3Q])
      (by norm_num [sideD3Q]) hz3.le hv3.le
  have hend := centralEndpoint_le_endpointCost hz4.le hz4hi hv4.le
  unfold scheduleControlEnergy
  apply max_le
  · exact hend.trans (by linarith)
  · exact le_add_of_nonneg_right (scheduleControlError_nonneg m)

/-- Cap-free finite-rank alternative. This is the exact pointwise statement
to be averaged in the new normalized-floor proof. -/
theorem schedulePointwiseDichotomy
    {T Q lo m : ℕ} {h : StepSchedule T}
    (hQ : (criticalTheta)⁻¹ < (Q : ℝ))
    (hh : IsNonnegativeSchedule h)
    (hm : 2000 ≤ m) (hQ2m : Q ≤ 2 * m) (hlo : lo ≤ 2 * m)
    (hq : 4 * m ≤ longCount h)
    (hcut : CutoffConditions criticalP h lo (longCount h))
    (hexp : Real.exp
        (oneStepLyapunovConstant criticalP / (12 * m : ℕ)) ≤
      (8201 / 8200 : ℝ)) :
    (4 : ℝ)⁻¹ / unresolvedMass h (4 * m) < lowerBoundFunctional h ∨
      robustLocalGap < scheduleDilationEnergy h m + scheduleControlError m := by
  have hm0 : 0 < m := by omega
  have h2mem : 2 * m ∈ Finset.Icc lo (longCount h) :=
    Finset.mem_Icc.mpr ⟨hlo, by omega⟩
  have h3mem : 3 * m ∈ Finset.Icc lo (longCount h) :=
    Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  have h4mem : 4 * m ∈ Finset.Icc lo (longCount h) :=
    Finset.mem_Icc.mpr ⟨by omega, hq⟩
  obtain ⟨_hz2, hv2, _hv2hi, _hd2⟩ := hcut (2 * m) h2mem
  obtain ⟨_hz3, hv3, _hv3hi, _hd3⟩ := hcut (3 * m) h3mem
  obtain ⟨_hz4, hv4, _hv4hi, _hd4⟩ := hcut (4 * m) h4mem
  have he2 : 0 ≤ endpointCost sideC2Q sideD2Q
      (zetaState h (2 * m)) (relativeMassIncrement h (2 * m)) :=
    endpointCost_nonneg_of_cutoff (by norm_num [sideC2Q])
      (by norm_num [sideD2Q]) _hz2.le hv2.le
  have he3 : 0 ≤ endpointCost sideC3Q sideD3Q
      (zetaState h (3 * m)) (relativeMassIncrement h (3 * m)) :=
    endpointCost_nonneg_of_cutoff (by norm_num [sideC3Q])
      (by norm_num [sideD3Q]) _hz3.le hv3.le
  have he4 : 0 ≤ endpointCost centralC4Q centralD4Q
      (zetaState h (4 * m)) (relativeMassIncrement h (4 * m)) :=
    endpointCost_nonneg_of_cutoff (by norm_num [centralC4Q])
      (by norm_num [centralD4Q]) _hz4.le hv4.le
  have hsum := scheduleEndpointSum_le_add_error hQ hh hm0 hQ2m hlo hq hcut
  have hgapTarget : robustLocalGap < (tailTargetQ : ℝ) := by
    norm_num [robustLocalGap, tailTargetQ]
  by_cases hz2hi : zetaState h (2 * m) ≤ (29 / 10 : ℝ)
  · by_cases hz3hi : zetaState h (3 * m) ≤ (121 / 100 : ℝ)
    · by_cases hz4hi : zetaState h (4 * m) ≤ (119 / 250 : ℝ)
      · rcases scheduleRobustLocalDichotomy hQ hh hm hQ2m hlo hq hcut
            hz2hi hz3hi hz4hi hexp with hsmall | hcontrol
        · exact Or.inl hsmall
        · exact Or.inr (hcontrol.trans_le
            (scheduleControlEnergy_le_add_error_of_cap
              hQ hh hm0 hQ2m hlo hq hcut hz4hi))
      · have hcap := endpointFour_cap (le_of_not_ge hz4hi) hv4.le
        exact Or.inr (hgapTarget.trans (hcap.trans_le (by linarith)))
    · have hcap := endpointThree_cap (le_of_not_ge hz3hi) hv3.le
      exact Or.inr (hgapTarget.trans (hcap.trans_le (by linarith)))
  · have hcap := endpointTwo_cap (le_of_not_ge hz2hi) hv2.le
    exact Or.inr (hgapTarget.trans (hcap.trans_le (by linarith)))

end

end GDLowerBound.FourBlock
