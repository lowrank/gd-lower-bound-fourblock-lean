import GDLowerBound.FourBlock.RationalBounds
import GDLowerBound.FourBlock.Monotonicity

/-! # Executable upper certificates for the exact logarithmic kernel -/

namespace GDLowerBound.FourBlock

noncomputable section

theorem logKernel_closed {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v)
    (hsum : 0 < u + v) :
    logKernel u v =
      Real.log ((u + v) / 2) +
        Real.log (2 / delta (edgeParameter u v) - 1) +
          delta (edgeParameter u v) - 1 := by
  have hb := edgeParameter_nonneg hu hv
  have hd := delta_pos hb
  have hd1 := delta_le_one hb
  have hfactor : 0 < 2 / delta (edgeParameter u v) - 1 := by
    rw [sub_pos, lt_div_iff₀ hd]
    nlinarith
  unfold logKernel envelope
  change Real.log ((u + v) / 2) +
      Real.log ((2 / delta (edgeParameter u v) - 1) *
        Real.exp (delta (edgeParameter u v) - 1)) = _
  rw [Real.log_mul hfactor.ne' (Real.exp_pos _).ne']
  rw [Real.log_exp]
  ring

def qEdgeParameter (u v : ℚ) : ℚ := u * v / (2 * (u + v))

theorem coe_qEdgeParameter (u v : ℚ) :
    (qEdgeParameter u v : ℝ) = edgeParameter (u : ℝ) (v : ℝ) := by
  norm_num [qEdgeParameter, edgeParameter]

structure KernelUpperCert where
  u : ℚ
  v : ℚ
  sqrt : SqrtBoundCert
  deltaLower : ℚ
  deltaUpper : ℚ
  logTotal : LogBoundCert
  logFactor : LogBoundCert
  upper : ℚ
deriving Repr, DecidableEq

def KernelUpperCert.Valid (c : KernelUpperCert) : Prop :=
  let b := qEdgeParameter c.u c.v
  0 ≤ c.u ∧ 0 ≤ c.v ∧ 0 < c.u + c.v ∧
  c.sqrt.x = 4 * b ^ 2 + 1 ∧ c.sqrt.valid = true ∧
  0 < c.deltaLower ∧
  c.deltaLower ≤ 2 / (2 * b + 1 + c.sqrt.upper) ∧
  2 / (2 * b + 1 + c.sqrt.lower) ≤ c.deltaUpper ∧
  c.logTotal.y = (c.u + c.v) / 2 ∧ c.logTotal.valid = true ∧
  c.logFactor.y = 2 / c.deltaLower - 1 ∧ c.logFactor.valid = true ∧
  c.logTotal.upper + c.logFactor.upper + c.deltaUpper - 1 ≤ c.upper

instance (c : KernelUpperCert) : Decidable c.Valid := by
  unfold KernelUpperCert.Valid
  infer_instance

def KernelUpperCert.valid (c : KernelUpperCert) : Bool := decide c.Valid

theorem KernelUpperCert.sound {c : KernelUpperCert} (hc : c.valid = true) :
    logKernel (c.u : ℝ) (c.v : ℝ) ≤ (c.upper : ℝ) := by
  have h := of_decide_eq_true hc
  dsimp only [KernelUpperCert.Valid] at h
  rcases h with
    ⟨huq, hvq, hsumq, hsqrtx, hsqrtValid, hdlo0, hdlo, hdhi,
      htotalY, htotalValid, hfactorY, hfactorValid, hfinal⟩
  let bq := qEdgeParameter c.u c.v
  have hu : (0 : ℝ) ≤ c.u := by exact_mod_cast huq
  have hv : (0 : ℝ) ≤ c.v := by exact_mod_cast hvq
  have hsum : (0 : ℝ) < c.u + c.v := by exact_mod_cast hsumq
  have hb : 0 ≤ edgeParameter (c.u : ℝ) (c.v : ℝ) :=
    edgeParameter_nonneg hu hv
  have hsqrt := SqrtBoundCert.sound hsqrtValid
  have hsqrtxReal :
      (c.sqrt.x : ℝ) = 4 * edgeParameter (c.u : ℝ) (c.v : ℝ) ^ 2 + 1 := by
    rw [hsqrtx]
    push_cast
    rw [coe_qEdgeParameter]
  rw [hsqrtxReal] at hsqrt
  let den := 2 * edgeParameter (c.u : ℝ) (c.v : ℝ) + 1 +
    Real.sqrt (4 * edgeParameter (c.u : ℝ) (c.v : ℝ) ^ 2 + 1)
  have hden : 0 < den := by
    dsimp only [den]
    exact delta_denominator_pos hb
  have hsqrtData : 0 ≤ c.sqrt.x ∧ 0 ≤ c.sqrt.lower ∧
      c.sqrt.lower ^ 2 ≤ c.sqrt.x ∧ 0 ≤ c.sqrt.upper ∧
        c.sqrt.x ≤ c.sqrt.upper ^ 2 := of_decide_eq_true hsqrtValid
  have hslo0 : (0 : ℝ) ≤ c.sqrt.lower := by exact_mod_cast hsqrtData.2.1
  have hshi0 : (0 : ℝ) ≤ c.sqrt.upper := by
    exact_mod_cast hsqrtData.2.2.2.1
  have hdenLo : 0 <
      2 * edgeParameter (c.u : ℝ) (c.v : ℝ) + 1 + c.sqrt.lower := by
    positivity
  have hdenHi : 0 <
      2 * edgeParameter (c.u : ℝ) (c.v : ℝ) + 1 + c.sqrt.upper := by
    positivity
  have hdLower : (c.deltaLower : ℝ) ≤
      delta (edgeParameter (c.u : ℝ) (c.v : ℝ)) := by
    have hdloReal : (c.deltaLower : ℝ) ≤
        2 / (2 * edgeParameter (c.u : ℝ) (c.v : ℝ) + 1 + c.sqrt.upper) := by
      have ht : (c.deltaLower : ℝ) ≤
          2 / (2 * (qEdgeParameter c.u c.v : ℝ) + 1 + (c.sqrt.upper : ℝ)) := by
        exact_mod_cast hdlo
      rw [coe_qEdgeParameter] at ht
      exact ht
    have hfrac :
        2 / (2 * edgeParameter (c.u : ℝ) (c.v : ℝ) + 1 + c.sqrt.upper) ≤
          2 / den := by
      apply div_le_div_of_nonneg_left (by norm_num) hden
      dsimp only [den]
      linarith
    unfold delta
    exact hdloReal.trans hfrac
  have hdUpper : delta (edgeParameter (c.u : ℝ) (c.v : ℝ)) ≤
      (c.deltaUpper : ℝ) := by
    have hdhiReal :
        2 / (2 * edgeParameter (c.u : ℝ) (c.v : ℝ) + 1 + c.sqrt.lower) ≤
          (c.deltaUpper : ℝ) := by
      have ht :
          2 / (2 * (qEdgeParameter c.u c.v : ℝ) + 1 + (c.sqrt.lower : ℝ)) ≤
            (c.deltaUpper : ℝ) := by
        exact_mod_cast hdhi
      rw [coe_qEdgeParameter] at ht
      exact ht
    have hfrac : 2 / den ≤
        2 / (2 * edgeParameter (c.u : ℝ) (c.v : ℝ) + 1 + c.sqrt.lower) := by
      apply div_le_div_of_nonneg_left (by norm_num) hdenLo
      dsimp only [den]
      linarith
    unfold delta
    exact hfrac.trans hdhiReal
  have hdloReal : (0 : ℝ) < c.deltaLower := by exact_mod_cast hdlo0
  have hdeltaPos := delta_pos hb
  have hfactorPos : 0 < 2 / delta (edgeParameter (c.u : ℝ) (c.v : ℝ)) - 1 := by
    have hd1 := delta_le_one hb
    rw [sub_pos, lt_div_iff₀ hdeltaPos]
    nlinarith
  have hfactorMono :
      2 / delta (edgeParameter (c.u : ℝ) (c.v : ℝ)) - 1 ≤
        2 / (c.deltaLower : ℝ) - 1 := by
    have := div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 2)
      hdloReal hdLower
    linarith
  have htotal := LogBoundCert.sound htotalValid
  have hfactor := LogBoundCert.sound hfactorValid
  rw [htotalY] at htotal
  rw [hfactorY] at hfactor
  have htotalUpper : Real.log (((c.u : ℝ) + c.v) / 2) ≤
      (c.logTotal.upper : ℝ) := by
    exact_mod_cast htotal.2
  have hfactorUpper :
      Real.log (2 / delta (edgeParameter (c.u : ℝ) (c.v : ℝ)) - 1) ≤
        (c.logFactor.upper : ℝ) := by
    have hlogMono := Real.log_le_log hfactorPos hfactorMono
    exact hlogMono.trans (by exact_mod_cast hfactor.2)
  rw [logKernel_closed hu hv hsum]
  have hfinalReal :
      (c.logTotal.upper : ℝ) + c.logFactor.upper + c.deltaUpper - 1 ≤
        (c.upper : ℝ) := by exact_mod_cast hfinal
  linarith

end

end GDLowerBound.FourBlock
