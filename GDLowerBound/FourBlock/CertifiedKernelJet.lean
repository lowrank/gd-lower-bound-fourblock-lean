import GDLowerBound.FourBlock.KernelCertificate
import GDLowerBound.FourBlock.KernelGradient

/-!
# Compact certified kernel values and gradients

`KernelUpperCert` stores short outward-rounded witnesses instead of enormous
exact Newton fractions.  This module proves that the same record also gives
rational enclosures for both partial derivatives.
-/

namespace GDLowerBound.FourBlock

noncomputable section

theorem KernelUpperCert.delta_bounds {c : KernelUpperCert} (hc : c.Valid) :
    (c.deltaLower : ℝ) ≤ delta (edgeParameter (c.u : ℝ) (c.v : ℝ)) ∧
      delta (edgeParameter (c.u : ℝ) (c.v : ℝ)) ≤ (c.deltaUpper : ℝ) := by
  dsimp only [KernelUpperCert.Valid] at hc
  rcases hc with
    ⟨huq, hvq, hsumq, hsqrtx, hsqrtValid, hdlo0, hdlo, hdhi,
      htotalY, htotalValid, hfactorY, hfactorValid, hfinal⟩
  have hu : (0 : ℝ) ≤ c.u := by exact_mod_cast huq
  have hv : (0 : ℝ) ≤ c.v := by exact_mod_cast hvq
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
  have hshi0 : (0 : ℝ) ≤ c.sqrt.upper := by exact_mod_cast hsqrtData.2.2.2.1
  have hdenLo : 0 < 2 * edgeParameter (c.u : ℝ) (c.v : ℝ) + 1 + c.sqrt.lower := by
    positivity
  have hdenHi : 0 < 2 * edgeParameter (c.u : ℝ) (c.v : ℝ) + 1 + c.sqrt.upper := by
    positivity
  constructor
  · have hdloReal : (c.deltaLower : ℝ) ≤
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
  · have hdhiReal :
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

structure KernelJetCert where
  value : KernelUpperCert
deriving Repr, DecidableEq

def KernelJetCert.Valid (c : KernelJetCert) : Prop :=
  c.value.Valid ∧ 0 < c.value.u ∧ 0 < c.value.v ∧ c.value.deltaUpper ≤ 1

instance (c : KernelJetCert) : Decidable c.Valid := by
  unfold KernelJetCert.Valid
  infer_instance

def KernelJetCert.valid (c : KernelJetCert) : Bool := decide c.Valid

def KernelJetCert.gradULower (c : KernelJetCert) : ℚ :=
  1 / (c.value.u + c.value.v) +
    c.value.deltaLower * (2 - c.value.deltaLower) * c.value.v ^ 2 /
      (2 * (c.value.u + c.value.v) ^ 2)

def KernelJetCert.gradUUpper (c : KernelJetCert) : ℚ :=
  1 / (c.value.u + c.value.v) +
    c.value.deltaUpper * (2 - c.value.deltaUpper) * c.value.v ^ 2 /
      (2 * (c.value.u + c.value.v) ^ 2)

def KernelJetCert.gradVLower (c : KernelJetCert) : ℚ :=
  1 / (c.value.u + c.value.v) +
    c.value.deltaLower * (2 - c.value.deltaLower) * c.value.u ^ 2 /
      (2 * (c.value.u + c.value.v) ^ 2)

def KernelJetCert.gradVUpper (c : KernelJetCert) : ℚ :=
  1 / (c.value.u + c.value.v) +
    c.value.deltaUpper * (2 - c.value.deltaUpper) * c.value.u ^ 2 /
      (2 * (c.value.u + c.value.v) ^ 2)

theorem KernelJetCert.sound {c : KernelJetCert} (hc : c.valid = true) :
    logKernel (c.value.u : ℝ) (c.value.v : ℝ) ≤ (c.value.upper : ℝ) ∧
    (c.gradULower : ℝ) ≤ kernelGradU c.value.u c.value.v ∧
      kernelGradU c.value.u c.value.v ≤ (c.gradUUpper : ℝ) ∧
    (c.gradVLower : ℝ) ≤ kernelGradV c.value.u c.value.v ∧
      kernelGradV c.value.u c.value.v ≤ (c.gradVUpper : ℝ) := by
  have hvalid : c.Valid := of_decide_eq_true hc
  have hbase : c.value.valid = true := by
    exact decide_eq_true hvalid.1
  have hvalue := KernelUpperCert.sound hbase
  have hd := KernelUpperCert.delta_bounds hvalid.1
  have hu : (0 : ℝ) < c.value.u := by exact_mod_cast hvalid.2.1
  have hv : (0 : ℝ) < c.value.v := by exact_mod_cast hvalid.2.2.1
  have hb := edgeParameter_nonneg hu.le hv.le
  have hd0 := delta_pos hb
  have hd1 := delta_le_one hb
  have hdlo0 : (0 : ℝ) < c.value.deltaLower := by
    exact_mod_cast hvalid.1.2.2.2.2.2.1
  have hdhi1 : (c.value.deltaUpper : ℝ) ≤ 1 := by exact_mod_cast hvalid.2.2.2
  have hslopeLo : (c.value.deltaLower : ℝ) * (2 - c.value.deltaLower) ≤
      logEnvelopeSlope (edgeParameter c.value.u c.value.v) := by
    unfold logEnvelopeSlope
    nlinarith
  have hslopeHi : logEnvelopeSlope (edgeParameter c.value.u c.value.v) ≤
      (c.value.deltaUpper : ℝ) * (2 - c.value.deltaUpper) := by
    unfold logEnvelopeSlope
    nlinarith
  have hru : (0 : ℝ) ≤ (c.value.v : ℝ) ^ 2 /
      (2 * ((c.value.u : ℝ) + c.value.v) ^ 2) := by positivity
  have hrv : (0 : ℝ) ≤ (c.value.u : ℝ) ^ 2 /
      (2 * ((c.value.u : ℝ) + c.value.v) ^ 2) := by positivity
  have huLo := mul_le_mul_of_nonneg_right hslopeLo hru
  have huHi := mul_le_mul_of_nonneg_right hslopeHi hru
  have hvLo := mul_le_mul_of_nonneg_right hslopeLo hrv
  have hvHi := mul_le_mul_of_nonneg_right hslopeHi hrv
  constructor
  · exact hvalue
  constructor
  · unfold KernelJetCert.gradULower kernelGradU
    push_cast
    simpa only [div_eq_mul_inv, mul_assoc] using
      add_le_add_right huLo (1 / ((c.value.u : ℝ) + c.value.v))
  constructor
  · unfold KernelJetCert.gradUUpper kernelGradU
    push_cast
    simpa only [div_eq_mul_inv, mul_assoc] using
      add_le_add_right huHi (1 / ((c.value.u : ℝ) + c.value.v))
  constructor
  · unfold KernelJetCert.gradVLower kernelGradV
    push_cast
    simpa only [div_eq_mul_inv, mul_assoc] using
      add_le_add_right hvLo (1 / ((c.value.u : ℝ) + c.value.v))
  · unfold KernelJetCert.gradVUpper kernelGradV
    push_cast
    simpa only [div_eq_mul_inv, mul_assoc] using
      add_le_add_right hvHi (1 / ((c.value.u : ℝ) + c.value.v))

end

end GDLowerBound.FourBlock
