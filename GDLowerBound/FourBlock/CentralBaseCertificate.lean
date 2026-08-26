import GDLowerBound.FourBlock.SideGCertificateData
import GDLowerBound.FourBlock.SideQ2CertificateData
import GDLowerBound.FourBlock.TailPowerBounds

/-! # Exact bridge from the side constants to the central base constant -/

namespace GDLowerBound.FourBlock

noncomputable section

def qScaledLogUpperN (y : ℚ) (n : ℕ) : ℚ :=
  let k := qLogScale y
  qLogUpper (y * 2 ^ k) n - k * qLogLower 2 n

theorem qScaledLogUpperN_sound {y : ℚ} (hy : 0 < y) (n : ℕ) :
    Real.log (y : ℝ) ≤ (qScaledLogUpperN y n : ℝ) := by
  let k := qLogScale y
  have hyR : (0 : ℝ) < y := by exact_mod_cast hy
  have hpow : (0 : ℝ) < 2 ^ k := by positivity
  have hscaledQ : (0 : ℚ) < y * 2 ^ k := by positivity
  have hscaled := le_logUpper
    (y := ((y * 2 ^ k : ℚ) : ℝ)) (by exact_mod_cast hscaledQ) n
  rw [← coe_qLogUpper] at hscaled
  push_cast at hscaled
  have htwo := logLower_le (y := ((2 : ℚ) : ℝ)) (by norm_num) n
  rw [← coe_qLogLower] at htwo
  have hk0 : (0 : ℝ) ≤ k := by positivity
  have hkbound := mul_le_mul_of_nonneg_left htwo hk0
  have hmul := Real.log_mul hyR.ne' hpow.ne'
  rw [Real.log_pow] at hmul
  dsimp only [k] at hscaled hkbound hmul
  norm_num at htwo hkbound hmul
  unfold qScaledLogUpperN
  dsimp only [k]
  push_cast
  linarith

def qCentralBaseWitness : ℚ :=
  tailQ2LowerQ + sideG66CertificateTarget -
    centralLambda2Q * (centralBetaLowerQ + 2) *
      qScaledLogUpperN (1 / 2) 16 -
    centralAlphaQ * (centralBetaLowerQ + 2) *
      qScaledLogUpperN (3 / 4) 16

theorem centralBaseWitness_valid :
    centralCBaseLowerQ < qCentralBaseWitness := by
  native_decide

def centralTrueBase : ℝ :=
  (tailQ2LowerQ : ℝ) + (sideG66CertificateTarget : ℝ) -
    (centralLambda2Q : ℝ) * Real.log tailR20 -
    (centralAlphaQ : ℝ) * Real.log tailR30

theorem centralCBase_lt_trueBase :
    (centralCBaseLowerQ : ℝ) < centralTrueBase := by
  have hhalf := qScaledLogUpperN_sound (y := (1 / 2 : ℚ)) (by norm_num) 16
  have hthree := qScaledLogUpperN_sound (y := (3 / 4 : ℚ)) (by norm_num) 16
  norm_num at hhalf hthree
  have heq : (centralBetaLowerQ : ℝ) = betaLower := by
    norm_num [centralBetaLowerQ, betaLower]
  have hexp : (0 : ℝ) ≤ betaLower + 2 := by linarith [betaLower_pos]
  have h20 : Real.log tailR20 ≤
      (betaLower + 2) * (qScaledLogUpperN (1 / 2) 16 : ℚ) := by
    rw [tailR20, Real.log_rpow (by norm_num : (0 : ℝ) < 1 / 2)]
    exact mul_le_mul_of_nonneg_left hhalf hexp
  have h30 : Real.log tailR30 ≤
      (betaLower + 2) * (qScaledLogUpperN (3 / 4) 16 : ℚ) := by
    rw [tailR30, Real.log_rpow (by norm_num : (0 : ℝ) < 3 / 4)]
    exact mul_le_mul_of_nonneg_left hthree hexp
  have hl2 : (0 : ℝ) ≤ centralLambda2Q := by norm_num [centralLambda2Q]
  have ha : (0 : ℝ) ≤ centralAlphaQ := by norm_num [centralAlphaQ]
  have h20term := mul_le_mul_of_nonneg_left h20 hl2
  have h30term := mul_le_mul_of_nonneg_left h30 ha
  have hwitness : (centralCBaseLowerQ : ℝ) <
      (qCentralBaseWitness : ℝ) := by exact_mod_cast centralBaseWitness_valid
  unfold qCentralBaseWitness at hwitness
  unfold centralTrueBase
  push_cast at hwitness h20term h30term ⊢
  rw [heq] at hwitness
  ring_nf at hwitness h20term h30term ⊢
  linarith

end

end GDLowerBound.FourBlock
