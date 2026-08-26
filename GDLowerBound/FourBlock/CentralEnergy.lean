import GDLowerBound.FourBlock.Constants
import GDLowerBound.FourBlock.ScaledLog

/-! # Certified monotone lower bound for the central local energy -/

namespace GDLowerBound.FourBlock

noncomputable section

def centralThetaLowerQ : ℚ := 4086960373221888 / 10000000000000000
def centralThetaUpperQ : ℚ := 40869603732218882 / 100000000000000000
def centralZUpperQ : ℚ := 476 / 1000
def centralBetaLowerQ : ℚ := 8565576222695287 / 10000000000000000
def centralCBaseLowerQ : ℚ := 927669024051 / 10000000000000
def centralC4Q : ℚ := 9658 / 100000
def centralD4Q : ℚ := 49302 / 100000
def centralLambda2Q : ℚ := 11 / 1000
def centralAlphaQ : ℚ := 358 / 10000
def centralLambda3Q : ℚ := 468 / 10000

def qCentralEndpointRaw (z : ℚ) : ℚ :=
  centralD4Q * centralBetaLowerQ * (z - centralThetaUpperQ) -
    centralD4Q ^ 2 * (z - centralThetaLowerQ) ^ 2 / (4 * centralC4Q)

def qCentralEndpoint (z : ℚ) : ℚ := max 0 (qCentralEndpointRaw z)

def centralEndpointRaw (z : ℝ) : ℝ :=
  (centralD4Q : ℝ) * centralBetaLowerQ * (z - centralThetaUpperQ) -
    (centralD4Q : ℝ) ^ 2 * (z - centralThetaLowerQ) ^ 2 /
      (4 * (centralC4Q : ℝ))

def centralEndpoint (z : ℝ) : ℝ := max 0 (centralEndpointRaw z)

def centralEnergy (z r s : ℝ) : ℝ :=
  max (centralEndpoint z)
    ((centralCBaseLowerQ : ℝ) + centralEndpoint z +
      (centralLambda2Q : ℝ) * Real.log r +
      (centralAlphaQ : ℝ) * Real.log s +
      (centralLambda3Q : ℝ) * Real.log z)

def qCentralEnergyLower (z r s : ℚ) : ℚ :=
  max (qCentralEndpoint z)
    (centralCBaseLowerQ + qCentralEndpoint z +
      centralLambda2Q * qScaledLogLower r +
      centralAlphaQ * qScaledLogLower s +
      centralLambda3Q * qScaledLogLower z)

theorem coe_qCentralEndpointRaw (z : ℚ) :
    (qCentralEndpointRaw z : ℝ) = centralEndpointRaw (z : ℝ) := by
  norm_num [qCentralEndpointRaw, centralEndpoint, centralEndpointRaw]

theorem coe_qCentralEndpoint (z : ℚ) :
    (qCentralEndpoint z : ℝ) = centralEndpoint (z : ℝ) := by
  unfold qCentralEndpoint centralEndpoint
  push_cast
  rw [coe_qCentralEndpointRaw]

theorem qCentralEnergyLower_sound {z r s : ℚ}
    (hz : 0 < z) (hr : 0 < r) (hs : 0 < s) :
    (qCentralEnergyLower z r s : ℝ) ≤ centralEnergy z r s := by
  have hlz := qScaledLogLower_sound hz
  have hlr := qScaledLogLower_sound hr
  have hls := qScaledLogLower_sound hs
  unfold qCentralEnergyLower centralEnergy
  push_cast
  rw [coe_qCentralEndpoint]
  apply max_le_max le_rfl
  have hl2 : (0 : ℝ) ≤ centralLambda2Q := by norm_num [centralLambda2Q]
  have hla : (0 : ℝ) ≤ centralAlphaQ := by norm_num [centralAlphaQ]
  have hl3 : (0 : ℝ) ≤ centralLambda3Q := by norm_num [centralLambda3Q]
  gcongr

theorem centralEndpointRaw_mono {z z' : ℝ}
    (hz : (centralThetaLowerQ : ℝ) ≤ z)
    (hzz : z ≤ z') (hz' : z' ≤ (centralZUpperQ : ℝ)) :
    centralEndpointRaw z ≤ centralEndpointRaw z' := by
  have hzup : z ≤ (centralZUpperQ : ℝ) := hzz.trans hz'
  have hcoef : 0 ≤
      (centralD4Q : ℝ) * centralBetaLowerQ -
        (centralD4Q : ℝ) ^ 2 *
          (z' + z - 2 * (centralThetaLowerQ : ℝ)) /
            (4 * (centralC4Q : ℝ)) := by
    norm_num [centralD4Q, centralBetaLowerQ, centralThetaLowerQ,
      centralZUpperQ, centralC4Q] at hz hzup hz' ⊢
    nlinarith
  have hid : centralEndpointRaw z' - centralEndpointRaw z =
      (z' - z) *
        ((centralD4Q : ℝ) * centralBetaLowerQ -
          (centralD4Q : ℝ) ^ 2 *
            (z' + z - 2 * (centralThetaLowerQ : ℝ)) /
              (4 * (centralC4Q : ℝ))) := by
    unfold centralEndpointRaw
    ring
  rw [← sub_nonneg, hid]
  exact mul_nonneg (sub_nonneg.mpr hzz) hcoef

theorem centralEndpoint_mono {z z' : ℝ}
    (hz : (centralThetaLowerQ : ℝ) ≤ z)
    (hzz : z ≤ z') (hz' : z' ≤ (centralZUpperQ : ℝ)) :
    centralEndpoint z ≤ centralEndpoint z' := by
  unfold centralEndpoint
  exact max_le_max le_rfl (centralEndpointRaw_mono hz hzz hz')

theorem centralEnergy_mono {z z' r r' s s' : ℝ}
    (hz0 : 0 < z) (hr0 : 0 < r) (hs0 : 0 < s)
    (hz : (centralThetaLowerQ : ℝ) ≤ z) (hzz : z ≤ z')
    (hz' : z' ≤ (centralZUpperQ : ℝ)) (hrr : r ≤ r') (hss : s ≤ s') :
    centralEnergy z r s ≤ centralEnergy z' r' s' := by
  have hz'0 : 0 < z' := hz0.trans_le hzz
  have hr'0 : 0 < r' := hr0.trans_le hrr
  have hs'0 : 0 < s' := hs0.trans_le hss
  have hep := centralEndpoint_mono hz hzz hz'
  have hlz := Real.log_le_log hz0 hzz
  have hlr := Real.log_le_log hr0 hrr
  have hls := Real.log_le_log hs0 hss
  unfold centralEnergy
  apply max_le_max hep
  have hl2 : (0 : ℝ) ≤ centralLambda2Q := by norm_num [centralLambda2Q]
  have hla : (0 : ℝ) ≤ centralAlphaQ := by norm_num [centralAlphaQ]
  have hl3 : (0 : ℝ) ≤ centralLambda3Q := by norm_num [centralLambda3Q]
  gcongr

end

end GDLowerBound.FourBlock
