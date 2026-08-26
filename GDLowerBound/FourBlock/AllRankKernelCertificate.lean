import GDLowerBound.FourBlock.KernelCertificate
import GDLowerBound.FourBlock.CriticalLyapunov

/-!
# Negative exact-envelope kernel at the all-rank cutoff

The internal critical exponent is rounded upward by two units in the last
displayed decimal place.  This makes the exact balanced envelope strictly
subcritical.  The very small margin is retained exactly: the square root and
both logarithms below are checked with rational interval arithmetic.
-/

namespace GDLowerBound.FourBlock

noncomputable section

/-- A deliberately large finite cutoff.  Its only purpose is to make the
single auxiliary endpoint of the exact augmented path negligible. -/
def allRankCutoff : ℕ := 200000000

def allRankThetaUpperQ : ℚ :=
  40869603732218882 / 100000000000000000

def allRankUCapQ : ℚ :=
  2 * allRankThetaUpperQ +
    1 / ((allRankCutoff : ℚ) * (allRankCutoff - 1))

def allRankKernelB : ℚ := qEdgeParameter allRankUCapQ allRankUCapQ

def allRankKernelSqrtLower : ℚ :=
  5401463808364497333857043 / 5000000000000000000000000

def allRankKernelSqrtUpper : ℚ :=
  10802927616728994667714087 / 10000000000000000000000000

def allRankKernelDeltaLower : ℚ :=
  2 / (2 * allRankKernelB + 1 + allRankKernelSqrtUpper)

def allRankKernelDeltaUpper : ℚ :=
  2 / (2 * allRankKernelB + 1 + allRankKernelSqrtLower)

def allRankKernelFactor : ℚ := 2 / allRankKernelDeltaLower - 1

def allRankKernelCert : KernelUpperCert where
  u := allRankUCapQ
  v := allRankUCapQ
  sqrt :=
    { x := 4 * allRankKernelB ^ 2 + 1
      lower := allRankKernelSqrtLower
      upper := allRankKernelSqrtUpper }
  deltaLower := allRankKernelDeltaLower
  deltaUpper := allRankKernelDeltaUpper
  logTotal :=
    { y := allRankUCapQ
      n := 24
      lower := qLogLower allRankUCapQ 24
      upper := qLogUpper allRankUCapQ 24 }
  logFactor :=
    { y := allRankKernelFactor
      n := 24
      lower := qLogLower allRankKernelFactor 24
      upper := qLogUpper allRankKernelFactor 24 }
  upper := qLogUpper allRankUCapQ 24 +
    qLogUpper allRankKernelFactor 24 + allRankKernelDeltaUpper - 1

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem allRankKernelCert_valid : allRankKernelCert.valid = true := by
  norm_num [KernelUpperCert.valid, KernelUpperCert.Valid,
    allRankKernelCert, allRankKernelB, allRankUCapQ,
    allRankThetaUpperQ, allRankCutoff, allRankKernelSqrtLower,
    allRankKernelSqrtUpper, allRankKernelDeltaLower,
    allRankKernelDeltaUpper, allRankKernelFactor,
    SqrtBoundCert.valid, LogBoundCert.valid, qEdgeParameter,
    qLogLower, qLogUpper, qLogSeriesError, qLogSeries, qLogRadius]

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem allRankKernelUpper_neg : allRankKernelCert.upper < 0 := by
  norm_num [allRankKernelCert, allRankKernelB, allRankUCapQ,
    allRankThetaUpperQ, allRankCutoff, allRankKernelSqrtLower,
    allRankKernelSqrtUpper, allRankKernelDeltaLower,
    allRankKernelDeltaUpper, allRankKernelFactor,
    qEdgeParameter, qLogUpper, qLogSeriesError, qLogSeries, qLogRadius]

theorem logKernel_allRankUCap_neg :
    logKernel (allRankUCapQ : ℝ) (allRankUCapQ : ℝ) < 0 := by
  have hsound := KernelUpperCert.sound allRankKernelCert_valid
  have hneg : (allRankKernelCert.upper : ℝ) < 0 := by
    exact_mod_cast allRankKernelUpper_neg
  exact hsound.trans_lt hneg

theorem criticalTheta_le_allRankThetaUpper :
    criticalTheta ≤ (allRankThetaUpperQ : ℝ) := by
  rw [criticalTheta_eq]
  norm_num [allRankThetaUpperQ, betaLower]

end

end GDLowerBound.FourBlock
