import GDLowerBound.FourBlock.KernelCertificate

/-!
# A native-checked kernel certificate

This small certificate is deliberately hand-readable.  It exercises the full
Boolean-to-real soundness path used by the generated four-block certificate.
-/

namespace GDLowerBound.FourBlock

def unitKernelCert : KernelUpperCert where
  u := 1
  v := 1
  sqrt := {
    x := 5 / 4
    lower := 559 / 500
    upper := 1119 / 1000
  }
  deltaLower := 763 / 1000
  deltaUpper := 153 / 200
  logTotal := {
    y := 1
    n := 1
    lower := 0
    upper := 0
  }
  logFactor := {
    y := 1237 / 763
    n := 2
    lower := 0
    upper := 97 / 200
  }
  upper := 1 / 4

theorem unitKernelCert_valid : unitKernelCert.valid = true := by
  native_decide

theorem unitKernel_le_quarter : logKernel 1 1 ≤ (1 : ℝ) / 4 := by
  simpa [unitKernelCert] using KernelUpperCert.sound unitKernelCert_valid

end GDLowerBound.FourBlock
