import GDLowerBound.FourBlock.CompactMatchingCertificate

/-!
# Minimal data representation for generated matching certificates

Only six rounded endpoints are stored per kernel.  All remaining fields of
`KernelUpperCert` are reconstructed and checked by Lean.
-/

namespace GDLowerBound.FourBlock

structure KernelWitness where
  sqrtLower : ℚ
  sqrtUpper : ℚ
  deltaLower : ℚ
  deltaUpper : ℚ
  logTotalUpper : ℚ
  logFactorUpper : ℚ
deriving Repr, DecidableEq

def KernelWitness.toJet (w : KernelWitness) (u v : ℚ) : KernelJetCert :=
  let b := qEdgeParameter u v
  let factor := 2 / w.deltaLower - 1
  { value :=
    { u := u
      v := v
      sqrt :=
        { x := 4 * b ^ 2 + 1
          lower := w.sqrtLower
          upper := w.sqrtUpper }
      deltaLower := w.deltaLower
      deltaUpper := w.deltaUpper
      logTotal :=
        { y := (u + v) / 2
          n := 8
          lower := qLogLower ((u + v) / 2) 8
          upper := w.logTotalUpper }
      logFactor :=
        { y := factor
          n := 8
          lower := qLogLower factor 8
          upper := w.logFactorUpper }
      upper := w.logTotalUpper + w.logFactorUpper + w.deltaUpper - 1 } }

structure MatchingWitness where
  z : ℚ
  a₀ : ℚ
  r₀ : ℚ
  s₀ : ℚ
  w14 : KernelWitness
  w23 : KernelWitness
deriving Repr, DecidableEq

def MatchingWitness.toSupportCert (c : MatchingWitness) : MatchingSupportCert :=
  { z := c.z
    a₀ := c.a₀
    r₀ := c.r₀
    s₀ := c.s₀
    k14 := c.w14.toJet (8 * c.z * c.a₀) (8 * c.z * (1 - c.s₀))
    k23 := c.w23.toJet (8 * c.z * (c.r₀ - c.a₀)) (8 * c.z * (c.s₀ - c.r₀)) }

def MatchingWitness.valid (c : MatchingWitness) : Bool := c.toSupportCert.valid

def MatchingWitness.boxUpper (c : MatchingWitness)
    (alo ahi rlo rhi slo shi : ℚ) : ℚ :=
  c.toSupportCert.boxUpper alo ahi rlo rhi slo shi

theorem MatchingWitness.sound {c : MatchingWitness} (hc : c.valid = true)
    {alo ahi rlo rhi slo shi : ℚ} {a r s : ℝ}
    (ha : 0 < a) (h2 : 0 < r - a) (h3 : 0 < s - r) (h4 : 0 < 1 - s)
    (hal : (alo : ℝ) ≤ a) (hah : a ≤ (ahi : ℝ))
    (hrl : (rlo : ℝ) ≤ r) (hrh : r ≤ (rhi : ℝ))
    (hsl : (slo : ℝ) ≤ s) (hsh : s ≤ (shi : ℝ)) :
    fourBlockMatching (c.z : ℝ) a r s ≤ (c.boxUpper alo ahi rlo rhi slo shi : ℝ) := by
  exact MatchingSupportCert.sound hc ha h2 h3 h4 hal hah hrl hrh hsl hsh

end GDLowerBound.FourBlock
