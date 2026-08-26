import GDLowerBound.FourBlock.ExactMatchingScoreDichotomy

/-!
# Scalar kernel bound for a small two-block prefix

Concavity compresses the four-block outside-in matching to one kernel with
fixed total mass.  On the range `z ≤ 0.4760001`, `r ≤ 0.0500001`, this
kernel is far below the uniform matching-score cutoff.  The numerical value
at the northeast corner is checked by an exact-rational kernel certificate;
the extension to the full coupled rectangle is analytic.
-/

namespace GDLowerBound.FourBlock

noncomputable section

def smallPrefixZCapQ : ℚ := 4760001 / 10000000
def smallPrefixRCapQ : ℚ := 500001 / 10000000
def smallPrefixUCapQ : ℚ := 4 * smallPrefixZCapQ * smallPrefixRCapQ
def smallPrefixVCapQ : ℚ := 4 * smallPrefixZCapQ * (1 - smallPrefixRCapQ)

def smallPrefixKernelWitness : KernelWitness where
  sqrtLower := 1004081385163 / 1000000000000
  sqrtUpper := 251020346291 / 250000000000
  deltaLower := 2387179993 / 2500000000
  deltaUpper := 954871997201 / 1000000000000
  logTotalUpper := -24595017053 / 500000000000
  logFactorUpper := 1411208601 / 15625000000

def smallPrefixKernelCert : KernelJetCert :=
  smallPrefixKernelWitness.toJet smallPrefixUCapQ smallPrefixVCapQ

theorem smallPrefixKernelCert_valid : smallPrefixKernelCert.valid = true := by
  native_decide

theorem smallPrefixKernel_at_cap_lt :
    logKernel (smallPrefixUCapQ : ℝ) (smallPrefixVCapQ : ℝ) <
      matchingScoreCutoff := by
  have h := (KernelJetCert.sound smallPrefixKernelCert_valid).1
  have hrat : smallPrefixKernelCert.value.upper < -(1 / 2000000 : ℚ) := by
    native_decide
  have hratR : (smallPrefixKernelCert.value.upper : ℝ) <
      -(1 / 2000000 : ℝ) := by
    norm_num [smallPrefixKernelCert, smallPrefixKernelWitness,
      KernelWitness.toJet] at hrat ⊢
  exact h.trans_lt (by simpa only [matchingScoreCutoff] using hratR)

/-- Along the coupled pair `(4zr, 4z(1-r))`, the kernel is increasing in
both the total scale `z` and the smaller mass fraction `r` on `r ≤ 1/2`.
The proof uses the exact supporting plane at the certified corner. -/
theorem splitLogKernel_le_smallPrefixCap {z r : ℝ}
    (hz0 : 0 < z) (hz : z ≤ (smallPrefixZCapQ : ℝ))
    (hr0 : 0 < r) (hr : r ≤ (smallPrefixRCapQ : ℝ)) :
    logKernel (4 * z * r) (4 * z * (1 - r)) ≤
      logKernel (smallPrefixUCapQ : ℝ) (smallPrefixVCapQ : ℝ) := by
  let u := 4 * z * r
  let v := 4 * z * (1 - r)
  let u₀ : ℝ := smallPrefixUCapQ
  let v₀ : ℝ := smallPrefixVCapQ
  have hrcap : (smallPrefixRCapQ : ℝ) < 1 := by
    norm_num [smallPrefixRCapQ]
  have hrOne : r < 1 := hr.trans_lt hrcap
  have hu : 0 < u := by dsimp only [u]; positivity
  have hv : 0 < v := by dsimp only [v]; positivity
  have hu₀ : 0 < u₀ := by
    dsimp only [u₀, smallPrefixUCapQ]
    norm_num [smallPrefixZCapQ, smallPrefixRCapQ]
  have hv₀ : 0 < v₀ := by
    dsimp only [v₀, smallPrefixVCapQ]
    norm_num [smallPrefixZCapQ, smallPrefixRCapQ]
  have huv₀ : u₀ ≤ v₀ := by
    dsimp only [u₀, v₀, smallPrefixUCapQ, smallPrefixVCapQ]
    norm_num [smallPrefixZCapQ, smallPrefixRCapQ]
  let gu := kernelGradU u₀ v₀
  let gv := kernelGradV u₀ v₀
  have hb₀ : 0 ≤ edgeParameter u₀ v₀ :=
    edgeParameter_nonneg hu₀.le hv₀.le
  have hslope : 0 ≤ logEnvelopeSlope (edgeParameter u₀ v₀) :=
    logEnvelopeSlope_nonneg hb₀
  have hgv : 0 ≤ gv := by
    dsimp only [gv, kernelGradV]
    positivity
  have hdiff : 0 ≤ gu - gv := by
    have hid : gu - gv =
        logEnvelopeSlope (edgeParameter u₀ v₀) * (v₀ ^ 2 - u₀ ^ 2) /
          (2 * (u₀ + v₀) ^ 2) := by
      dsimp only [gu, gv, kernelGradU, kernelGradV]
      ring
    rw [hid]
    have hsq : 0 ≤ v₀ ^ 2 - u₀ ^ 2 := by nlinarith
    positivity
  have hrnonneg : 0 ≤ r := hr0.le
  have hrcap0 : 0 ≤ (smallPrefixRCapQ : ℝ) := by
    norm_num [smallPrefixRCapQ]
  have hzcap0 : 0 ≤ 4 * (smallPrefixZCapQ : ℝ) := by
    norm_num [smallPrefixZCapQ]
  have hB0 : 0 ≤ gv + (gu - gv) * r := by positivity
  have hBle : gv + (gu - gv) * r ≤
      gv + (gu - gv) * (smallPrefixRCapQ : ℝ) := by
    gcongr
  have hBcap0 : 0 ≤ gv + (gu - gv) * (smallPrefixRCapQ : ℝ) := by
    exact add_nonneg hgv (mul_nonneg hdiff hrcap0)
  have hmass :
      4 * z * (gv + (gu - gv) * r) ≤
        4 * (smallPrefixZCapQ : ℝ) *
          (gv + (gu - gv) * (smallPrefixRCapQ : ℝ)) := by
    exact mul_le_mul (by nlinarith) hBle hB0 hzcap0
  have hcurrent : gu * u + gv * v =
      4 * z * (gv + (gu - gv) * r) := by
    dsimp only [u, v]
    ring
  have href : gu * u₀ + gv * v₀ =
      4 * (smallPrefixZCapQ : ℝ) *
        (gv + (gu - gv) * (smallPrefixRCapQ : ℝ)) := by
    dsimp only [u₀, v₀, smallPrefixUCapQ, smallPrefixVCapQ]
    push_cast
    ring
  have hlinear : gu * (u - u₀) + gv * (v - v₀) ≤ 0 := by
    rw [show gu * (u - u₀) + gv * (v - v₀) =
      (gu * u + gv * v) - (gu * u₀ + gv * v₀) by ring,
      hcurrent, href]
    linarith
  have hsupport := pairLogKernelClosed_le_support hu₀ hv₀ hu hv
  rw [pairLogKernelClosed_eq ⟨hu, hv⟩,
    pairLogKernelClosed_eq ⟨hu₀, hv₀⟩] at hsupport
  dsimp only [gu, gv] at hlinear
  dsimp only [u, v, u₀, v₀] at hsupport ⊢
  linarith

end

end GDLowerBound.FourBlock
