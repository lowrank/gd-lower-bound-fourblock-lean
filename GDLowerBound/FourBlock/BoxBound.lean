import GDLowerBound.FourBlock.Monotonicity

/-! # Monotonicity-only exact matching box bound -/

namespace GDLowerBound.FourBlock

noncomputable section

/-- Upper bound used on one `(z,r,s,a)` box.  Each of the four endpoint
weights is enlarged independently, which is valid by coordinate
monotonicity and requires no concavity assumption. -/
def monotoneMatchingUpper
    (zh rl rh sl sh al ah : ℝ) : ℝ :=
  (logKernel (8 * zh * ah) (8 * zh * (1 - sl)) +
    logKernel (8 * zh * (rh - al)) (8 * zh * (sh - rl))) / 2

theorem fourBlockMatching_le_monotoneUpper
    {z zh a al ah r rl rh s sl sh : ℝ}
    (hz : 0 < z) (hzz : z ≤ zh)
    (ha : 0 < a) (hal : al ≤ a) (hah : a ≤ ah)
    (hr : a < r) (hrl : rl ≤ r) (hrh : r ≤ rh)
    (hs : r < s) (hsl : sl ≤ s) (hsh : s ≤ sh)
    (hs1 : s < 1) :
    fourBlockMatching z a r s ≤
      monotoneMatchingUpper zh rl rh sl sh al ah := by
  have hzh : 0 < zh := hz.trans_le hzz
  have hnonneg : 0 ≤ z := hz.le
  have hzh0 : 0 ≤ zh := hzh.le
  have ha0 : 0 ≤ a := ha.le
  have hp20 : 0 ≤ r - a := sub_nonneg.mpr hr.le
  have hp30 : 0 ≤ s - r := sub_nonneg.mpr hs.le
  have hp40 : 0 ≤ 1 - s := sub_nonneg.mpr hs1.le
  have hah0 : 0 ≤ ah := ha0.trans hah
  have hrhal0 : 0 ≤ rh - al := by linarith
  have hshrl0 : 0 ≤ sh - rl := by linarith
  have hsl1 : 0 ≤ 1 - sl := by linarith
  have hu14 : 8 * z * a ≤ 8 * zh * ah := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hzz) ha0,
      mul_nonneg hzh0 (sub_nonneg.mpr hah)]
  have hv14 : 8 * z * (1 - s) ≤ 8 * zh * (1 - sl) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hzz) hp40,
      mul_nonneg hzh0 (by linarith : 0 ≤ s - sl)]
  have hu23 : 8 * z * (r - a) ≤ 8 * zh * (rh - al) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hzz) hp20,
      mul_nonneg hzh0 (by linarith : 0 ≤ (rh - al) - (r - a))]
  have hv23 : 8 * z * (s - r) ≤ 8 * zh * (sh - rl) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hzz) hp30,
      mul_nonneg hzh0 (by linarith : 0 ≤ (sh - rl) - (s - r))]
  have hsum14 : 0 < 8 * z * a + 8 * z * (1 - s) := by positivity
  have hsum23 : 0 < 8 * z * (r - a) + 8 * z * (s - r) := by
    have : 0 < s - a := by linarith
    nlinarith
  have hedge14 := logKernel_mono
    (mul_nonneg (mul_nonneg (by norm_num) hnonneg) ha0)
    (mul_nonneg (mul_nonneg (by norm_num) hnonneg) hp40)
    hu14 hv14 hsum14
  have hedge23 := logKernel_mono
    (mul_nonneg (mul_nonneg (by norm_num) hnonneg) hp20)
    (mul_nonneg (mul_nonneg (by norm_num) hnonneg) hp30)
    hu23 hv23 hsum23
  unfold fourBlockMatching monotoneMatchingUpper
  linarith

end

end GDLowerBound.FourBlock
