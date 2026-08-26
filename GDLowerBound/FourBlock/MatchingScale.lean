import GDLowerBound.FourBlock.BlockGeometry
import GDLowerBound.FourBlock.Monotonicity

/-! # Monotonicity of four-block matching in its scale -/

namespace GDLowerBound.FourBlock

noncomputable section

theorem fourBlockMatching_mono_scale {z z' a r s : ℝ}
    (hz : 0 < z) (hzz : z ≤ z')
    (ha : 0 < a) (h2 : 0 < r - a) (h3 : 0 < s - r) (h4 : 0 < 1 - s) :
    fourBlockMatching z a r s ≤ fourBlockMatching z' a r s := by
  have hz' : 0 < z' := hz.trans_le hzz
  have h14 := logKernel_mono
    (u := 8 * z * a) (u' := 8 * z' * a)
    (v := 8 * z * (1 - s)) (v' := 8 * z' * (1 - s))
    (by positivity) (by positivity) (by gcongr) (by gcongr) (by positivity)
  have h23 := logKernel_mono
    (u := 8 * z * (r - a)) (u' := 8 * z' * (r - a))
    (v := 8 * z * (s - r)) (v' := 8 * z' * (s - r))
    (by positivity) (by positivity) (by gcongr) (by gcongr) (by positivity)
  unfold fourBlockMatching
  linarith

end

end GDLowerBound.FourBlock
