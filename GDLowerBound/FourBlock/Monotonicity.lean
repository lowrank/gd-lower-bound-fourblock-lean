import GDLowerBound.FourBlock.BlockGeometry

/-! # Coordinate monotonicity of the exact envelope kernel -/

namespace GDLowerBound.FourBlock

noncomputable section

def edgeParameter (u v : ℝ) : ℝ := u * v / (2 * (u + v))

def edgeKernel (u v : ℝ) : ℝ :=
  (u + v) / 2 * envelope (edgeParameter u v)

theorem edgeParameter_nonneg {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) :
    0 ≤ edgeParameter u v := by
  unfold edgeParameter
  positivity

theorem envelope_mono {b b' : ℝ} (hb : 0 ≤ b) (hbb : b ≤ b') :
    envelope b ≤ envelope b' := by
  have hb' : 0 ≤ b' := hb.trans hbb
  let x := maximizer b
  have hx : 0 < x := maximizer_pos hb
  rw [envelope_eq_maximizer_value hb]
  calc
    x * (1 + b * x) * Real.exp (1 - x) ≤
        x * (1 + b' * x) * Real.exp (1 - x) := by
      have hlin : 1 + b * x ≤ 1 + b' * x := by gcongr
      gcongr
    _ ≤ envelope b' := equalization_le_envelope hb' hx

theorem edgeParameter_mono_left {u u' v : ℝ}
    (hu : 0 ≤ u) (hv : 0 ≤ v) (huu : u ≤ u')
    (hsum : 0 < u + v) :
    edgeParameter u v ≤ edgeParameter u' v := by
  have hu' : 0 ≤ u' := hu.trans huu
  have hsum' : 0 < u' + v := by linarith
  unfold edgeParameter
  apply (div_le_div_iff₀ (by positivity : 0 < 2 * (u + v))
    (by positivity : 0 < 2 * (u' + v))).2
  have hdiff : 0 ≤ v ^ 2 * (u' - u) := by positivity
  nlinarith

theorem edgeParameter_mono_right {u v v' : ℝ}
    (hu : 0 ≤ u) (hv : 0 ≤ v) (hvv : v ≤ v')
    (hsum : 0 < u + v) :
    edgeParameter u v ≤ edgeParameter u v' := by
  rw [show edgeParameter u v = edgeParameter v u by unfold edgeParameter; ring]
  rw [show edgeParameter u v' = edgeParameter v' u by unfold edgeParameter; ring]
  exact edgeParameter_mono_left hv hu hvv (by linarith)

theorem edgeKernel_mono_left {u u' v : ℝ}
    (hu : 0 ≤ u) (hv : 0 ≤ v) (huu : u ≤ u')
    (hsum : 0 < u + v) :
    edgeKernel u v ≤ edgeKernel u' v := by
  have hu' : 0 ≤ u' := hu.trans huu
  have hsum' : 0 < u' + v := by linarith
  have hb := edgeParameter_nonneg hu hv
  have hb' := edgeParameter_nonneg hu' hv
  have hparam := edgeParameter_mono_left hu hv huu hsum
  have henv := envelope_mono hb hparam
  unfold edgeKernel
  exact mul_le_mul (by linarith) henv (envelope_pos hb).le
    (by positivity)

theorem edgeKernel_mono_right {u v v' : ℝ}
    (hu : 0 ≤ u) (hv : 0 ≤ v) (hvv : v ≤ v')
    (hsum : 0 < u + v) :
    edgeKernel u v ≤ edgeKernel u v' := by
  rw [show edgeKernel u v = edgeKernel v u by
    unfold edgeKernel edgeParameter; congr 1 <;> ring]
  rw [show edgeKernel u v' = edgeKernel v' u by
    unfold edgeKernel edgeParameter; congr 1 <;> ring]
  exact edgeKernel_mono_left hv hu hvv (by linarith)

theorem logKernel_eq_log_edgeKernel {u v : ℝ}
    (hu : 0 ≤ u) (hv : 0 ≤ v) (hsum : 0 < u + v) :
    logKernel u v = Real.log (edgeKernel u v) := by
  have hb := edgeParameter_nonneg hu hv
  have hleft : (u + v) / 2 ≠ 0 := by positivity
  have henv : envelope (edgeParameter u v) ≠ 0 :=
    (envelope_pos hb).ne'
  unfold logKernel edgeKernel
  change Real.log ((u + v) / 2) + Real.log (envelope (edgeParameter u v)) =
    Real.log ((u + v) / 2 * envelope (edgeParameter u v))
  exact (Real.log_mul hleft henv).symm

theorem logKernel_mono_left {u u' v : ℝ}
    (hu : 0 ≤ u) (hv : 0 ≤ v) (huu : u ≤ u')
    (hsum : 0 < u + v) :
    logKernel u v ≤ logKernel u' v := by
  have hu' : 0 ≤ u' := hu.trans huu
  have hsum' : 0 < u' + v := by linarith
  rw [logKernel_eq_log_edgeKernel hu hv hsum,
    logKernel_eq_log_edgeKernel hu' hv hsum']
  have hkpos : 0 < edgeKernel u v := by
    unfold edgeKernel
    positivity [envelope_pos (edgeParameter_nonneg hu hv)]
  exact Real.log_le_log hkpos (edgeKernel_mono_left hu hv huu hsum)

theorem logKernel_mono_right {u v v' : ℝ}
    (hu : 0 ≤ u) (hv : 0 ≤ v) (hvv : v ≤ v')
    (hsum : 0 < u + v) :
    logKernel u v ≤ logKernel u v' := by
  rw [logKernel_comm u v, logKernel_comm u v']
  exact logKernel_mono_left hv hu hvv (by linarith)

theorem logKernel_mono {u u' v v' : ℝ}
    (hu : 0 ≤ u) (hv : 0 ≤ v) (huu : u ≤ u') (hvv : v ≤ v')
    (hsum : 0 < u + v) :
    logKernel u v ≤ logKernel u' v' :=
  (logKernel_mono_left hu hv huu hsum).trans
    (logKernel_mono_right (hu.trans huu) hv hvv (by linarith))

end

end GDLowerBound.FourBlock
