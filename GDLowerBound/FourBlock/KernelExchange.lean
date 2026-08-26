import GDLowerBound.FourBlock.KernelMonge
import Mathlib.Analysis.Calculus.Deriv.Shift

/-! # Outside-in exchange for the exact edge kernel -/

namespace GDLowerBound.FourBlock

noncomputable section

theorem kernelGradU_antitone_right {u : ℝ} (hu : 0 < u) :
    AntitoneOn (kernelGradU u) (Set.Ioi 0) := by
  apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ioi 0)
  · intro v hv
    exact (hasDerivAt_kernelGradU_right hu hv).continuousAt.continuousWithinAt
  · intro v hv
    exact (hasDerivAt_kernelGradU_right hu (interior_subset hv)).hasDerivWithinAt
  · intro v hv
    exact kernelCrossRaw_nonpos hu (interior_subset hv)

theorem hasDerivAt_pairLogKernelClosed_left {u v : ℝ}
    (hu : 0 < u) (hv : 0 < v) :
    HasDerivAt (fun x : ℝ ↦ pairLogKernelClosed (x, v))
      (kernelGradU u v) u := by
  have hline := hasDerivAt_pairLogKernelClosed_line
    (du := (1 : ℝ)) (dv := (0 : ℝ)) hu hv
  have hline' : HasDerivAt
      (fun t : ℝ ↦ pairLogKernelClosed (u + t * 1, v + t * 0))
      (kernelGradU u v * 1 + kernelGradV u v * 0) (-u + u) := by
    simpa only [neg_add_cancel] using hline
  have hcomp := hline'.comp_const_add (-u) u
  apply (hcomp.congr_of_eventuallyEq (by
    filter_upwards [] with x
    simp)).congr_deriv
  ring

theorem pairLogKernelClosed_exchange_cross_le
    {a b c d : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hc : 0 < c) (hcd : c ≤ d) :
    pairLogKernelClosed (a, c) + pairLogKernelClosed (b, d) ≤
      pairLogKernelClosed (a, d) + pairLogKernelClosed (b, c) := by
  have hb : 0 < b := ha.trans_le hab
  have hd : 0 < d := hc.trans_le hcd
  let g : ℝ → ℝ := fun x ↦
    pairLogKernelClosed (x, d) - pairLogKernelClosed (x, c)
  have hgAnti : AntitoneOn g (Set.Ioi 0) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ioi 0)
    · intro x hx
      exact ((hasDerivAt_pairLogKernelClosed_left hx hd).sub
        (hasDerivAt_pairLogKernelClosed_left hx hc)).continuousAt.continuousWithinAt
    · intro x hx
      have hx' : 0 < x := interior_subset hx
      exact ((hasDerivAt_pairLogKernelClosed_left hx' hd).sub
        (hasDerivAt_pairLogKernelClosed_left hx' hc)).hasDerivWithinAt
    · intro x hx
      have hx' : 0 < x := interior_subset hx
      exact sub_nonpos.mpr
        (kernelGradU_antitone_right hx' hc hd hcd)
  have h := hgAnti ha hb hab
  dsimp only [g] at h
  linarith

theorem pairLogKernelClosed_exchange_parallel_le
    {a b c d : ℝ} (ha : 0 < a) (hac : a ≤ c)
    (hb : 0 < b) (hbd : b ≤ d) :
    pairLogKernelClosed (a, b) + pairLogKernelClosed (c, d) ≤
      pairLogKernelClosed (a, d) + pairLogKernelClosed (b, c) := by
  have h := pairLogKernelClosed_exchange_cross_le ha hac hb hbd
  rw [show pairLogKernelClosed (c, b) = pairLogKernelClosed (b, c) by
    unfold pairLogKernelClosed pairEdgeParameter edgeParameter
    congr 2 <;> ring] at h
  exact h

theorem edgeKernel_exchange_cross_le
    {a b c d : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hc : 0 < c) (hcd : c ≤ d) :
    edgeKernel a c * edgeKernel b d ≤ edgeKernel a d * edgeKernel b c := by
  have hb : 0 < b := ha.trans_le hab
  have hd : 0 < d := hc.trans_le hcd
  have hlog := pairLogKernelClosed_exchange_cross_le ha hab hc hcd
  rw [pairLogKernelClosed_eq ⟨ha, hc⟩,
    pairLogKernelClosed_eq ⟨hb, hd⟩,
    pairLogKernelClosed_eq ⟨ha, hd⟩,
    pairLogKernelClosed_eq ⟨hb, hc⟩,
    logKernel_eq_log_edgeKernel ha.le hc.le (by linarith),
    logKernel_eq_log_edgeKernel hb.le hd.le (by linarith),
    logKernel_eq_log_edgeKernel ha.le hd.le (by linarith),
    logKernel_eq_log_edgeKernel hb.le hc.le (by linarith)] at hlog
  have hExp := Real.exp_le_exp.mpr hlog
  have hk {u v : ℝ} (hu : 0 < u) (hv : 0 < v) :
      0 < edgeKernel u v := by
    unfold edgeKernel
    positivity [envelope_pos (edgeParameter_nonneg hu.le hv.le)]
  simpa only [Real.exp_add, Real.exp_log (hk ha hc),
    Real.exp_log (hk hb hd), Real.exp_log (hk ha hd),
    Real.exp_log (hk hb hc)] using hExp

theorem edgeKernel_exchange_parallel_le
    {a b c d : ℝ} (ha : 0 < a) (hac : a ≤ c)
    (hb : 0 < b) (hbd : b ≤ d) :
    edgeKernel a b * edgeKernel c d ≤ edgeKernel a d * edgeKernel b c := by
  have h := edgeKernel_exchange_cross_le ha hac hb hbd
  rw [show edgeKernel c b = edgeKernel b c by
    unfold edgeKernel edgeParameter
    congr 1 <;> ring] at h
  exact h

end

end GDLowerBound.FourBlock
