import GDLowerBound.FourBlock.EnvelopeCalculus
import GDLowerBound.FourBlock.Monotonicity

/-!
# Concavity of the exact logarithmic edge kernel

The proof factors the kernel into a logarithm of the total endpoint mass and
the concave increasing logarithmic envelope composed with the harmonic edge
parameter.  The latter parameter has an exact rational Jensen remainder.
-/

namespace GDLowerBound.FourBlock

noncomputable section

def positiveQuadrant : Set (ℝ × ℝ) := {p | 0 < p.1 ∧ 0 < p.2}

theorem positiveQuadrant_convex : Convex ℝ positiveQuadrant := by
  rw [show positiveQuadrant = Set.Ioi (0 : ℝ) ×ˢ Set.Ioi (0 : ℝ) by
    ext p
    simp [positiveQuadrant]]
  exact (convex_Ioi (0 : ℝ)).prod (convex_Ioi (0 : ℝ))

def pairEdgeParameter (p : ℝ × ℝ) : ℝ := edgeParameter p.1 p.2

def pairLogKernelClosed (p : ℝ × ℝ) : ℝ :=
  Real.log ((p.1 + p.2) / 2) + logEnvelope (pairEdgeParameter p)

theorem pairEdgeParameter_nonneg {p : ℝ × ℝ}
    (hp : p ∈ positiveQuadrant) : 0 ≤ pairEdgeParameter p :=
  edgeParameter_nonneg hp.1.le hp.2.le

theorem pairLogKernelClosed_eq {p : ℝ × ℝ}
    (hp : p ∈ positiveQuadrant) :
    pairLogKernelClosed p = logKernel p.1 p.2 := by
  unfold pairLogKernelClosed pairEdgeParameter logKernel
  rw [logEnvelope_eq_log_envelope (edgeParameter_nonneg hp.1.le hp.2.le)]
  rfl

theorem pairEdgeParameter_concave :
    ConcaveOn ℝ positiveQuadrant pairEdgeParameter := by
  refine ⟨positiveQuadrant_convex, ?_⟩
  rintro ⟨u₁, v₁⟩ ⟨hu₁, hv₁⟩ ⟨u₂, v₂⟩ ⟨hu₂, hv₂⟩ a b ha hb hab
  change a * edgeParameter u₁ v₁ + b * edgeParameter u₂ v₂ ≤
    edgeParameter (a * u₁ + b * u₂) (a * v₁ + b * v₂)
  have hbEq : b = 1 - a := by linarith
  subst b
  have ha1 : a ≤ 1 := by linarith
  have hs₁ : 0 < u₁ + v₁ := by linarith
  have hs₂ : 0 < u₂ + v₂ := by linarith
  have hsmix : 0 < a * u₁ + (1 - a) * u₂ +
      (a * v₁ + (1 - a) * v₂) := by
    have h₁ : 0 ≤ a * (u₁ + v₁) := mul_nonneg ha (le_of_lt hs₁)
    have h₂ : 0 ≤ (1 - a) * (u₂ + v₂) :=
      mul_nonneg (sub_nonneg.mpr ha1) (le_of_lt hs₂)
    have hpos : 0 < a * (u₁ + v₁) + (1 - a) * (u₂ + v₂) := by
      rcases ha.eq_or_lt with rfl | ha0
      · simpa using hs₂
      · exact add_pos_of_pos_of_nonneg (mul_pos ha0 hs₁) h₂
    linarith
  have hid :
      edgeParameter (a * u₁ + (1 - a) * u₂)
          (a * v₁ + (1 - a) * v₂) -
        (a * edgeParameter u₁ v₁ +
          (1 - a) * edgeParameter u₂ v₂) =
      a * (1 - a) * (u₁ * v₂ - u₂ * v₁) ^ 2 /
        (2 * (u₁ + v₁) * (u₂ + v₂) *
          (a * u₁ + (1 - a) * u₂ + (a * v₁ + (1 - a) * v₂))) := by
    unfold edgeParameter
    field_simp [hs₁.ne', hs₂.ne', hsmix.ne']
    ring
  rw [← sub_nonneg, hid]
  positivity

theorem logHalfSum_concave : ConcaveOn ℝ positiveQuadrant
    (fun p : ℝ × ℝ ↦ Real.log ((p.1 + p.2) / 2)) := by
  refine ⟨positiveQuadrant_convex, ?_⟩
  intro x hx y hy a b ha hb hab
  change 0 < x.1 ∧ 0 < x.2 at hx
  change 0 < y.1 ∧ 0 < y.2 at hy
  have hxpos : 0 < (x.1 + x.2) / 2 := by linarith [hx.1, hx.2]
  have hypos : 0 < (y.1 + y.2) / 2 := by linarith [hy.1, hy.2]
  have hlog := strictConcaveOn_log_Ioi.concaveOn.2 hxpos hypos ha hb hab
  change a * Real.log ((x.1 + x.2) / 2) +
      b * Real.log ((y.1 + y.2) / 2) ≤
    Real.log (((a • x + b • y).1 + (a • x + b • y).2) / 2)
  have harg :
      ((a • x + b • y).1 + (a • x + b • y).2) / 2 =
        a * ((x.1 + x.2) / 2) + b * ((y.1 + y.2) / 2) := by
    simp only [Prod.smul_fst, Prod.smul_snd, Prod.fst_add, Prod.snd_add, smul_eq_mul]
    ring
  rw [harg]
  simpa only [smul_eq_mul] using hlog

theorem logEnvelope_comp_edgeParameter_concave :
    ConcaveOn ℝ positiveQuadrant (logEnvelope ∘ pairEdgeParameter) := by
  refine ⟨positiveQuadrant_convex, ?_⟩
  intro x hx y hy a b ha hb hab
  have hbx := pairEdgeParameter_nonneg hx
  have hby := pairEdgeParameter_nonneg hy
  have hconc := logEnvelope_concave.2 hbx hby ha hb hab
  have hparam := pairEdgeParameter_concave.2 hx hy ha hb hab
  have hweighted : 0 ≤ a * pairEdgeParameter x + b * pairEdgeParameter y := by
    positivity
  have hmono := logEnvelope_monotoneOn hweighted
    (pairEdgeParameter_nonneg (positiveQuadrant_convex hx hy ha hb hab)) hparam
  exact hconc.trans hmono

theorem pairLogKernelClosed_concave :
    ConcaveOn ℝ positiveQuadrant pairLogKernelClosed := by
  unfold pairLogKernelClosed
  change ConcaveOn ℝ positiveQuadrant
    ((fun p : ℝ × ℝ ↦ Real.log ((p.1 + p.2) / 2)) +
      (logEnvelope ∘ pairEdgeParameter))
  exact logHalfSum_concave.add logEnvelope_comp_edgeParameter_concave

end

end GDLowerBound.FourBlock
