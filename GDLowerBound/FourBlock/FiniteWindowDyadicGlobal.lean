import GDLowerBound.FourBlock.FiniteWindowDyadicScan
import GDLowerBound.FourBlock.ExactEnvelopeNormalized

/-!
# Terminating global dyadic scan

Each functional branch moves to a strictly larger rank; each complementary
branch already gives the target mass bound.  Well-founded recursion on the
remaining rank gap therefore converts any positive functional contribution
at a cutoff rank into a normalized floor with exponent `massExponent`.
-/

namespace GDLowerBound.FourBlock

open GDLowerBound.Schedule GDLowerBound.RankAnalysis

noncomputable section

private theorem scale_functional_by_mass_bound
    {a C B R D F : ℝ}
    (ha : 0 ≤ a) (hC : 0 < C) (hB : 0 < B) (hR : 0 < R)
    (hD : 0 < D) (hmass : D ≤ C * B * R)
    (hfunctional : a / D ≤ F) :
    (a / C) / (B * R) ≤ F := by
  have hCBR : 0 < C * B * R := by positivity
  have hscaled : a / (C * B * R) ≤ a / D :=
    div_le_div_of_nonneg_left ha hD hmass
  have hreassoc : (a / C) / (B * R) = a / (C * B * R) := by
    field_simp [hC.ne', hB.ne', hR.ne']
  exact (hreassoc ▸ hscaled).trans hfunctional

/-- A terminating scan from any rank carrying a positive functional
coefficient no larger than `1/4`. -/
theorem dyadicScan_normalizedFunctional
    {R₀ M₀ : ℕ} (huniform : UniformFiniteWindowDyadicDichotomy R₀ M₀)
    {T Q k : ℕ} {h : StepSchedule T}
    (hQ2 : 2 ≤ Q) (hQtheta : criticalTheta⁻¹ < (Q : ℝ))
    (hh : IsNonnegativeSchedule h) (hQk : Q ≤ k)
    (hkr : k ≤ longCount h)
    (hcut : CutoffConditions criticalP h (k + 1) (longCount h))
    {a : ℝ} (ha : 0 < a) (haQuarter : a ≤ (4 : ℝ)⁻¹)
    (hfunctional : a / unresolvedMass h k ≤ lowerBoundFunctional h) :
    (a / dyadicScanMassConstant R₀ M₀) /
        (cappedMass h *
          (((longCount h : ℝ) + 1) ^ massExponent)) ≤
      lowerBoundFunctional h := by
  rcases dyadicScanStep huniform hQ2 hQtheta hh hQk hkr hcut with
    hmass | hnext
  · have hM₀large : 2000 ≤ M₀ := huniform.2.1
    have hM₀one : 1 ≤ M₀ := by omega
    have hC := dyadicScanMassConstant_pos
      (R₀ := R₀) (M₀ := M₀) hM₀one
    exact scale_functional_by_mass_bound ha.le hC (cappedMass_pos hh)
      (Real.rpow_pos_of_pos (by positivity) _) (unresolvedMass_pos hh k)
      hmass hfunctional
  · obtain ⟨q, hkq, hqr, hfunq⟩ := hnext
    have hQq : Q ≤ q := hQk.trans hkq.le
    have hcutq :
        CutoffConditions criticalP h (q + 1) (longCount h) := by
      intro s hs
      have hsIcc := Finset.mem_Icc.mp hs
      exact hcut s (Finset.mem_Icc.mpr ⟨by omega, hsIcc.2⟩)
    have hDq : 0 < unresolvedMass h q := unresolvedMass_pos hh q
    have hcoef :
        a / unresolvedMass h q ≤
          (4 : ℝ)⁻¹ / unresolvedMass h q :=
      div_le_div_of_nonneg_right haQuarter hDq.le
    exact dyadicScan_normalizedFunctional huniform hQ2 hQtheta hh hQq hqr
      hcutq ha haQuarter (hcoef.trans hfunq.le)
termination_by longCount h - k
decreasing_by omega

end

end GDLowerBound.FourBlock
