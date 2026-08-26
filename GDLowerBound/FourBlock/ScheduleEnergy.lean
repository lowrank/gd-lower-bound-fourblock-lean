import GDLowerBound.FourBlock.BlockDilation
import GDLowerBound.FourBlock.EndpointConsequences
import GDLowerBound.FourBlock.LocalEnergyComposition

/-!
# Exact algebraic bridge from block defects to the certified local energy

The numerical certificate is phrased using `fourBlockLocalEnergy`, whereas
the global schedule argument naturally produces three endpoint costs and two
adjacent block defects.  The theorem below proves that these are exactly the
same quantity once the two block-ratio identities are inserted.
-/

namespace GDLowerBound.FourBlock

noncomputable section

/-- The local weighted quantity directly produced by a finite schedule. -/
def weightedScheduleEnergy
    (z₂ v₂ z₃ v₃ z₄ v₄ h₂ h₃ : ℝ) : ℝ :=
  endpointCost sideC2Q sideD2Q z₂ v₂ +
    endpointCost sideC3Q sideD3Q z₃ v₃ +
    endpointCost centralC4Q centralD4Q z₄ v₄ +
    (centralLambda2Q : ℝ) * h₂ +
    (centralLambda3Q : ℝ) * h₃

/-- Exact algebraic form of the manuscript's `Wsplit` identity.  This lemma
contains no approximation and no numerical certification. -/
theorem weightedScheduleEnergy_eq_localEnergy
    {z₂ v₂ z₃ v₃ z₄ v₄ h₂ h₃ r s : ℝ}
    (h23 : h₂ + h₃ =
      betaLower *
          (v₂ * (z₂ - criticalTheta) + v₃ * (z₃ - criticalTheta)) +
        Real.log (r / tailR20) + Real.log z₄ - Real.log z₂)
    (h3 : h₃ =
      betaLower * v₃ * (z₃ - criticalTheta) +
        Real.log (s * z₄ / tailR30) - Real.log z₃) :
    weightedScheduleEnergy z₂ v₂ z₃ v₃ z₄ v₄ h₂ h₃ =
      fourBlockLocalEnergy z₂ v₂ z₃ v₃
        (s * z₄ / tailR30) z₄ r +
        endpointCost centralC4Q centralD4Q z₄ v₄ -
        centralEndpoint z₄ := by
  have hlambda : (centralLambda3Q : ℝ) =
      (centralLambda2Q : ℝ) + (centralAlphaQ : ℝ) := by
    norm_num [centralLambda3Q, centralLambda2Q, centralAlphaQ]
  have hdecomp :
      (centralLambda2Q : ℝ) * h₂ +
          (centralLambda3Q : ℝ) * h₃ =
        (centralLambda2Q : ℝ) * (h₂ + h₃) +
          (centralAlphaQ : ℝ) * h₃ := by
    rw [hlambda]
    ring
  unfold weightedScheduleEnergy
  conv_lhs => rw [add_assoc]
  rw [hdecomp, h23, h3]
  unfold endpointCost fourBlockLocalEnergy q3Contribution sideQ2 sideG
  norm_num [sideLambda2Q, sideLambda3Q, centralLambda2Q,
    centralLambda3Q, centralAlphaQ, sideAlphaQ]
  ring

/-- If the fourth endpoint cost is bounded by `w`, then the certified local
energy is bounded by the same weighted schedule energy. -/
theorem localEnergy_le_weightedScheduleEnergy
    {z₂ v₂ z₃ v₃ z₄ v₄ h₂ h₃ r s : ℝ}
    (h23 : h₂ + h₃ =
      betaLower *
          (v₂ * (z₂ - criticalTheta) + v₃ * (z₃ - criticalTheta)) +
        Real.log (r / tailR20) + Real.log z₄ - Real.log z₂)
    (h3 : h₃ =
      betaLower * v₃ * (z₃ - criticalTheta) +
        Real.log (s * z₄ / tailR30) - Real.log z₃)
    (hz₄ : criticalTheta ≤ z₄) (hz₄hi : z₄ ≤ (119 / 250 : ℝ))
    (hv₄ : 0 ≤ v₄) :
    fourBlockLocalEnergy z₂ v₂ z₃ v₃
        (s * z₄ / tailR30) z₄ r ≤
      weightedScheduleEnergy z₂ v₂ z₃ v₃ z₄ v₄ h₂ h₃ := by
  have hend := centralEndpoint_le_endpointCost hz₄ hz₄hi hv₄
  rw [weightedScheduleEnergy_eq_localEnergy h23 h3]
  linarith

end

end GDLowerBound.FourBlock
