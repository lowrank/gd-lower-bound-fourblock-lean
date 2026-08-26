import GDLowerBound.FourBlock.Constants
import GDLowerBound.RankAnalysis.Lyapunov

/-!
# Exact rational critical Lyapunov parameter

Choosing the rational `betaLower` first and defining the state threshold by
`1 / (beta * (beta + 2))` preserves the critical identity exactly.  The
resulting threshold lies inside the directed interval used by the numerical
certificates, so Ma--Chen's already formalized finite one-step theorem can be
reused without an asymptotic Taylor argument.
-/

namespace GDLowerBound.FourBlock

open GDLowerBound.RankAnalysis

noncomputable section

def criticalP : ℝ := 1 + betaLower

def criticalTheta : ℝ := lyapunovTheta criticalP

theorem criticalP_sub_one : criticalP - 1 = betaLower := by
  unfold criticalP
  ring

theorem one_lt_criticalP : 1 < criticalP := by
  unfold criticalP
  linarith [betaLower_pos]

theorem criticalTheta_eq :
    criticalTheta = (betaLower * (betaLower + 2))⁻¹ := by
  unfold criticalTheta criticalP lyapunovTheta
  congr 1
  ring

theorem critical_identity :
    criticalTheta * betaLower * (betaLower + 2) = 1 := by
  rw [criticalTheta_eq]
  have hne : betaLower * (betaLower + 2) ≠ 0 := by positivity [betaLower_pos]
  simpa only [div_eq_mul_inv, mul_assoc] using inv_mul_cancel₀ hne

 theorem criticalTheta_pos : 0 < criticalTheta := by
  rw [criticalTheta_eq]
  positivity [betaLower_pos]

theorem thetaLower_lt_criticalTheta : thetaLower < criticalTheta := by
  rw [criticalTheta_eq]
  norm_num [thetaLower, betaLower]

theorem criticalTheta_lt_thetaUpper : criticalTheta < thetaUpper := by
  rw [criticalTheta_eq]
  norm_num [thetaUpper, betaLower]

/-- The potential appearing in the four-block note is definitionally the
existing Ma--Chen Lyapunov potential at the exact rational critical point. -/
def criticalPotential (v z : ℝ) : ℝ :=
  lyapunovPotential criticalP v z

theorem criticalPotential_formula (v z : ℝ) :
    criticalPotential v z =
      v / (criticalTheta * (v + betaLower + 2)) *
        (z - criticalTheta) := by
  unfold criticalPotential lyapunovPotential lyapunovCoeff criticalTheta criticalP
  ring

/-- Finite one-step drift with the explicit `C/n^2` remainder. -/
theorem criticalOneStep
    {n : ℕ} (hn : 2 ≤ n)
    {u v zPrev zNext : ℝ}
    (hN : criticalP ^ 2 - 1 < (n : ℝ) - 1)
    (hu0 : 0 < u) (huB : u ≤ criticalP ^ 2 - 1)
    (hv0 : 0 < v) (hvB : v ≤ criticalP ^ 2 - 1)
    (hzPrev : criticalTheta ≤ zPrev)
    (hmass : v ≤ (n : ℝ) * u / ((n : ℝ) - 1 - u))
    (hzNext :
      zNext = lyapunovOmega (n : ℝ) v * zPrev +
        1 / ((n : ℝ) * v)) :
    criticalPotential v zNext - criticalPotential u zPrev ≤
      (betaLower - v) / (n : ℝ) +
        oneStepLyapunovConstant criticalP / (n : ℝ) ^ 2 := by
  simpa only [criticalPotential, criticalP_sub_one] using
    oneStepLyapunov one_lt_criticalP hn hN hu0 huB hv0 hvB hzPrev hmass hzNext

end

end GDLowerBound.FourBlock
