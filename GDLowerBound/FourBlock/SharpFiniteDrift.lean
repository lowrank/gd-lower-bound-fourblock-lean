import GDLowerBound.FourBlock.CriticalLyapunov

/-!
# Defect-weighted finite critical drift

The original one-step theorem discarded the negative contraction term.  This
module retains the weaker, but sufficient, coefficient `betaLower`.  The
result is the finite-rank form of the sharpened rigidity drift and has an
explicit absolute remainder `25 / n^2`.
-/

namespace GDLowerBound.FourBlock

open GDLowerBound.RankAnalysis

noncomputable section

def sharpDriftConstant : ℝ := 25

private theorem criticalCoeff_mono {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) :
    lyapunovCoeff criticalP u ≤ lyapunovCoeff criticalP v := by
  have hv : 0 ≤ v := hu.trans huv
  have hdu : 0 < criticalTheta * (u + betaLower + 2) := by
    have : 0 < u + betaLower + 2 := by linarith [betaLower_pos]
    positivity [criticalTheta_pos]
  have hdv : 0 < criticalTheta * (v + betaLower + 2) := by
    have : 0 < v + betaLower + 2 := by linarith [betaLower_pos]
    positivity [criticalTheta_pos]
  unfold lyapunovCoeff
  rw [show lyapunovTheta criticalP = criticalTheta from rfl]
  simp only [criticalP]
  rw [show u + (1 + betaLower) + 1 = u + betaLower + 2 by ring,
    show v + (1 + betaLower) + 1 = v + betaLower + 2 by ring]
  change u / (criticalTheta * (u + betaLower + 2)) ≤
    v / (criticalTheta * (v + betaLower + 2))
  apply (div_le_div_iff₀ hdu hdv).2
  have hc : 0 < betaLower + 2 := by linarith [betaLower_pos]
  nlinarith [mul_nonneg (sub_nonneg.mpr huv) hc.le]

private theorem reset_lower
    {N u v : ℝ} (hN : 1 < N) (hu0 : 0 < u) (hv0 : 0 < v)
    (hsmall : u < N - 1)
    (hmass : v ≤ N * u / (N - 1 - u)) :
    (N - 1) * v / (N + v) ≤ u := by
  have hden : 0 < N - 1 - u := by linarith
  have hNv : 0 < N + v := by linarith
  have hcross : v * (N - 1 - u) ≤ N * u :=
    (le_div_iff₀ hden).mp hmass
  apply (div_le_iff₀ hNv).2
  nlinarith

private theorem criticalCoeff_finite_margin
    {N v : ℝ} (hN : 1 < N) (hv : 0 < v) :
    lyapunovCoeff criticalP v * lyapunovOmega N v +
        betaLower * v * lyapunovOmega N v / N ≤
      lyapunovCoeff criticalP ((N - 1) * v / (N + v)) := by
  have hN0 : 0 < N := by linarith
  have hNm1 : 0 < N - 1 := by linarith
  have hNv : 0 < N + v := by linarith
  have hb : 0 < betaLower := betaLower_pos
  have hbc : 0 < betaLower + v + 2 := by linarith
  have hlast : 0 <
      N * betaLower + N * v + 2 * N + betaLower * v + v := by positivity
  have hinner : 0 ≤
      N * betaLower * v ^ 2 * (N - 1) + N ^ 2 * v ^ 2 +
        N * betaLower ^ 2 + 2 * N * betaLower * v +
        4 * N * betaLower + 4 * N * v + 4 * N +
        betaLower ^ 2 * v + betaLower * v ^ 2 +
        3 * betaLower * v + v ^ 2 + 2 * v := by positivity
  have hid :
      lyapunovCoeff criticalP ((N - 1) * v / (N + v)) -
          (lyapunovCoeff criticalP v * lyapunovOmega N v +
            betaLower * v * lyapunovOmega N v / N) =
        betaLower * v * (N - 1) *
          (N * betaLower * v ^ 2 * (N - 1) + N ^ 2 * v ^ 2 +
            N * betaLower ^ 2 + 2 * N * betaLower * v +
            4 * N * betaLower + 4 * N * v + 4 * N +
            betaLower ^ 2 * v + betaLower * v ^ 2 +
            3 * betaLower * v + v ^ 2 + 2 * v) /
          (N ^ 2 * (N + v) * (betaLower + v + 2) *
            (N * betaLower + N * v + 2 * N + betaLower * v + v)) := by
    unfold lyapunovCoeff lyapunovOmega
    rw [show lyapunovTheta criticalP = criticalTheta from rfl]
    simp only [criticalP]
    ring_nf
    rw [criticalTheta_eq]
    field_simp [hN0.ne', hNv.ne', hbc.ne', hlast.ne', betaLower_pos.ne']
    ring
  rw [← sub_nonneg, hid]
  positivity

private theorem criticalCoeff_sharp
    {N u v : ℝ} (hN : 1 < N) (hu0 : 0 < u) (hv0 : 0 < v)
    (hsmall : u < N - 1)
    (hmass : v ≤ N * u / (N - 1 - u)) :
    lyapunovCoeff criticalP v * lyapunovOmega N v -
        lyapunovCoeff criticalP u +
        betaLower * v * lyapunovOmega N v / N ≤ 0 := by
  let u₀ := (N - 1) * v / (N + v)
  have hu₀ : 0 ≤ u₀ := by
    dsimp only [u₀]
    positivity
  have hu₀u : u₀ ≤ u := reset_lower hN hu0 hv0 hsmall hmass
  have hmono := criticalCoeff_mono hu₀ hu₀u
  have hfinite := criticalCoeff_finite_margin hN hv0
  dsimp only [u₀] at hmono
  linarith

private theorem critical_recursion_sub_theta
    {N v zPrev zNext : ℝ} (hN : 0 < N) (hv : 0 < v)
    (hzNext : zNext = lyapunovOmega N v * zPrev + 1 / (N * v)) :
    zNext - criticalTheta =
      lyapunovOmega N v * (zPrev - criticalTheta) +
        lyapunovDrift criticalP N v := by
  rw [hzNext]
  unfold lyapunovOmega lyapunovDrift
  rw [show lyapunovTheta criticalP = criticalTheta from rfl]
  have hNv : 0 < N + v := by positivity
  field_simp [hN.ne', hv.ne', hNv.ne']
  ring

private theorem critical_drift_identity
    {N v : ℝ} (hN : 0 < N) (hv : 0 < v) :
    lyapunovCoeff criticalP v * lyapunovDrift criticalP N v =
      (betaLower - v + lyapunovRemainder criticalP N v) / N := by
  have hNv : 0 < N + v := by positivity
  have hvp : 0 < v + criticalP + 1 := by
    unfold criticalP
    linarith [betaLower_pos]
  have hb2 : 0 < betaLower + 2 := by linarith [betaLower_pos]
  have hvb2 : 0 < v + betaLower + 2 := by linarith [betaLower_pos]
  unfold lyapunovCoeff lyapunovDrift lyapunovRemainder
  rw [show lyapunovTheta criticalP = criticalTheta from rfl]
  simp only [criticalP]
  rw [show v + (1 + betaLower) + 1 = v + betaLower + 2 by ring]
  change v / (criticalTheta * (v + betaLower + 2)) *
      (1 / (N * v) - criticalTheta * (N * (v + 2) - 1) / (N * (N + v))) =
    (betaLower - v + v * (1 + v * (v + 2)) /
      ((N + v) * (v + betaLower + 2))) / N
  rw [criticalTheta_eq]
  field_simp [hN.ne', hv.ne', hNv.ne', hvp.ne', hb2.ne', hvb2.ne',
    betaLower_pos.ne']
  ring

private theorem critical_remainder_le
    {N v : ℝ} (hN : 2 ≤ N) (hv0 : 0 < v)
    (hvB : v ≤ criticalP ^ 2 - 1) :
    lyapunovRemainder criticalP N v ≤ 24 / N := by
  have hN0 : 0 < N := by linarith
  have hv3 : v ≤ 3 := by
    unfold criticalP at hvB
    have hb : betaLower * (betaLower + 2) < 3 := by
      norm_num [betaLower]
    nlinarith
  have hv2 : v + 2 ≤ 5 := by linarith
  have hvpoly : v * (v + 2) ≤ 15 := by
    have ht := mul_le_mul hv3 hv2 (by linarith : 0 ≤ v + 2) (by norm_num : (0 : ℝ) ≤ 3)
    norm_num at ht ⊢
    exact ht
  have hpoly : 1 + v * (v + 2) ≤ 16 := by linarith
  have hnum : v * (1 + v * (v + 2)) ≤ 48 := by
    have ht := mul_le_mul hv3 hpoly (by positivity : 0 ≤ 1 + v * (v + 2)) (by norm_num : (0 : ℝ) ≤ 3)
    norm_num at ht ⊢
    exact ht
  have hp2 : 2 ≤ v + criticalP + 1 := by
    unfold criticalP
    linarith [betaLower_pos]
  have hden : 2 * N ≤ (N + v) * (v + criticalP + 1) := by
    nlinarith [mul_nonneg hv0.le (by linarith : 0 ≤ N + v),
      mul_nonneg (by linarith : 0 ≤ v + criticalP - 1) hN0.le]
  have hden0 : 0 < (N + v) * (v + criticalP + 1) := by positivity
  unfold lyapunovRemainder
  apply (div_le_iff₀ hden0).2
  calc
    v * (1 + v * (v + 2)) ≤ 48 := hnum
    _ = (24 / N) * (2 * N) := by
      field_simp [hN0.ne']
      norm_num
    _ ≤ (24 / N) * ((N + v) * (v + criticalP + 1)) := by
      exact mul_le_mul_of_nonneg_left hden (by positivity)

private theorem critical_drift_le {N v : ℝ} (hN : 2 ≤ N) (hv : 0 < v) :
    lyapunovDrift criticalP N v ≤ 1 / (N * v) := by
  have hN0 : 0 < N := by linarith
  have hNv : 0 < N + v := by positivity
  have hnum : 0 ≤ N * (v + 2) - 1 := by nlinarith
  have hterm : 0 ≤ criticalTheta * (N * (v + 2) - 1) /
      (N * (N + v)) := by
    exact div_nonneg (mul_nonneg criticalTheta_pos.le hnum)
      (mul_nonneg hN0.le hNv.le)
  unfold lyapunovDrift
  rw [show lyapunovTheta criticalP = criticalTheta from rfl]
  linarith

private theorem critical_error_le
    {N v : ℝ} (hN : 2 ≤ N) (hv0 : 0 < v)
    (hvB : v ≤ criticalP ^ 2 - 1) :
    lyapunovRemainder criticalP N v / N +
        betaLower * v * lyapunovDrift criticalP N v / N ≤
      sharpDriftConstant / N ^ 2 := by
  have hN0 : 0 < N := by linarith
  have hb1 : betaLower ≤ 1 := by norm_num [betaLower]
  have hrem := critical_remainder_le hN hv0 hvB
  have hremN := div_le_div_of_nonneg_right hrem hN0.le
  have hdrift := critical_drift_le hN hv0
  have hscaled := mul_le_mul_of_nonneg_left hdrift
    (mul_nonneg betaLower_pos.le hv0.le)
  have hscaledN := div_le_div_of_nonneg_right hscaled hN0.le
  have hvN : betaLower * v * (1 / (N * v)) / N = betaLower / N ^ 2 := by
    field_simp [hN0.ne', hv0.ne']
  have hremEq : (24 / N) / N = 24 / N ^ 2 := by ring
  rw [hvN] at hscaledN
  rw [hremEq] at hremN
  unfold sharpDriftConstant
  have hone : betaLower / N ^ 2 ≤ 1 / N ^ 2 := by
    exact div_le_div_of_nonneg_right hb1 (sq_nonneg N)
  calc
    lyapunovRemainder criticalP N v / N +
        betaLower * v * lyapunovDrift criticalP N v / N ≤
      24 / N ^ 2 + betaLower / N ^ 2 := add_le_add hremN hscaledN
    _ ≤ 24 / N ^ 2 + 1 / N ^ 2 := add_le_add le_rfl hone
    _ = 25 / N ^ 2 := by ring

/-- Exact one-step drift retaining the endpoint defect with coefficient
`betaLower`. -/
theorem criticalOneStepSharp
    {n : ℕ} (hn : 2 ≤ n) {u v zPrev zNext : ℝ}
    (hN : criticalP ^ 2 - 1 < (n : ℝ) - 1)
    (hu0 : 0 < u) (huB : u ≤ criticalP ^ 2 - 1)
    (hv0 : 0 < v) (hvB : v ≤ criticalP ^ 2 - 1)
    (hzPrev : criticalTheta ≤ zPrev)
    (hmass : v ≤ (n : ℝ) * u / ((n : ℝ) - 1 - u))
    (hzNext : zNext = lyapunovOmega (n : ℝ) v * zPrev +
      1 / ((n : ℝ) * v)) :
    criticalPotential v zNext - criticalPotential u zPrev ≤
      (betaLower - v - betaLower * v * (zNext - criticalTheta)) / n +
        sharpDriftConstant / (n : ℝ) ^ 2 := by
  let N : ℝ := n
  have hNR : 2 ≤ N := by
    dsimp only [N]
    exact_mod_cast hn
  have hN0 : 0 < N := by linarith
  have hsmall : u < N - 1 := by linarith
  have hcoeff := criticalCoeff_sharp (N := N) (u := u) (v := v)
    (by linarith) hu0 hv0 hsmall hmass
  have hshift := critical_recursion_sub_theta hN0 hv0 hzNext
  have hdrift := critical_drift_identity hN0 hv0
  have herr := critical_error_le hNR hv0 hvB
  have hX : 0 ≤ zPrev - criticalTheta := sub_nonneg.mpr hzPrev
  have hdecomp :
      criticalPotential v zNext - criticalPotential u zPrev =
        (lyapunovCoeff criticalP v * lyapunovOmega N v -
            lyapunovCoeff criticalP u) * (zPrev - criticalTheta) +
          lyapunovCoeff criticalP v * lyapunovDrift criticalP N v := by
    unfold criticalPotential lyapunovPotential
    rw [show lyapunovTheta criticalP = criticalTheta from rfl, hshift]
    ring
  have he : v * (zNext - criticalTheta) =
      v * lyapunovOmega N v * (zPrev - criticalTheta) +
        v * lyapunovDrift criticalP N v := by
    rw [hshift]
    ring
  have heBeta : betaLower * v * (zNext - criticalTheta) =
      betaLower * (v * lyapunovOmega N v * (zPrev - criticalTheta) +
        v * lyapunovDrift criticalP N v) := by
    calc
      betaLower * v * (zNext - criticalTheta) =
          betaLower * (v * (zNext - criticalTheta)) := by ring
      _ = betaLower * (v * lyapunovOmega N v * (zPrev - criticalTheta) +
          v * lyapunovDrift criticalP N v) := congrArg (fun x : ℝ ↦ betaLower * x) he
  rw [hdecomp, hdrift, heBeta]
  have hcoeffX := mul_nonpos_of_nonpos_of_nonneg hcoeff hX
  dsimp only [N] at herr hcoeffX ⊢
  ring_nf at hcoeffX herr ⊢
  linarith

end

end GDLowerBound.FourBlock
