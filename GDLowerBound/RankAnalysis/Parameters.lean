import GDLowerBound.Basic
import GDLowerBound.RankAnalysis.Lyapunov

namespace GDLowerBound.RankAnalysis

/-- The strict exponent threshold is exactly what makes the limiting
matching coefficient smaller than one. -/
theorem lyapunovTheta_threshold {p : ℝ} (hp : pStar < p) :
    2 * lyapunovTheta p + 2 * (lyapunovTheta p) ^ 2 < 1 := by
  have hpstar_pos : 0 < pStar := one_lt_pStar.trans' zero_lt_one
  have hp_pos : 0 < p := hpstar_pos.trans hp
  have hp_one : 1 < p := one_lt_pStar.trans hp
  have hsq : pStar ^ 2 < p ^ 2 := by
    have hprod : 0 < (p - pStar) * (p + pStar) :=
      mul_pos (sub_pos.mpr hp) (add_pos hp_pos hpstar_pos)
    nlinarith
  have hsqrt_nonneg : 0 ≤ Real.sqrt 3 := Real.sqrt_nonneg _
  have hsqrt_sq : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hd : 1 + Real.sqrt 3 < p ^ 2 - 1 := by
    rw [pStar_sq] at hsq
    linarith
  have hfactor1 : 0 < (p ^ 2 - 1) - (1 + Real.sqrt 3) := by linarith
  have hfactor2 : 0 < (p ^ 2 - 1) + (Real.sqrt 3 - 1) := by
    nlinarith
  have hpoly : 0 < (p ^ 2 - 1) ^ 2 - 2 * (p ^ 2 - 1) - 2 := by
    have hprod := mul_pos hfactor1 hfactor2
    nlinarith
  have hden : 0 < p ^ 2 - 1 := by nlinarith
  have hden_sq : 0 < (p ^ 2 - 1) ^ 2 := sq_pos_of_pos hden
  have hid :
      (2 * lyapunovTheta p + 2 * (lyapunovTheta p) ^ 2 - 1) *
          (p ^ 2 - 1) ^ 2 =
        -((p ^ 2 - 1) ^ 2 - 2 * (p ^ 2 - 1) - 2) := by
    unfold lyapunovTheta
    field_simp [hden.ne']
    ring
  have hmul :
      (2 * lyapunovTheta p + 2 * (lyapunovTheta p) ^ 2 - 1) *
          (p ^ 2 - 1) ^ 2 < 0 := by
    rw [hid]
    linarith
  have : 2 * lyapunovTheta p + 2 * (lyapunovTheta p) ^ 2 - 1 < 0 := by
    nlinarith
  linarith

theorem exists_rho {p : ℝ} (hp : pStar < p) :
    ∃ rho : ℝ,
      2 * lyapunovTheta p + 2 * (lyapunovTheta p) ^ 2 < rho ∧ rho < 1 := by
  let a := 2 * lyapunovTheta p + 2 * (lyapunovTheta p) ^ 2
  refine ⟨(a + 1) / 2, ?_, ?_⟩
  · have ha := lyapunovTheta_threshold hp
    dsimp only [a]
    linarith
  · have ha := lyapunovTheta_threshold hp
    dsimp only [a]
    linarith

theorem lyapunovTheta_pos_of_pStar_lt {p : ℝ} (hp : pStar < p) :
    0 < lyapunovTheta p :=
  lyapunovTheta_pos (one_lt_pStar.trans hp)

/-- The scalar quantity that bounds the geometric mean of the endpoint
matching product at rank `Q`. -/
noncomputable def cutoffMatchingArgument (p : ℝ) (Q : ℕ) : ℝ :=
  2 * lyapunovTheta p +
    (2 * lyapunovTheta p + 1) / ((Q : ℝ) - 1)

/-- The matching bound `x + x²/2` evaluated at the uniform cutoff
argument. -/
noncomputable def cutoffMatchingBound (p : ℝ) (Q : ℕ) : ℝ :=
  cutoffMatchingArgument p Q + cutoffMatchingArgument p Q ^ 2 / 2

/-- Once `rho` is strictly above the limiting matching coefficient, a
single integer cutoff makes the finite-rank coefficient smaller than
`rho` and also lies beyond the Lyapunov threshold. -/
theorem exists_cutoffRank {p rho : ℝ} (hp : pStar < p)
    (hrho :
      2 * lyapunovTheta p + 2 * (lyapunovTheta p) ^ 2 < rho) :
    ∃ Q : ℕ, 2 ≤ Q ∧ (lyapunovTheta p)⁻¹ < (Q : ℝ) ∧
      cutoffMatchingBound p Q < rho := by
  let theta := lyapunovTheta p
  let margin := rho - (2 * theta + 2 * theta ^ 2)
  let coeff := (3 : ℝ) / 2 + 2 * theta
  let delta := min 1 (margin / coeff)
  have htheta : 0 < theta := by
    exact lyapunovTheta_pos_of_pStar_lt hp
  have hmargin : 0 < margin := by
    dsimp only [margin, theta]
    linarith
  have hcoeff : 0 < coeff := by
    dsimp only [coeff]
    linarith
  have hdelta : 0 < delta := by
    dsimp only [delta]
    exact lt_min zero_lt_one (div_pos hmargin hcoeff)
  have hdelta_one : delta ≤ 1 := min_le_left _ _
  have hdelta_coeff : delta * coeff ≤ margin := by
    apply (le_div_iff₀ hcoeff).mp
    exact min_le_right _ _
  let cutoff : ℝ := max theta⁻¹ ((2 * theta + 1) / delta)
  obtain ⟨N, hN⟩ := exists_nat_gt cutoff
  let Q := N + 1
  have hNtheta : theta⁻¹ < (N : ℝ) := by
    exact (le_max_left _ _).trans_lt hN
  have hNposR : 0 < (N : ℝ) := (inv_pos.mpr htheta).trans hNtheta
  have hNpos : 0 < N := by exact_mod_cast hNposR
  have hNfraction : (2 * theta + 1) / delta < (N : ℝ) := by
    exact (le_max_right _ _).trans_lt hN
  have hnumerator : 0 < 2 * theta + 1 := by linarith
  let error := (2 * theta + 1) / (N : ℝ)
  have herror_pos : 0 < error := div_pos hnumerator hNposR
  have herror_delta : error < delta := by
    have hcross : 2 * theta + 1 < (N : ℝ) * delta := by
      have := (div_lt_iff₀ hdelta).mp hNfraction
      nlinarith
    dsimp only [error]
    exact (div_lt_iff₀ hNposR).mpr (by nlinarith)
  have herror_one : error ≤ 1 :=
    (le_of_lt herror_delta).trans hdelta_one
  have hremainder :
      error * (1 + 2 * theta) + error ^ 2 / 2 < margin := by
    have hsquare : error ^ 2 / 2 ≤ error / 2 := by
      nlinarith [herror_pos.le, herror_one]
    have hfirst :
        error * (1 + 2 * theta) + error ^ 2 / 2 ≤
          error * coeff := by
      dsimp only [coeff]
      nlinarith
    have hsecond : error * coeff < delta * coeff :=
      mul_lt_mul_of_pos_right herror_delta hcoeff
    exact hfirst.trans_lt (hsecond.trans_le hdelta_coeff)
  refine ⟨Q, ?_, ?_, ?_⟩
  · dsimp only [Q]
    omega
  · calc
      theta⁻¹ < (N : ℝ) := hNtheta
      _ < (Q : ℕ) := by
        dsimp only [Q]
        norm_num
  · have hQden : (Q : ℝ) - 1 = (N : ℝ) := by
      dsimp only [Q]
      norm_num
    change cutoffMatchingBound p Q < rho
    rw [cutoffMatchingBound, cutoffMatchingArgument, hQden]
    change (2 * theta + error) + (2 * theta + error) ^ 2 / 2 < rho
    dsimp only [margin] at hremainder
    nlinarith

/-- Parameter package used by the normalized rank argument. -/
theorem exists_cutoffParameters {p : ℝ} (hp : pStar < p) :
    ∃ rho : ℝ, ∃ Q : ℕ,
      2 * lyapunovTheta p + 2 * (lyapunovTheta p) ^ 2 < rho ∧
      rho < 1 ∧ 2 ≤ Q ∧ (lyapunovTheta p)⁻¹ < (Q : ℝ) ∧
      cutoffMatchingBound p Q < rho := by
  obtain ⟨rho, hrho, hrho_one⟩ := exists_rho hp
  obtain ⟨Q, hQtwo, hQtheta, hQmatch⟩ := exists_cutoffRank hp hrho
  exact ⟨rho, Q, hrho, hrho_one, hQtwo, hQtheta, hQmatch⟩

end GDLowerBound.RankAnalysis
