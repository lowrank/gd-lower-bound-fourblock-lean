import Mathlib

namespace GDLowerBound
namespace RankAnalysis

noncomputable section

/-- The parameter denoted by `\vartheta` in the manuscript. -/
def lyapunovTheta (p : ℝ) : ℝ := (p ^ 2 - 1)⁻¹

/-- The coefficient of the one-step Lyapunov potential. -/
def lyapunovCoeff (p v : ℝ) : ℝ :=
  v / (lyapunovTheta p * (v + p + 1))

/-- The scalar Lyapunov potential used in the rank propagation argument. -/
def lyapunovPotential (p v z : ℝ) : ℝ :=
  lyapunovCoeff p v * (z - lyapunovTheta p)

/-- The affine contraction coefficient in the adjacent-rank recursion. -/
def lyapunovOmega (N v : ℝ) : ℝ :=
  (N - 1) ^ 2 / (N * (N + v))

/-- The non-affine part left after subtracting `lyapunovTheta p` from the
adjacent-rank recursion. -/
def lyapunovDrift (p N v : ℝ) : ℝ :=
  1 / (N * v) -
    lyapunovTheta p * (N * (v + 2) - 1) / (N * (N + v))

/-- The positive remainder in the exact one-step drift identity. -/
def lyapunovRemainder (p N v : ℝ) : ℝ :=
  v * (1 + v * (v + 2)) / ((N + v) * (v + p + 1))

/-- An explicit admissible value of the manuscript's constant `C_p`. -/
def oneStepLyapunovConstant (p : ℝ) : ℝ :=
  max 1
    ((p ^ 2 - 1) *
      (1 + (p ^ 2 - 1) * ((p ^ 2 - 1) + 2)) / (p + 1))

private lemma exponentSquareSubOne_pos {p : ℝ} (hp : 1 < p) :
    0 < p ^ 2 - 1 := by
  nlinarith [sq_nonneg (p - 1)]

lemma lyapunovTheta_pos {p : ℝ} (hp : 1 < p) :
    0 < lyapunovTheta p := by
  exact inv_pos.mpr (exponentSquareSubOne_pos hp)

lemma lyapunovTheta_inv (p : ℝ) :
    (lyapunovTheta p)⁻¹ = p ^ 2 - 1 := by
  simp [lyapunovTheta]

lemma lyapunovTheta_inv_factor (p : ℝ) :
    (lyapunovTheta p)⁻¹ = (p - 1) * (p + 1) := by
  rw [lyapunovTheta_inv]
  ring

lemma oneStepLyapunovConstant_ge_one (p : ℝ) :
    1 ≤ oneStepLyapunovConstant p := by
  exact le_max_left _ _

private lemma reset_lower_bound
    {p N u v : ℝ}
    (hp : 1 < p)
    (hN : p ^ 2 - 1 < N - 1)
    (huB : u ≤ p ^ 2 - 1)
    (hv0 : 0 < v)
    (hmass : v ≤ N * u / (N - 1 - u)) :
    (N - 1) * v / (N + v) ≤ u := by
  have hb0 : 0 < p ^ 2 - 1 := exponentSquareSubOne_pos hp
  have hden0 : 0 < N - 1 - u := by linarith
  have hN0 : 0 < N := by linarith
  have hNv0 : 0 < N + v := by linarith
  have hcross : v * (N - 1 - u) ≤ N * u :=
    (le_div_iff₀ hden0).mp hmass
  apply (div_le_iff₀ hNv0).2
  nlinarith

private lemma omega_bounds
    {p N v : ℝ}
    (hp : 1 < p)
    (hN : p ^ 2 - 1 < N - 1)
    (hv0 : 0 < v) :
    0 ≤ lyapunovOmega N v ∧ lyapunovOmega N v ≤ 1 := by
  have hb0 : 0 < p ^ 2 - 1 := exponentSquareSubOne_pos hp
  have hNm10 : 0 < N - 1 := by linarith
  have hN0 : 0 < N := by linarith
  have hNv0 : 0 < N + v := by linarith
  constructor
  · unfold lyapunovOmega
    positivity
  · unfold lyapunovOmega
    apply (div_le_iff₀ (mul_pos hN0 hNv0)).2
    have hNv : 0 < N * v := mul_pos hN0 hv0
    nlinarith

private lemma omega_mul_le
    {p N u v : ℝ}
    (hp : 1 < p)
    (hN : p ^ 2 - 1 < N - 1)
    (hu0 : 0 < u)
    (huB : u ≤ p ^ 2 - 1)
    (hv0 : 0 < v)
    (hmass : v ≤ N * u / (N - 1 - u)) :
    lyapunovOmega N v * v ≤ u := by
  have hb0 : 0 < p ^ 2 - 1 := exponentSquareSubOne_pos hp
  have hNm10 : 0 < N - 1 := by linarith
  have hN0 : 0 < N := by linarith
  have hNv0 : 0 < N + v := by linarith
  have hreset := reset_lower_bound hp hN huB hv0 hmass
  have hcross : (N - 1) * v ≤ u * (N + v) :=
    (div_le_iff₀ hNv0).mp hreset
  have hfirst := mul_le_mul_of_nonneg_left hcross (le_of_lt hNm10)
  have hsecond :
      (N - 1) * (u * (N + v)) ≤ N * (u * (N + v)) := by
    exact mul_le_mul_of_nonneg_right (by linarith)
      (mul_nonneg (le_of_lt hu0) (le_of_lt hNv0))
  have hnum :
      (N - 1) ^ 2 * v ≤ u * (N * (N + v)) := by
    calc
      (N - 1) ^ 2 * v = (N - 1) * ((N - 1) * v) := by ring
      _ ≤ (N - 1) * (u * (N + v)) := hfirst
      _ ≤ N * (u * (N + v)) := hsecond
      _ = u * (N * (N + v)) := by ring
  rw [lyapunovOmega]
  calc
    ((N - 1) ^ 2 / (N * (N + v))) * v =
        ((N - 1) ^ 2 * v) / (N * (N + v)) := by ring
    _ ≤ u := (div_le_iff₀ (mul_pos hN0 hNv0)).2 hnum

private lemma coefficient_compare
    {p N u v : ℝ}
    (hp : 1 < p)
    (hN : p ^ 2 - 1 < N - 1)
    (hu0 : 0 < u)
    (huB : u ≤ p ^ 2 - 1)
    (hv0 : 0 < v)
    (hmass : v ≤ N * u / (N - 1 - u)) :
    lyapunovCoeff p v * lyapunovOmega N v ≤ lyapunovCoeff p u := by
  have htheta0 : 0 < lyapunovTheta p := lyapunovTheta_pos hp
  have hp10 : 0 < p + 1 := by linarith
  have huDen0 : 0 < u + p + 1 := by linarith
  have hvDen0 : 0 < v + p + 1 := by linarith
  have homega := omega_bounds hp hN hv0
  have homegaV := omega_mul_le hp hN hu0 huB hv0 hmass
  have hterm1 :
      (lyapunovOmega N v * v) * u ≤ v * u := by
    have h := mul_le_mul_of_nonneg_right homega.2
      (mul_nonneg (le_of_lt hv0) (le_of_lt hu0))
    simpa [mul_assoc, mul_left_comm, mul_comm] using h
  have hterm2 :
      (lyapunovOmega N v * v) * (p + 1) ≤ u * (p + 1) :=
    mul_le_mul_of_nonneg_right homegaV (le_of_lt hp10)
  have hnumerator :
      (lyapunovOmega N v * v) * (u + p + 1) ≤
        u * (v + p + 1) := by
    calc
      (lyapunovOmega N v * v) * (u + p + 1) =
          (lyapunovOmega N v * v) * u +
            (lyapunovOmega N v * v) * (p + 1) := by ring
      _ ≤ v * u + u * (p + 1) := add_le_add hterm1 hterm2
      _ = u * (v + p + 1) := by ring
  rw [lyapunovCoeff]
  rw [show v / (lyapunovTheta p * (v + p + 1)) * lyapunovOmega N v =
      (lyapunovOmega N v * v) /
        (lyapunovTheta p * (v + p + 1)) by ring]
  apply (div_le_div_iff₀
    (mul_pos htheta0 hvDen0) (mul_pos htheta0 huDen0)).2
  have hscaled := mul_le_mul_of_nonneg_left hnumerator (le_of_lt htheta0)
  convert hscaled using 1 <;> ring

private lemma recursion_sub_theta
    {p N v zPrev zNext : ℝ}
    (hp : 1 < p)
    (hN : p ^ 2 - 1 < N - 1)
    (hv0 : 0 < v)
    (hzNext :
      zNext = lyapunovOmega N v * zPrev + 1 / (N * v)) :
    zNext - lyapunovTheta p =
      lyapunovOmega N v * (zPrev - lyapunovTheta p) +
        lyapunovDrift p N v := by
  have hb0 : 0 < p ^ 2 - 1 := exponentSquareSubOne_pos hp
  have hN0 : 0 < N := by linarith
  have hNv0 : 0 < N + v := by linarith
  rw [hzNext]
  unfold lyapunovOmega lyapunovDrift
  field_simp [ne_of_gt hN0, ne_of_gt hv0, ne_of_gt hNv0]
  ring

private lemma drift_identity
    {p N v : ℝ}
    (hp : 1 < p)
    (hN : p ^ 2 - 1 < N - 1)
    (hv0 : 0 < v) :
    lyapunovCoeff p v * lyapunovDrift p N v =
      (p - 1 - v + lyapunovRemainder p N v) / N := by
  have hb0 : 0 < p ^ 2 - 1 := exponentSquareSubOne_pos hp
  have hN0 : 0 < N := by linarith
  have hNv0 : 0 < N + v := by linarith
  have hvp0 : 0 < v + p + 1 := by linarith
  unfold lyapunovCoeff lyapunovDrift lyapunovRemainder lyapunovTheta
  field_simp [ne_of_gt hb0, ne_of_gt hN0, ne_of_gt hv0,
    ne_of_gt hNv0, ne_of_gt hvp0]
  ring

private lemma remainder_bound
    {p N v : ℝ}
    (hp : 1 < p)
    (hN : p ^ 2 - 1 < N - 1)
    (hv0 : 0 < v)
    (hvB : v ≤ p ^ 2 - 1) :
    lyapunovRemainder p N v ≤ oneStepLyapunovConstant p / N := by
  let b : ℝ := p ^ 2 - 1
  have hb0 : 0 < b := by
    dsimp [b]
    exact exponentSquareSubOne_pos hp
  have hN0 : 0 < N := by
    dsimp [b] at hb0
    linarith
  have hNv0 : 0 < N + v := by linarith
  have hp10 : 0 < p + 1 := by linarith
  have hvp0 : 0 < v + p + 1 := by linarith
  have hvb : v ≤ b := by simpa [b] using hvB
  have hNfrac : N / (N + v) ≤ 1 := by
    exact (div_le_one hNv0).2 (by linarith)
  have hvfrac : v / (v + p + 1) ≤ b / (p + 1) := by
    apply (div_le_div_iff₀ hvp0 hp10).2
    calc
      v * (p + 1) ≤ b * (p + 1) :=
        mul_le_mul_of_nonneg_right hvb (le_of_lt hp10)
      _ ≤ b * (v + p + 1) := by
        exact mul_le_mul_of_nonneg_left (by linarith) (le_of_lt hb0)
  have hpoly : 1 + v * (v + 2) ≤ 1 + b * (b + 2) := by
    have hfactor : 0 ≤ (b - v) * (b + v + 2) :=
      mul_nonneg (sub_nonneg.mpr hvb) (by positivity)
    nlinarith
  have hfactorization :
      lyapunovRemainder p N v =
        (1 / N) * (N / (N + v)) * (v / (v + p + 1)) *
          (1 + v * (v + 2)) := by
    unfold lyapunovRemainder
    field_simp [ne_of_gt hN0, ne_of_gt hNv0, ne_of_gt hvp0]
  rw [hfactorization]
  calc
    (1 / N) * (N / (N + v)) * (v / (v + p + 1)) *
          (1 + v * (v + 2)) ≤
        (1 / N) * 1 * (b / (p + 1)) * (1 + b * (b + 2)) := by
      gcongr
    _ =
        (b * (1 + b * (b + 2)) / (p + 1)) / N := by ring
    _ ≤ oneStepLyapunovConstant p / N := by
      apply div_le_div_of_nonneg_right _ (le_of_lt hN0)
      dsimp [oneStepLyapunovConstant]
      apply le_max_of_le_right
      simp [b]

/-- Real-index form of the one-step Lyapunov estimate.  Keeping the rank as a
real number isolates the scalar algebra from casts; `oneStepLyapunov` below
is the manuscript-facing natural-rank wrapper. -/
theorem oneStepLyapunovReal
    {p N u v zPrev zNext : ℝ}
    (hp : 1 < p)
    (hN : p ^ 2 - 1 < N - 1)
    (hu0 : 0 < u)
    (huB : u ≤ p ^ 2 - 1)
    (hv0 : 0 < v)
    (hvB : v ≤ p ^ 2 - 1)
    (hzPrev : lyapunovTheta p ≤ zPrev)
    (hmass : v ≤ N * u / (N - 1 - u))
    (hzNext :
      zNext = lyapunovOmega N v * zPrev + 1 / (N * v)) :
    lyapunovPotential p v zNext - lyapunovPotential p u zPrev ≤
      (p - 1 - v) / N + oneStepLyapunovConstant p / N ^ 2 := by
  have hb0 : 0 < p ^ 2 - 1 := exponentSquareSubOne_pos hp
  have hN0 : 0 < N := by linarith
  have hcoeff := coefficient_compare hp hN hu0 huB hv0 hmass
  have hshift := recursion_sub_theta hp hN hv0 hzNext
  have hdrift := drift_identity hp hN hv0
  have hrem := remainder_bound hp hN hv0 hvB
  have hpotential :
      lyapunovPotential p v zNext - lyapunovPotential p u zPrev =
        (lyapunovCoeff p v * lyapunovOmega N v - lyapunovCoeff p u) *
            (zPrev - lyapunovTheta p) +
          lyapunovCoeff p v * lyapunovDrift p N v := by
    unfold lyapunovPotential
    rw [hshift]
    ring
  have hpotentialTerm :
      (lyapunovCoeff p v * lyapunovOmega N v - lyapunovCoeff p u) *
          (zPrev - lyapunovTheta p) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hcoeff)
      (sub_nonneg.mpr hzPrev)
  have hremDiv :
      lyapunovRemainder p N v / N ≤
        (oneStepLyapunovConstant p / N) / N :=
    div_le_div_of_nonneg_right hrem (le_of_lt hN0)
  rw [hpotential, hdrift]
  calc
    (lyapunovCoeff p v * lyapunovOmega N v - lyapunovCoeff p u) *
          (zPrev - lyapunovTheta p) +
        (p - 1 - v + lyapunovRemainder p N v) / N ≤
      (p - 1 - v + lyapunovRemainder p N v) / N := by linarith
    _ = (p - 1 - v) / N + lyapunovRemainder p N v / N := by ring
    _ ≤ (p - 1 - v) / N +
        (oneStepLyapunovConstant p / N) / N :=
      add_le_add_right hremDiv _
    _ = (p - 1 - v) / N + oneStepLyapunovConstant p / N ^ 2 := by
      field_simp [ne_of_gt hN0]

/-- The one-step Lyapunov estimate with a natural rank, matching the indexing
used in the manuscript.  The assumptions `u = ν_(n-1)`, `v = ν_n`,
`zPrev = ζ_(n-1)`, and `zNext = ζ_n` are kept as scalar arguments. -/
theorem oneStepLyapunov
    {p : ℝ}
    (hp : 1 < p)
    {n : ℕ}
    (_hn : 2 ≤ n)
    {u v zPrev zNext : ℝ}
    (hN : p ^ 2 - 1 < (n : ℝ) - 1)
    (hu0 : 0 < u)
    (huB : u ≤ p ^ 2 - 1)
    (hv0 : 0 < v)
    (hvB : v ≤ p ^ 2 - 1)
    (hzPrev : lyapunovTheta p ≤ zPrev)
    (hmass : v ≤ (n : ℝ) * u / ((n : ℝ) - 1 - u))
    (hzNext :
      zNext = lyapunovOmega (n : ℝ) v * zPrev +
        1 / ((n : ℝ) * v)) :
    lyapunovPotential p v zNext - lyapunovPotential p u zPrev ≤
      (p - 1 - v) / (n : ℝ) +
        oneStepLyapunovConstant p / (n : ℝ) ^ 2 := by
  exact oneStepLyapunovReal hp hN hu0 huB hv0 hvB hzPrev hmass hzNext

end
end RankAnalysis
end GDLowerBound
