import Mathlib.Analysis.MeanInequalities

/-!
# Total-weight estimates for the matching kernel

This file isolates the algebraic core of the matching argument in the manuscript.  Vertices are
always regarded as labelled: in the sequence formulations below, the index is the label, so equal
numerical weights remain distinct.
-/

namespace GDLowerBound.Matching

open scoped BigOperators

noncomputable section

/-- The symmetric edge kernel used in the matching reduction. -/
def psi (u v : ℝ) : ℝ := (u + v + u * v) / 2

@[simp]
theorem psi_comm (u v : ℝ) : psi u v = psi v u := by
  simp only [psi]
  ring

theorem two_mul_psi (u v : ℝ) : 2 * psi u v = (1 + u) * (1 + v) - 1 := by
  simp only [psi]
  ring

theorem psi_nonneg {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) : 0 ≤ psi u v := by
  simp only [psi]
  positivity

/-- First four-point exchange identity. -/
theorem psi_exchange_cross (a b c d : ℝ) :
    4 * (psi a d * psi b c - psi a c * psi b d) = (b - a) * (d - c) := by
  simp only [psi]
  ring

/-- Second four-point exchange identity. -/
theorem psi_exchange_parallel (a b c d : ℝ) :
    4 * (psi a d * psi b c - psi a b * psi c d) = (c - a) * (d - b) := by
  simp only [psi]
  ring

/-- Crossing two inner edges to create the outside-in pair cannot decrease their product. -/
theorem psi_exchange_cross_le {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d) :
    psi a c * psi b d ≤ psi a d * psi b c := by
  have hprod : 0 ≤ (b - a) * (d - c) :=
    mul_nonneg (sub_nonneg.mpr hab) (sub_nonneg.mpr hcd)
  nlinarith [psi_exchange_cross a b c d]

/-- Replacing two separated edges by the corresponding outside-in edges cannot decrease product. -/
theorem psi_exchange_parallel_le {a b c d : ℝ} (hac : a ≤ c) (hbd : b ≤ d) :
    psi a b * psi c d ≤ psi a d * psi b c := by
  have hprod : 0 ≤ (c - a) * (d - b) :=
    mul_nonneg (sub_nonneg.mpr hac) (sub_nonneg.mpr hbd)
  nlinarith [psi_exchange_parallel a b c d]

/-- The covariance identity underlying the reverse-Chebyshev inequality. -/
theorem reverseChebyshev_identity {I : Type*} (s : Finset I) (x y : I → ℝ) :
    (s.card : ℝ) * ∑ i ∈ s, x i * y i -
        (∑ i ∈ s, x i) * (∑ i ∈ s, y i) =
      (1 / 2 : ℝ) * ∑ i ∈ s, ∑ j ∈ s, (x i - x j) * (y i - y j) := by
  classical
  have hdiag₁ : ∑ i ∈ s, ∑ _j ∈ s, x i * y i =
      (s.card : ℝ) * ∑ i ∈ s, x i * y i := by
    simp only [Finset.sum_const, nsmul_eq_mul]
    rw [Finset.mul_sum]
  have hcross₁ : ∑ i ∈ s, ∑ j ∈ s, x i * y j =
      (∑ i ∈ s, x i) * (∑ j ∈ s, y j) := by
    exact (Finset.sum_mul_sum s s x y).symm
  have hcross₂ : ∑ i ∈ s, ∑ j ∈ s, x j * y i =
      (∑ i ∈ s, x i) * (∑ j ∈ s, y j) := by
    rw [Finset.sum_comm]
    exact (Finset.sum_mul_sum s s x y).symm
  have hdiag₂ : ∑ _i ∈ s, ∑ j ∈ s, x j * y j =
      (s.card : ℝ) * ∑ j ∈ s, x j * y j := by
    simp only [Finset.sum_const, nsmul_eq_mul]
  simp_rw [sub_mul, mul_sub]
  simp only [Finset.sum_sub_distrib]
  rw [hdiag₁, hcross₁, hcross₂, hdiag₂]
  ring

/-- Reverse Chebyshev in a form that only assumes pairwise opposite variation. -/
theorem reverseChebyshev_le {I : Type*} (s : Finset I) (x y : I → ℝ)
    (hanti : ∀ i ∈ s, ∀ j ∈ s, (x i - x j) * (y i - y j) ≤ 0) :
    (s.card : ℝ) * ∑ i ∈ s, x i * y i ≤
      (∑ i ∈ s, x i) * (∑ i ∈ s, y i) := by
  have hdouble : ∑ i ∈ s, ∑ j ∈ s, (x i - x j) * (y i - y j) ≤ 0 := by
    exact Finset.sum_nonpos fun i hi ↦ Finset.sum_nonpos fun j hj ↦ hanti i hi j hj
  have hdiff :
      (s.card : ℝ) * ∑ i ∈ s, x i * y i -
          (∑ i ∈ s, x i) * (∑ i ∈ s, y i) ≤ 0 := by
    rw [reverseChebyshev_identity s x y]
    exact mul_nonpos_of_nonneg_of_nonpos (by norm_num) hdouble
  linarith

/-- A nondecreasing sequence and a nonincreasing sequence have nonpositive covariance. -/
theorem reverseChebyshev_sorted {n : ℕ} (x y : Fin n → ℝ)
    (hx : Monotone x) (hy : Antitone y) :
    (n : ℝ) * ∑ i, x i * y i ≤ (∑ i, x i) * (∑ i, y i) := by
  simpa using reverseChebyshev_le Finset.univ x y (by
    intro i _ j _
    rcases le_total i j with hij | hji
    · exact mul_nonpos_of_nonpos_of_nonneg
        (sub_nonpos.mpr (hx hij)) (sub_nonneg.mpr (hy hij))
    · exact mul_nonpos_of_nonneg_of_nonpos
        (sub_nonneg.mpr (hx hji)) (sub_nonpos.mpr (hy hji)))

/-- Summing the matching kernel separates the linear and bilinear contributions. -/
theorem sum_psi_eq {n : ℕ} (x y : Fin n → ℝ) :
    ∑ i, psi (x i) (y i) =
      ((∑ i, x i) + ∑ i, y i) / 2 + (∑ i, x i * y i) / 2 := by
  simp_rw [psi, div_eq_mul_inv, add_mul]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  simp_rw [← Finset.sum_mul]

/-- The bilinear part of an outside-in pairing is controlled by its total selected mass. -/
theorem pairedProductSum_le {k : ℕ} (hk : 0 < k) (x y : Fin k → ℝ)
    (hx : Monotone x) (hy : Antitone y) :
    ∑ i, x i * y i ≤ (((∑ i, x i) + ∑ i, y i) ^ 2) / (4 * k) := by
  have hkℝ : 0 < (k : ℝ) := by exact_mod_cast hk
  have hcheb := reverseChebyshev_sorted x y hx hy
  have hmeans :
      4 * ((∑ i, x i) * ∑ i, y i) ≤ ((∑ i, x i) + ∑ i, y i) ^ 2 := by
    nlinarith [sq_nonneg ((∑ i, x i) - ∑ i, y i)]
  apply (le_div_iff₀ (mul_pos (by norm_num) hkℝ)).2
  nlinarith

/-- Arithmetic-mean form of the total-weight estimate for an outside-in pairing. -/
theorem outsideIn_arithMean_le_totalWeight {k : ℕ} (hk : 0 < k) (x y : Fin k → ℝ)
    (hx : Monotone x) (hy : Antitone y) :
    (∑ i, psi (x i) (y i)) / k ≤
      ((∑ i, x i) + ∑ i, y i) / (2 * k) +
        (((∑ i, x i) + ∑ i, y i) ^ 2) / (8 * (k : ℝ) ^ 2) := by
  have hkℝ : 0 < (k : ℝ) := by exact_mod_cast hk
  have hprod := pairedProductSum_le hk x y hx hy
  rw [sum_psi_eq]
  calc
    (((∑ i, x i) + ∑ i, y i) / 2 + (∑ i, x i * y i) / 2) / k ≤
        (((∑ i, x i) + ∑ i, y i) / 2 +
          ((((∑ i, x i) + ∑ i, y i) ^ 2) / (4 * k)) / 2) / k := by
      gcongr
    _ = ((∑ i, x i) + ∑ i, y i) / (2 * k) +
        (((∑ i, x i) + ∑ i, y i) ^ 2) / (8 * (k : ℝ) ^ 2) := by
      field_simp
      ring

/-- AM--GM converts the arithmetic-mean estimate into the per-edge geometric-mean bound. -/
theorem outsideIn_geomMean_le_totalWeight {k : ℕ} (hk : 0 < k) (x y : Fin k → ℝ)
    (hx₀ : ∀ i, 0 ≤ x i) (hy₀ : ∀ i, 0 ≤ y i)
    (hx : Monotone x) (hy : Antitone y) :
    (∏ i, psi (x i) (y i)) ^ ((k : ℝ)⁻¹) ≤
      ((∑ i, x i) + ∑ i, y i) / (2 * k) +
        (((∑ i, x i) + ∑ i, y i) ^ 2) / (8 * (k : ℝ) ^ 2) := by
  have hkℝ : 0 < (k : ℝ) := by exact_mod_cast hk
  have hamgm := Real.geom_mean_le_arith_mean
    (Finset.univ : Finset (Fin k)) (fun _ ↦ (1 : ℝ)) (fun i ↦ psi (x i) (y i))
    (fun _ _ ↦ by norm_num) (by simpa using hkℝ)
    (fun i _ ↦ psi_nonneg (hx₀ i) (hy₀ i))
  have hgeom :
      (∏ i, psi (x i) (y i)) ^ ((k : ℝ)⁻¹) ≤ (∑ i, psi (x i) (y i)) / k := by
    simpa using hamgm
  exact hgeom.trans (outsideIn_arithMean_le_totalWeight hk x y hx hy)

/--
Interface between the exchange argument and the scalar total-weight estimate.  Once repeated
four-point exchanges exhibit an outside-in pairing whose product dominates `P`, this theorem gives
the desired bound without referring to how the original matching was encoded.
-/
theorem matching_geomMean_le_of_outsideIn_domination {k : ℕ} (hk : 0 < k)
    (P total : ℝ) (x y : Fin k → ℝ)
    (hP₀ : 0 ≤ P) (hx₀ : ∀ i, 0 ≤ x i) (hy₀ : ∀ i, 0 ≤ y i)
    (hx : Monotone x) (hy : Antitone y)
    (hdom : P ≤ ∏ i, psi (x i) (y i))
    (hselected : (∑ i, x i) + ∑ i, y i ≤ total) :
    P ^ ((k : ℝ)⁻¹) ≤ total / (2 * k) + total ^ 2 / (8 * (k : ℝ) ^ 2) := by
  have hkℝ : 0 < (k : ℝ) := by exact_mod_cast hk
  have hinv : 0 ≤ (k : ℝ)⁻¹ := inv_nonneg.mpr hkℝ.le
  have hroot :
      P ^ ((k : ℝ)⁻¹) ≤ (∏ i, psi (x i) (y i)) ^ ((k : ℝ)⁻¹) :=
    Real.rpow_le_rpow hP₀ hdom hinv
  refine hroot.trans <| (outsideIn_geomMean_le_totalWeight hk x y hx₀ hy₀ hx hy).trans ?_
  have hselected₀ : 0 ≤ (∑ i, x i) + ∑ i, y i := by
    exact add_nonneg (Finset.sum_nonneg fun i _ ↦ hx₀ i)
      (Finset.sum_nonneg fun i _ ↦ hy₀ i)
  have htotal₀ : 0 ≤ total := hselected₀.trans hselected
  field_simp
  nlinarith

end

end GDLowerBound.Matching
