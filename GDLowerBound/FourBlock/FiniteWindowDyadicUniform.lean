import GDLowerBound.FourBlock.FiniteWindowDyadicSelection

/-!
# Uniform tail of good dyadic windows

For the global cutoff scan one must choose the dyadic endpoint near a terminal
rank, rather than use one preselected window.  The master reciprocal numerator
is affine in the depth.  Consequently all sufficiently deep windows with all
sufficiently large base scales fit the strict finite margin.
-/

namespace GDLowerBound.FourBlock

noncomputable section

def dyadicWindowSlope : ℝ :=
  squareWeightSum * (52 / criticalTheta) +
    ((sideC2Q : ℝ) + (sideC3Q : ℝ) + (centralC4Q : ℝ)) * 288 +
    ((sideD2Q : ℝ) + (sideD3Q : ℝ) + (centralD4Q : ℝ)) * 104 +
    lambdaTwo * (betaLower * 104) +
    lambdaThree * (betaLower * 104)

theorem dyadicWindowSlope_nonneg : 0 ≤ dyadicWindowSlope := by
  unfold dyadicWindowSlope
  have hs : (0 : ℝ) ≤ squareWeightSum := by norm_num [squareWeightSum]
  have hb := betaLower_pos.le
  have ht := criticalTheta_pos.le
  norm_num [sideC2Q, sideC3Q, centralC4Q,
    sideD2Q, sideD3Q, centralD4Q, lambdaTwo, lambdaThree]
  positivity

/-- The reciprocal numerator in the master bound is exactly affine in the
dyadic depth. -/
theorem dyadicWindowNumerator_eq_affine (R : ℕ) :
    dyadicWindowNumerator R =
      dyadicWindowSlope * (R : ℝ) + dyadicWindowNumerator 0 := by
  unfold dyadicWindowNumerator dyadicWindowSlope dyadicJointNumerator
    scheduleSamplingDyadicNumerator endpointSamplingDyadicNumerator
    blockSamplingDyadicNumerator
  ring

/-- Uniform form of dyadic finite-window selection.  The thresholds are
schedule-independent and every larger depth/base pair is valid. -/
theorem exists_uniform_dyadicFourBlockWindow :
    ∃ R₀ M₀ : ℕ, 3 ≤ R₀ ∧ 2 ≤ M₀ ∧
      ∀ R M : ℕ, R₀ ≤ R → M₀ ≤ M →
        fourBlockWindowError M ((2 ^ R) * M) < fourBlockFiniteMargin := by
  let C := dyadicWindowConstant
  let S := dyadicWindowSlope
  let A₀ := dyadicWindowNumerator 0
  let epsilon := fourBlockFiniteMargin
  have hC : 0 ≤ C := dyadicWindowConstant_nonneg
  have hS : 0 ≤ S := dyadicWindowSlope_nonneg
  have hA₀ : 0 ≤ A₀ := dyadicWindowNumerator_nonneg 0
  have hepsilon : 0 < epsilon := fourBlockFiniteMargin_pos
  have hCratio : 0 ≤ C / epsilon := div_nonneg hC hepsilon.le
  have hSAratio : 0 ≤ (S + A₀) / epsilon :=
    div_nonneg (add_nonneg hS hA₀) hepsilon.le
  obtain ⟨R₀, hR₀big⟩ := exists_nat_gt (6 * (C / epsilon) + 3)
  obtain ⟨M₀, hM₀big⟩ := exists_nat_gt (6 * ((S + A₀) / epsilon) + 2)
  have hR₀real : (3 : ℝ) ≤ R₀ := by nlinarith
  have hM₀real : (2 : ℝ) ≤ M₀ := by nlinarith
  have hR₀ : 3 ≤ R₀ := by exact_mod_cast hR₀real
  have hM₀ : 2 ≤ M₀ := by exact_mod_cast hM₀real
  refine ⟨R₀, M₀, hR₀, hM₀, ?_⟩
  intro R M hR₀R hM₀M
  have hR : 3 ≤ R := hR₀.trans hR₀R
  have hM : 2 ≤ M := hM₀.trans hM₀M
  have hRreal : (R₀ : ℝ) ≤ R := by exact_mod_cast hR₀R
  have hMreal : (M₀ : ℝ) ≤ M := by exact_mod_cast hM₀M
  have hRpos : (0 : ℝ) < R := by positivity
  have hMpos : (0 : ℝ) < M := by positivity
  let H := averagingHarmonicWeight M ((2 ^ R) * M)
  have hHlower := dyadic_averagingHarmonicWeight_lower
    (R := R) (show 1 ≤ M by omega)
  have hMinv : 1 / (M : ℝ) ≤ 1 := by
    exact (div_le_one hMpos).2 (by exact_mod_cast (show 1 ≤ M by omega))
  have hRthird : (1 : ℝ) ≤ (R : ℝ) / 3 := by
    have : (3 : ℝ) ≤ R := by exact_mod_cast hR
    linarith
  have hHthird : (R : ℝ) / 3 ≤ H := by
    dsimp only [H]
    nlinarith [hMinv.trans hRthird]
  have hHpos : 0 < H := lt_of_lt_of_le (by positivity) hHthird
  have hRbound : 6 * (C / epsilon) < (R : ℝ) := by
    linarith
  have hCmul := mul_lt_mul_of_pos_left hRbound hepsilon
  have hepsilon0 : epsilon ≠ 0 := hepsilon.ne'
  have h6C : 6 * C < epsilon * (R : ℝ) := by
    calc
      6 * C = epsilon * (6 * (C / epsilon)) := by
        field_simp [hepsilon0]
      _ < epsilon * (R : ℝ) := hCmul
  have hCpart : C < epsilon * (R : ℝ) / 6 := by nlinarith
  have hMbound : 6 * ((S + A₀) / epsilon) < (M : ℝ) := by
    linarith
  have hSAmul := mul_lt_mul_of_pos_left hMbound hepsilon
  have h6SA : 6 * (S + A₀) < epsilon * (M : ℝ) := by
    calc
      6 * (S + A₀) = epsilon * (6 * ((S + A₀) / epsilon)) := by
        field_simp [hepsilon0]
      _ < epsilon * (M : ℝ) := hSAmul
  have hSAdiv : (S + A₀) / (M : ℝ) < epsilon / 6 := by
    apply (div_lt_iff₀ hMpos).2
    nlinarith
  have hRone : (1 : ℝ) ≤ R := by exact_mod_cast (show 1 ≤ R by omega)
  have haffine : S * (R : ℝ) + A₀ ≤ (S + A₀) * (R : ℝ) := by
    nlinarith
  have haffineDiv := div_le_div_of_nonneg_right haffine hMpos.le
  have hscaled := mul_lt_mul_of_pos_right hSAdiv hRpos
  have hApart :
      dyadicWindowNumerator R / (M : ℝ) <
        epsilon * (R : ℝ) / 6 := by
    rw [dyadicWindowNumerator_eq_affine]
    calc
      (S * (R : ℝ) + A₀) / (M : ℝ) ≤
          ((S + A₀) * (R : ℝ)) / (M : ℝ) := haffineDiv
      _ = ((S + A₀) / (M : ℝ)) * (R : ℝ) := by ring
      _ < (epsilon / 6) * (R : ℝ) := hscaled
      _ = epsilon * (R : ℝ) / 6 := by ring
  have hnumerator :
      C + dyadicWindowNumerator R / (M : ℝ) <
        epsilon * ((R : ℝ) / 3) := by
    nlinarith
  have htarget :
      (C + dyadicWindowNumerator R / (M : ℝ)) / H < epsilon := by
    apply (div_lt_iff₀ hHpos).2
    have hHscaled := mul_le_mul_of_nonneg_left hHthird hepsilon.le
    exact hnumerator.trans_le (by
      convert hHscaled using 1 <;> ring)
  exact (fourBlockWindowError_dyadic_le hM (by omega : 1 ≤ R)).trans_lt
    (by simpa only [C, epsilon, H] using htarget)

end

end GDLowerBound.FourBlock
