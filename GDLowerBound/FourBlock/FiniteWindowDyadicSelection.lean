import GDLowerBound.FourBlock.FiniteWindowDyadicError

/-!
# Existence of a certified dyadic finite window

The master dyadic estimate is now converted into a genuine existence theorem:
first choose the depth to absorb the fixed boundary constant, then choose the
base scale to absorb the reciprocal numerator.
-/

namespace GDLowerBound.FourBlock

noncomputable section

/-- A general quantitative selection lemma for the exact harmonic mass. -/
theorem exists_dyadicWindow_of_nonneg
    {C : ℝ} {A : ℕ → ℝ} {epsilon : ℝ}
    (hC : 0 ≤ C) (hA : ∀ R, 0 ≤ A R) (hepsilon : 0 < epsilon) :
    ∃ R M : ℕ, 1 ≤ R ∧ 2 ≤ M ∧
      (C + A R / (M : ℝ)) /
          averagingHarmonicWeight M ((2 ^ R) * M) < epsilon := by
  have hratioC : 0 ≤ C / epsilon := div_nonneg hC hepsilon.le
  obtain ⟨R, hRbig⟩ := exists_nat_gt (3 * (C / epsilon + 1))
  have hRreal : (1 : ℝ) ≤ R := by nlinarith
  have hR : 1 ≤ R := by exact_mod_cast hRreal
  have hAR : 0 ≤ A R := hA R
  have hratioA : 0 ≤ A R / epsilon := div_nonneg hAR hepsilon.le
  obtain ⟨M, hMbig⟩ := exists_nat_gt (2 * (A R / epsilon) + 2)
  have hMreal : (2 : ℝ) ≤ M := by nlinarith
  have hM : 2 ≤ M := by exact_mod_cast hMreal
  have hMpos : (0 : ℝ) < M := lt_of_lt_of_le (by norm_num) hMreal
  have hMinv : 1 / (M : ℝ) ≤ 1 := by
    exact (div_le_one hMpos).2 (by linarith)
  let H := averagingHarmonicWeight M ((2 ^ R) * M)
  have hHlower := dyadic_averagingHarmonicWeight_lower
    (R := R) (show 1 ≤ M by omega)
  have hHbase : (2 / 3 : ℝ) * (R : ℝ) - 1 ≤ H := by
    dsimp only [H]
    linarith
  have hHstrong : 2 * (C / epsilon) + 1 < H := by
    nlinarith
  have hHone : 1 < H := by nlinarith
  have hCover : 2 * (C / epsilon) < H := by linarith
  have hCmul := mul_lt_mul_of_pos_left hCover hepsilon
  have hepsilon0 : epsilon ≠ 0 := hepsilon.ne'
  have h2C : 2 * C < epsilon * H := by
    calc
      2 * C = epsilon * (2 * (C / epsilon)) := by
        field_simp [hepsilon0]
      _ < epsilon * H := hCmul
  have hChalf : C < (epsilon / 2) * H := by nlinarith
  have hAover : 2 * (A R / epsilon) < (M : ℝ) := by linarith
  have hAmul := mul_lt_mul_of_pos_left hAover hepsilon
  have h2A : 2 * A R < epsilon * (M : ℝ) := by
    calc
      2 * A R = epsilon * (2 * (A R / epsilon)) := by
        field_simp [hepsilon0]
      _ < epsilon * (M : ℝ) := hAmul
  have hAhalf : A R / (M : ℝ) < epsilon / 2 := by
    apply (div_lt_iff₀ hMpos).2
    nlinarith
  have hhalfpos : 0 < epsilon / 2 := by positivity
  have hhalfH : epsilon / 2 < (epsilon / 2) * H := by
    have hmul := mul_lt_mul_of_pos_left hHone hhalfpos
    simpa using hmul
  have hnumerator : C + A R / (M : ℝ) < epsilon * H := by
    nlinarith [hAhalf.trans hhalfH]
  have hHpos : 0 < H := lt_trans zero_lt_one hHone
  refine ⟨R, M, hR, hM, ?_⟩
  exact (div_lt_iff₀ hHpos).2 hnumerator

/-- There exists an explicit dyadic shape for which the entire
schedule-independent four-block finite error lies inside the certified
strict margin. -/
theorem exists_dyadicFourBlockWindow :
    ∃ R M : ℕ, 1 ≤ R ∧ 2 ≤ M ∧
      fourBlockWindowError M ((2 ^ R) * M) < fourBlockFiniteMargin := by
  obtain ⟨R, M, hR, hM, hbound⟩ :=
    exists_dyadicWindow_of_nonneg
      dyadicWindowConstant_nonneg dyadicWindowNumerator_nonneg
      fourBlockFiniteMargin_pos
  refine ⟨R, M, hR, hM, ?_⟩
  exact (fourBlockWindowError_dyadic_le hM hR).trans_lt hbound

end

end GDLowerBound.FourBlock
