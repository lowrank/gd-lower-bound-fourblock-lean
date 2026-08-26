import GDLowerBound.FourBlock.Equalization

/-!
# Finite coupled equalization

This is the exact finite product inequality used before any block limit is
taken.  The common exponential multiplier cancels using the single mass
budget; no `O(1/q)` term occurs in this lemma.
-/

namespace GDLowerBound.FourBlock

open scoped BigOperators

noncomputable section

theorem coupledEqualization {q : ℕ} (hq : 0 < q)
    (u A B : Fin q → ℝ) (D : ℝ)
    (hD : 0 < D) (hu : ∀ i, 0 < u i)
    (hA : ∀ i, 0 < A i) (hB : ∀ i, 0 ≤ B i)
    (hmass : ∑ i, u i ≤ D) :
    ∏ i, u i * (A i + B i * u i) ≤
      ∏ i, (D / q) * A i *
        envelope ((D / q) * B i / A i) := by
  let ubar : ℝ := D / q
  let x : Fin q → ℝ := fun i ↦ u i / ubar
  let b : Fin q → ℝ := fun i ↦ ubar * B i / A i
  let base : Fin q → ℝ := fun i ↦ ubar * A i * envelope (b i)
  have hqR : 0 < (q : ℝ) := by exact_mod_cast hq
  have hubar : 0 < ubar := div_pos hD hqR
  have hb : ∀ i, 0 ≤ b i := by
    intro i
    dsimp only [b]
    exact div_nonneg (mul_nonneg hubar.le (hB i)) (hA i).le
  have hx : ∀ i, 0 < x i := fun i ↦ div_pos (hu i) hubar
  have hbase : ∀ i, 0 < base i := by
    intro i
    dsimp only [base]
    positivity [hubar, hA i, envelope_pos (hb i)]
  have hpoint : ∀ i,
      u i * (A i + B i * u i) ≤
        base i * Real.exp (x i - 1) := by
    intro i
    have heq := equalization_le_envelope (hb i) (hx i)
    have hscale : 0 < ubar * A i := mul_pos hubar (hA i)
    have hraw :
        x i * (1 + b i * x i) ≤
          envelope (b i) * Real.exp (x i - 1) := by
      calc
        x i * (1 + b i * x i) =
            (x i * (1 + b i * x i) * Real.exp (1 - x i)) *
              Real.exp (x i - 1) := by
          symm
          calc
            (x i * (1 + b i * x i) * Real.exp (1 - x i)) *
                Real.exp (x i - 1) =
              x i * (1 + b i * x i) *
                (Real.exp (1 - x i) * Real.exp (x i - 1)) := by ring
            _ = x i * (1 + b i * x i) := by
              rw [← Real.exp_add]
              simp
        _ ≤ envelope (b i) * Real.exp (x i - 1) :=
          mul_le_mul_of_nonneg_right heq (Real.exp_pos _).le
    have hid :
        ubar * A i * (x i * (1 + b i * x i)) =
          u i * (A i + B i * u i) := by
      dsimp only [x, b]
      field_simp [hubar.ne', (hA i).ne']
    rw [← hid]
    have hmul := mul_le_mul_of_nonneg_left hraw hscale.le
    simpa only [base, mul_assoc] using hmul
  have hsumx : ∑ i, x i ≤ q := by
    have hscaled : (∑ i, u i) / ubar ≤ D / ubar :=
      div_le_div_of_nonneg_right hmass hubar.le
    have hDdiv : D / ubar = (q : ℝ) := by
      dsimp only [ubar]
      field_simp [hD.ne', hqR.ne']
    rw [hDdiv] at hscaled
    change ∑ i, u i / ubar ≤ (q : ℝ)
    calc
      ∑ i, u i / ubar = (∑ i, u i) / ubar := by
        simp only [div_eq_mul_inv]
        rw [Finset.sum_mul]
      _ ≤ (q : ℝ) := hscaled
  have hsum : ∑ i, (x i - 1) ≤ 0 := by
    rw [Finset.sum_sub_distrib]
    simpa using hsumx
  have hexp : Real.exp (∑ i, (x i - 1)) ≤ 1 :=
    Real.exp_le_one_iff.mpr hsum
  calc
    ∏ i, u i * (A i + B i * u i) ≤
        ∏ i, base i * Real.exp (x i - 1) := by
      apply Finset.prod_le_prod
      · intro i _
        positivity [hu i, hA i, hB i]
      · intro i _
        exact hpoint i
    _ = (∏ i, base i) * Real.exp (∑ i, (x i - 1)) := by
      rw [Finset.prod_mul_distrib, Real.exp_sum]
    _ ≤ ∏ i, base i := by
      simpa only [mul_one] using
        mul_le_mul_of_nonneg_left hexp
          (Finset.prod_nonneg fun i _ ↦ (hbase i).le)
    _ = ∏ i, (D / q) * A i * envelope ((D / q) * B i / A i) := by
      rfl

end

end GDLowerBound.FourBlock
