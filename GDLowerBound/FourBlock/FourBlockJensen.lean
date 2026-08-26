import GDLowerBound.FourBlock.OutsideInFourBlock

/-!
# Four quarter-block Jensen bound for the outside-in score

The statement here is exact and finite: it contains no limit and no
asymptotic error.
-/

namespace GDLowerBound.FourBlock

open scoped BigOperators

noncomputable section

/-- The first (smallest) quarter, in increasing order. -/
def outsideQuarterOne {m : ℕ} (w : Fin (2 * (m + m)) → ℝ) : Fin m → ℝ :=
  fun i ↦ w ⟨i, by omega⟩

/-- The second quarter, in increasing order. -/
def outsideQuarterTwo {m : ℕ} (w : Fin (2 * (m + m)) → ℝ) : Fin m → ℝ :=
  fun i ↦ w ⟨m + i, by omega⟩

/-- The third quarter, read in decreasing order as it appears in the
outside-in matching. -/
def outsideQuarterThree {m : ℕ} (w : Fin (2 * (m + m)) → ℝ) : Fin m → ℝ :=
  fun i ↦ w ⟨2 * (m + m) - 1 - (m + i), by omega⟩

/-- The fourth (largest) quarter, read in decreasing order. -/
def outsideQuarterFour {m : ℕ} (w : Fin (2 * (m + m)) → ℝ) : Fin m → ℝ :=
  fun i ↦ w ⟨2 * (m + m) - 1 - i, by omega⟩

theorem outsideInLogScore_two_mul_split {m : ℕ}
    (w : Fin (2 * (m + m)) → ℝ) :
    outsideInLogScore (m + m) w =
      (∑ i : Fin m,
        logKernel (outsideQuarterOne w i) (outsideQuarterFour w i)) +
      ∑ i : Fin m,
        logKernel (outsideQuarterTwo w i) (outsideQuarterThree w i) := by
  unfold outsideInLogScore outsideInLeft outsideInRight
  rw [Fin.sum_univ_add]
  apply congrArg₂ (fun x y : ℝ ↦ x + y)
  · apply Finset.sum_congr rfl
    intro i hi
    apply congrArg₂ logKernel <;> apply congrArg w <;> apply Fin.ext <;>
      simp [outsideQuarterOne, outsideQuarterFour] <;> omega
  · apply Finset.sum_congr rfl
    intro i hi
    apply congrArg₂ logKernel <;> apply congrArg w <;> apply Fin.ext <;>
      simp [outsideQuarterTwo, outsideQuarterThree] <;> omega

/-- The exact outside-in score is controlled by the average of the two
exact kernels evaluated at the four quarter means. -/
theorem outsideInLogScore_average_le_fourBlock {m : ℕ} (hm : 0 < m)
    (w : Fin (2 * (m + m)) → ℝ) (hw : ∀ i, 0 < w i) :
    outsideInLogScore (m + m) w / (2 * m) ≤
      (logKernel (finMean (outsideQuarterOne w))
          (finMean (outsideQuarterFour w)) +
        logKernel (finMean (outsideQuarterTwo w))
          (finMean (outsideQuarterThree w))) / 2 := by
  have h1 := mean_logKernel_le_logKernel_means hm
    (outsideQuarterOne w) (outsideQuarterFour w)
    (fun i ↦ hw _) (fun i ↦ hw _)
  have h2 := mean_logKernel_le_logKernel_means hm
    (outsideQuarterTwo w) (outsideQuarterThree w)
    (fun i ↦ hw _) (fun i ↦ hw _)
  rw [outsideInLogScore_two_mul_split]
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hnorm :
      ((∑ i : Fin m,
          logKernel (outsideQuarterOne w i) (outsideQuarterFour w i)) +
        ∑ i : Fin m,
          logKernel (outsideQuarterTwo w i) (outsideQuarterThree w i)) /
          (((2 * m : ℕ) : ℝ)) =
        (((∑ i : Fin m,
            logKernel (outsideQuarterOne w i) (outsideQuarterFour w i)) / m) +
          ((∑ i : Fin m,
            logKernel (outsideQuarterTwo w i) (outsideQuarterThree w i)) / m)) / 2 := by
    norm_num [Nat.cast_mul]
    field_simp [hmR.ne'] <;> ring
  norm_num [Nat.cast_mul] at hnorm
  rw [hnorm]
  linarith

end

end GDLowerBound.FourBlock
