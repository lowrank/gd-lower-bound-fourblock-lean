import GDLowerBound.FourBlock.FixedDilationSampling

/-!
# Quantitative fixed-dilation errors for the cutoff observables

This file applies the exact block sampler to the endpoint defect and to the
squared relative-increment deviation.  Every error is explicit and tends to
zero as the initial rank tends to infinity.
-/

namespace GDLowerBound.FourBlock

open scoped BigOperators
open GDLowerBound.Schedule GDLowerBound.RankAnalysis

noncomputable section

private theorem sum_adjacent_difference_normalized (x : ℕ → ℝ)
    {lo hi : ℕ} (hlohi : lo ≤ hi) :
    ∑ n ∈ Finset.Ico (lo + 1) (hi + 1),
        (x n - x (n - 1)) = x hi - x lo := by
  induction hi, hlohi using Nat.le_induction with
  | base => simp
  | succ hi hlohi ih =>
      rw [Finset.sum_Ico_succ_top (by omega), ih]
      simp only [Nat.add_sub_cancel]
      ring

/-- Dividing a bounded observable by its rank costs only one weighted
variation term and one endpoint term. -/
theorem rankNormalized_totalVariation_le
    {x : ℕ → ℝ} {B : ℝ} {lo hi : ℕ}
    (hlo : 1 ≤ lo) (hlohi : lo ≤ hi) (hB : 0 ≤ B)
    (hx : ∀ n ∈ Finset.Icc lo hi, |x n| ≤ B) :
    adjacentTotalVariation (rankNormalized x) lo hi ≤
      adjacentWeightedVariation x lo hi + B / (lo : ℝ) := by
  have hterm : ∀ n ∈ Finset.Ico (lo + 1) (hi + 1),
      |rankNormalized x n - rankNormalized x (n - 1)| ≤
        |x n - x (n - 1)| / (n : ℝ) +
          B * (1 / ((n - 1 : ℕ) : ℝ) - 1 / (n : ℝ)) := by
    intro n hn
    have hnIco := Finset.mem_Ico.mp hn
    have hn0 : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
    have hp0 : 0 < ((n - 1 : ℕ) : ℝ) := by
      exact_mod_cast (show 0 < n - 1 by omega)
    have hpMem : n - 1 ∈ Finset.Icc lo hi :=
      Finset.mem_Icc.mpr ⟨by omega, by omega⟩
    have hxp := hx (n - 1) hpMem
    have hinv : 1 / (n : ℝ) ≤ 1 / ((n - 1 : ℕ) : ℝ) := by
      apply one_div_le_one_div_of_le hp0
      exact_mod_cast (show n - 1 ≤ n by omega)
    have hdiff0 :
        0 ≤ 1 / ((n - 1 : ℕ) : ℝ) - 1 / (n : ℝ) :=
      sub_nonneg.mpr hinv
    have hid : rankNormalized x n - rankNormalized x (n - 1) =
        (x n - x (n - 1)) / (n : ℝ) +
          x (n - 1) *
            (1 / (n : ℝ) - 1 / ((n - 1 : ℕ) : ℝ)) := by
      unfold rankNormalized
      field_simp [ne_of_gt hn0, ne_of_gt hp0]
      ring
    rw [hid]
    calc
      |(x n - x (n - 1)) / (n : ℝ) +
          x (n - 1) *
            (1 / (n : ℝ) - 1 / ((n - 1 : ℕ) : ℝ))| ≤
          |(x n - x (n - 1)) / (n : ℝ)| +
            |x (n - 1) *
              (1 / (n : ℝ) - 1 / ((n - 1 : ℕ) : ℝ))| :=
        abs_add_le _ _
      _ = |x n - x (n - 1)| / (n : ℝ) +
          |x (n - 1)| *
            (1 / ((n - 1 : ℕ) : ℝ) - 1 / (n : ℝ)) := by
        rw [abs_div, abs_of_pos hn0, abs_mul,
          abs_of_nonpos (sub_nonpos.mpr hinv)]
        ring
      _ ≤ |x n - x (n - 1)| / (n : ℝ) +
          B * (1 / ((n - 1 : ℕ) : ℝ) - 1 / (n : ℝ)) := by
        exact add_le_add_right (mul_le_mul_of_nonneg_right hxp hdiff0) _
  have htel :
      ∑ n ∈ Finset.Ico (lo + 1) (hi + 1),
          (1 / ((n - 1 : ℕ) : ℝ) - 1 / (n : ℝ)) =
        1 / (lo : ℝ) - 1 / (hi : ℝ) := by
    calc
      ∑ n ∈ Finset.Ico (lo + 1) (hi + 1),
          (1 / ((n - 1 : ℕ) : ℝ) - 1 / (n : ℝ)) =
          -∑ n ∈ Finset.Ico (lo + 1) (hi + 1),
            (1 / (n : ℝ) - 1 / ((n - 1 : ℕ) : ℝ)) := by
        rw [← Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl
        intro n _
        ring
      _ = -(1 / (hi : ℝ) - 1 / (lo : ℝ)) := by
        rw [sum_adjacent_difference_normalized
          (fun n ↦ 1 / (n : ℝ)) hlohi]
      _ = 1 / (lo : ℝ) - 1 / (hi : ℝ) := by ring
  have hi0 : 0 < (hi : ℝ) := by
    exact_mod_cast (show 0 < hi by omega)
  calc
    adjacentTotalVariation (rankNormalized x) lo hi ≤
        ∑ n ∈ Finset.Ico (lo + 1) (hi + 1),
          (|x n - x (n - 1)| / (n : ℝ) +
            B * (1 / ((n - 1 : ℕ) : ℝ) - 1 / (n : ℝ))) := by
      exact Finset.sum_le_sum hterm
    _ = adjacentWeightedVariation x lo hi +
        B * (1 / (lo : ℝ) - 1 / (hi : ℝ)) := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, htel]
      rfl
    _ ≤ adjacentWeightedVariation x lo hi + B / (lo : ℝ) := by
      have hdrop : B * (1 / (lo : ℝ) - 1 / (hi : ℝ)) ≤ B / (lo : ℝ) := by
        calc
          B * (1 / (lo : ℝ) - 1 / (hi : ℝ)) =
              B / (lo : ℝ) - B / (hi : ℝ) := by ring
          _ ≤ B / (lo : ℝ) := sub_le_self _ (by positivity)
      exact add_le_add le_rfl hdrop

/-- Squaring the centered cutoff increment is `6`-Lipschitz in weighted
variation on the coarse interval `0 < v < 3`. -/
theorem squareDeviation_weightedVariation_le
    {T : ℕ} {h : StepSchedule T} {lo hi : ℕ}
    (hcut : CutoffConditions criticalP h lo hi) :
    adjacentWeightedVariation
        (fun n ↦ (relativeMassIncrement h n - betaLower) ^ 2) lo hi ≤
      6 * adjacentWeightedVariation (relativeMassIncrement h) lo hi := by
  have hterm : ∀ n ∈ Finset.Ico (lo + 1) (hi + 1),
      |(relativeMassIncrement h n - betaLower) ^ 2 -
          (relativeMassIncrement h (n - 1) - betaLower) ^ 2| /
          (n : ℝ) ≤
        6 * |relativeMassIncrement h n -
          relativeMassIncrement h (n - 1)| / (n : ℝ) := by
    intro n hn
    have hnIco := Finset.mem_Ico.mp hn
    have hnMem : n ∈ Finset.Icc lo hi :=
      Finset.mem_Icc.mpr ⟨by omega, by omega⟩
    have hpMem : n - 1 ∈ Finset.Icc lo hi :=
      Finset.mem_Icc.mpr ⟨by omega, by omega⟩
    obtain ⟨hv0, hv3⟩ := relativeMassIncrement_cutoff_bounds hcut hnMem
    obtain ⟨hu0, hu3⟩ := relativeMassIncrement_cutoff_bounds hcut hpMem
    have hb0 := betaLower_pos
    have hb1 : betaLower < 1 := by norm_num [betaLower]
    have hfactor :
        |relativeMassIncrement h n + relativeMassIncrement h (n - 1) -
          2 * betaLower| ≤ 6 := by
      rw [abs_le]
      constructor <;> linarith
    have hsquare :
        |(relativeMassIncrement h n - betaLower) ^ 2 -
            (relativeMassIncrement h (n - 1) - betaLower) ^ 2| ≤
          6 * |relativeMassIncrement h n -
            relativeMassIncrement h (n - 1)| := by
      have hid :
          (relativeMassIncrement h n - betaLower) ^ 2 -
              (relativeMassIncrement h (n - 1) - betaLower) ^ 2 =
            (relativeMassIncrement h n - relativeMassIncrement h (n - 1)) *
              (relativeMassIncrement h n + relativeMassIncrement h (n - 1) -
                2 * betaLower) := by ring
      rw [hid, abs_mul]
      have hm := mul_le_mul_of_nonneg_left hfactor
        (abs_nonneg (relativeMassIncrement h n - relativeMassIncrement h (n - 1)))
      nlinarith
    exact div_le_div_of_nonneg_right hsquare (by positivity)
  calc
    adjacentWeightedVariation
        (fun n ↦ (relativeMassIncrement h n - betaLower) ^ 2) lo hi ≤
        ∑ n ∈ Finset.Ico (lo + 1) (hi + 1),
          6 * |relativeMassIncrement h n -
            relativeMassIncrement h (n - 1)| / (n : ℝ) := by
      exact Finset.sum_le_sum hterm
    _ = 6 * adjacentWeightedVariation (relativeMassIncrement h) lo hi := by
      unfold adjacentWeightedVariation
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n _
      ring

private theorem squareDeviation_cutoff_bound
    {T : ℕ} {h : StepSchedule T} {lo hi q : ℕ}
    (hcut : CutoffConditions criticalP h lo hi)
    (hq : q ∈ Finset.Icc lo hi) :
    |(relativeMassIncrement h q - betaLower) ^ 2| ≤ 9 := by
  obtain ⟨hv0, hv3⟩ := relativeMassIncrement_cutoff_bounds hcut hq
  have hb0 := betaLower_pos
  have hb1 : betaLower < 1 := by norm_num [betaLower]
  rw [abs_of_nonneg (sq_nonneg _)]
  have hprod : 0 ≤
      (3 - (relativeMassIncrement h q - betaLower)) *
        (3 + (relativeMassIncrement h q - betaLower)) :=
    mul_nonneg (by linarith) (by linarith)
  nlinarith

/-- Normalized endpoint-defect variation with a fully explicit cutoff error. -/
theorem endpointDefect_rankNormalized_totalVariation
    {T Q : ℕ} (hQ : criticalTheta⁻¹ < (Q : ℝ))
    {h : StepSchedule T} (hh : IsNonnegativeSchedule h)
    {lo hi : ℕ} (hQlo : Q ≤ lo) (hlohi : lo ≤ hi)
    (hhir : hi ≤ longCount h)
    (hcut : CutoffConditions criticalP h lo (longCount h)) :
    adjacentTotalVariation (rankNormalized (endpointDefect h)) lo hi ≤
      (104 * adjacentHarmonicWeight lo hi + 2) / (lo : ℝ) := by
  have hQpos : 1 ≤ Q := by
    have : 0 < (Q : ℝ) := (inv_pos.mpr criticalTheta_pos).trans hQ
    exact_mod_cast this
  have hlo : 1 ≤ lo := hQpos.trans hQlo
  have hnorm := rankNormalized_totalVariation_le
    (x := endpointDefect h) (B := 1) hlo hlohi (by norm_num)
    (fun n hn ↦ by
      have hnIcc := Finset.mem_Icc.mp hn
      obtain ⟨he0, he1⟩ := endpointDefect_cutoff_bounds hcut
        (Finset.mem_Icc.mpr ⟨hnIcc.1, hnIcc.2.trans hhir⟩)
      simpa [abs_of_nonneg he0] using he1)
  have hv := adjacentWeightedVariation_le_total_div
    (x := endpointDefect h) (hi := hi) hlo
  have ht := endpointDefect_totalVariation hQ hh hQlo hlohi hhir hcut
  have hvb : adjacentWeightedVariation (endpointDefect h) lo hi ≤
      (104 * adjacentHarmonicWeight lo hi + 1) / (lo : ℝ) :=
    hv.trans (div_le_div_of_nonneg_right ht (by positivity))
  calc
    adjacentTotalVariation (rankNormalized (endpointDefect h)) lo hi ≤
        adjacentWeightedVariation (endpointDefect h) lo hi + 1 / (lo : ℝ) := hnorm
    _ ≤ (104 * adjacentHarmonicWeight lo hi + 1) / (lo : ℝ) +
        1 / (lo : ℝ) := add_le_add hvb le_rfl
    _ = (104 * adjacentHarmonicWeight lo hi + 2) / (lo : ℝ) := by ring

/-- Normalized square-deviation variation with a fully explicit cutoff
error. -/
theorem squareDeviation_rankNormalized_totalVariation
    {T : ℕ} {h : StepSchedule T} (hh : IsNonnegativeSchedule h)
    {lo hi : ℕ} (hlo : 8 ≤ lo) (hlohi : lo ≤ hi)
    (hhir : hi ≤ longCount h)
    (hcut : CutoffConditions criticalP h lo hi) :
    adjacentTotalVariation
        (rankNormalized
          (fun n ↦ (relativeMassIncrement h n - betaLower) ^ 2)) lo hi ≤
      (288 * adjacentHarmonicWeight lo hi + 27) / (lo : ℝ) := by
  have hlo1 : 1 ≤ lo := by omega
  have hnorm := rankNormalized_totalVariation_le
    (x := fun n ↦ (relativeMassIncrement h n - betaLower) ^ 2)
    (B := 9) hlo1 hlohi (by norm_num)
    (fun n hn ↦ squareDeviation_cutoff_bound hcut hn)
  have hsq := squareDeviation_weightedVariation_le hcut
  have hv := adjacentWeightedVariation_le_total_div
    (x := relativeMassIncrement h) (hi := hi) hlo1
  have ht := relativeMassIncrement_totalVariation hh hlo hlohi hhir hcut
  have hvb : adjacentWeightedVariation (relativeMassIncrement h) lo hi ≤
      (48 * adjacentHarmonicWeight lo hi + 3) / (lo : ℝ) :=
    hv.trans (div_le_div_of_nonneg_right ht (by positivity))
  calc
    adjacentTotalVariation
        (rankNormalized
          (fun n ↦ (relativeMassIncrement h n - betaLower) ^ 2)) lo hi ≤
        adjacentWeightedVariation
            (fun n ↦ (relativeMassIncrement h n - betaLower) ^ 2) lo hi +
          9 / (lo : ℝ) := hnorm
    _ ≤ 6 * adjacentWeightedVariation (relativeMassIncrement h) lo hi +
          9 / (lo : ℝ) := add_le_add hsq le_rfl
    _ ≤ 6 * ((48 * adjacentHarmonicWeight lo hi + 3) / (lo : ℝ)) +
          9 / (lo : ℝ) := by
      exact add_le_add (mul_le_mul_of_nonneg_left hvb (by norm_num)) le_rfl
    _ = (288 * adjacentHarmonicWeight lo hi + 27) / (lo : ℝ) := by ring

/-- Fixed-dilation endpoint-defect sampling with an explicit vanishing error. -/
theorem endpointDefect_fixedDilationHarmonicSample
    {T Q : ℕ} (hQ : criticalTheta⁻¹ < (Q : ℝ))
    {h : StepSchedule T} (hh : IsNonnegativeSchedule h)
    {j M N : ℕ} (hj : 1 ≤ j) (hMN : M ≤ N)
    (hQlo : Q ≤ j * M) (hhir : j * N ≤ longCount h)
    (hcut : CutoffConditions criticalP h (j * M) (longCount h)) :
    ∑ m ∈ Finset.Ico (M + 1) (N + 1), endpointDefect h (j * m) / (m : ℝ) ≤
      ∑ n ∈ Finset.Ico (j * M + 1) (j * N + 1), endpointDefect h n / (n : ℝ) +
        j * ((104 * adjacentHarmonicWeight (j * M) (j * N) + 2) /
          ((j * M : ℕ) : ℝ)) := by
  have hs := fixedDilationHarmonicSample_le (endpointDefect h) hj hMN
  have hv := endpointDefect_rankNormalized_totalVariation
    hQ hh hQlo (Nat.mul_le_mul_left j hMN) hhir hcut
  have hj0 : 0 ≤ (j : ℝ) := by exact_mod_cast (Nat.zero_le j)
  exact hs.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left hv hj0))

/-- Fixed-dilation square-deviation sampling with an explicit vanishing
error. -/
theorem squareDeviation_fixedDilationHarmonicSample
    {T : ℕ} {h : StepSchedule T} (hh : IsNonnegativeSchedule h)
    {j M N : ℕ} (hj : 1 ≤ j) (hMN : M ≤ N)
    (hlo : 8 ≤ j * M) (hhir : j * N ≤ longCount h)
    (hcut : CutoffConditions criticalP h (j * M) (longCount h)) :
    ∑ m ∈ Finset.Ico (M + 1) (N + 1),
        (relativeMassIncrement h (j * m) - betaLower) ^ 2 / (m : ℝ) ≤
      ∑ n ∈ Finset.Ico (j * M + 1) (j * N + 1),
          (relativeMassIncrement h n - betaLower) ^ 2 / (n : ℝ) +
        j * ((288 * adjacentHarmonicWeight (j * M) (j * N) + 27) /
          ((j * M : ℕ) : ℝ)) := by
  have hs := fixedDilationHarmonicSample_le
    (fun n ↦ (relativeMassIncrement h n - betaLower) ^ 2) hj hMN
  have hcutSub : CutoffConditions criticalP h (j * M) (j * N) := by
    intro q hq
    have hqIcc := Finset.mem_Icc.mp hq
    exact hcut q (Finset.mem_Icc.mpr ⟨hqIcc.1, hqIcc.2.trans hhir⟩)
  have hv := squareDeviation_rankNormalized_totalVariation hh hlo
    (Nat.mul_le_mul_left j hMN) hhir hcutSub
  have hj0 : 0 ≤ (j : ℝ) := by exact_mod_cast (Nat.zero_le j)
  exact hs.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left hv hj0))

end

end GDLowerBound.FourBlock
