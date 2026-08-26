import GDLowerBound.FourBlock.FixedDilationApplications
import GDLowerBound.FourBlock.ScheduleBlockIdentity
import GDLowerBound.FourBlock.BlockDilation

/-!
# Upper bounds for finite dilation defects

The local theorem uses the dilation defects with positive coefficients, so
the averaging argument needs upper bounds.  This file expands each defect
into the middle-block mean deficit, its lower endpoint defect, and explicit
`O(1/lo)` errors.
-/

namespace GDLowerBound.FourBlock

open scoped BigOperators
open GDLowerBound.Schedule GDLowerBound.RankAnalysis

noncomputable section

private theorem sum_adjacent_difference_upper (x : ℕ → ℝ)
    {lo hi : ℕ} (hlohi : lo ≤ hi) :
    ∑ n ∈ Finset.Ico (lo + 1) (hi + 1),
        (x n - x (n - 1)) = x hi - x lo := by
  induction hi, hlohi using Nat.le_induction with
  | base => simp
  | succ hi hlohi ih =>
      rw [Finset.sum_Ico_succ_top (by omega), ih]
      simp only [Nat.add_sub_cancel]
      ring

/-- A convenient quadratic lower bound for `log (1+x)`. -/
theorem sub_half_sq_le_log_one_add {x : ℝ} (hx : 0 ≤ x) :
    x - x ^ 2 / 2 ≤ Real.log (1 + x) := by
  have hden : 0 < x + 2 := by linarith
  have hrational : x - x ^ 2 / 2 ≤ 2 * x / (x + 2) := by
    apply (le_div_iff₀ hden).2
    nlinarith [mul_nonneg (sq_nonneg x) hx]
  exact hrational.trans (Real.le_log_one_add_of_nonneg hx)

private theorem log_ratio_eq_sum_adjacent
    {lo hi : ℕ} (hlo : 1 ≤ lo) (hlohi : lo ≤ hi) :
    Real.log ((hi : ℝ) / (lo : ℝ)) =
      ∑ n ∈ Finset.Ico (lo + 1) (hi + 1),
        Real.log ((n : ℝ) / ((n - 1 : ℕ) : ℝ)) := by
  have hlo0 : (lo : ℝ) ≠ 0 := by positivity
  have hhi0 : (hi : ℝ) ≠ 0 := by
    exact_mod_cast (show hi ≠ 0 by omega)
  calc
    Real.log ((hi : ℝ) / (lo : ℝ)) =
        Real.log (hi : ℝ) - Real.log (lo : ℝ) := by
      rw [Real.log_div hhi0 hlo0]
    _ = ∑ n ∈ Finset.Ico (lo + 1) (hi + 1),
        (Real.log (n : ℝ) - Real.log ((n - 1 : ℕ) : ℝ)) := by
      rw [sum_adjacent_difference_upper (fun n ↦ Real.log (n : ℝ)) hlohi]
    _ = ∑ n ∈ Finset.Ico (lo + 1) (hi + 1),
        Real.log ((n : ℝ) / ((n - 1 : ℕ) : ℝ)) := by
      apply Finset.sum_congr rfl
      intro n hn
      have hnIco := Finset.mem_Ico.mp hn
      rw [Real.log_div
        (by exact_mod_cast (show n ≠ 0 by omega))
        (by exact_mod_cast (show n - 1 ≠ 0 by omega))]

private theorem adjacent_log_le_inv_prev
    {n : ℕ} (hn : 2 ≤ n) :
    Real.log ((n : ℝ) / ((n - 1 : ℕ) : ℝ)) ≤
      1 / ((n - 1 : ℕ) : ℝ) := by
  have hn0 : 0 < (n : ℝ) := by positivity
  have hp0 : 0 < ((n - 1 : ℕ) : ℝ) := by
    exact_mod_cast (show 0 < n - 1 by omega)
  have hlog := Real.log_le_sub_one_of_pos (div_pos hn0 hp0)
  have hid : (n : ℝ) / ((n - 1 : ℕ) : ℝ) - 1 =
      1 / ((n - 1 : ℕ) : ℝ) := by
    field_simp [ne_of_gt hp0]
    rw [Nat.cast_sub (by omega : 1 ≤ n)]
    ring
  rwa [hid] at hlog

private theorem sum_reciprocal_prev_eq
    {lo hi : ℕ} (hlo : 1 ≤ lo) (hlohi : lo ≤ hi) :
    ∑ n ∈ Finset.Ico (lo + 1) (hi + 1),
        1 / ((n - 1 : ℕ) : ℝ) =
      adjacentHarmonicWeight lo hi + 1 / (lo : ℝ) - 1 / (hi : ℝ) := by
  have hdiff :
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
        rw [sum_adjacent_difference_upper
          (fun n ↦ 1 / (n : ℝ)) hlohi]
      _ = 1 / (lo : ℝ) - 1 / (hi : ℝ) := by ring
  unfold adjacentHarmonicWeight
  calc
    ∑ n ∈ Finset.Ico (lo + 1) (hi + 1),
        1 / ((n - 1 : ℕ) : ℝ) =
      ∑ n ∈ Finset.Ico (lo + 1) (hi + 1),
        (1 / (n : ℝ) +
          (1 / ((n - 1 : ℕ) : ℝ) - 1 / (n : ℝ))) := by
        apply Finset.sum_congr rfl
        intro n _
        ring
    _ = (∑ n ∈ Finset.Ico (lo + 1) (hi + 1), 1 / (n : ℝ)) +
        (1 / (lo : ℝ) - 1 / (hi : ℝ)) := by
      rw [Finset.sum_add_distrib, hdiff]
    _ = (∑ n ∈ Finset.Ico (lo + 1) (hi + 1), 1 / (n : ℝ)) +
        1 / (lo : ℝ) - 1 / (hi : ℝ) := by ring

/-- The dilation logarithm exceeds its right-endpoint harmonic sum by at
most the reciprocal of the initial rank. -/
theorem log_ratio_le_adjacentHarmonic_add_inv
    {lo hi : ℕ} (hlo : 1 ≤ lo) (hlohi : lo ≤ hi) :
    Real.log ((hi : ℝ) / (lo : ℝ)) ≤
      adjacentHarmonicWeight lo hi + 1 / (lo : ℝ) := by
  have hterm : ∀ n ∈ Finset.Ico (lo + 1) (hi + 1),
      Real.log ((n : ℝ) / ((n - 1 : ℕ) : ℝ)) ≤
        1 / ((n - 1 : ℕ) : ℝ) := by
    intro n hn
    exact adjacent_log_le_inv_prev (by
      have hnIco := Finset.mem_Ico.mp hn
      omega)
  rw [log_ratio_eq_sum_adjacent hlo hlohi]
  have hsum := Finset.sum_le_sum hterm
  rw [sum_reciprocal_prev_eq hlo hlohi] at hsum
  have hhi : 0 ≤ 1 / (hi : ℝ) := by positivity
  linarith

/-- The exact finite block defect is controlled above by the mean deficit
plus a reciprocal-square remainder. -/
theorem finiteBlockDefect_upper
    {T : ℕ} {h : StepSchedule T} (hh : IsNonnegativeSchedule h)
    {lo hi : ℕ} (hlo : 1 ≤ lo) (hlohi : lo ≤ hi)
    (hhir : hi ≤ longCount h)
    (hcut : CutoffConditions criticalP h lo hi) :
    finiteBlockDefect (relativeMassIncrement h) lo hi ≤
      ∑ n ∈ Finset.Ico (lo + 1) (hi + 1),
          (betaLower - relativeMassIncrement h n) / (n : ℝ) +
        (9 / 2 : ℝ) *
          ∑ n ∈ Finset.Ico (lo + 1) (hi + 1), 1 / (n : ℝ) ^ 2 := by
  have hterm : ∀ n ∈ Finset.Ico (lo + 1) (hi + 1),
      betaLower / (n : ℝ) -
          Real.log (1 + relativeMassIncrement h n / (n : ℝ)) ≤
        (betaLower - relativeMassIncrement h n) / (n : ℝ) +
          (9 / 2 : ℝ) * (1 / (n : ℝ) ^ 2) := by
    intro n hn
    have hnIco := Finset.mem_Ico.mp hn
    have hnMem : n ∈ Finset.Icc lo hi :=
      Finset.mem_Icc.mpr ⟨by omega, by omega⟩
    obtain ⟨hv0, hv3⟩ := relativeMassIncrement_cutoff_bounds hcut hnMem
    have hn0 : 0 < (n : ℝ) := by
      exact_mod_cast (show 0 < n by omega)
    have hx0 : 0 ≤ relativeMassIncrement h n / (n : ℝ) := by positivity
    have hlog := sub_half_sq_le_log_one_add hx0
    have hvSq : (relativeMassIncrement h n) ^ 2 ≤ 9 := by
      have hp : 0 ≤ relativeMassIncrement h n *
          (3 - relativeMassIncrement h n) := mul_nonneg hv0.le (by linarith)
      nlinarith
    have herr :
        (relativeMassIncrement h n / (n : ℝ)) ^ 2 / 2 ≤
          (9 / 2 : ℝ) * (1 / (n : ℝ) ^ 2) := by
      have hnSq : 0 ≤ (n : ℝ) ^ 2 := sq_nonneg _
      field_simp [ne_of_gt hn0]
      nlinarith
    ring_nf at hlog herr ⊢
    linarith
  unfold finiteBlockDefect
  calc
    betaLower * ∑ n ∈ Finset.Ico (lo + 1) (hi + 1), 1 / (n : ℝ) -
        ∑ n ∈ Finset.Ico (lo + 1) (hi + 1),
          Real.log (1 + relativeMassIncrement h n / (n : ℝ)) =
      ∑ n ∈ Finset.Ico (lo + 1) (hi + 1),
        (betaLower / (n : ℝ) -
          Real.log (1 + relativeMassIncrement h n / (n : ℝ))) := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro n _
      ring
    _ ≤ ∑ n ∈ Finset.Ico (lo + 1) (hi + 1),
        ((betaLower - relativeMassIncrement h n) / (n : ℝ) +
          (9 / 2 : ℝ) * (1 / (n : ℝ) ^ 2)) := by
      exact Finset.sum_le_sum hterm
    _ = ∑ n ∈ Finset.Ico (lo + 1) (hi + 1),
          (betaLower - relativeMassIncrement h n) / (n : ℝ) +
        (9 / 2 : ℝ) *
          ∑ n ∈ Finset.Ico (lo + 1) (hi + 1), 1 / (n : ℝ) ^ 2 := by
      rw [Finset.sum_add_distrib, Finset.mul_sum]

/-- Upper bound for the dilation defect used by the local energy. -/
theorem dilationBlockH_upper
    {T : ℕ} {h : StepSchedule T} (hh : IsNonnegativeSchedule h)
    {lo hi : ℕ} (hlo : 1 ≤ lo) (hlohi : lo ≤ hi)
    (hhir : hi ≤ longCount h)
    (hcut : CutoffConditions criticalP h lo hi) :
    dilationBlockH h lo hi ≤
      ∑ n ∈ Finset.Ico (lo + 1) (hi + 1),
          (betaLower - relativeMassIncrement h n) / (n : ℝ) +
        betaLower * endpointDefect h lo + betaLower / (lo : ℝ) +
        (9 / 2 : ℝ) *
          ∑ n ∈ Finset.Ico (lo + 1) (hi + 1), 1 / (n : ℝ) ^ 2 := by
  have hfinite := finiteBlockDefect_upper hh hlo hlohi hhir hcut
  have hlog := log_ratio_le_adjacentHarmonic_add_inv hlo hlohi
  have hbeta := mul_le_mul_of_nonneg_left hlog betaLower_pos.le
  have hid :
      dilationBlockH h lo hi =
        finiteBlockDefect (relativeMassIncrement h) lo hi +
          betaLower *
            (Real.log ((hi : ℝ) / (lo : ℝ)) -
              adjacentHarmonicWeight lo hi) +
          betaLower * endpointDefect h lo := by
    rw [finiteBlockDefect_eq_log_mass_ratio hh hlohi hhir]
    unfold dilationBlockH adjacentHarmonicWeight
    ring
  have hgap :
      betaLower *
          (Real.log ((hi : ℝ) / (lo : ℝ)) -
            adjacentHarmonicWeight lo hi) ≤ betaLower / (lo : ℝ) := by
    calc
      betaLower *
          (Real.log ((hi : ℝ) / (lo : ℝ)) -
            adjacentHarmonicWeight lo hi) =
          betaLower * Real.log ((hi : ℝ) / (lo : ℝ)) -
            betaLower * adjacentHarmonicWeight lo hi := by ring
      _ ≤ betaLower *
            (adjacentHarmonicWeight lo hi + 1 / (lo : ℝ)) -
          betaLower * adjacentHarmonicWeight lo hi :=
        sub_le_sub_right hbeta _
      _ = betaLower / (lo : ℝ) := by ring
  rw [hid]
  calc
    finiteBlockDefect (relativeMassIncrement h) lo hi +
          betaLower *
            (Real.log ((hi : ℝ) / (lo : ℝ)) -
              adjacentHarmonicWeight lo hi) +
        betaLower * endpointDefect h lo ≤
      (∑ n ∈ Finset.Ico (lo + 1) (hi + 1),
          (betaLower - relativeMassIncrement h n) / (n : ℝ) +
        (9 / 2 : ℝ) *
          ∑ n ∈ Finset.Ico (lo + 1) (hi + 1), 1 / (n : ℝ) ^ 2) +
        betaLower / (lo : ℝ) + betaLower * endpointDefect h lo := by
      exact add_le_add (add_le_add hfinite hgap) le_rfl
    _ = ∑ n ∈ Finset.Ico (lo + 1) (hi + 1),
          (betaLower - relativeMassIncrement h n) / (n : ℝ) +
        betaLower * endpointDefect h lo + betaLower / (lo : ℝ) +
        (9 / 2 : ℝ) *
          ∑ n ∈ Finset.Ico (lo + 1) (hi + 1), 1 / (n : ℝ) ^ 2 := by
      ring

end

end GDLowerBound.FourBlock
