import GDLowerBound.FourBlock.CriticalLyapunov

/-!
# Finite block drift with explicit errors

This module replaces the note's `O(1/m)` block defect by an exact theorem.
It is deliberately sequence-level: the schedule-specific adjacent theorem
only has to supply `hstep`.
-/

namespace GDLowerBound.FourBlock

open scoped BigOperators

noncomputable section

private theorem sum_adjacent_sub (P : ℕ → ℝ) {lo hi : ℕ} (hlohi : lo ≤ hi) :
    ∑ n ∈ Finset.Ico (lo + 1) (hi + 1), (P (n - 1) - P n) =
      P lo - P hi := by
  induction hi, hlohi using Nat.le_induction with
  | base => simp
  | succ hi hlohi ih =>
      rw [Finset.sum_Ico_succ_top (by omega), ih]
      simp only [Nat.add_sub_cancel]
      ring

/-- The exact finite sum of the one-step Lyapunov inequalities. -/
theorem sum_finite_drift {P v : ℕ → ℝ} {lo hi : ℕ} (hlohi : lo ≤ hi)
    (C : ℝ)
    (hstep : ∀ n ∈ Finset.Ico (lo + 1) (hi + 1),
      P n - P (n - 1) ≤
        (betaLower - v n) / (n : ℝ) + C / (n : ℝ) ^ 2) :
    ∑ n ∈ Finset.Ico (lo + 1) (hi + 1),
        (v n - betaLower) / (n : ℝ) ≤
      P lo - P hi +
        C * ∑ n ∈ Finset.Ico (lo + 1) (hi + 1),
          1 / (n : ℝ) ^ 2 := by
  have hterm : ∀ n ∈ Finset.Ico (lo + 1) (hi + 1),
      (v n - betaLower) / (n : ℝ) ≤
        P (n - 1) - P n + C * (1 / (n : ℝ) ^ 2) := by
    intro n hn
    have hnNat : 0 < n := by
      have := (Finset.mem_Ico.mp hn).1
      omega
    have hnpos : 0 < (n : ℝ) := by exact_mod_cast hnNat
    have hs := hstep n hn
    rw [show C * (1 / (n : ℝ) ^ 2) = C / (n : ℝ) ^ 2 by ring]
    have hneg : (v n - betaLower) / (n : ℝ) =
        -(betaLower - v n) / (n : ℝ) := by ring
    rw [hneg]
    ring_nf at hs ⊢
    linarith
  calc
    ∑ n ∈ Finset.Ico (lo + 1) (hi + 1),
        (v n - betaLower) / (n : ℝ) ≤
      ∑ n ∈ Finset.Ico (lo + 1) (hi + 1),
        (P (n - 1) - P n + C * (1 / (n : ℝ) ^ 2)) :=
      Finset.sum_le_sum hterm
    _ = P lo - P hi +
        C * ∑ n ∈ Finset.Ico (lo + 1) (hi + 1),
          1 / (n : ℝ) ^ 2 := by
      rw [Finset.sum_add_distrib, sum_adjacent_sub P hlohi,
        Finset.mul_sum]

/-- Logarithmic block defect with the exact harmonic sum, before replacing
it by a dilation logarithm. -/
def finiteBlockDefect (v : ℕ → ℝ) (lo hi : ℕ) : ℝ :=
  betaLower * ∑ n ∈ Finset.Ico (lo + 1) (hi + 1), 1 / (n : ℝ) -
    ∑ n ∈ Finset.Ico (lo + 1) (hi + 1),
      Real.log (1 + v n / (n : ℝ))

theorem log_mass_increment_le {v : ℕ → ℝ} {lo hi : ℕ}
    (hv : ∀ n ∈ Finset.Ico (lo + 1) (hi + 1), 0 ≤ v n) :
    ∑ n ∈ Finset.Ico (lo + 1) (hi + 1),
        Real.log (1 + v n / (n : ℝ)) ≤
      ∑ n ∈ Finset.Ico (lo + 1) (hi + 1), v n / (n : ℝ) := by
  apply Finset.sum_le_sum
  intro n hn
  have hnNat : 0 < n := by
    have := (Finset.mem_Ico.mp hn).1
    omega
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast hnNat
  have hx : 0 < 1 + v n / (n : ℝ) := by
    have := hv n hn
    positivity
  have hlog := Real.log_le_sub_one_of_pos hx
  simpa using hlog

/-- Fully explicit block defect.  The right side is the finite reciprocal
square sum which was denoted only by `O(1/m)` in the paper draft. -/
theorem finiteBlockDefect_add_potential_lower
    {P v : ℕ → ℝ} {lo hi : ℕ} (hlohi : lo ≤ hi)
    (C : ℝ)
    (hv : ∀ n ∈ Finset.Ico (lo + 1) (hi + 1), 0 ≤ v n)
    (hstep : ∀ n ∈ Finset.Ico (lo + 1) (hi + 1),
      P n - P (n - 1) ≤
        (betaLower - v n) / (n : ℝ) + C / (n : ℝ) ^ 2) :
    finiteBlockDefect v lo hi + P lo - P hi ≥
      -C * ∑ n ∈ Finset.Ico (lo + 1) (hi + 1),
        1 / (n : ℝ) ^ 2 := by
  have hdrift := sum_finite_drift hlohi C hstep
  have hlog := log_mass_increment_le hv
  unfold finiteBlockDefect
  have hsplit :
      ∑ n ∈ Finset.Ico (lo + 1) (hi + 1),
          (v n - betaLower) / (n : ℝ) =
        (∑ n ∈ Finset.Ico (lo + 1) (hi + 1), v n / (n : ℝ)) -
          betaLower *
            ∑ n ∈ Finset.Ico (lo + 1) (hi + 1), 1 / (n : ℝ) := by
    simp_rw [sub_div]
    rw [Finset.sum_sub_distrib, Finset.mul_sum]
    ring
  rw [hsplit] at hdrift
  linarith

end

end GDLowerBound.FourBlock
