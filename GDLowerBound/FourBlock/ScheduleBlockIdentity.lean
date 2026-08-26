import GDLowerBound.FourBlock.BlockDefect

/-!
# Exact mass identities on a finite schedule block

This module identifies the logarithmic sum occurring in `finiteBlockDefect`
with the unresolved-mass ratio at the two endpoints.  It is the exact finite
counterpart of the block variable denoted `h_j` in the analytic note.
-/

namespace GDLowerBound.FourBlock

open scoped BigOperators
open GDLowerBound.Schedule GDLowerBound.RankAnalysis

noncomputable section

/-- The adjacent mass ratios telescope on every interior block. -/
theorem blockMassProduct
    {T : ℕ} {h : StepSchedule T} (hh : IsNonnegativeSchedule h)
    {lo hi : ℕ} (hlohi : lo ≤ hi) (hhir : hi ≤ longCount h) :
    unresolvedMass h lo / unresolvedMass h hi =
      ∏ n ∈ Finset.Ico (lo + 1) (hi + 1),
        (1 + relativeMassIncrement h n / (n : ℝ)) := by
  induction hi, hlohi using Nat.le_induction with
  | base =>
      simp [(unresolvedMass_pos hh lo).ne']
  | succ hi hlohi ih =>
      rw [Finset.prod_Ico_succ_top (by omega), ← ih (by omega)]
      have hratio := oneRankMassRatio hh (q := hi + 1)
        (by omega : 1 ≤ hi + 1) (by omega : hi + 1 ≤ longCount h)
      unfold massRatio at hratio
      simp only [Nat.add_sub_cancel] at hratio
      rw [← hratio]
      have hDlo := (unresolvedMass_pos hh lo).ne'
      have hDhi := (unresolvedMass_pos hh hi).ne'
      have hDnext := (unresolvedMass_pos hh (hi + 1)).ne'
      field_simp [hDlo, hDhi, hDnext]

/-- The logarithmic increment sum is exactly the logarithm of the endpoint
unresolved-mass ratio. -/
theorem sum_log_mass_increment_eq_log_ratio
    {T : ℕ} {h : StepSchedule T} (hh : IsNonnegativeSchedule h)
    {lo hi : ℕ} (hlohi : lo ≤ hi) (hhir : hi ≤ longCount h) :
    ∑ n ∈ Finset.Ico (lo + 1) (hi + 1),
        Real.log (1 + relativeMassIncrement h n / (n : ℝ)) =
      Real.log (unresolvedMass h lo / unresolvedMass h hi) := by
  have hfactor : ∀ n ∈ Finset.Ico (lo + 1) (hi + 1),
      1 + relativeMassIncrement h n / (n : ℝ) ≠ 0 := by
    intro n hn
    have hnIco := Finset.mem_Ico.mp hn
    have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    have hv := relativeMassIncrement_pos hh
      (q := n) (by omega) (by omega)
    positivity
  calc
    ∑ n ∈ Finset.Ico (lo + 1) (hi + 1),
        Real.log (1 + relativeMassIncrement h n / (n : ℝ)) =
        Real.log (∏ n ∈ Finset.Ico (lo + 1) (hi + 1),
          (1 + relativeMassIncrement h n / (n : ℝ))) :=
      (Real.log_prod hfactor).symm
    _ = Real.log (unresolvedMass h lo / unresolvedMass h hi) := by
      rw [← blockMassProduct hh hlohi hhir]

/-- Exact endpoint form of the finite block defect. -/
theorem finiteBlockDefect_eq_log_mass_ratio
    {T : ℕ} {h : StepSchedule T} (hh : IsNonnegativeSchedule h)
    {lo hi : ℕ} (hlohi : lo ≤ hi) (hhir : hi ≤ longCount h) :
    finiteBlockDefect (relativeMassIncrement h) lo hi =
      betaLower *
          ∑ n ∈ Finset.Ico (lo + 1) (hi + 1), 1 / (n : ℝ) -
        Real.log (unresolvedMass h lo / unresolvedMass h hi) := by
  unfold finiteBlockDefect
  rw [sum_log_mass_increment_eq_log_ratio hh hlohi hhir]

/-- The exact schedule quantity corresponding to the note's finite block
defect plus its lower-endpoint Lyapunov correction. -/
def scheduleBlockH {T : ℕ} (h : StepSchedule T) (lo hi : ℕ) : ℝ :=
  finiteBlockDefect (relativeMassIncrement h) lo hi +
    betaLower * endpointDefect h lo

theorem scheduleBlockH_eq
    {T : ℕ} {h : StepSchedule T} (hh : IsNonnegativeSchedule h)
    {lo hi : ℕ} (hlohi : lo ≤ hi) (hhir : hi ≤ longCount h) :
    scheduleBlockH h lo hi =
      betaLower *
          ∑ n ∈ Finset.Ico (lo + 1) (hi + 1), 1 / (n : ℝ) -
        Real.log (unresolvedMass h lo / unresolvedMass h hi) +
        betaLower * endpointDefect h lo := by
  unfold scheduleBlockH
  rw [finiteBlockDefect_eq_log_mass_ratio hh hlohi hhir]

theorem scheduleBlockH_lower
    {T Q : ℕ} (hQ : (criticalTheta)⁻¹ < (Q : ℝ))
    {h : StepSchedule T} (hh : IsNonnegativeSchedule h)
    {lo hi : ℕ} (hQlo : Q ≤ lo) (hlohi : lo ≤ hi)
    (hhir : hi ≤ longCount h)
    (hcut : CutoffConditions criticalP h lo (longCount h)) :
    scheduleBlockH h lo hi ≥
      -oneStepLyapunovConstant criticalP *
        ∑ n ∈ Finset.Ico (lo + 1) (hi + 1), 1 / (n : ℝ) ^ 2 := by
  exact scheduleFiniteBlockDefectTo hQ hh hQlo hlohi hhir hcut

end

end GDLowerBound.FourBlock
