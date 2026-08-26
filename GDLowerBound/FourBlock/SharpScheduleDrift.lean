import GDLowerBound.FourBlock.SharpFiniteDrift
import GDLowerBound.FourBlock.ScheduleDrift

/-! # Schedule-level defect-weighted drift and finite rigidity budget -/

namespace GDLowerBound.FourBlock

open scoped BigOperators
open GDLowerBound.Schedule GDLowerBound.RankAnalysis

noncomputable section

/-- The schedule identities discharge the hypotheses of the sharpened
one-step scalar theorem. -/
theorem scheduleCriticalOneStepSharp
    {T Q : ℕ} (hQ : criticalTheta⁻¹ < (Q : ℝ))
    {h : StepSchedule T} (hh : IsNonnegativeSchedule h)
    {ell n : ℕ} (hQell : Q ≤ ell)
    (hcut : CutoffConditions criticalP h ell (longCount h))
    (hn : n ∈ Finset.Ico (ell + 1) (longCount h + 1)) :
    scheduleCriticalPotential h n - scheduleCriticalPotential h (n - 1) ≤
      (betaLower - relativeMassIncrement h n -
          betaLower * endpointDefect h n) / (n : ℝ) +
        sharpDriftConstant / (n : ℝ) ^ 2 := by
  have hnIco := Finset.mem_Ico.mp hn
  have hthetaInv0 : 0 < criticalTheta⁻¹ := inv_pos.mpr criticalTheta_pos
  have hQR0 : 0 < (Q : ℝ) := hthetaInv0.trans hQ
  have hQnat : 1 ≤ Q := by exact_mod_cast hQR0
  have hn_le : n ≤ longCount h := by omega
  have hnprev0 : 1 ≤ n - 1 := by omega
  have hnprev_lt : n - 1 < longCount h := by omega
  have hnprev_mem : n - 1 ∈ Finset.Icc ell (longCount h) :=
    Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  have hn_mem : n ∈ Finset.Icc ell (longCount h) :=
    Finset.mem_Icc.mpr ⟨by omega, hn_le⟩
  obtain ⟨hzPrev, hu0, huB, _⟩ := hcut (n - 1) hnprev_mem
  obtain ⟨_, hv0, hvB, _⟩ := hcut n hn_mem
  have hnR : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ n)]
    norm_num
  have hthetaInv : criticalTheta⁻¹ = criticalP ^ 2 - 1 := by
    unfold criticalTheta
    exact lyapunovTheta_inv criticalP
  have hN : criticalP ^ 2 - 1 < (n : ℝ) - 1 := by
    rw [← hthetaInv]
    have hQcast : (Q : ℝ) ≤ (n - 1 : ℕ) := by
      exact_mod_cast (by omega : Q ≤ n - 1)
    exact hQ.trans_le (hQcast.trans_eq hnR)
  have hsmall : relativeMassIncrement h (n - 1) < ((n - 1 : ℕ) : ℝ) := by
    have hQcast : (Q : ℝ) ≤ (n - 1 : ℕ) := by
      exact_mod_cast (by omega : Q ≤ n - 1)
    exact huB.trans (hQ.trans_le hQcast)
  have hmass := massIncrementBound hh hnprev0 hnprev_lt hsmall
  have hzrec := zetaRecursion hh hnprev0 hnprev_lt
  have hnSucc : n - 1 + 1 = n := Nat.sub_add_cancel (by omega : 1 ≤ n)
  rw [hnSucc] at hmass hzrec
  have hzNext : zetaState h n =
      lyapunovOmega (n : ℝ) (relativeMassIncrement h n) *
          zetaState h (n - 1) +
        1 / ((n : ℝ) * relativeMassIncrement h n) := by
    simpa [lyapunovOmega, hnR, div_eq_mul_inv, mul_assoc, mul_left_comm,
      mul_comm] using hzrec
  unfold scheduleCriticalPotential endpointDefect
  have hs := criticalOneStepSharp (by omega : 2 ≤ n) hN hu0
    (by simpa only [lyapunovTheta_inv] using huB.le) hv0
    (by simpa only [lyapunovTheta_inv] using hvB.le)
    (by simpa only [criticalTheta] using hzPrev.le)
    (by simpa [hnR] using hmass) hzNext
  simpa only [mul_assoc] using hs

private theorem sum_adjacent_sub_sharp (P : ℕ → ℝ)
    {lo hi : ℕ} (hlohi : lo ≤ hi) :
    ∑ n ∈ Finset.Ico (lo + 1) (hi + 1), (P (n - 1) - P n) =
      P lo - P hi := by
  induction hi, hlohi using Nat.le_induction with
  | base => simp
  | succ hi hlohi ih =>
      rw [Finset.sum_Ico_succ_top (by omega), ih]
      simp only [Nat.add_sub_cancel]
      ring

/-- Telescoped finite rigidity budget retaining the endpoint defect. -/
theorem sum_sharp_drift
    {P v e : ℕ → ℝ} {lo hi : ℕ} (hlohi : lo ≤ hi)
    (C : ℝ)
    (hstep : ∀ n ∈ Finset.Ico (lo + 1) (hi + 1),
      P n - P (n - 1) ≤
        (betaLower - v n - betaLower * e n) / (n : ℝ) +
          C / (n : ℝ) ^ 2) :
    ∑ n ∈ Finset.Ico (lo + 1) (hi + 1),
        ((v n - betaLower) + betaLower * e n) / (n : ℝ) ≤
      P lo - P hi +
        C * ∑ n ∈ Finset.Ico (lo + 1) (hi + 1),
          1 / (n : ℝ) ^ 2 := by
  have hterm : ∀ n ∈ Finset.Ico (lo + 1) (hi + 1),
      ((v n - betaLower) + betaLower * e n) / (n : ℝ) ≤
        P (n - 1) - P n + C * (1 / (n : ℝ) ^ 2) := by
    intro n hn
    have hn0 : 0 < (n : ℝ) := by
      exact_mod_cast (show 0 < n by have := (Finset.mem_Ico.mp hn).1; omega)
    have hs := hstep n hn
    rw [show C * (1 / (n : ℝ) ^ 2) = C / (n : ℝ) ^ 2 by ring]
    ring_nf at hs ⊢
    linarith
  calc
    ∑ n ∈ Finset.Ico (lo + 1) (hi + 1),
        ((v n - betaLower) + betaLower * e n) / (n : ℝ) ≤
      ∑ n ∈ Finset.Ico (lo + 1) (hi + 1),
        (P (n - 1) - P n + C * (1 / (n : ℝ) ^ 2)) :=
      Finset.sum_le_sum hterm
    _ = P lo - P hi + C *
        ∑ n ∈ Finset.Ico (lo + 1) (hi + 1),
          1 / (n : ℝ) ^ 2 := by
      rw [Finset.sum_add_distrib, sum_adjacent_sub_sharp P hlohi,
        Finset.mul_sum]

/-- Schedule-specialized finite defect budget. -/
theorem scheduleSharpRigidityBudget
    {T Q : ℕ} (hQ : criticalTheta⁻¹ < (Q : ℝ))
    {h : StepSchedule T} (hh : IsNonnegativeSchedule h)
    {lo hi : ℕ} (hQlo : Q ≤ lo) (hlohi : lo ≤ hi)
    (hhir : hi ≤ longCount h)
    (hcut : CutoffConditions criticalP h lo (longCount h)) :
    ∑ n ∈ Finset.Ico (lo + 1) (hi + 1),
        ((relativeMassIncrement h n - betaLower) +
          betaLower * endpointDefect h n) / (n : ℝ) ≤
      scheduleCriticalPotential h lo - scheduleCriticalPotential h hi +
        sharpDriftConstant *
          ∑ n ∈ Finset.Ico (lo + 1) (hi + 1),
            1 / (n : ℝ) ^ 2 := by
  apply sum_sharp_drift hlohi sharpDriftConstant
  intro n hn
  have hnFull : n ∈ Finset.Ico (lo + 1) (longCount h + 1) := by
    have hnIco := Finset.mem_Ico.mp hn
    exact Finset.mem_Ico.mpr ⟨hnIco.1, by omega⟩
  exact scheduleCriticalOneStepSharp hQ hh hQlo hcut hnFull

end

end GDLowerBound.FourBlock
