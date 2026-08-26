import GDLowerBound.FourBlock.FiniteDrift
import GDLowerBound.RankAnalysis.Boundary
import GDLowerBound.RankAnalysis.Density

/-! # Schedule-level finite four-block drift -/

namespace GDLowerBound.FourBlock

open scoped BigOperators
open GDLowerBound.Schedule GDLowerBound.RankAnalysis

noncomputable section

def scheduleCriticalPotential {T : ℕ} (h : StepSchedule T) (q : ℕ) : ℝ :=
  criticalPotential (relativeMassIncrement h q) (zetaState h q)

def endpointDefect {T : ℕ} (h : StepSchedule T) (q : ℕ) : ℝ :=
  relativeMassIncrement h q * (zetaState h q - criticalTheta)

/-- The schedule identities discharge every scalar hypothesis of the exact
critical one-step theorem. -/
theorem scheduleCriticalOneStep
    {T Q : ℕ} (hQ : (criticalTheta)⁻¹ < (Q : ℝ))
    {h : StepSchedule T} (hh : IsNonnegativeSchedule h)
    {ell n : ℕ} (hQell : Q ≤ ell)
    (hcut : CutoffConditions criticalP h ell (longCount h))
    (hn : n ∈ Finset.Ico (ell + 1) (longCount h + 1)) :
    scheduleCriticalPotential h n - scheduleCriticalPotential h (n - 1) ≤
      (betaLower - relativeMassIncrement h n) / (n : ℝ) +
        oneStepLyapunovConstant criticalP / (n : ℝ) ^ 2 := by
  have hnIco := Finset.mem_Ico.mp hn
  have hthetaInv0 : 0 < (criticalTheta)⁻¹ := inv_pos.mpr criticalTheta_pos
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
  have hthetaInv : (criticalTheta)⁻¹ = criticalP ^ 2 - 1 := by
    unfold criticalTheta
    exact lyapunovTheta_inv criticalP
  have hN : criticalP ^ 2 - 1 < (n : ℝ) - 1 := by
    rw [← hthetaInv]
    have hQcast : (Q : ℝ) ≤ (n - 1 : ℕ) := by
      exact_mod_cast (by omega : Q ≤ n - 1)
    exact hQ.trans_le (hQcast.trans_eq hnR)
  have hsmall :
      relativeMassIncrement h (n - 1) < ((n - 1 : ℕ) : ℝ) := by
    have hQcast : (Q : ℝ) ≤ (n - 1 : ℕ) := by
      exact_mod_cast (by omega : Q ≤ n - 1)
    exact huB.trans (hQ.trans_le hQcast)
  have hmass := massIncrementBound hh hnprev0 hnprev_lt hsmall
  have hzrec := zetaRecursion hh hnprev0 hnprev_lt
  have hnSucc : n - 1 + 1 = n := Nat.sub_add_cancel (by omega : 1 ≤ n)
  rw [hnSucc] at hmass hzrec
  have hzNext :
      zetaState h n =
        lyapunovOmega (n : ℝ) (relativeMassIncrement h n) *
            zetaState h (n - 1) +
          1 / ((n : ℝ) * relativeMassIncrement h n) := by
    simpa [lyapunovOmega, hnR, div_eq_mul_inv, mul_assoc, mul_left_comm,
      mul_comm] using hzrec
  unfold scheduleCriticalPotential
  apply criticalOneStep (by omega : 2 ≤ n) hN
  · exact hu0
  · simpa only [lyapunovTheta_inv] using huB.le
  · exact hv0
  · simpa only [lyapunovTheta_inv] using hvB.le
  · simpa only [criticalTheta] using hzPrev.le
  · simpa [hnR] using hmass
  · exact hzNext

theorem scheduleCriticalPotential_nonneg
    {T : ℕ} {h : StepSchedule T} {q : ℕ}
    (hnu : 0 ≤ relativeMassIncrement h q)
    (hzeta : criticalTheta ≤ zetaState h q) :
    0 ≤ scheduleCriticalPotential h q := by
  unfold scheduleCriticalPotential
  rw [criticalPotential_formula]
  have hden : 0 < criticalTheta *
      (relativeMassIncrement h q + betaLower + 2) := by
    have : 0 < relativeMassIncrement h q + betaLower + 2 := by
      linarith [betaLower_pos]
    positivity [criticalTheta_pos]
  positivity

theorem scheduleCriticalPotential_le_endpointDefect
    {T : ℕ} {h : StepSchedule T} {q : ℕ}
    (hnu : 0 ≤ relativeMassIncrement h q)
    (hzeta : criticalTheta ≤ zetaState h q) :
    scheduleCriticalPotential h q ≤ betaLower * endpointDefect h q := by
  unfold scheduleCriticalPotential endpointDefect
  rw [criticalPotential_formula]
  have hsum : 0 < relativeMassIncrement h q + betaLower + 2 := by
    linarith [betaLower_pos]
  have hden : 0 < criticalTheta *
      (relativeMassIncrement h q + betaLower + 2) :=
    mul_pos criticalTheta_pos hsum
  have hcoeff :
      1 / (criticalTheta *
          (relativeMassIncrement h q + betaLower + 2)) ≤ betaLower := by
    rw [div_le_iff₀ hden]
    have hid := critical_identity
    nlinarith [mul_nonneg criticalTheta_pos.le
      (mul_nonneg betaLower_pos.le hnu)]
  have hfactor :
      0 ≤ relativeMassIncrement h q *
        (zetaState h q - criticalTheta) :=
    mul_nonneg hnu (sub_nonneg.mpr hzeta)
  calc
    relativeMassIncrement h q /
          (criticalTheta *
            (relativeMassIncrement h q + betaLower + 2)) *
          (zetaState h q - criticalTheta) =
        (1 / (criticalTheta *
            (relativeMassIncrement h q + betaLower + 2))) *
          (relativeMassIncrement h q *
            (zetaState h q - criticalTheta)) := by ring
    _ ≤ betaLower *
          (relativeMassIncrement h q *
            (zetaState h q - criticalTheta)) :=
      mul_le_mul_of_nonneg_right hcoeff hfactor

/-- Exact schedule block defect, with all finite-rank error exposed. -/
theorem scheduleFiniteBlockDefect
    {T Q : ℕ} (hQ : (criticalTheta)⁻¹ < (Q : ℝ))
    {h : StepSchedule T} (hh : IsNonnegativeSchedule h)
    {ell : ℕ} (hQell : Q ≤ ell) (hellr : ell ≤ longCount h)
    (hcut : CutoffConditions criticalP h ell (longCount h)) :
    finiteBlockDefect (relativeMassIncrement h) ell (longCount h) +
        betaLower * endpointDefect h ell ≥
      -oneStepLyapunovConstant criticalP *
        ∑ n ∈ Finset.Ico (ell + 1) (longCount h + 1),
          1 / (n : ℝ) ^ 2 := by
  let P : ℕ → ℝ := scheduleCriticalPotential h
  let v : ℕ → ℝ := relativeMassIncrement h
  have hstep : ∀ n ∈ Finset.Ico (ell + 1) (longCount h + 1),
      P n - P (n - 1) ≤
        (betaLower - v n) / (n : ℝ) +
          oneStepLyapunovConstant criticalP / (n : ℝ) ^ 2 := by
    intro n hn
    exact scheduleCriticalOneStep hQ hh hQell hcut hn
  have hv : ∀ n ∈ Finset.Ico (ell + 1) (longCount h + 1), 0 ≤ v n := by
    intro n hn
    have hnIco := Finset.mem_Ico.mp hn
    exact (relativeMassIncrement_pos hh (by omega) (by omega)).le
  have hfinite := finiteBlockDefect_add_potential_lower
    hellr (oneStepLyapunovConstant criticalP) hv hstep
  have hellMem : ell ∈ Finset.Icc ell (longCount h) :=
    Finset.mem_Icc.mpr ⟨le_rfl, hellr⟩
  obtain ⟨hzell, hnuell, _, _⟩ := hcut ell hellMem
  have hrMem : longCount h ∈ Finset.Icc ell (longCount h) :=
    Finset.mem_Icc.mpr ⟨hellr, le_rfl⟩
  obtain ⟨hzr, hnur, _, _⟩ := hcut (longCount h) hrMem
  have hPell := scheduleCriticalPotential_le_endpointDefect hnuell.le hzell.le
  have hPr := scheduleCriticalPotential_nonneg hnur.le hzr.le
  dsimp only [P, v] at hfinite ⊢
  linarith

end

end GDLowerBound.FourBlock
