import GDLowerBound.FourBlock.ScheduleDrift

/-! # Exact finite defect on an arbitrary interior block -/

namespace GDLowerBound.FourBlock

open scoped BigOperators
open GDLowerBound.Schedule GDLowerBound.RankAnalysis

noncomputable section

theorem scheduleFiniteBlockDefectTo
    {T Q : ℕ} (hQ : (criticalTheta)⁻¹ < (Q : ℝ))
    {h : StepSchedule T} (hh : IsNonnegativeSchedule h)
    {ell hi : ℕ} (hQell : Q ≤ ell) (hellhi : ell ≤ hi)
    (hhir : hi ≤ longCount h)
    (hcut : CutoffConditions criticalP h ell (longCount h)) :
    finiteBlockDefect (relativeMassIncrement h) ell hi +
        betaLower * endpointDefect h ell ≥
      -oneStepLyapunovConstant criticalP *
        ∑ n ∈ Finset.Ico (ell + 1) (hi + 1), 1 / (n : ℝ) ^ 2 := by
  let P : ℕ → ℝ := scheduleCriticalPotential h
  let v : ℕ → ℝ := relativeMassIncrement h
  have hstep : ∀ n ∈ Finset.Ico (ell + 1) (hi + 1),
      P n - P (n - 1) ≤
        (betaLower - v n) / (n : ℝ) +
          oneStepLyapunovConstant criticalP / (n : ℝ) ^ 2 := by
    intro n hn
    have hnIco := Finset.mem_Ico.mp hn
    have hnFull : n ∈ Finset.Ico (ell + 1) (longCount h + 1) :=
      Finset.mem_Ico.mpr ⟨hnIco.1, by omega⟩
    exact scheduleCriticalOneStep hQ hh hQell hcut hnFull
  have hv : ∀ n ∈ Finset.Ico (ell + 1) (hi + 1), 0 ≤ v n := by
    intro n hn
    have hnIco := Finset.mem_Ico.mp hn
    exact (relativeMassIncrement_pos hh (by omega) (by omega)).le
  have hfinite := finiteBlockDefect_add_potential_lower
    hellhi (oneStepLyapunovConstant criticalP) hv hstep
  have hellMem : ell ∈ Finset.Icc ell (longCount h) :=
    Finset.mem_Icc.mpr ⟨le_rfl, hellhi.trans hhir⟩
  obtain ⟨hzell, hnuell, _, _⟩ := hcut ell hellMem
  have hiMem : hi ∈ Finset.Icc ell (longCount h) :=
    Finset.mem_Icc.mpr ⟨hellhi, hhir⟩
  obtain ⟨hzhi, hnuhi, _, _⟩ := hcut hi hiMem
  have hPell := scheduleCriticalPotential_le_endpointDefect hnuell.le hzell.le
  have hPhi := scheduleCriticalPotential_nonneg hnuhi.le hzhi.le
  dsimp only [P, v] at hfinite ⊢
  linarith

/- The explicit error above tends to zero on fixed-dilation blocks; a separate
comparison lemma can sharpen it to `C / ell` when needed by the final cutoff. -/

end

end GDLowerBound.FourBlock
