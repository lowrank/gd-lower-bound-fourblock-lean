import GDLowerBound.FourBlock.FiniteWindowTerminalDyadic

/-!
# Finite prefix comparison for a dyadic window

When a four-block window starts just above the last small rank, only a
bounded number of adjacent mass ratios is skipped.  Every such ratio is at
most two under the cutoff conditions, yielding a schedule-independent
finite loss.
-/

namespace GDLowerBound.FourBlock

open GDLowerBound.Schedule GDLowerBound.RankAnalysis

noncomputable section

/-- Iterating the elementary one-rank bound over a cutoff interval. -/
theorem unresolvedMass_le_two_pow_gap_mul_of_cutoff
    {T Q : ℕ} {p : ℝ} {h : StepSchedule T}
    (hQ : (lyapunovTheta p)⁻¹ < (Q : ℝ))
    (hh : IsNonnegativeSchedule h)
    {k ell : ℕ} (hQk : Q ≤ k) (hkle : k ≤ ell)
    (hellr : ell ≤ longCount h)
    (hcut : CutoffConditions p h (k + 1) (longCount h)) :
    unresolvedMass h k ≤
      (2 : ℝ) ^ (ell - k) * unresolvedMass h ell := by
  induction ell, hkle using Nat.le_induction with
  | base => simp
  | succ ell hkle ih =>
      have hellr' : ell ≤ longCount h := by omega
      have hellOne : 1 ≤ ell + 1 := by omega
      have hmem : ell + 1 ∈ Finset.Icc (k + 1) (longCount h) :=
        Finset.mem_Icc.mpr ⟨by omega, hellr⟩
      have hnuB := (hcut (ell + 1) hmem).2.2.1
      have hQcast : (Q : ℝ) ≤ (ell + 1 : ℕ) := by
        exact_mod_cast (show Q ≤ ell + 1 by omega)
      have hnuRank :
          relativeMassIncrement h (ell + 1) < ((ell + 1 : ℕ) : ℝ) :=
        hnuB.trans (hQ.trans_le hQcast)
      have hratioEq := oneRankMassRatio hh (q := ell + 1)
        hellOne hellr
      have hratioEq' :
          unresolvedMass h ell / unresolvedMass h (ell + 1) =
            1 + relativeMassIncrement h (ell + 1) /
              ((ell + 1 : ℕ) : ℝ) := by
        simpa [massRatio] using hratioEq
      have hqR : (0 : ℝ) < (ell + 1 : ℕ) := by positivity
      have hratioLe :
          unresolvedMass h ell / unresolvedMass h (ell + 1) ≤ 2 := by
        rw [hratioEq']
        have hfrac :
            relativeMassIncrement h (ell + 1) /
                ((ell + 1 : ℕ) : ℝ) < 1 :=
          (div_lt_one hqR).2 hnuRank
        linarith
      have hnextPos := unresolvedMass_pos hh (ell + 1)
      have hone :
          unresolvedMass h ell ≤ 2 * unresolvedMass h (ell + 1) :=
        (div_le_iff₀ hnextPos).mp hratioLe
      have hpow :
          (2 : ℝ) ^ ((ell + 1) - k) =
            (2 : ℝ) ^ (ell - k) * 2 := by
        have hgap : (ell + 1) - k = (ell - k) + 1 := by omega
        rw [hgap, pow_succ]
      calc
        unresolvedMass h k ≤
            (2 : ℝ) ^ (ell - k) * unresolvedMass h ell := ih hellr'
        _ ≤ (2 : ℝ) ^ (ell - k) *
              (2 * unresolvedMass h (ell + 1)) := by
          exact mul_le_mul_of_nonneg_left hone (by positivity)
        _ = (2 : ℝ) ^ ((ell + 1) - k) *
              unresolvedMass h (ell + 1) := by rw [hpow]; ring

end

end GDLowerBound.FourBlock
