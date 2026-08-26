import GDLowerBound.FourBlock.ScheduleCoordinatePerturbation

/-!
# Direct domination of the ideal matching by the augmented matching

Although the auxiliary vertex perturbs normalized coordinates, it is not
necessary to propagate that perturbation through the matching certificate.
The actual selected weights dominate the genuine ranked weights pointwise,
and the exact logarithmic kernel is coordinatewise monotone.  Hence the
matching functional at the exact reciprocal-prefix state is directly below
the actual augmented matching functional.
-/

namespace GDLowerBound.FourBlock

open scoped BigOperators
open GDLowerBound.Schedule GDLowerBound.RankAnalysis

noncomputable section

theorem finMean_mono {m : ℕ} (hm : 0 < m)
    {u v : Fin m → ℝ} (huv : ∀ i, u i ≤ v i) :
    finMean u ≤ finMean v := by
  unfold finMean
  apply div_le_div_of_nonneg_right _ (by positivity : (0 : ℝ) ≤ m)
  exact Finset.sum_le_sum fun i hi ↦ huv i

/-- The normalized four-block functional is monotone under pointwise
enlargement of the underlying positive weights. -/
theorem fourBlockMatching_mono_weights {m : ℕ} (hm : 0 < m)
    {x y : Fin (2 * (m + m)) → ℝ}
    (hx : ∀ i, 0 < x i) (hxy : ∀ i, x i ≤ y i) :
    fourBlockMatching (fourBlockZ x) (fourBlockA x)
        (fourBlockR x) (fourBlockS x) ≤
      fourBlockMatching (fourBlockZ y) (fourBlockA y)
        (fourBlockR y) (fourBlockS y) := by
  have hy : ∀ i, 0 < y i := fun i ↦ (hx i).trans_le (hxy i)
  have h1 := finMean_mono hm
    (u := outsideQuarterOne x) (v := outsideQuarterOne y) (fun i ↦ hxy _)
  have h2 := finMean_mono hm
    (u := outsideQuarterTwo x) (v := outsideQuarterTwo y) (fun i ↦ hxy _)
  have h3 := finMean_mono hm
    (u := outsideQuarterThree x) (v := outsideQuarterThree y) (fun i ↦ hxy _)
  have h4 := finMean_mono hm
    (u := outsideQuarterFour x) (v := outsideQuarterFour y) (fun i ↦ hxy _)
  have hx1 : 0 < finMean (outsideQuarterOne x) := by
    unfold finMean
    positivity [quarterSum_pos hm (outsideQuarterOne x) (fun i ↦ hx _)]
  have hx2 : 0 < finMean (outsideQuarterTwo x) := by
    unfold finMean
    positivity [quarterSum_pos hm (outsideQuarterTwo x) (fun i ↦ hx _)]
  have hx3 : 0 < finMean (outsideQuarterThree x) := by
    unfold finMean
    positivity [quarterSum_pos hm (outsideQuarterThree x) (fun i ↦ hx _)]
  have hx4 : 0 < finMean (outsideQuarterFour x) := by
    unfold finMean
    positivity [quarterSum_pos hm (outsideQuarterFour x) (fun i ↦ hx _)]
  have hout := logKernel_mono hx1.le hx4.le h1 h4 (by positivity)
  have hin := logKernel_mono hx2.le hx3.le h2 h3 (by positivity)
  rw [finMean_outsideQuarterOne_eq hm hx,
    finMean_outsideQuarterFour_eq hm hx,
    finMean_outsideQuarterOne_eq hm hy,
    finMean_outsideQuarterFour_eq hm hy] at hout
  rw [finMean_outsideQuarterTwo_eq hm hx,
    finMean_outsideQuarterThree_eq hm hx,
    finMean_outsideQuarterTwo_eq hm hy,
    finMean_outsideQuarterThree_eq hm hy] at hin
  unfold fourBlockMatching
  linarith

theorem rankedFourBlockZ_eq_zeta
    {T m : ℕ} (h : StepSchedule T) (hm : 0 < m) :
    fourBlockZ (rankedPathWeights (q := 2 * (m + m)) h) =
      zetaState h (2 * (m + m)) := by
  unfold fourBlockZ
  rw [rankedFourBlockTotal_eq h hm]
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  field_simp [hmR]

/-- The ideal reciprocal-prefix matching value is bounded by the actual
augmented four-block matching value, with no continuity error. -/
theorem scheduleIdealMatching_le_actualMatching
    {T m : ℕ} {h : StepSchedule T} (hh : IsNonnegativeSchedule h)
    (hm : 0 < m) (hq : 2 * (m + m) ≤ longCount h) :
    fourBlockMatching (zetaState h (2 * (m + m)))
        (schedulePrefixA h m) (schedulePrefixR h m) (schedulePrefixS h m) ≤
      fourBlockMatching
        (fourBlockZ (scheduleFourBlockWeights h hq))
        (fourBlockA (scheduleFourBlockWeights h hq))
        (fourBlockR (scheduleFourBlockWeights h hq))
        (fourBlockS (scheduleFourBlockWeights h hq)) := by
  have hmono := fourBlockMatching_mono_weights hm
    (rankedPathWeights_pos hh (by omega) hq)
    (rankedPathWeight_le_scheduleFourBlockWeight hh hm hq)
  rw [rankedFourBlockZ_eq_zeta h hm,
    rankedFourBlockA_eq_schedulePrefixA hh hm,
    rankedFourBlockR_eq_schedulePrefixR hh hm,
    rankedFourBlockS_eq_schedulePrefixS hh hm] at hmono
  exact hmono

end

end GDLowerBound.FourBlock
