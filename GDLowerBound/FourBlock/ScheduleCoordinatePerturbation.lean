import GDLowerBound.FourBlock.CoordinateScaling

/-!
# Explicit auxiliary-vertex perturbation of four-block coordinates

The augmented endpoint path has one extra vertex of weight `1/(4m-1)`.
Interlacing shows that sorting and removing the least augmented entry only
increases the genuine rank-ordered weights.  Since the total added mass is
at most that single auxiliary weight, all three normalized cumulative
coordinates differ from the reciprocal-prefix coordinates by an explicit
`O(m⁻²)` quantity.
-/

namespace GDLowerBound.FourBlock

open scoped BigOperators
open GDLowerBound.Schedule GDLowerBound.RankAnalysis GDLowerBound.Matching

noncomputable section

/-- A general algebraic estimate for normalized cumulative masses. -/
theorem normalized_ratio_abs_le
    {X Y C D e : ℝ}
    (hX : 0 < X) (hXY : X ≤ Y) (hYe : Y ≤ X + e)
    (hC0 : 0 ≤ C) (hCX : C ≤ X)
    (hCD : C ≤ D) (hDe : D ≤ C + e) (he : 0 ≤ e) :
    |D / Y - C / X| ≤ e / X := by
  have hY : 0 < Y := hX.trans_le hXY
  rw [abs_le]
  constructor
  · rw [neg_le_sub_iff_le_add]
    have hdiff : 0 ≤ Y - X := sub_nonneg.mpr hXY
    have hdiffE : Y - X ≤ e := by linarith
    have hCY : C * (Y - X) ≤ Y * e := by
      calc
        C * (Y - X) ≤ Y * (Y - X) := by
          exact mul_le_mul_of_nonneg_right (hCX.trans hXY) hdiff
        _ ≤ Y * e := mul_le_mul_of_nonneg_left hdiffE hY.le
    have hDX : C * X ≤ D * X :=
      mul_le_mul_of_nonneg_right hCD hX.le
    field_simp [hX.ne', hY.ne']
    nlinarith
  · have hDX : D * X ≤ (C + e) * X :=
      mul_le_mul_of_nonneg_right hDe hX.le
    have hCY : C * X ≤ C * Y :=
      mul_le_mul_of_nonneg_left hXY hC0
    have heY : e * X ≤ e * Y :=
      mul_le_mul_of_nonneg_left hXY he
    field_simp [hX.ne', hY.ne']
    nlinarith

/-- Pointwise enlargement by total mass at most `e` moves each normalized
cumulative four-block coordinate by at most `e / total`. -/
theorem fourBlockCoordinates_abs_le_of_pointwise
    {m : ℕ} (hm : 0 < m)
    {x y : Fin (2 * (m + m)) → ℝ} {e : ℝ}
    (hx : ∀ i, 0 < x i) (hxy : ∀ i, x i ≤ y i)
    (hYe : fourBlockTotal y ≤ fourBlockTotal x + e) (he : 0 ≤ e) :
    |fourBlockA y - fourBlockA x| ≤ e / fourBlockTotal x ∧
      |fourBlockR y - fourBlockR x| ≤ e / fourBlockTotal x ∧
      |fourBlockS y - fourBlockS x| ≤ e / fourBlockTotal x := by
  have hy : ∀ i, 0 < y i := fun i ↦ (hx i).trans_le (hxy i)
  have hX := fourBlockTotal_pos hm hx
  have h1 : quarterSumOne x ≤ quarterSumOne y := by
    apply Finset.sum_le_sum
    intro i hi
    exact hxy _
  have h2 : quarterSumTwo x ≤ quarterSumTwo y := by
    apply Finset.sum_le_sum
    intro i hi
    exact hxy _
  have h3 : quarterSumThree x ≤ quarterSumThree y := by
    apply Finset.sum_le_sum
    intro i hi
    exact hxy _
  have h4 : quarterSumFour x ≤ quarterSumFour y := by
    apply Finset.sum_le_sum
    intro i hi
    exact hxy _
  have hXY : fourBlockTotal x ≤ fourBlockTotal y := by
    unfold fourBlockTotal
    linarith
  have h1x : 0 ≤ quarterSumOne x := by
    apply Finset.sum_nonneg
    intro i hi
    exact (hx _).le
  have h2x : 0 ≤ quarterSumTwo x := by
    apply Finset.sum_nonneg
    intro i hi
    exact (hx _).le
  have h3x : 0 ≤ quarterSumThree x := by
    apply Finset.sum_nonneg
    intro i hi
    exact (hx _).le
  have h4x : 0 ≤ quarterSumFour x := by
    apply Finset.sum_nonneg
    intro i hi
    exact (hx _).le
  have h1e : quarterSumOne y ≤ quarterSumOne x + e := by
    unfold fourBlockTotal at hYe
    linarith
  have h12e : quarterSumOne y + quarterSumTwo y ≤
      quarterSumOne x + quarterSumTwo x + e := by
    unfold fourBlockTotal at hYe
    linarith
  have h123e : quarterSumOne y + quarterSumTwo y + quarterSumThree y ≤
      quarterSumOne x + quarterSumTwo x + quarterSumThree x + e := by
    unfold fourBlockTotal at hYe
    linarith
  constructor
  · unfold fourBlockA
    apply normalized_ratio_abs_le hX hXY hYe h1x
    · unfold fourBlockTotal
      linarith
    · exact h1
    · exact h1e
    · exact he
  constructor
  · unfold fourBlockR
    apply normalized_ratio_abs_le hX hXY hYe
      (by linarith : 0 ≤ quarterSumOne x + quarterSumTwo x)
    · unfold fourBlockTotal
      linarith
    · linarith
    · exact h12e
    · exact he
  · unfold fourBlockS
    apply normalized_ratio_abs_le hX hXY hYe
      (by linarith :
        0 ≤ quarterSumOne x + quarterSumTwo x + quarterSumThree x)
    · unfold fourBlockTotal
      linarith
    · linarith
    · exact h123e
    · exact he

theorem rankedPathWeights_pos
    {T q : ℕ} {h : StepSchedule T} (hh : IsNonnegativeSchedule h)
    (hq0 : 0 < q) (hq : q ≤ longCount h) :
    ∀ i, 0 < rankedPathWeights (q := q) h i := by
  intro i
  unfold rankedPathWeights
  positivity [unresolvedMass_pos hh q,
    rankedExcessOne_pos h (q := i.val + 1) (by omega) (by omega)]

theorem rankedPathWeights_sum
    {T q : ℕ} (h : StepSchedule T) (hq0 : 0 < q) :
    (∑ i, rankedPathWeights (q := q) h i) =
      2 * q * zetaState h q := by
  unfold rankedPathWeights zetaState reciprocalPrefix
  rw [← Finset.mul_sum]
  rw [Fin.sum_univ_eq_sum_range
    (fun i : ℕ ↦ (rankedExcessOne h (i + 1))⁻¹) q]
  have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast hq0.ne'
  field_simp [hqR]

/-- Every selected augmented weight is at least the corresponding genuine
ranked path weight. -/
theorem rankedPathWeight_le_scheduleFourBlockWeight
    {T m : ℕ} {h : StepSchedule T} (hh : IsNonnegativeSchedule h)
    (hm : 0 < m) (hq : 2 * (m + m) ≤ longCount h)
    (i : Fin (2 * (m + m))) :
    rankedPathWeights (q := 2 * (m + m)) h i ≤
      scheduleFourBlockWeights h hq i := by
  have hinter := sortedWeight_castSucc_le_sortedNearTail
    (v := topPathWeight h (2 * (m + m)) hq) i
  change sortedWeight (topPathInternalWeights h hq) i ≤
    scheduleFourBlockWeights h hq i at hinter
  rw [sortedWeight_topPathInternalWeights_eq_rankedPathWeights
    hh (by omega) hq] at hinter
  exact hinter

theorem rankedFourBlockTotal_eq
    {T m : ℕ} (h : StepSchedule T) (hm : 0 < m) :
    fourBlockTotal (rankedPathWeights (q := 2 * (m + m)) h) =
      8 * m * zetaState h (2 * (m + m)) := by
  rw [fourBlockTotal_eq_sum, rankedPathWeights_sum h (by omega)]
  let z := zetaState h (2 * (m + m))
  change 2 * ((2 * (m + m) : ℕ) : ℝ) * z = 8 * (m : ℝ) * z
  norm_num only [Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat]
  ring

theorem scheduleFourBlockTotal_le_ranked_add_aux
    {T m : ℕ} {h : StepSchedule T} (hh : IsNonnegativeSchedule h)
    (hm : 0 < m) (hq : 2 * (m + m) ≤ longCount h) :
    fourBlockTotal (scheduleFourBlockWeights h hq) ≤
      fourBlockTotal (rankedPathWeights (q := 2 * (m + m)) h) +
        1 / ((2 * (m + m) : ℝ) - 1) := by
  rw [rankedFourBlockTotal_eq h hm]
  have htotal := fourBlockTotal_sortedNearTail_le_topPathTotal hh hm hq
  have hcoeff : 2 * (2 * ((m : ℝ) + m)) = 8 * (m : ℝ) := by ring
  rw [hcoeff] at htotal
  simpa only [scheduleFourBlockWeights] using htotal

theorem rankedFourBlockA_eq_schedulePrefixA
    {T m : ℕ} {h : StepSchedule T} (hh : IsNonnegativeSchedule h)
    (hm : 0 < m) :
    fourBlockA (rankedPathWeights (q := 2 * (m + m)) h) =
      schedulePrefixA h m := by
  let c : ℝ := 2 * unresolvedMass h (2 * (m + m)) /
    (2 * (m + m) : ℕ)
  have hc : c ≠ 0 := by
    dsimp only [c]
    positivity [unresolvedMass_pos hh (2 * (m + m))]
  calc
    fourBlockA (rankedPathWeights (q := 2 * (m + m)) h) =
        fourBlockA (fun i ↦ c * idealReciprocalWeights h m i) := by
      rw [rankedPathWeights_fourBlock_eq]
    _ = fourBlockA (idealReciprocalWeights h m) := fourBlockA_scale hc _
    _ = schedulePrefixA h m := idealFourBlockA_eq_schedulePrefixA h

theorem rankedFourBlockR_eq_schedulePrefixR
    {T m : ℕ} {h : StepSchedule T} (hh : IsNonnegativeSchedule h)
    (hm : 0 < m) :
    fourBlockR (rankedPathWeights (q := 2 * (m + m)) h) =
      schedulePrefixR h m := by
  let c : ℝ := 2 * unresolvedMass h (2 * (m + m)) /
    (2 * (m + m) : ℕ)
  have hc : c ≠ 0 := by
    dsimp only [c]
    positivity [unresolvedMass_pos hh (2 * (m + m))]
  calc
    fourBlockR (rankedPathWeights (q := 2 * (m + m)) h) =
        fourBlockR (fun i ↦ c * idealReciprocalWeights h m i) := by
      rw [rankedPathWeights_fourBlock_eq]
    _ = fourBlockR (idealReciprocalWeights h m) := fourBlockR_scale hc _
    _ = schedulePrefixR h m := idealFourBlockR_eq_schedulePrefixR h

theorem rankedFourBlockS_eq_schedulePrefixS
    {T m : ℕ} {h : StepSchedule T} (hh : IsNonnegativeSchedule h)
    (hm : 0 < m) :
    fourBlockS (rankedPathWeights (q := 2 * (m + m)) h) =
      schedulePrefixS h m := by
  let c : ℝ := 2 * unresolvedMass h (2 * (m + m)) /
    (2 * (m + m) : ℕ)
  have hc : c ≠ 0 := by
    dsimp only [c]
    positivity [unresolvedMass_pos hh (2 * (m + m))]
  calc
    fourBlockS (rankedPathWeights (q := 2 * (m + m)) h) =
        fourBlockS (fun i ↦ c * idealReciprocalWeights h m i) := by
      rw [rankedPathWeights_fourBlock_eq]
    _ = fourBlockS (idealReciprocalWeights h m) := fourBlockS_scale hc _
    _ = schedulePrefixS h m := idealFourBlockS_eq_schedulePrefixS h

/-- Explicit common error bound for all three normalized coordinates. -/
def scheduleCoordinateError {T : ℕ} (h : StepSchedule T) (m : ℕ) : ℝ :=
  (1 / ((2 * (m + m) : ℝ) - 1)) /
    (8 * m * zetaState h (2 * (m + m)))

/-- Simultaneous `O(m⁻²)` comparison of the matching tuple's actual
coordinates with the exact reciprocal-prefix coordinates. -/
theorem scheduleFourBlockCoordinates_close
    {T m : ℕ} {h : StepSchedule T} (hh : IsNonnegativeSchedule h)
    (hm : 0 < m) (hq : 2 * (m + m) ≤ longCount h) :
    |fourBlockA (scheduleFourBlockWeights h hq) - schedulePrefixA h m| ≤
        scheduleCoordinateError h m ∧
      |fourBlockR (scheduleFourBlockWeights h hq) - schedulePrefixR h m| ≤
        scheduleCoordinateError h m ∧
      |fourBlockS (scheduleFourBlockWeights h hq) - schedulePrefixS h m| ≤
        scheduleCoordinateError h m := by
  let x := rankedPathWeights (q := 2 * (m + m)) h
  let y := scheduleFourBlockWeights h hq
  let e : ℝ := 1 / ((2 * (m + m) : ℝ) - 1)
  have hx : ∀ i, 0 < x i := rankedPathWeights_pos hh (by omega) hq
  have hxy : ∀ i, x i ≤ y i :=
    rankedPathWeight_le_scheduleFourBlockWeight hh hm hq
  have hYe : fourBlockTotal y ≤ fourBlockTotal x + e :=
    scheduleFourBlockTotal_le_ranked_add_aux hh hm hq
  have he : 0 ≤ e := by
    dsimp only [e]
    have hmR : (1 : ℝ) < 2 * ((m : ℝ) + m) := by
      exact_mod_cast (show 1 < 2 * (m + m) by omega)
    exact one_div_nonneg.mpr (sub_nonneg.mpr hmR.le)
  have hclose := fourBlockCoordinates_abs_le_of_pointwise
    hm hx hxy hYe he
  dsimp only [x, y, e] at hclose
  rw [rankedFourBlockTotal_eq h hm,
    rankedFourBlockA_eq_schedulePrefixA hh hm,
    rankedFourBlockR_eq_schedulePrefixR hh hm,
    rankedFourBlockS_eq_schedulePrefixS hh hm] at hclose
  exact hclose

end

end GDLowerBound.FourBlock
