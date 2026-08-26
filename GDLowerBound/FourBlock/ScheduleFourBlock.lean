import GDLowerBound.FourBlock.FourBlockTotal

/-!
# Exact schedule-level four-block endpoint theorem

This module composes the exact augmented-path endpoint estimate, sorting,
outside-in exchange, finite Jensen, and four-block normalization.  The result
is a single finite theorem with an explicit auxiliary-vertex correction.
-/

namespace GDLowerBound.FourBlock

open scoped BigOperators
open GDLowerBound.Schedule GDLowerBound.RankAnalysis GDLowerBound.Matching

noncomputable section

def scheduleFourBlockWeights {T m : ℕ} (h : StepSchedule T)
    (hq : 2 * (m + m) ≤ longCount h) : Fin (2 * (m + m)) → ℝ :=
  sortedNearTail (topPathWeight h (2 * (m + m)) hq)

theorem scheduleFourBlockWeights_pos {T m : ℕ} {h : StepSchedule T}
    (hh : IsNonnegativeSchedule h) (hm : 0 < m)
    (hq : 2 * (m + m) ≤ longCount h) :
    ∀ i, 0 < scheduleFourBlockWeights h hq i := by
  apply tailWeight_pos
  apply sortedWeight_pos
  exact topPathWeight_pos hh (by omega : 2 ≤ 2 * (m + m)) hq

theorem scheduleFourBlockWeights_monotone {T m : ℕ} (h : StepSchedule T)
    (hq : 2 * (m + m) ≤ longCount h) :
    Monotone (scheduleFourBlockWeights h hq) := by
  exact tailWeight_monotone (sortedWeight_monotone
    (topPathWeight h (2 * (m + m)) hq))

theorem scheduleFourBlock_ordered {T m : ℕ} {h : StepSchedule T}
    (hh : IsNonnegativeSchedule h) (hm : 0 < m)
    (hq : 2 * (m + m) ≤ longCount h) :
    OrderedFourBlocks
      (fourBlockA (scheduleFourBlockWeights h hq))
      (fourBlockR (scheduleFourBlockWeights h hq))
      (fourBlockS (scheduleFourBlockWeights h hq)) := by
  exact orderedFourBlocks_of_sortedWeights hm
    (scheduleFourBlockWeights_pos hh hm hq)
    (scheduleFourBlockWeights_monotone h hq)

/-- The selected four-block scale is at most `ζ_(4m)` plus the exact
auxiliary endpoint correction. -/
theorem scheduleFourBlockZ_le_zeta_add_aux {T m : ℕ} {h : StepSchedule T}
    (hh : IsNonnegativeSchedule h) (hm : 0 < m)
    (hq : 2 * (m + m) ≤ longCount h) :
    fourBlockZ (scheduleFourBlockWeights h hq) ≤
      zetaState h (2 * (m + m)) +
        1 / ((8 * (m : ℝ)) * ((2 * (m + m) : ℝ) - 1)) := by
  have htotal := fourBlockTotal_sortedNearTail_le_topPathTotal hh hm hq
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hqR : (1 : ℝ) < (2 * (m + m) : ℕ) := by exact_mod_cast
    (show 1 < 2 * (m + m) by omega)
  norm_num [Nat.cast_mul, Nat.cast_add] at hqR
  have hden : 0 < 8 * (m : ℝ) := by positivity
  have hscaled := div_le_div_of_nonneg_right htotal hden.le
  calc
    fourBlockZ (scheduleFourBlockWeights h hq) =
        fourBlockTotal (scheduleFourBlockWeights h hq) / (8 * (m : ℝ)) := rfl
    _ ≤ (2 * (2 * (m + m) : ℝ) * zetaState h (2 * (m + m)) +
          1 / ((2 * (m + m) : ℝ) - 1)) / (8 * (m : ℝ)) := hscaled
    _ = zetaState h (2 * (m + m)) +
          1 / ((8 * (m : ℝ)) * ((2 * (m + m) : ℝ) - 1)) := by
      have hqm1 : (2 * (m + m) : ℝ) - 1 ≠ 0 :=
        (sub_pos.mpr hqR).ne'
      norm_num [Nat.cast_mul, Nat.cast_add]
      field_simp [hmR.ne', hqm1]
      ring

theorem scheduleOutsideInLogScore_le_fourBlock {T m : ℕ}
    {h : StepSchedule T} (hh : IsNonnegativeSchedule h) (hm : 0 < m)
    (hq : 2 * (m + m) ≤ longCount h) :
    outsideInLogScore (m + m) (scheduleFourBlockWeights h hq) /
        (2 * m) ≤
      fourBlockMatching
        (fourBlockZ (scheduleFourBlockWeights h hq))
        (fourBlockA (scheduleFourBlockWeights h hq))
        (fourBlockR (scheduleFourBlockWeights h hq))
        (fourBlockS (scheduleFourBlockWeights h hq)) := by
  exact outsideInLogScore_average_le_fourBlockMatching hm
    (scheduleFourBlockWeights h hq)
    (scheduleFourBlockWeights_pos hh hm hq)

theorem scheduleOutsideInProduct_le_fourBlockExp {T m : ℕ}
    {h : StepSchedule T} (hh : IsNonnegativeSchedule h) (hm : 0 < m)
    (hq : 2 * (m + m) ≤ longCount h) :
    outsideInProduct (m + m) (scheduleFourBlockWeights h hq) ≤
      Real.exp ((2 * m : ℕ) *
        fourBlockMatching
          (fourBlockZ (scheduleFourBlockWeights h hq))
          (fourBlockA (scheduleFourBlockWeights h hq))
          (fourBlockR (scheduleFourBlockWeights h hq))
          (fourBlockS (scheduleFourBlockWeights h hq))) := by
  let w := scheduleFourBlockWeights h hq
  let H := fourBlockMatching (fourBlockZ w) (fourBlockA w)
    (fourBlockR w) (fourBlockS w)
  have hw : ∀ i, 0 < w i := scheduleFourBlockWeights_pos hh hm hq
  rw [outsideInProduct_eq_exp_logScore hw]
  apply Real.exp_le_exp.mpr
  have hj := scheduleOutsideInLogScore_le_fourBlock hh hm hq
  norm_num [Nat.cast_mul] at hj ⊢
  have hmR : (0 : ℝ) < 2 * (m : ℝ) := by positivity
  have hmul := (div_le_iff₀ hmR).mp hj
  dsimp only [w, H] at hmul ⊢
  linarith

/-- Complete exact four-block endpoint inequality at rank `4m`. -/
theorem topChain_reciprocalProduct_le_fourBlockExp
    {T m : ℕ} {h : StepSchedule T} (hh : IsNonnegativeSchedule h)
    (hm : 0 < m) (hq : 2 * (m + m) ≤ longCount h) :
    (topChain h (2 * (m + m))).terminalScale *
        ∏ i : Fin (2 * (m + m)),
          (chronologicalLocalBound h (2 * (m + m)) hq i)⁻¹ ≤
      (4 * unresolvedMass h (2 * (m + m)) *
          (2 * (m + m) - 1) / (2 * (m + m))) *
        Real.exp ((4 * m : ℕ) *
          fourBlockMatching
            (fourBlockZ (scheduleFourBlockWeights h hq))
            (fourBlockA (scheduleFourBlockWeights h hq))
            (fourBlockR (scheduleFourBlockWeights h hq))
            (fourBlockS (scheduleFourBlockWeights h hq))) := by
  let w := scheduleFourBlockWeights h hq
  let H := fourBlockMatching (fourBlockZ w) (fourBlockA w)
    (fourBlockR w) (fourBlockS w)
  have hend := topChain_reciprocalProduct_le_sortedOutsideIn
    (h := h) hh (k := m + m) (by omega) hq
  have hout := scheduleOutsideInProduct_le_fourBlockExp hh hm hq
  have hout0 : 0 ≤ outsideInProduct (m + m) w := by
    apply Finset.prod_nonneg
    intro i hi
    exact (edgeKernel_pos
      (scheduleFourBlockWeights_pos hh hm hq _)
      (scheduleFourBlockWeights_pos hh hm hq _)).le
  have hexp0 : 0 ≤ Real.exp (((2 * m : ℕ) : ℝ) * H) := (Real.exp_pos _).le
  have hsquare : outsideInProduct (m + m) w ^ 2 ≤
      Real.exp (((4 * m : ℕ) : ℝ) * H) := by
    calc
      outsideInProduct (m + m) w ^ 2 =
          outsideInProduct (m + m) w * outsideInProduct (m + m) w := pow_two _
      _ ≤ Real.exp (((2 * m : ℕ) : ℝ) * H) *
          Real.exp (((2 * m : ℕ) : ℝ) * H) :=
        mul_le_mul hout hout hout0 hexp0
      _ = Real.exp (((4 * m : ℕ) : ℝ) * H) := by
        rw [← Real.exp_add]
        congr 1
        norm_num [Nat.cast_mul]
        ring
  have hcoeff :
      0 ≤ 4 * unresolvedMass h (2 * (m + m)) *
        (2 * (m + m) - 1) / (2 * (m + m)) := by
    have hD := unresolvedMass_pos hh (2 * (m + m))
    have hmRone : (1 : ℝ) ≤ m := by exact_mod_cast hm
    norm_num [Nat.cast_mul, Nat.cast_add,
      Nat.cast_sub (by omega : 1 ≤ 2 * (m + m))]
    have htail : 0 ≤ 2 * ((m : ℝ) + m) - 1 := by nlinarith
    exact div_nonneg
      (mul_nonneg (mul_nonneg (by norm_num) hD.le) htail) (by positivity)
  have hscaled := mul_le_mul_of_nonneg_left hsquare hcoeff
  calc
    (topChain h (2 * (m + m))).terminalScale *
          ∏ i : Fin (2 * (m + m)),
            (chronologicalLocalBound h (2 * (m + m)) hq i)⁻¹ ≤
        (4 * unresolvedMass h (2 * (m + m)) *
          (2 * (m + m) - 1) / (2 * (m + m))) *
          outsideInProduct (m + m) w ^ 2 := by
      norm_num [Nat.cast_add] at hend
      simpa only [← Finset.prod_inv_distrib, w, scheduleFourBlockWeights] using hend
    _ ≤ (4 * unresolvedMass h (2 * (m + m)) *
          (2 * (m + m) - 1) / (2 * (m + m))) *
        Real.exp (((4 * m : ℕ) : ℝ) * H) := hscaled
    _ = (4 * unresolvedMass h (2 * (m + m)) *
          (2 * (m + m) - 1) / (2 * (m + m))) *
        Real.exp ((4 * m : ℕ) *
          fourBlockMatching
            (fourBlockZ (scheduleFourBlockWeights h hq))
            (fourBlockA (scheduleFourBlockWeights h hq))
            (fourBlockR (scheduleFourBlockWeights h hq))
            (fourBlockS (scheduleFourBlockWeights h hq))) := by rfl

end

end GDLowerBound.FourBlock
