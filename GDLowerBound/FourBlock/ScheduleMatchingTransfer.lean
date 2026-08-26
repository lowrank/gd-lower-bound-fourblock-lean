import GDLowerBound.FourBlock.ScheduleMatchingPerturbation

/-!
# Finite matching-floor transfer for a schedule

This module specializes the general perturbation bound to the augmented
endpoint path.  It turns a lower bound for the actual outside-in matching
tuple into the `-10⁻⁶` lower bound accepted by the robust central certificate.
-/

namespace GDLowerBound.FourBlock

open GDLowerBound.Schedule GDLowerBound.RankAnalysis

noncomputable section

def scheduleMatchingError (m : ℕ) : ℝ :=
  7 / (2 * (m : ℝ) * (4 * (m : ℝ) - 1))

theorem scheduleActualMatching_le_ideal_add
    {T m : ℕ} {h : StepSchedule T} (hh : IsNonnegativeSchedule h)
    (hm : 0 < m) (hq : 2 * (m + m) ≤ longCount h)
    (hzlo : (centralThetaLowerQ : ℝ) ≤ zetaState h (2 * (m + m)))
    (hord : OrderedFourBlocks (schedulePrefixA h m)
      (schedulePrefixR h m) (schedulePrefixS h m))
    (hrlo : (1 / 20 : ℝ) ≤ schedulePrefixR h m) :
    fourBlockMatching
        (fourBlockZ (scheduleFourBlockWeights h hq))
        (fourBlockA (scheduleFourBlockWeights h hq))
        (fourBlockR (scheduleFourBlockWeights h hq))
        (fourBlockS (scheduleFourBlockWeights h hq)) ≤
      fourBlockMatching (zetaState h (2 * (m + m)))
          (schedulePrefixA h m) (schedulePrefixR h m) (schedulePrefixS h m) +
        scheduleMatchingError m := by
  let x := rankedPathWeights (q := 2 * (m + m)) h
  let y := scheduleFourBlockWeights h hq
  let e : ℝ := 1 / ((2 * (m + m) : ℝ) - 1)
  have hx : ∀ i, 0 < x i := rankedPathWeights_pos hh (by omega) hq
  have hxy : ∀ i, x i ≤ y i :=
    rankedPathWeight_le_scheduleFourBlockWeight hh hm hq
  have htotal : fourBlockTotal y ≤ fourBlockTotal x + e :=
    scheduleFourBlockTotal_le_ranked_add_aux hh hm hq
  have hzlo' : (centralThetaLowerQ : ℝ) ≤ fourBlockZ x := by
    dsimp only [x]
    rw [rankedFourBlockZ_eq_zeta h hm]
    exact hzlo
  have hord' : OrderedFourBlocks (fourBlockA x) (fourBlockR x) (fourBlockS x) := by
    dsimp only [x]
    rw [rankedFourBlockA_eq_schedulePrefixA hh hm,
      rankedFourBlockR_eq_schedulePrefixR hh hm,
      rankedFourBlockS_eq_schedulePrefixS hh hm]
    exact hord
  have hrlo' : (1 / 20 : ℝ) ≤ fourBlockR x := by
    dsimp only [x]
    rw [rankedFourBlockR_eq_schedulePrefixR hh hm]
    exact hrlo
  have hbound := fourBlockMatching_le_add_of_pointwise hm hx hxy htotal
    hzlo' hord' hrlo'
  dsimp only [x, y, e] at hbound
  rw [rankedFourBlockZ_eq_zeta h hm,
    rankedFourBlockA_eq_schedulePrefixA hh hm,
    rankedFourBlockR_eq_schedulePrefixR hh hm,
    rankedFourBlockS_eq_schedulePrefixS hh hm] at hbound
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hlast : (0 : ℝ) < 4 * (m : ℝ) - 1 := by
    have hmOne : (1 : ℝ) ≤ m := by exact_mod_cast hm
    linarith
  convert hbound using 1
  unfold scheduleMatchingError
  norm_num [Nat.cast_mul, Nat.cast_add]
  field_simp [hmR.ne', hlast.ne']
  ring

theorem scheduleIdealMatching_ge_floor
    {T m : ℕ} {h : StepSchedule T} (hh : IsNonnegativeSchedule h)
    (hm : 0 < m) (hq : 2 * (m + m) ≤ longCount h)
    (hzlo : (centralThetaLowerQ : ℝ) ≤ zetaState h (2 * (m + m)))
    (hord : OrderedFourBlocks (schedulePrefixA h m)
      (schedulePrefixR h m) (schedulePrefixS h m))
    (hrlo : (1 / 20 : ℝ) ≤ schedulePrefixR h m)
    (hactual : (-1 / 2000000 : ℝ) ≤
      fourBlockMatching
        (fourBlockZ (scheduleFourBlockWeights h hq))
        (fourBlockA (scheduleFourBlockWeights h hq))
        (fourBlockR (scheduleFourBlockWeights h hq))
        (fourBlockS (scheduleFourBlockWeights h hq)))
    (herror : scheduleMatchingError m ≤ (1 / 2000000 : ℝ)) :
    (centralMatchingFloorQ : ℝ) ≤
      fourBlockMatching (zetaState h (2 * (m + m)))
        (schedulePrefixA h m) (schedulePrefixR h m) (schedulePrefixS h m) := by
  have hupper := scheduleActualMatching_le_ideal_add
    hh hm hq hzlo hord hrlo
  norm_num [centralMatchingFloorQ] at ⊢
  linarith

theorem scheduleMatchingError_le_half_floor {m : ℕ} (hm : 2000 ≤ m) :
    scheduleMatchingError m ≤ (1 / 2000000 : ℝ) := by
  have hmR : (2000 : ℝ) ≤ m := by exact_mod_cast hm
  have hden : 0 < 2 * (m : ℝ) * (4 * (m : ℝ) - 1) := by
    have hm0 : (0 : ℝ) < m := by linarith
    have hlast : (0 : ℝ) < 4 * (m : ℝ) - 1 := by linarith
    exact mul_pos (mul_pos (by norm_num) hm0) hlast
  have hdenLower :
      (2 : ℝ) * 2000 * 7999 ≤ 2 * (m : ℝ) * (4 * (m : ℝ) - 1) := by
    nlinarith [sq_nonneg ((m : ℝ) - 2000)]
  unfold scheduleMatchingError
  apply (div_le_iff₀ hden).2
  nlinarith

end

end GDLowerBound.FourBlock
