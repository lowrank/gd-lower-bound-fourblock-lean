import GDLowerBound.Schedule.Excess

namespace GDLowerBound.RankAnalysis

open scoped Real

/-- A normalized lower bound with denominator `B (r+1)^(p-1)` implies the
corresponding horizon bound once `B ≤ T+1` and `r+1 ≤ T+1`. -/
theorem normalizedFloor_to_horizon
    {T r : ℕ} {p c B value : ℝ}
    (hp : 1 ≤ p) (hc : 0 ≤ c) (hB : 0 < B)
    (hB_le : B ≤ (T : ℝ) + 1) (hr_le : r + 1 ≤ T + 1)
    (hfloor : c / (B * Real.rpow ((r : ℝ) + 1) (p - 1)) ≤ value) :
    c * Real.rpow ((T : ℝ) + 1) (-p) ≤ value := by
  have hN_pos : 0 < (T : ℝ) + 1 := by positivity
  have hm_pos : 0 < (r : ℝ) + 1 := by positivity
  have hexp : 0 ≤ p - 1 := sub_nonneg.mpr hp
  have hbase : (r : ℝ) + 1 ≤ (T : ℝ) + 1 := by
    exact_mod_cast hr_le
  have hpow : Real.rpow ((r : ℝ) + 1) (p - 1) ≤
      Real.rpow ((T : ℝ) + 1) (p - 1) :=
    Real.rpow_le_rpow (le_of_lt hm_pos) hbase hexp
  have hden_pos : 0 < B * Real.rpow ((r : ℝ) + 1) (p - 1) :=
    mul_pos hB (Real.rpow_pos_of_pos hm_pos _)
  have hpower_identity :
      ((T : ℝ) + 1) * Real.rpow ((T : ℝ) + 1) (p - 1) =
        Real.rpow ((T : ℝ) + 1) p := by
    calc
      ((T : ℝ) + 1) * Real.rpow ((T : ℝ) + 1) (p - 1) =
          Real.rpow ((T : ℝ) + 1) 1 *
            Real.rpow ((T : ℝ) + 1) (p - 1) := by
              congr 1
              exact (Real.rpow_one _).symm
      _ = Real.rpow ((T : ℝ) + 1) (1 + (p - 1)) := by
        exact (Real.rpow_add hN_pos 1 (p - 1)).symm
      _ = Real.rpow ((T : ℝ) + 1) p := by ring_nf
  have hden_le : B * Real.rpow ((r : ℝ) + 1) (p - 1) ≤
      Real.rpow ((T : ℝ) + 1) p := by
    calc
      B * Real.rpow ((r : ℝ) + 1) (p - 1) ≤
          ((T : ℝ) + 1) * Real.rpow ((r : ℝ) + 1) (p - 1) := by
        gcongr
        exact Real.rpow_nonneg (le_of_lt hm_pos) _
      _ ≤ ((T : ℝ) + 1) * Real.rpow ((T : ℝ) + 1) (p - 1) := by
        gcongr
      _ = Real.rpow ((T : ℝ) + 1) p := hpower_identity
  have hN_power_pos : 0 < Real.rpow ((T : ℝ) + 1) p :=
    Real.rpow_pos_of_pos hN_pos _
  have hinv : (Real.rpow ((T : ℝ) + 1) p)⁻¹ ≤
      (B * Real.rpow ((r : ℝ) + 1) (p - 1))⁻¹ :=
    inv_anti₀ hden_pos hden_le
  calc
    c * Real.rpow ((T : ℝ) + 1) (-p) =
        c * (Real.rpow ((T : ℝ) + 1) p)⁻¹ := by
      congr 1
      exact Real.rpow_neg (le_of_lt hN_pos) p
    _ ≤ c * (B * Real.rpow ((r : ℝ) + 1) (p - 1))⁻¹ := by
      exact mul_le_mul_of_nonneg_left hinv hc
    _ = c / (B * Real.rpow ((r : ℝ) + 1) (p - 1)) := by
      rw [div_eq_mul_inv]
    _ ≤ value := hfloor

/-- Schedule-specialized form of `normalizedFloor_to_horizon`. -/
theorem scheduleFloor_to_horizon
    {T : ℕ} {p c value : ℝ} {h : Schedule.StepSchedule T}
    (hp : 1 ≤ p) (hc : 0 ≤ c)
    (hh : IsNonnegativeSchedule h)
    (hfloor :
      c / (Schedule.cappedMass h *
        Real.rpow ((Schedule.longCount h : ℝ) + 1) (p - 1)) ≤ value) :
    c * Real.rpow ((T : ℝ) + 1) (-p) ≤ value := by
  exact normalizedFloor_to_horizon (T := T) (r := Schedule.longCount h)
    hp hc (Schedule.cappedMass_pos hh) (Schedule.cappedMass_le_horizon h)
    (Nat.succ_le_succ (Schedule.longCount_le_horizon h)) hfloor

end GDLowerBound.RankAnalysis
