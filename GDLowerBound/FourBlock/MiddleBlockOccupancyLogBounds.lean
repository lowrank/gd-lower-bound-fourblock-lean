import GDLowerBound.FourBlock.MiddleBlockOccupancyBounds

/-! # Logarithmic enclosure of the interior occupancy weights -/

namespace GDLowerBound.FourBlock

open scoped BigOperators

noncomputable section

/-- The `(2m,3m]` occupancy is enclosed by the two neighboring logarithmic
integrals. -/
theorem middleBlockOccupancy_two_log_bounds
    {M N n : ℕ} (hn : 12 ≤ n)
    (hM : 3 * (M + 1) ≤ n) (hN : n ≤ 2 * N) :
    Real.log (((twoBlockOccupancyHi n + 1 : ℕ) : ℝ) /
          (twoBlockOccupancyLo n : ℝ)) ≤
        middleBlockOccupancy 2 M N n ∧
      middleBlockOccupancy 2 M N n ≤
        Real.log ((twoBlockOccupancyHi n : ℝ) /
          ((twoBlockOccupancyLo n - 1 : ℕ) : ℝ)) := by
  have hLo2 : 2 ≤ twoBlockOccupancyLo n := by
    unfold twoBlockOccupancyLo
    omega
  have hLoHi : twoBlockOccupancyLo n ≤ twoBlockOccupancyHi n := by
    unfold twoBlockOccupancyLo twoBlockOccupancyHi
    omega
  rw [middleBlockOccupancy_two_eq_harmonic hM hN]
  constructor
  · exact log_succ_ratio_le_harmonic_interval (by omega) hLoHi
  · have hup := harmonicBlock_le_log_ratio
        (lo := twoBlockOccupancyLo n - 1)
        (hi := twoBlockOccupancyHi n) (by omega) (by omega)
    have hsucc : twoBlockOccupancyLo n - 1 + 1 = twoBlockOccupancyLo n := by
      omega
    simpa only [adjacentHarmonicWeight, hsucc] using hup

/-- The `(3m,4m]` occupancy is enclosed by the two neighboring logarithmic
integrals. -/
theorem middleBlockOccupancy_three_log_bounds
    {M N n : ℕ} (hn : 16 ≤ n)
    (hM : 4 * (M + 1) ≤ n) (hN : n ≤ 3 * N) :
    Real.log (((threeBlockOccupancyHi n + 1 : ℕ) : ℝ) /
          (threeBlockOccupancyLo n : ℝ)) ≤
        middleBlockOccupancy 3 M N n ∧
      middleBlockOccupancy 3 M N n ≤
        Real.log ((threeBlockOccupancyHi n : ℝ) /
          ((threeBlockOccupancyLo n - 1 : ℕ) : ℝ)) := by
  have hLo2 : 2 ≤ threeBlockOccupancyLo n := by
    unfold threeBlockOccupancyLo
    omega
  have hLoHi : threeBlockOccupancyLo n ≤ threeBlockOccupancyHi n := by
    unfold threeBlockOccupancyLo threeBlockOccupancyHi
    omega
  rw [middleBlockOccupancy_three_eq_harmonic hM hN]
  constructor
  · exact log_succ_ratio_le_harmonic_interval (by omega) hLoHi
  · have hup := harmonicBlock_le_log_ratio
        (lo := threeBlockOccupancyLo n - 1)
        (hi := threeBlockOccupancyHi n) (by omega) (by omega)
    have hsucc : threeBlockOccupancyLo n - 1 + 1 = threeBlockOccupancyLo n := by
      omega
    simpa only [adjacentHarmonicWeight, hsucc] using hup

end

end GDLowerBound.FourBlock
