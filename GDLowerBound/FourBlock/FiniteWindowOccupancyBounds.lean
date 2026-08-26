import GDLowerBound.FourBlock.FiniteWindowEndpointSamplingBounds

/-!
# Uniform bounds for the occupancy boundary bands

The interior occupancy errors are reciprocal-square summable.  The remaining
`1/n` errors occur only in two fixed-ratio boundary bands, so their total is
bounded independently of the dyadic depth.  This is the key distinction from
a bound over the entire common rank interval.
-/

namespace GDLowerBound.FourBlock

open scoped BigOperators

noncomputable section

private theorem harmonicSum_le_adjacentHarmonicWeight
    {s : Finset ℕ} {lo hi : ℕ}
    (hsub : s ⊆ Finset.Ico (lo + 1) (hi + 1)) :
    (∑ n ∈ s, 1 / (n : ℝ)) ≤ adjacentHarmonicWeight lo hi := by
  unfold adjacentHarmonicWeight
  apply Finset.sum_le_sum_of_subset_of_nonneg hsub
  intro n _ _
  positivity

theorem adjacentHarmonicWeight_doubling_le_one
    {K : ℕ} (hK : 1 ≤ K) :
    adjacentHarmonicWeight K (2 * K) ≤ 1 := by
  have hlog := harmonicBlock_le_log_ratio hK (by omega : K ≤ 2 * K)
  have hK0 : (K : ℝ) ≠ 0 := by positivity
  have hratio : (((2 * K : ℕ) : ℝ) / (K : ℝ)) = (2 : ℝ) := by
    push_cast
    field_simp [hK0]
  unfold adjacentHarmonicWeight
  rw [hratio] at hlog
  exact hlog.trans log_two_le_one

theorem adjacentHarmonicWeight_quadrupling_le_two
    {K : ℕ} (hK : 1 ≤ K) :
    adjacentHarmonicWeight K (4 * K) ≤ 2 := by
  have hlog := harmonicBlock_le_log_ratio hK (by omega : K ≤ 4 * K)
  have hK0 : (K : ℝ) ≠ 0 := by positivity
  have hratio : (((4 * K : ℕ) : ℝ) / (K : ℝ)) = (4 : ℝ) := by
    push_cast
    field_simp [hK0]
  have hlogFour : Real.log 4 ≤ (2 : ℝ) := by
    rw [show (4 : ℝ) = 2 * 2 by norm_num,
      Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by norm_num : (2 : ℝ) ≠ 0)]
    linarith [log_two_le_one]
  unfold adjacentHarmonicWeight
  rw [hratio] at hlog
  exact hlog.trans hlogFour

private theorem twoLowBoundaryHarmonic_le_one
    {M N : ℕ} (hM : 2 ≤ M) :
    (∑ n ∈ Finset.Ico (2 * M + 1) (4 * N + 1),
        if n < 3 * (M + 1) then 1 / (n : ℝ) else 0) ≤ 1 := by
  rw [← Finset.sum_filter]
  have hsub :
      (Finset.Ico (2 * M + 1) (4 * N + 1)).filter
          (fun n ↦ n < 3 * (M + 1)) ⊆
        Finset.Ico (2 * M + 1) (4 * M + 1) := by
    intro n hn
    have hn' := Finset.mem_filter.mp hn
    have hnIco := Finset.mem_Ico.mp hn'.1
    exact Finset.mem_Ico.mpr ⟨hnIco.1, by omega⟩
  have hsum := harmonicSum_le_adjacentHarmonicWeight hsub
  have hdouble := adjacentHarmonicWeight_doubling_le_one
    (show 1 ≤ 2 * M by omega)
  have hdouble' : adjacentHarmonicWeight (2 * M) (4 * M) ≤ 1 := by
    simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hdouble
  exact hsum.trans hdouble'

private theorem twoHighBoundaryHarmonic_le_one
    {M N : ℕ} (hN : 1 ≤ N) :
    (∑ n ∈ Finset.Ico (2 * M + 1) (4 * N + 1),
        if 2 * N < n then 1 / (n : ℝ) else 0) ≤ 1 := by
  rw [← Finset.sum_filter]
  have hsub :
      (Finset.Ico (2 * M + 1) (4 * N + 1)).filter
          (fun n ↦ 2 * N < n) ⊆
        Finset.Ico (2 * N + 1) (4 * N + 1) := by
    intro n hn
    have hn' := Finset.mem_filter.mp hn
    have hnIco := Finset.mem_Ico.mp hn'.1
    exact Finset.mem_Ico.mpr ⟨by omega, hnIco.2⟩
  have hsum := harmonicSum_le_adjacentHarmonicWeight hsub
  have hdouble := adjacentHarmonicWeight_doubling_le_one
    (show 1 ≤ 2 * N by omega)
  have hdouble' : adjacentHarmonicWeight (2 * N) (4 * N) ≤ 1 := by
    simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hdouble
  exact hsum.trans hdouble'

private theorem threeLowBoundaryHarmonic_le_two
    {M N : ℕ} (hM : 1 ≤ M) :
    (∑ n ∈ Finset.Ico (2 * M + 1) (4 * N + 1),
        if n < 4 * (M + 1) then 1 / (n : ℝ) else 0) ≤ 2 := by
  rw [← Finset.sum_filter]
  have hsub :
      (Finset.Ico (2 * M + 1) (4 * N + 1)).filter
          (fun n ↦ n < 4 * (M + 1)) ⊆
        Finset.Ico (2 * M + 1) (8 * M + 1) := by
    intro n hn
    have hn' := Finset.mem_filter.mp hn
    have hnIco := Finset.mem_Ico.mp hn'.1
    exact Finset.mem_Ico.mpr ⟨hnIco.1, by omega⟩
  have hsum := harmonicSum_le_adjacentHarmonicWeight hsub
  have hquad := adjacentHarmonicWeight_quadrupling_le_two
    (show 1 ≤ 2 * M by omega)
  have hquad' : adjacentHarmonicWeight (2 * M) (8 * M) ≤ 2 := by
    simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hquad
  exact hsum.trans hquad'

private theorem threeHighBoundaryHarmonic_le_one
    {M N : ℕ} (hN : 1 ≤ N) :
    (∑ n ∈ Finset.Ico (2 * M + 1) (4 * N + 1),
        if 3 * N < n then 1 / (n : ℝ) else 0) ≤ 1 := by
  rw [← Finset.sum_filter]
  have hsub :
      (Finset.Ico (2 * M + 1) (4 * N + 1)).filter
          (fun n ↦ 3 * N < n) ⊆
        Finset.Ico (3 * N + 1) (6 * N + 1) := by
    intro n hn
    have hn' := Finset.mem_filter.mp hn
    have hnIco := Finset.mem_Ico.mp hn'.1
    exact Finset.mem_Ico.mpr ⟨by omega, by omega⟩
  have hsum := harmonicSum_le_adjacentHarmonicWeight hsub
  have hdouble := adjacentHarmonicWeight_doubling_le_one
    (show 1 ≤ 3 * N by omega)
  have hdouble' : adjacentHarmonicWeight (3 * N) (6 * N) ≤ 1 := by
    simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hdouble
  exact hsum.trans hdouble'

/-- The full `(2m,3m]` occupancy finite error is bounded by a fixed boundary
constant plus a reciprocal-square tail. -/
theorem sum_twoOccupancyFiniteError_le
    {M N : ℕ} (hM : 2 ≤ M) (hMN : M ≤ N) :
    (∑ n ∈ Finset.Ico (2 * M + 1) (4 * N + 1),
        twoOccupancyFiniteError M N n) ≤
      6 + 9 / (M : ℝ) := by
  have hlog : Real.log (3 / 2 : ℝ) ≤ 1 := by
    have hpos : (0 : ℝ) < 3 / 2 := by norm_num
    have hle : (3 / 2 : ℝ) ≤ 2 := by norm_num
    exact (Real.strictMonoOn_log.monotoneOn hpos (by norm_num) hle).trans
      log_two_le_one
  have hpoint : ∀ n ∈ Finset.Ico (2 * M + 1) (4 * N + 1),
      twoOccupancyFiniteError M N n ≤
        18 / (n : ℝ) ^ 2 +
          3 * (if n < 3 * (M + 1) then 1 / (n : ℝ) else 0) +
          3 * (if 2 * N < n then 1 / (n : ℝ) else 0) := by
    intro n hn
    have hnIco := Finset.mem_Ico.mp hn
    have hn0 : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
    unfold twoOccupancyFiniteError
    by_cases hinterior : 3 * (M + 1) ≤ n ∧ n ≤ 2 * N
    · simp [hinterior, show ¬ n < 3 * (M + 1) by omega,
        show ¬ 2 * N < n by omega]
    · have hboundary : n < 3 * (M + 1) ∨ 2 * N < n := by omega
      rw [if_neg hinterior]
      have hbasic :
          3 * (Real.log (3 / 2 : ℝ) + 6 / (n : ℝ)) / (n : ℝ) ≤
            18 / (n : ℝ) ^ 2 + 3 * (1 / (n : ℝ)) := by
        calc
          _ = 18 / (n : ℝ) ^ 2 +
                3 * Real.log (3 / 2 : ℝ) / (n : ℝ) := by ring
          _ ≤ 18 / (n : ℝ) ^ 2 + 3 * (1 / (n : ℝ)) := by
            have hd := div_le_div_of_nonneg_right hlog hn0.le
            have hd3 := mul_le_mul_of_nonneg_left hd
              (by norm_num : (0 : ℝ) ≤ 3)
            simpa only [mul_div_assoc] using
              add_le_add_right hd3 (18 / (n : ℝ) ^ 2)
      by_cases hlow : n < 3 * (M + 1)
      · by_cases hhigh : 2 * N < n
        · simp only [if_pos hlow, if_pos hhigh]
          exact hbasic.trans (le_add_of_nonneg_right (by positivity))
        · simpa [hlow, hhigh] using hbasic
      · have hhigh : 2 * N < n := by omega
        simpa [hlow, hhigh] using hbasic
  have hsquare := commonReciprocalSquareSum_le_inv
    (show 1 ≤ M by omega) hMN
  have hlow := twoLowBoundaryHarmonic_le_one (M := M) (N := N) hM
  have hhigh := twoHighBoundaryHarmonic_le_one
    (M := M) (N := N) (by omega)
  have hsum := Finset.sum_le_sum hpoint
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum] at hsum
  unfold commonReciprocalSquareSum at hsquare
  have hsquareSum :
      (∑ n ∈ Finset.Ico (2 * M + 1) (4 * N + 1), 18 / (n : ℝ) ^ 2) =
        18 * (∑ n ∈ Finset.Ico (2 * M + 1) (4 * N + 1),
          1 / (n : ℝ) ^ 2) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n _
    ring
  have hsquare' :
      18 * (∑ n ∈ Finset.Ico (2 * M + 1) (4 * N + 1),
        1 / (n : ℝ) ^ 2) ≤ 9 / (M : ℝ) := by
    have h := mul_le_mul_of_nonneg_left hsquare (by norm_num : (0 : ℝ) ≤ 18)
    have hM0 : (M : ℝ) ≠ 0 := by positivity
    calc
      _ ≤ 18 * (1 / (((2 * M : ℕ) : ℝ))) := h
      _ = 9 / (M : ℝ) := by
        push_cast
        field_simp [hM0]
        norm_num
  rw [hsquareSum] at hsum
  linarith

/-- The `(3m,4m]` occupancy error has the corresponding uniform bound. -/
theorem sum_threeOccupancyFiniteError_le
    {M N : ℕ} (hM : 2 ≤ M) (hMN : M ≤ N) :
    (∑ n ∈ Finset.Ico (2 * M + 1) (4 * N + 1),
        threeOccupancyFiniteError M N n) ≤
      9 + 12 / (M : ℝ) := by
  have hlog : Real.log (4 / 3 : ℝ) ≤ 1 := by
    have hpos : (0 : ℝ) < 4 / 3 := by norm_num
    have hle : (4 / 3 : ℝ) ≤ 2 := by norm_num
    exact (Real.strictMonoOn_log.monotoneOn hpos (by norm_num) hle).trans
      log_two_le_one
  have hpoint : ∀ n ∈ Finset.Ico (2 * M + 1) (4 * N + 1),
      threeOccupancyFiniteError M N n ≤
        24 / (n : ℝ) ^ 2 +
          3 * (if n < 4 * (M + 1) then 1 / (n : ℝ) else 0) +
          3 * (if 3 * N < n then 1 / (n : ℝ) else 0) := by
    intro n hn
    have hnIco := Finset.mem_Ico.mp hn
    have hn0 : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
    unfold threeOccupancyFiniteError
    by_cases hinterior : 4 * (M + 1) ≤ n ∧ n ≤ 3 * N
    · simp [hinterior, show ¬ n < 4 * (M + 1) by omega,
        show ¬ 3 * N < n by omega]
    · have hboundary : n < 4 * (M + 1) ∨ 3 * N < n := by omega
      rw [if_neg hinterior]
      have hbasic :
          3 * (Real.log (4 / 3 : ℝ) + 8 / (n : ℝ)) / (n : ℝ) ≤
            24 / (n : ℝ) ^ 2 + 3 * (1 / (n : ℝ)) := by
        calc
          _ = 24 / (n : ℝ) ^ 2 +
                3 * Real.log (4 / 3 : ℝ) / (n : ℝ) := by ring
          _ ≤ 24 / (n : ℝ) ^ 2 + 3 * (1 / (n : ℝ)) := by
            have hd := div_le_div_of_nonneg_right hlog hn0.le
            have hd3 := mul_le_mul_of_nonneg_left hd
              (by norm_num : (0 : ℝ) ≤ 3)
            simpa only [mul_div_assoc] using
              add_le_add_right hd3 (24 / (n : ℝ) ^ 2)
      by_cases hlow : n < 4 * (M + 1)
      · by_cases hhigh : 3 * N < n
        · simp only [if_pos hlow, if_pos hhigh]
          exact hbasic.trans (le_add_of_nonneg_right (by positivity))
        · simpa [hlow, hhigh] using hbasic
      · have hhigh : 3 * N < n := by omega
        simpa [hlow, hhigh] using hbasic
  have hsquare := commonReciprocalSquareSum_le_inv
    (show 1 ≤ M by omega) hMN
  have hlow := threeLowBoundaryHarmonic_le_two
    (M := M) (N := N) (by omega)
  have hhigh := threeHighBoundaryHarmonic_le_one
    (M := M) (N := N) (by omega)
  have hsum := Finset.sum_le_sum hpoint
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum] at hsum
  unfold commonReciprocalSquareSum at hsquare
  have hsquareSum :
      (∑ n ∈ Finset.Ico (2 * M + 1) (4 * N + 1), 24 / (n : ℝ) ^ 2) =
        24 * (∑ n ∈ Finset.Ico (2 * M + 1) (4 * N + 1),
          1 / (n : ℝ) ^ 2) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n _
    ring
  have hsquare' :
      24 * (∑ n ∈ Finset.Ico (2 * M + 1) (4 * N + 1),
        1 / (n : ℝ) ^ 2) ≤ 12 / (M : ℝ) := by
    have h := mul_le_mul_of_nonneg_left hsquare (by norm_num : (0 : ℝ) ≤ 24)
    have hM0 : (M : ℝ) ≠ 0 := by positivity
    calc
      _ ≤ 24 * (1 / (((2 * M : ℕ) : ℝ))) := h
      _ = 12 / (M : ℝ) := by
        push_cast
        field_simp [hM0]
        norm_num
  rw [hsquareSum] at hsum
  linarith

end

end GDLowerBound.FourBlock
