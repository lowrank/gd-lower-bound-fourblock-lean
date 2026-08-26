import GDLowerBound.FourBlock.MomentRigidity

/-!
# Fixed-dilation sampling on cutoff intervals

The local four-block inequality is evaluated only at ranks `2m`, `3m`, and
`4m`, whereas the Lyapunov budgets control all consecutive ranks.  Passing
between these two types of averages requires regularity; no residue-class
equidistribution is available for an arbitrary schedule.

This file starts the rigorous replacement.  A bounded sequence whose upward
jumps are `O(1/n)` has controlled total variation: the downward variation is
paid for by telescoping.  The cutoff recurrences give such one-sided bounds
for both the relative mass increment and the endpoint defect.
-/

namespace GDLowerBound.FourBlock

open scoped BigOperators
open GDLowerBound.Schedule GDLowerBound.RankAnalysis

noncomputable section

/-- Harmonic weight on the adjacent-rank interval `(lo, hi]`. -/
def adjacentHarmonicWeight (lo hi : ℕ) : ℝ :=
  ∑ n ∈ Finset.Ico (lo + 1) (hi + 1), 1 / (n : ℝ)

/-- Unweighted total variation on the adjacent-rank interval `(lo, hi]`. -/
def adjacentTotalVariation (x : ℕ → ℝ) (lo hi : ℕ) : ℝ :=
  ∑ n ∈ Finset.Ico (lo + 1) (hi + 1), |x n - x (n - 1)|

/-- Harmonic-weighted total variation on `(lo, hi]`. -/
def adjacentWeightedVariation (x : ℕ → ℝ) (lo hi : ℕ) : ℝ :=
  ∑ n ∈ Finset.Ico (lo + 1) (hi + 1),
    |x n - x (n - 1)| / (n : ℝ)

private theorem sum_adjacent_difference (x : ℕ → ℝ)
    {lo hi : ℕ} (hlohi : lo ≤ hi) :
    ∑ n ∈ Finset.Ico (lo + 1) (hi + 1),
        (x n - x (n - 1)) = x hi - x lo := by
  induction hi, hlohi using Nat.le_induction with
  | base => simp
  | succ hi hlohi ih =>
      rw [Finset.sum_Ico_succ_top (by omega), ih]
      simp only [Nat.add_sub_cancel]
      ring

private theorem abs_le_two_upper_sub
    {d a : ℝ} (ha : 0 ≤ a) (hd : d ≤ a) :
    |d| ≤ 2 * a - d := by
  by_cases hsign : 0 ≤ d
  · rw [abs_of_nonneg hsign]
    linarith
  · have hnonpos : d ≤ 0 := le_of_not_ge hsign
    rw [abs_of_nonpos hnonpos]
    linarith

/-- A one-sided `A/n` increment bound and endpoint bounds control all
variation.  Large downward jumps are harmless: their total size telescopes
against the upward jumps. -/
theorem adjacentTotalVariation_le_of_oneSided
    {x : ℕ → ℝ} {A B : ℝ} {lo hi : ℕ}
    (hlohi : lo ≤ hi) (hA : 0 ≤ A)
    (hxhi : 0 ≤ x hi) (hxlo : x lo ≤ B)
    (hstep : ∀ n ∈ Finset.Ico (lo + 1) (hi + 1),
      x n - x (n - 1) ≤ A / (n : ℝ)) :
    adjacentTotalVariation x lo hi ≤
      2 * A * adjacentHarmonicWeight lo hi + B := by
  have hterm : ∀ n ∈ Finset.Ico (lo + 1) (hi + 1),
      |x n - x (n - 1)| ≤
        2 * (A / (n : ℝ)) - (x n - x (n - 1)) := by
    intro n hn
    have hn0 : 0 < (n : ℝ) := by
      exact_mod_cast (show 0 < n by
        have hnIco := Finset.mem_Ico.mp hn
        omega)
    exact abs_le_two_upper_sub (div_nonneg hA hn0.le) (hstep n hn)
  calc
    adjacentTotalVariation x lo hi ≤
        ∑ n ∈ Finset.Ico (lo + 1) (hi + 1),
          (2 * (A / (n : ℝ)) - (x n - x (n - 1))) := by
      exact Finset.sum_le_sum hterm
    _ = 2 * A * adjacentHarmonicWeight lo hi - (x hi - x lo) := by
      rw [Finset.sum_sub_distrib, sum_adjacent_difference x hlohi]
      unfold adjacentHarmonicWeight
      apply congrArg (fun t : ℝ ↦ t - (x hi - x lo))
      calc
        ∑ n ∈ Finset.Ico (lo + 1) (hi + 1), 2 * (A / (n : ℝ)) =
            ∑ n ∈ Finset.Ico (lo + 1) (hi + 1),
              (2 * A) * (1 / (n : ℝ)) := by
          apply Finset.sum_congr rfl
          intro n _
          ring
        _ = (2 * A) * ∑ n ∈ Finset.Ico (lo + 1) (hi + 1),
              1 / (n : ℝ) := by rw [Finset.mul_sum]
        _ = 2 * A * ∑ n ∈ Finset.Ico (lo + 1) (hi + 1),
              1 / (n : ℝ) := by ring
    _ ≤ 2 * A * adjacentHarmonicWeight lo hi + B := by
      linarith

/-- The weighted variation is at most `1/lo` times the unweighted variation. -/
theorem adjacentWeightedVariation_le_total_div
    {x : ℕ → ℝ} {lo hi : ℕ}
    (hlo : 1 ≤ lo) :
    adjacentWeightedVariation x lo hi ≤
      adjacentTotalVariation x lo hi / (lo : ℝ) := by
  have hloR : 0 < (lo : ℝ) := by exact_mod_cast (show 0 < lo by omega)
  have hterm : ∀ n ∈ Finset.Ico (lo + 1) (hi + 1),
      |x n - x (n - 1)| / (n : ℝ) ≤
        |x n - x (n - 1)| / (lo : ℝ) := by
    intro n hn
    have hnlo : (lo : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast (show lo ≤ n by
        have hnIco := Finset.mem_Ico.mp hn
        omega)
    exact div_le_div_of_nonneg_left (abs_nonneg _) hloR hnlo
  calc
    adjacentWeightedVariation x lo hi ≤
        ∑ n ∈ Finset.Ico (lo + 1) (hi + 1),
          |x n - x (n - 1)| / (lo : ℝ) := by
      exact Finset.sum_le_sum hterm
    _ = adjacentTotalVariation x lo hi / (lo : ℝ) := by
      unfold adjacentTotalVariation
      rw [Finset.sum_div]

/-- Combined weighted-variation consequence of a one-sided increment bound. -/
theorem adjacentWeightedVariation_le_of_oneSided
    {x : ℕ → ℝ} {A B : ℝ} {lo hi : ℕ}
    (hlo : 1 ≤ lo) (hlohi : lo ≤ hi) (hA : 0 ≤ A)
    (hxhi : 0 ≤ x hi) (hxlo : x lo ≤ B)
    (hstep : ∀ n ∈ Finset.Ico (lo + 1) (hi + 1),
      x n - x (n - 1) ≤ A / (n : ℝ)) :
    adjacentWeightedVariation x lo hi ≤
      (2 * A * adjacentHarmonicWeight lo hi + B) / (lo : ℝ) := by
  calc
    adjacentWeightedVariation x lo hi ≤
        adjacentTotalVariation x lo hi / (lo : ℝ) :=
      adjacentWeightedVariation_le_total_div hlo
    _ ≤ (2 * A * adjacentHarmonicWeight lo hi + B) / (lo : ℝ) := by
      exact div_le_div_of_nonneg_right
        (adjacentTotalVariation_le_of_oneSided hlohi hA hxhi hxlo hstep)
        (by positivity)

theorem criticalTheta_inv_lt_three : criticalTheta⁻¹ < 3 := by
  rw [criticalTheta_eq]
  norm_num [betaLower]

theorem criticalTheta_lt_one : criticalTheta < 1 := by
  rw [criticalTheta_eq]
  norm_num [betaLower]

/-- On a cutoff interval the relative mass increment lies in `(0,3)`. -/
theorem relativeMassIncrement_cutoff_bounds
    {T : ℕ} {h : StepSchedule T} {lo hi q : ℕ}
    (hcut : CutoffConditions criticalP h lo hi)
    (hq : q ∈ Finset.Icc lo hi) :
    0 < relativeMassIncrement h q ∧ relativeMassIncrement h q < 3 := by
  obtain ⟨_, hv0, hvB, _⟩ := hcut q hq
  exact ⟨hv0, hvB.trans criticalTheta_inv_lt_three⟩

/-- The exact mass-increment recurrence implies a coarse but uniform
`24/n` upper bound for adjacent increases. -/
theorem relativeMassIncrement_oneSided
    {T : ℕ} {h : StepSchedule T} (hh : IsNonnegativeSchedule h)
    {lo hi n : ℕ} (hlo : 8 ≤ lo) (hhir : hi ≤ longCount h)
    (hcut : CutoffConditions criticalP h lo hi)
    (hn : n ∈ Finset.Ico (lo + 1) (hi + 1)) :
    relativeMassIncrement h n - relativeMassIncrement h (n - 1) ≤
      24 / (n : ℝ) := by
  have hnIco := Finset.mem_Ico.mp hn
  have hnprevMem : n - 1 ∈ Finset.Icc lo hi :=
    Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  have hnMem : n ∈ Finset.Icc lo hi :=
    Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  obtain ⟨hu0, hu3⟩ := relativeMassIncrement_cutoff_bounds hcut hnprevMem
  obtain ⟨hv0, _hv3⟩ := relativeMassIncrement_cutoff_bounds hcut hnMem
  let N : ℝ := n
  let u : ℝ := relativeMassIncrement h (n - 1)
  let v : ℝ := relativeMassIncrement h n
  have hn0 : 1 ≤ n - 1 := by omega
  have hnlt : n - 1 < longCount h := by omega
  have hsmall : relativeMassIncrement h (n - 1) < ((n - 1 : ℕ) : ℝ) := by
    have : (3 : ℝ) ≤ (n - 1 : ℕ) := by exact_mod_cast (show 3 ≤ n - 1 by omega)
    exact hu3.trans_le this
  have hmass := massIncrementBound hh hn0 hnlt hsmall
  have hnSucc : n - 1 + 1 = n := Nat.sub_add_cancel (by omega : 1 ≤ n)
  rw [hnSucc] at hmass
  have hNR : 8 ≤ N := by
    dsimp only [N]
    exact_mod_cast (show 8 ≤ n by omega)
  have hN0 : 0 < N := by linarith
  have hu0R : 0 < u := hu0
  have hu3R : u < 3 := hu3
  have hv0R : 0 < v := hv0
  have hden : 0 < N - 1 - u := by linarith
  have hmassR : v ≤ N * u / (N - 1 - u) := by
    dsimp only [N, u, v]
    have hnCast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ n)]
      norm_num
    rw [hnCast] at hmass
    simpa using hmass
  have huquad : u * (u + 1) ≤ 12 := by
    have hprod : 0 ≤ (3 - u) * (u + 4) :=
      mul_nonneg (by linarith) (by linarith)
    nlinarith
  have hcross : N * (u * (u + 1)) ≤ 24 * (N - 1 - u) := by
    have hleft : N * (u * (u + 1)) ≤ N * 12 :=
      mul_le_mul_of_nonneg_left huquad hN0.le
    nlinarith
  have hfrac : u * (u + 1) / (N - 1 - u) ≤ 24 / N := by
    rw [div_le_div_iff₀ hden hN0]
    nlinarith
  have hid : N * u / (N - 1 - u) - u =
      u * (u + 1) / (N - 1 - u) := by
    field_simp [hden.ne']
    ring
  dsimp only [N, u, v] at hmassR hfrac hid ⊢
  linarith

/-- The endpoint defect is nonnegative and at most one on a cutoff interval. -/
theorem endpointDefect_cutoff_bounds
    {T : ℕ} {h : StepSchedule T} {lo hi q : ℕ}
    (hcut : CutoffConditions criticalP h lo hi)
    (hq : q ∈ Finset.Icc lo hi) :
    0 ≤ endpointDefect h q ∧ endpointDefect h q ≤ 1 := by
  obtain ⟨hz, hv0, _, hdensity⟩ := hcut q hq
  unfold endpointDefect
  constructor
  · exact mul_nonneg hv0.le (sub_nonneg.mpr hz.le)
  · have hthetaTerm :
        0 ≤ relativeMassIncrement h q * criticalTheta :=
      mul_nonneg hv0.le criticalTheta_pos.le
    nlinarith [show zetaState h q * relativeMassIncrement h q ≤ 1 by
      simpa [mul_comm] using hdensity]

/-- The moment/defect recurrence gives a uniform one-sided increment bound
for the endpoint defect. -/
theorem endpointDefect_oneSided
    {T Q : ℕ} (hQ : criticalTheta⁻¹ < (Q : ℝ))
    {h : StepSchedule T} (hh : IsNonnegativeSchedule h)
    {lo hi n : ℕ} (hQlo : Q ≤ lo) (hlohi : lo ≤ hi)
    (hhir : hi ≤ longCount h)
    (hcut : CutoffConditions criticalP h lo (longCount h))
    (hn : n ∈ Finset.Ico (lo + 1) (hi + 1)) :
    endpointDefect h n - endpointDefect h (n - 1) ≤ 52 / (n : ℝ) := by
  have hnIco := Finset.mem_Ico.mp hn
  have hnFull : n ∈ Finset.Ico (lo + 1) (longCount h + 1) :=
    Finset.mem_Ico.mpr ⟨hnIco.1, by omega⟩
  have hnprevMem : n - 1 ∈ Finset.Icc lo (longCount h) :=
    Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  have hnMem : n ∈ Finset.Icc lo (longCount h) :=
    Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  obtain ⟨heprev0, _⟩ := endpointDefect_cutoff_bounds hcut hnprevMem
  obtain ⟨_, hv0, _, _⟩ := hcut n hnMem
  have hs := scheduleMomentOneStep hQ hh hQlo hcut hnFull
  have hnR0 : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hlhs : 0 ≤
      ((relativeMassIncrement h n - betaLower) ^ 2 +
        endpointDefect h (n - 1) / criticalTheta) / (n : ℝ) := by
    positivity [criticalTheta_pos]
  have hsource :
      2 * (betaLower + 1) *
          (betaLower - relativeMassIncrement h n) / (n : ℝ) ≤
        4 / (n : ℝ) := by
    apply div_le_div_of_nonneg_right _ hnR0.le
    norm_num [betaLower] at hv0 ⊢
    linarith
  have herror : momentDriftConstant / (n : ℝ) ^ 2 ≤
      48 / (n : ℝ) := by
    unfold momentDriftConstant
    rw [div_le_div_iff₀ (sq_pos_of_pos hnR0) hnR0]
    have hnR1 : 1 ≤ (n : ℝ) := by exact_mod_cast (show 1 ≤ n by omega)
    nlinarith
  let d := endpointDefect h n - endpointDefect h (n - 1)
  by_cases hd : 0 ≤ d
  · have hdDiv : d / criticalTheta ≤ 52 / (n : ℝ) := by
      have hdRaw : d / criticalTheta ≤
          2 * (betaLower + 1) *
              (betaLower - relativeMassIncrement h n) / (n : ℝ) +
            momentDriftConstant / (n : ℝ) ^ 2 := by
        dsimp only [d]
        linarith
      calc
        d / criticalTheta ≤
            2 * (betaLower + 1) *
                (betaLower - relativeMassIncrement h n) / (n : ℝ) +
              momentDriftConstant / (n : ℝ) ^ 2 := hdRaw
        _ ≤ 4 / (n : ℝ) + 48 / (n : ℝ) := add_le_add hsource herror
        _ = 52 / (n : ℝ) := by ring
    have hdSelf : d ≤ d / criticalTheta := by
      apply (le_div_iff₀ criticalTheta_pos).2
      have ht := criticalTheta_lt_one
      nlinarith
    dsimp only [d] at hdDiv hdSelf ⊢
    exact hdSelf.trans hdDiv
  · have hdneg : d < 0 := lt_of_not_ge hd
    dsimp only [d] at hdneg ⊢
    have hright : 0 ≤ 52 / (n : ℝ) := by positivity
    linarith

/-- Total variation budget for the relative mass increment on a cutoff
interval. -/
theorem relativeMassIncrement_totalVariation
    {T : ℕ} {h : StepSchedule T} (hh : IsNonnegativeSchedule h)
    {lo hi : ℕ} (hlo : 8 ≤ lo) (hlohi : lo ≤ hi)
    (hhir : hi ≤ longCount h)
    (hcut : CutoffConditions criticalP h lo hi) :
    adjacentTotalVariation (relativeMassIncrement h) lo hi ≤
      48 * adjacentHarmonicWeight lo hi + 3 := by
  obtain ⟨hhi0, _⟩ := relativeMassIncrement_cutoff_bounds hcut
    (Finset.mem_Icc.mpr ⟨hlohi, le_rfl⟩)
  obtain ⟨_, hlo3⟩ := relativeMassIncrement_cutoff_bounds hcut
    (Finset.mem_Icc.mpr ⟨le_rfl, hlohi⟩)
  convert adjacentTotalVariation_le_of_oneSided
    (x := relativeMassIncrement h) (A := 24) (B := 3)
    hlohi (by norm_num) hhi0.le hlo3.le
    (fun n hn ↦ relativeMassIncrement_oneSided hh hlo hhir hcut hn) using 1 <;>
    ring

/-- Total variation budget for the endpoint defect. -/
theorem endpointDefect_totalVariation
    {T Q : ℕ} (hQ : criticalTheta⁻¹ < (Q : ℝ))
    {h : StepSchedule T} (hh : IsNonnegativeSchedule h)
    {lo hi : ℕ} (hQlo : Q ≤ lo) (hlohi : lo ≤ hi)
    (hhir : hi ≤ longCount h)
    (hcut : CutoffConditions criticalP h lo (longCount h)) :
    adjacentTotalVariation (endpointDefect h) lo hi ≤
      104 * adjacentHarmonicWeight lo hi + 1 := by
  obtain ⟨hhi0, _⟩ := endpointDefect_cutoff_bounds hcut
    (Finset.mem_Icc.mpr ⟨hlohi, hhir⟩)
  obtain ⟨_, hlo1⟩ := endpointDefect_cutoff_bounds hcut
    (Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩)
  convert adjacentTotalVariation_le_of_oneSided
    (x := endpointDefect h) (A := 52) (B := 1)
    hlohi (by norm_num) hhi0 hlo1
    (fun n hn ↦ endpointDefect_oneSided hQ hh hQlo hlohi hhir hcut hn) using 1 <;>
    ring


private theorem adjacentTotalVariation_mono_left
    {x : ℕ → ℝ} {a b c : ℕ} (hab : a ≤ b) (hbc : b ≤ c) :
    adjacentTotalVariation x b c ≤ adjacentTotalVariation x a c := by
  unfold adjacentTotalVariation
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro n hn
    have hnIco := Finset.mem_Ico.mp hn
    exact Finset.mem_Ico.mpr ⟨by omega, hnIco.2⟩
  · intro n _ _
    exact abs_nonneg _

private theorem abs_endpoint_sub_le_totalVariation
    (x : ℕ → ℝ) {a b : ℕ} (hab : a ≤ b) :
    |x b - x a| ≤ adjacentTotalVariation x a b := by
  rw [← sum_adjacent_difference x hab]
  exact Finset.abs_sum_le_sum_abs _ _

private theorem endpoint_le_point_add_blockVariation
    (x : ℕ → ℝ) {a b n : ℕ} (han : a ≤ n) (hnb : n ≤ b) :
    x b ≤ x n + adjacentTotalVariation x a b := by
  have htriangle : x b ≤ x n + |x b - x n| := by
    have habs : x b - x n ≤ |x b - x n| := le_abs_self _
    linarith
  have hsub := abs_endpoint_sub_le_totalVariation x hnb
  have hmono := adjacentTotalVariation_mono_left (x := x) han hnb
  linarith

private theorem dilationBlock_length
    {j m : ℕ} (hm : 1 ≤ m) :
    j * m + 1 - (j * (m - 1) + 1) = j := by
  have hmId : m - 1 + 1 = m := Nat.sub_add_cancel hm
  have hmul : j * m = j * (m - 1) + j := by
    calc
      j * m = j * ((m - 1) + 1) := congrArg (fun t : ℕ ↦ j * t) hmId.symm
      _ = j * (m - 1) + j := by rw [Nat.mul_add, Nat.mul_one]
  rw [hmul]
  omega

private theorem endpoint_block_le
    (x : ℕ → ℝ) {j m : ℕ} (hm : 1 ≤ m) :
    j * x (j * m) ≤
      ∑ n ∈ Finset.Ico (j * (m - 1) + 1) (j * m + 1), x n +
        j * adjacentTotalVariation x (j * (m - 1)) (j * m) := by
  let V := adjacentTotalVariation x (j * (m - 1)) (j * m)
  have hpoint : ∀ n ∈ Finset.Ico (j * (m - 1) + 1) (j * m + 1),
      x (j * m) ≤ x n + V := by
    intro n hn
    have hnIco := Finset.mem_Ico.mp hn
    exact endpoint_le_point_add_blockVariation x (by omega) (by omega)
  have hsum := Finset.sum_le_sum hpoint
  have hcard : (Finset.Ico (j * (m - 1) + 1) (j * m + 1)).card = j := by
    simp only [Nat.card_Ico]
    exact dilationBlock_length hm
  dsimp only [V] at hsum ⊢
  rw [Finset.sum_add_distrib, Finset.sum_const, hcard] at hsum
  simp only [nsmul_eq_mul] at hsum
  simpa [Finset.sum_const, hcard, nsmul_eq_mul, mul_comm, mul_left_comm,
    mul_assoc] using hsum

private theorem sum_dilation_blocks
    (f : ℕ → ℝ) (j : ℕ) {M N : ℕ} (hMN : M ≤ N) :
    ∑ m ∈ Finset.Ico (M + 1) (N + 1),
        ∑ n ∈ Finset.Ico (j * (m - 1) + 1) (j * m + 1), f n =
      ∑ n ∈ Finset.Ico (j * M + 1) (j * N + 1), f n := by
  induction N, hMN using Nat.le_induction with
  | base => simp
  | succ N hMN ih =>
      rw [Finset.sum_Ico_succ_top (by omega), ih]
      simp only [Nat.add_sub_cancel]
      have hleft : j * M + 1 ≤ j * N + 1 :=
        Nat.add_le_add_right (Nat.mul_le_mul_left j hMN) 1
      have hright : j * N + 1 ≤ j * (N + 1) + 1 :=
        Nat.add_le_add_right (Nat.mul_le_mul_left j (Nat.le_succ N)) 1
      exact Finset.sum_Ico_consecutive f hleft hright

/-- A fixed-dilation sample is bounded by the complete consecutive-rank sum
plus an explicit total-variation error.  This is the rigorous substitute for
the false assertion that residue classes of ranks are automatically
equidistributed. -/
theorem fixedDilationSample_le_fullSum_add_variation
    (x : ℕ → ℝ) {j M N : ℕ} (hMN : M ≤ N) :
    j * ∑ m ∈ Finset.Ico (M + 1) (N + 1), x (j * m) ≤
      ∑ n ∈ Finset.Ico (j * M + 1) (j * N + 1), x n +
        j * adjacentTotalVariation x (j * M) (j * N) := by
  have hlocal : ∀ m ∈ Finset.Ico (M + 1) (N + 1),
      j * x (j * m) ≤
        ∑ n ∈ Finset.Ico (j * (m - 1) + 1) (j * m + 1), x n +
          j * adjacentTotalVariation x (j * (m - 1)) (j * m) := by
    intro m hm
    exact endpoint_block_le x (by
      have hmIco := Finset.mem_Ico.mp hm
      omega)
  calc
    j * ∑ m ∈ Finset.Ico (M + 1) (N + 1), x (j * m) =
        ∑ m ∈ Finset.Ico (M + 1) (N + 1), j * x (j * m) := by
      rw [Finset.mul_sum]
    _ ≤ ∑ m ∈ Finset.Ico (M + 1) (N + 1),
        ((∑ n ∈ Finset.Ico (j * (m - 1) + 1) (j * m + 1), x n) +
          j * adjacentTotalVariation x (j * (m - 1)) (j * m)) := by
      exact Finset.sum_le_sum hlocal
    _ = (∑ n ∈ Finset.Ico (j * M + 1) (j * N + 1), x n) +
        j * adjacentTotalVariation x (j * M) (j * N) := by
      rw [Finset.sum_add_distrib, sum_dilation_blocks x j hMN]
      unfold adjacentTotalVariation
      rw [← Finset.mul_sum]
      rw [sum_dilation_blocks
        (fun n ↦ |x n - x (n - 1)|) j hMN]

/-- Rank normalization used to convert a harmonic sample at `jm` into the
ordinary block endpoint sample of `x(n)/n`. -/
def rankNormalized (x : ℕ → ℝ) (n : ℕ) : ℝ := x n / (n : ℝ)

/-- Harmonic form of the fixed-dilation sampler. -/
theorem fixedDilationHarmonicSample_le
    (x : ℕ → ℝ) {j M N : ℕ}
    (hj : 1 ≤ j) (hMN : M ≤ N) :
    ∑ m ∈ Finset.Ico (M + 1) (N + 1), x (j * m) / (m : ℝ) ≤
      ∑ n ∈ Finset.Ico (j * M + 1) (j * N + 1), x n / (n : ℝ) +
        j * adjacentTotalVariation (rankNormalized x) (j * M) (j * N) := by
  have hmterm : ∀ m ∈ Finset.Ico (M + 1) (N + 1),
      x (j * m) / (m : ℝ) = j * rankNormalized x (j * m) := by
    intro m hm
    have hm0 : (m : ℝ) ≠ 0 := by
      exact_mod_cast (show m ≠ 0 by
        have hmIco := Finset.mem_Ico.mp hm
        omega)
    have hj0 : (j : ℝ) ≠ 0 := by exact_mod_cast (show j ≠ 0 by omega)
    unfold rankNormalized
    push_cast
    field_simp [hm0, hj0]
  have hs := fixedDilationSample_le_fullSum_add_variation
    (x := rankNormalized x) (j := j) hMN
  rw [Finset.mul_sum] at hs
  calc
    ∑ m ∈ Finset.Ico (M + 1) (N + 1), x (j * m) / (m : ℝ) =
        ∑ m ∈ Finset.Ico (M + 1) (N + 1),
          j * rankNormalized x (j * m) := by
      exact Finset.sum_congr rfl hmterm
    _ ≤ ∑ n ∈ Finset.Ico (j * M + 1) (j * N + 1),
          rankNormalized x n +
        j * adjacentTotalVariation (rankNormalized x) (j * M) (j * N) := hs
    _ = ∑ n ∈ Finset.Ico (j * M + 1) (j * N + 1), x n / (n : ℝ) +
        j * adjacentTotalVariation (rankNormalized x) (j * M) (j * N) := by
      rfl

end

end GDLowerBound.FourBlock
