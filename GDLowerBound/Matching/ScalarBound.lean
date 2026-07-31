import GDLowerBound.Matching.Endpoint
import GDLowerBound.RankAnalysis.Adjacent
import GDLowerBound.RankAnalysis.Parameters

/-!
# Scalar consequences of the endpoint matching estimate

This file relates the order-free endpoint weights to the ranked reciprocal
mass `zetaState`.  In particular it checks that restoring the selected ranks
to chronological order does not change their reciprocal sum.
-/

namespace GDLowerBound

open scoped BigOperators Real

namespace Schedule.Chain

variable {T : ℕ} {h : StepSchedule T}

/-- Chronological selection is an equivalence from positions to the selected
time labels. -/
noncomputable def selectedEquiv (c : Chain h) : Fin c.length ≃ ↥c.times :=
  Equiv.ofBijective
    (fun i ↦ ⟨c.selected i, c.selected_mem i⟩)
    ((Fintype.bijective_iff_injective_and_card _).2 ⟨
      (fun i j hij ↦ c.selected_injective (Subtype.ext_iff.mp hij)), by
        rw [Fintype.card_fin, Fintype.card_coe]
        rfl⟩)

/-- Summing over chronological positions is the same as summing over the
underlying selected finset. -/
theorem sum_selected (c : Chain h) (f : Fin T → ℝ) :
    ∑ i : Fin c.length, f (c.selected i) = ∑ t ∈ c.times, f t := by
  let e := selectedEquiv c
  calc
    ∑ i : Fin c.length, f (c.selected i) =
        ∑ i : Fin c.length, f (e i) := rfl
    _ = ∑ t : ↥c.times, f t := e.sum_comp (fun t : ↥c.times ↦ f t)
    _ = ∑ t ∈ c.times, f t := by
      simpa using Finset.sum_attach c.times f

end Schedule.Chain

namespace RankAnalysis

open Schedule

/-- The one-based reciprocal-prefix definition is exactly the sum of the
first `q` entries of the ranked excess list. -/
theorem reciprocalPrefix_eq_sum_take {T : ℕ} (h : StepSchedule T) {q : ℕ}
    (hq : q ≤ longCount h) :
    reciprocalPrefix h q =
      (((rankedExcesses h).map fun a ↦ a⁻¹).take q).sum := by
  induction q with
  | zero => simp
  | succ q ih =>
      have hq_lt : q < longCount h := by omega
      have hq_le : q ≤ longCount h := Nat.le_of_lt hq_lt
      have hlen : q < (rankedExcesses h).length := by
        simpa only [rankedExcesses_length] using hq_lt
      rw [reciprocalPrefix_succ, ih hq_le]
      rw [List.sum_take_succ]
      · unfold rankedExcessOne
        simp only [Nat.add_sub_cancel]
        rw [List.getD_eq_getElem (rankedExcesses h) 0 hlen]
        rw [List.getElem_map (fun a : ℝ ↦ a⁻¹)]
      · simpa only [List.length_map, rankedExcesses_length] using hq_lt

/-- Chronological reordering of the top ranks preserves the sum of their
reciprocal excesses. -/
theorem chronologicalReciprocalSum {T : ℕ} (h : StepSchedule T) {q : ℕ}
    (hq : q ≤ longCount h) :
    (∑ i : Fin q, (Matching.chronologicalExcess h q hq i)⁻¹) =
      reciprocalPrefix h q := by
  let c : Chain h := topChain h q
  let e : Fin q ≃ Fin c.length :=
    (Fin.castOrderIso (topChain_length_of_le h hq).symm).toEquiv
  calc
    (∑ i : Fin q, (Matching.chronologicalExcess h q hq i)⁻¹) =
        ∑ i : Fin q, (excess h (c.selected (e i)))⁻¹ := by rfl
    _ = ∑ i : Fin c.length, (excess h (c.selected i))⁻¹ :=
      e.sum_comp (fun i : Fin c.length ↦ (excess h (c.selected i))⁻¹)
    _ = ∑ t ∈ c.times, (excess h t)⁻¹ :=
      Schedule.Chain.sum_selected c (fun t ↦ (excess h t)⁻¹)
    _ = ∑ t ∈ topTimes h q, (excess h t)⁻¹ := by rfl
    _ = (((rankedTimes h).take q).map
          (fun t ↦ (excess h t)⁻¹)).sum :=
      sum_topTimes h q (fun t ↦ (excess h t)⁻¹)
    _ = (((rankedExcesses h).map fun a ↦ a⁻¹).take q).sum := by
      simp only [rankedExcesses, List.map_map, List.map_take]
      rfl
    _ = reciprocalPrefix h q := (reciprocalPrefix_eq_sum_take h hq).symm

end RankAnalysis

namespace Matching

open Schedule RankAnalysis

/-- Exact total weight of the augmented endpoint path. -/
theorem topPathWeight_sum {T : ℕ} {h : StepSchedule T}
    {q : ℕ} (hq₂ : 2 ≤ q)
    (hq : q ≤ longCount h) :
    (∑ i, topPathWeight h q hq i) =
      2 * (q : ℝ) * zetaState h q + 1 / ((q : ℝ) - 1) := by
  have hq0 : 0 < q := lt_of_lt_of_le (by decide : 0 < 2) hq₂
  have hqR0 : 0 < (q : ℝ) := by exact_mod_cast hq0
  rw [Fin.sum_univ_castSucc]
  rw [topPathWeight_last]
  simp_rw [topPathWeight_castSucc h hq0 hq]
  rw [← Finset.mul_sum]
  rw [RankAnalysis.chronologicalReciprocalSum h hq]
  unfold zetaState
  field_simp [hqR0.ne']

/-- The geometric mean per edge of the two endpoint matchings is controlled
by the total augmented-path weight.  This is the scalar part of the matching
argument, before the total weight is expressed through `zetaState`. -/
theorem matchingEnvelope_geomMean_le_total {q : ℕ} (hq₂ : 2 ≤ q)
    (v : Fin (q + 1) → ℝ) (hv : ∀ i, 0 ≤ v i) :
    (matchingEnvelope v) ^ ((q : ℝ)⁻¹) ≤
      let x := (∑ i, v i) / ((q : ℝ) - 1)
      x + x ^ 2 / 2 := by
  let S : ℝ := ∑ i, v i
  let x : ℝ := S / ((q : ℝ) - 1)
  let R : ℝ := x + x ^ 2 / 2
  have hq₀ : 0 < q := by omega
  have hq_ne : q ≠ 0 := hq₀.ne'
  have hqR₀ : 0 < (q : ℝ) := by exact_mod_cast hq₀
  have hqm1 : 0 < (q : ℝ) - 1 := by
    have hqRone : (1 : ℝ) < (q : ℝ) := by
      exact_mod_cast (show 1 < q by omega)
    linarith
  have hS : 0 ≤ S := Finset.sum_nonneg fun i _ ↦ hv i
  have hx : 0 ≤ x := div_nonneg hS hqm1.le
  have hR : 0 ≤ R := by
    dsimp only [R]
    positivity
  have hkPlus₀ : 0 < kPlus q := kPlus_pos hq₀
  have hkMinus₀ : 0 < kMinus q := kMinus_pos hq₂
  have hkPlus_ne : kPlus q ≠ 0 := hkPlus₀.ne'
  have hkMinus_ne : kMinus q ≠ 0 := hkMinus₀.ne'
  have hcardPlus : 2 * kPlus q ≤ Fintype.card (Fin (q + 1)) := by
    simpa using two_kPlus_le q
  have hcardMinus : 2 * kMinus q ≤ Fintype.card (Fin (q + 1)) := by
    simpa using two_kMinus_le q
  have hPPlus₀ : 0 ≤ Pψ v (kPlus q) :=
    Pψ_nonneg hv ((labeledMatching_nonempty_iff (kPlus q)).2 hcardPlus)
  have hPMinus₀ : 0 ≤ Pψ v (kMinus q) :=
    Pψ_nonneg hv ((labeledMatching_nonempty_iff (kMinus q)).2 hcardMinus)
  have hkPlusLowerNat : q - 1 ≤ 2 * kPlus q := by
    simp only [kPlus]
    omega
  have hkMinusLowerNat : q - 1 ≤ 2 * kMinus q := by
    simp only [kMinus]
    omega
  have hkPlusLower : (q : ℝ) - 1 ≤ 2 * (kPlus q : ℝ) := by
    have hcast : ((q - 1 : ℕ) : ℝ) ≤ ((2 * kPlus q : ℕ) : ℝ) := by
      exact_mod_cast hkPlusLowerNat
    norm_num [Nat.cast_sub (by omega : 1 ≤ q)] at hcast
    linarith
  have hkMinusLower : (q : ℝ) - 1 ≤ 2 * (kMinus q : ℝ) := by
    have hcast : ((q - 1 : ℕ) : ℝ) ≤ ((2 * kMinus q : ℕ) : ℝ) := by
      exact_mod_cast hkMinusLowerNat
    norm_num [Nat.cast_sub (by omega : 1 ≤ q)] at hcast
    linarith
  have root_bound {k : ℕ} (hk : 0 < k)
      (hlower : (q : ℝ) - 1 ≤ 2 * (k : ℝ))
      (hcard : 2 * k ≤ Fintype.card (Fin (q + 1))) :
      (Pψ v k) ^ ((k : ℝ)⁻¹) ≤ R := by
    have hkR : 0 < (k : ℝ) := by exact_mod_cast hk
    have hlinear : S / (2 * (k : ℝ)) ≤ S / ((q : ℝ) - 1) :=
      div_le_div_of_nonneg_left hS hqm1 hlower
    have hsquare : ((q : ℝ) - 1) ^ 2 ≤ (2 * (k : ℝ)) ^ 2 :=
      (sq_le_sq₀ hqm1.le (by positivity)).2 hlower
    have hdenSquare :
        2 * ((q : ℝ) - 1) ^ 2 ≤ 8 * (k : ℝ) ^ 2 := by
      nlinarith
    have hquadratic :
        S ^ 2 / (8 * (k : ℝ) ^ 2) ≤
          S ^ 2 / (2 * ((q : ℝ) - 1) ^ 2) :=
      div_le_div_of_nonneg_left (sq_nonneg S) (by positivity) hdenSquare
    calc
      (Pψ v k) ^ ((k : ℝ)⁻¹) ≤
          S / (2 * (k : ℝ)) + S ^ 2 / (8 * (k : ℝ) ^ 2) := by
        simpa only [S] using Pψ_geomMean_le_total hk hcard v hv
      _ ≤ S / ((q : ℝ) - 1) +
          S ^ 2 / (2 * ((q : ℝ) - 1) ^ 2) :=
        add_le_add hlinear hquadratic
      _ = R := by
        dsimp only [R, x]
        field_simp [hqm1.ne']
  have hrootPlus : (Pψ v (kPlus q)) ^ ((kPlus q : ℝ)⁻¹) ≤ R :=
    root_bound hkPlus₀ hkPlusLower hcardPlus
  have hrootMinus : (Pψ v (kMinus q)) ^ ((kMinus q : ℝ)⁻¹) ≤ R :=
    root_bound hkMinus₀ hkMinusLower hcardMinus
  have hPPlus : Pψ v (kPlus q) ≤ R ^ kPlus q := by
    calc
      Pψ v (kPlus q) =
          ((Pψ v (kPlus q)) ^ ((kPlus q : ℝ)⁻¹)) ^ kPlus q :=
        (Real.rpow_inv_natCast_pow hPPlus₀ hkPlus_ne).symm
      _ ≤ R ^ kPlus q :=
        pow_le_pow_left₀ (Real.rpow_nonneg hPPlus₀ _) hrootPlus _
  have hPMinus : Pψ v (kMinus q) ≤ R ^ kMinus q := by
    calc
      Pψ v (kMinus q) =
          ((Pψ v (kMinus q)) ^ ((kMinus q : ℝ)⁻¹)) ^ kMinus q :=
        (Real.rpow_inv_natCast_pow hPMinus₀ hkMinus_ne).symm
      _ ≤ R ^ kMinus q :=
        pow_le_pow_left₀ (Real.rpow_nonneg hPMinus₀ _) hrootMinus _
  have hEnvelope₀ : 0 ≤ matchingEnvelope v := by
    exact mul_nonneg hPPlus₀ hPMinus₀
  have hEnvelope : matchingEnvelope v ≤ R ^ q := by
    unfold matchingEnvelope
    calc
      Pψ v (kPlus q) * Pψ v (kMinus q) ≤
          R ^ kPlus q * R ^ kMinus q :=
        mul_le_mul hPPlus hPMinus hPMinus₀ (pow_nonneg hR _)
      _ = R ^ (kPlus q + kMinus q) := (pow_add R _ _).symm
      _ = R ^ q := by rw [kPlus_add_kMinus]
  change (matchingEnvelope v) ^ ((q : ℝ)⁻¹) ≤ R
  calc
    (matchingEnvelope v) ^ ((q : ℝ)⁻¹) ≤
        (R ^ q) ^ ((q : ℝ)⁻¹) :=
      Real.rpow_le_rpow hEnvelope₀ hEnvelope (inv_nonneg.mpr hqR₀.le)
    _ = R := Real.pow_rpow_inv_natCast hR hq_ne

/-- Equation `eq:scalar-matching-bound`: after inserting the exact total
weight, the normalized endpoint matching factor depends only on
`zetaState`. -/
theorem topPath_matching_geomMean_le {T : ℕ} {h : StepSchedule T}
    (hh : IsNonnegativeSchedule h) {q : ℕ} (hq₂ : 2 ≤ q)
    (hq : q ≤ longCount h) :
    (matchingEnvelope (topPathWeight h q hq)) ^ ((q : ℝ)⁻¹) ≤
      let x :=
        (2 * (q : ℝ) * zetaState h q + 1 / ((q : ℝ) - 1)) /
          ((q : ℝ) - 1)
      x + x ^ 2 / 2 := by
  have hbound := matchingEnvelope_geomMean_le_total hq₂
    (topPathWeight h q hq) (fun i ↦ (topPathWeight_pos hh hq₂ hq i).le)
  simpa only [topPathWeight_sum hq₂ hq] using hbound

/-- The manuscript's normalized matching factor `mu_q`. -/
noncomputable def normalizedMatchingFactor {T : ℕ} (h : StepSchedule T)
    (q : ℕ) (hq : q ≤ longCount h) : ℝ :=
  (matchingEnvelope (topPathWeight h q hq)) ^ ((q : ℝ)⁻¹)

theorem normalizedMatchingFactor_nonneg {T : ℕ} {h : StepSchedule T}
    (hh : IsNonnegativeSchedule h) {q : ℕ} (hq₂ : 2 ≤ q)
    (hq : q ≤ longCount h) :
    0 ≤ normalizedMatchingFactor h q hq := by
  have hv : ∀ i, 0 ≤ topPathWeight h q hq i :=
    fun i ↦ (topPathWeight_pos hh hq₂ hq i).le
  have hcardPlus : 2 * kPlus q ≤ Fintype.card (Fin (q + 1)) := by
    simpa using two_kPlus_le q
  have hcardMinus : 2 * kMinus q ≤ Fintype.card (Fin (q + 1)) := by
    simpa using two_kMinus_le q
  have hplus : 0 ≤ Pψ (topPathWeight h q hq) (kPlus q) :=
    Pψ_nonneg hv ((labeledMatching_nonempty_iff (kPlus q)).2 hcardPlus)
  have hminus : 0 ≤ Pψ (topPathWeight h q hq) (kMinus q) :=
    Pψ_nonneg hv ((labeledMatching_nonempty_iff (kMinus q)).2 hcardMinus)
  unfold normalizedMatchingFactor
  exact Real.rpow_nonneg (mul_nonneg hplus hminus) _

/-- Raising the normalized matching factor back to the rank recovers the
endpoint matching envelope. -/
theorem matchingEnvelope_eq_normalizedMatchingFactor_pow
    {T : ℕ} {h : StepSchedule T} (hh : IsNonnegativeSchedule h)
    {q : ℕ} (hq₂ : 2 ≤ q) (hq : q ≤ longCount h) :
    matchingEnvelope (topPathWeight h q hq) =
      normalizedMatchingFactor h q hq ^ q := by
  have hq_ne : q ≠ 0 := by omega
  have hv : ∀ i, 0 ≤ topPathWeight h q hq i :=
    fun i ↦ (topPathWeight_pos hh hq₂ hq i).le
  have hcardPlus : 2 * kPlus q ≤ Fintype.card (Fin (q + 1)) := by
    simpa using two_kPlus_le q
  have hcardMinus : 2 * kMinus q ≤ Fintype.card (Fin (q + 1)) := by
    simpa using two_kMinus_le q
  have hEnvelope₀ : 0 ≤ matchingEnvelope (topPathWeight h q hq) := by
    unfold matchingEnvelope
    exact mul_nonneg
      (Pψ_nonneg hv ((labeledMatching_nonempty_iff (kPlus q)).2 hcardPlus))
      (Pψ_nonneg hv ((labeledMatching_nonempty_iff (kMinus q)).2 hcardMinus))
  exact (Real.rpow_inv_natCast_pow hEnvelope₀ hq_ne).symm

/-- Named form of `topPath_matching_geomMean_le` for the normalized
matching factor. -/
theorem normalizedMatchingFactor_le {T : ℕ} {h : StepSchedule T}
    (hh : IsNonnegativeSchedule h) {q : ℕ} (hq₂ : 2 ≤ q)
    (hq : q ≤ longCount h) :
    normalizedMatchingFactor h q hq ≤
      let x :=
        (2 * (q : ℝ) * zetaState h q + 1 / ((q : ℝ) - 1)) /
          ((q : ℝ) - 1)
      x + x ^ 2 / 2 := by
  exact topPath_matching_geomMean_le hh hq₂ hq

/-- If `zeta_q` is below the Lyapunov threshold, the scalar argument in
the matching estimate is bounded by the rank-independent cutoff argument
at every `q ≥ Q`. -/
theorem scalarMatchingArgument_le_cutoff {T : ℕ} {h : StepSchedule T}
    {p : ℝ} (hp : pStar < p) {Q q : ℕ} (hQ₂ : 2 ≤ Q) (hQq : Q ≤ q)
    (hzeta : zetaState h q ≤ lyapunovTheta p) :
    (2 * (q : ℝ) * zetaState h q + 1 / ((q : ℝ) - 1)) /
        ((q : ℝ) - 1) ≤ cutoffMatchingArgument p Q := by
  let theta : ℝ := lyapunovTheta p
  let zeta : ℝ := zetaState h q
  let d : ℝ := (q : ℝ) - 1
  let dQ : ℝ := (Q : ℝ) - 1
  have htheta : 0 < theta := by
    exact lyapunovTheta_pos_of_pStar_lt hp
  have hq₂ : 2 ≤ q := hQ₂.trans hQq
  have hd_one : 1 ≤ d := by
    have hqRtwo : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq₂
    dsimp only [d]
    linarith
  have hd : 0 < d := zero_lt_one.trans_le hd_one
  have hdQ : 0 < dQ := by
    have hQRtwo : (2 : ℝ) ≤ (Q : ℝ) := by exact_mod_cast hQ₂
    dsimp only [dQ]
    linarith
  have hdQd : dQ ≤ d := by
    have hcast : (Q : ℝ) ≤ (q : ℝ) := by exact_mod_cast hQq
    dsimp only [dQ, d]
    linarith
  have hzeta_le : zeta ≤ theta := hzeta
  have hzeta_div : 2 * zeta / d ≤ 2 * theta / d := by
    exact div_le_div_of_nonneg_right (by linarith) hd.le
  have hd_le_sq : d ≤ d ^ 2 := by
    nlinarith [mul_nonneg hd.le (sub_nonneg.mpr hd_one)]
  have hinv_sq : 1 / d ^ 2 ≤ 1 / d :=
    div_le_div_of_nonneg_left zero_le_one hd hd_le_sq
  have hidentity :
      (2 * (q : ℝ) * zeta + 1 / ((q : ℝ) - 1)) /
          ((q : ℝ) - 1) =
        2 * zeta + 2 * zeta / d + 1 / d ^ 2 := by
    have hqd : (q : ℝ) = d + 1 := by
      dsimp only [d]
      ring
    rw [hqd]
    field_simp [hd.ne']
    ring
  have hfirst :
      2 * zeta + 2 * zeta / d + 1 / d ^ 2 ≤
        2 * theta + (2 * theta + 1) / d := by
    have hzeta_linear : 2 * zeta ≤ 2 * theta := by linarith
    calc
      2 * zeta + 2 * zeta / d + 1 / d ^ 2 ≤
          2 * theta + 2 * theta / d + 1 / d := by
        linarith
      _ = 2 * theta + (2 * theta + 1) / d := by ring
  have hnumerator : 0 ≤ 2 * theta + 1 := by linarith
  have hcutoffDen :
      (2 * theta + 1) / d ≤ (2 * theta + 1) / dQ :=
    div_le_div_of_nonneg_left hnumerator hdQ hdQd
  rw [hidentity]
  calc
    2 * zeta + 2 * zeta / d + 1 / d ^ 2 ≤
        2 * theta + (2 * theta + 1) / d := hfirst
    _ ≤ 2 * theta + (2 * theta + 1) / dQ :=
      add_le_add (le_refl _) hcutoffDen
    _ = cutoffMatchingArgument p Q := by
      rfl

/-- Equation `eq:uniform-matching-bound`: one cutoff controls all ranks
`q ≥ Q` at which the reciprocal-mass state is at most the Lyapunov
threshold. -/
theorem normalizedMatchingFactor_lt_cutoff {T : ℕ} {h : StepSchedule T}
    (hh : IsNonnegativeSchedule h) {p rho : ℝ} (hp : pStar < p)
    {Q q : ℕ} (hQ₂ : 2 ≤ Q) (hQq : Q ≤ q)
    (hq : q ≤ longCount h)
    (hzeta : zetaState h q ≤ lyapunovTheta p)
    (hcutoff : cutoffMatchingBound p Q < rho) :
    normalizedMatchingFactor h q hq < rho := by
  let x : ℝ :=
    (2 * (q : ℝ) * zetaState h q + 1 / ((q : ℝ) - 1)) /
      ((q : ℝ) - 1)
  let y : ℝ := cutoffMatchingArgument p Q
  have hq₂ : 2 ≤ q := hQ₂.trans hQq
  have hqden : 0 < (q : ℝ) - 1 := by
    have hcast : (1 : ℝ) < (q : ℝ) := by
      exact_mod_cast (show 1 < q by omega)
    linarith
  have hmu : normalizedMatchingFactor h q hq ≤ x + x ^ 2 / 2 := by
    exact normalizedMatchingFactor_le hh hq₂ hq
  have hsum₀ : 0 ≤ ∑ i, topPathWeight h q hq i :=
    Finset.sum_nonneg fun i _ ↦ (topPathWeight_pos hh hq₂ hq i).le
  have hx : 0 ≤ x := by
    dsimp only [x]
    rw [← topPathWeight_sum hq₂ hq]
    exact div_nonneg hsum₀ hqden.le
  have hy : 0 ≤ y := by
    have htheta := lyapunovTheta_pos_of_pStar_lt hp
    have hQden : 0 < (Q : ℝ) - 1 := by
      have hcast : (1 : ℝ) < (Q : ℝ) := by
        exact_mod_cast (show 1 < Q by omega)
      linarith
    dsimp only [y, cutoffMatchingArgument]
    positivity
  have hxy : x ≤ y :=
    scalarMatchingArgument_le_cutoff hp hQ₂ hQq hzeta
  have hsquare : x ^ 2 ≤ y ^ 2 := by
    exact (sq_le_sq₀ hx hy).2 hxy
  have hpoly : x + x ^ 2 / 2 ≤ y + y ^ 2 / 2 := by
    linarith
  have hycutoff : y + y ^ 2 / 2 < rho := by
    simpa only [y, cutoffMatchingBound] using hcutoff
  exact hmu.trans_lt (hpoly.trans_lt hycutoff)

/-- The small-matching-product alternative.  A normalized matching factor
strictly below `rho` gives the endpoint lower bound used in the cutoff
argument. -/
theorem functional_lower_of_normalizedMatchingFactor_lt
    {T : ℕ} {h : StepSchedule T} (hh : IsNonnegativeSchedule h)
    {q : ℕ} (hq₂ : 2 ≤ q) (hq : q ≤ longCount h)
    {rho : ℝ} (hrho : 0 < rho)
    (hsmall : normalizedMatchingFactor h q hq < rho) :
    (rho ^ q)⁻¹ / (2 * unresolvedMass h q) < lowerBoundFunctional h := by
  let D : ℝ := unresolvedMass h q
  let M : ℝ := matchingEnvelope (topPathWeight h q hq)
  have hq₀ : 0 < q := by omega
  have hq_ne : q ≠ 0 := hq₀.ne'
  have hqR : 0 < (q : ℝ) := by exact_mod_cast hq₀
  have hqm1 : 0 < (q : ℝ) - 1 := by
    have hcast : (1 : ℝ) < (q : ℝ) := by
      exact_mod_cast (show 1 < q by omega)
    linarith
  have hD : 0 < D := unresolvedMass_pos hh q
  have hmu₀ : 0 ≤ normalizedMatchingFactor h q hq :=
    normalizedMatchingFactor_nonneg hh hq₂ hq
  have hMidentity : M = normalizedMatchingFactor h q hq ^ q := by
    exact matchingEnvelope_eq_normalizedMatchingFactor_pow hh hq₂ hq
  have hMlt : M < rho ^ q := by
    rw [hMidentity]
    exact pow_lt_pow_left₀ hsmall hmu₀ hq_ne
  have hM : 0 < M := by
    have hvpos : ∀ i, 0 < topPathWeight h q hq i :=
      topPathWeight_pos hh hq₂ hq
    have hpathPos := parityPathProduct_pos hvpos
    have hpathLe := parityPathProduct_le_matchingEnvelope
      (topPathWeight h q hq) (fun i ↦ (hvpos i).le)
    exact hpathPos.trans_le hpathLe
  have hrhoPow : 0 < rho ^ q := pow_pos hrho q
  have hfirst : 1 / (2 * D * rho ^ q) < 1 / (2 * D * M) := by
    apply one_div_lt_one_div_of_lt
    · positivity
    · gcongr
  have hsecond :
      1 / (2 * D * M) <
        (q : ℝ) / (2 * D * ((q : ℝ) - 1) * M) := by
    apply (div_lt_div_iff₀ (by positivity) (by positivity)).2
    have hDM : 0 < 2 * D * M := by positivity
    nlinarith
  have htarget :
      (rho ^ q)⁻¹ / (2 * D) = 1 / (2 * D * rho ^ q) := by
    field_simp [hD.ne', hrhoPow.ne']
  have hendpoint :
      (q : ℝ) / (2 * D * ((q : ℝ) - 1) * M) ≤
        lowerBoundFunctional h := by
    exact endpoint_matching_bound hh hq₂ hq
  change (rho ^ q)⁻¹ / (2 * D) < lowerBoundFunctional h
  rw [htarget]
  exact hfirst.trans (hsecond.trans_le hendpoint)

/-- The large-matching-product alternative begins with a strict density
inequality: failure of the small alternative forces `zeta_q` above the
Lyapunov threshold. -/
theorem zetaState_gt_of_normalizedMatchingFactor_ge
    {T : ℕ} {h : StepSchedule T} (hh : IsNonnegativeSchedule h)
    {p rho : ℝ} (hp : pStar < p) {Q q : ℕ}
    (hQ₂ : 2 ≤ Q) (hQq : Q ≤ q) (hq : q ≤ longCount h)
    (hcutoff : cutoffMatchingBound p Q < rho)
    (hlarge : rho ≤ normalizedMatchingFactor h q hq) :
    lyapunovTheta p < zetaState h q := by
  by_contra hnot
  have hzeta : zetaState h q ≤ lyapunovTheta p := le_of_not_gt hnot
  have hsmall := normalizedMatchingFactor_lt_cutoff
    hh hp hQ₂ hQq hq hzeta hcutoff
  exact (not_lt_of_ge hlarge) hsmall

end Matching
end GDLowerBound
