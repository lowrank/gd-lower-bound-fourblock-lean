import GDLowerBound.Matching.Endpoint

/-!
# The bounded-rank prefix estimate

This file formalizes the diffuse--dense prefix argument from Appendix `app:bounded-rank`.
For a positive cutoff, a dense last rank is handled by the chronological top chain.  A diffuse
last rank is removed and the induction hypothesis is applied to the preceding prefix.  This is the
inductive form of the manuscript's telescoping argument.
-/

namespace GDLowerBound.RankAnalysis

open scoped BigOperators
open GDLowerBound.Schedule
open GDLowerBound.Matching

noncomputable section

/-- The smallest excess among the first `n+1` ranked excesses. -/
def prefixMinimum {T : ℕ} (h : StepSchedule T) (n : ℕ)
    (hn : n + 1 ≤ longCount h) : ℝ :=
  rankedExcessAt h ⟨n, by omega⟩

theorem prefixMinimum_pos {T : ℕ} (h : StepSchedule T) (n : ℕ)
    (hn : n + 1 ≤ longCount h) : 0 < prefixMinimum h n hn :=
  rankedExcessAt_pos h ⟨n, by omega⟩

/-- Removing the last rank of a nonempty prefix gives the one-step residual-mass recursion. -/
theorem unresolvedMass_pred {T : ℕ} (h : StepSchedule T) (n : ℕ)
    (hn : n + 1 ≤ longCount h) :
    unresolvedMass h n = prefixMinimum h n hn + unresolvedMass h (n + 1) := by
  exact unresolvedMass_recurrence h (by omega)

/-- Every excess selected by the top-`n+1` chain dominates the last ranked excess in that prefix. -/
theorem prefixMinimum_le_chronologicalExcess {T : ℕ} (h : StepSchedule T)
    (n : ℕ) (hn : n + 1 ≤ longCount h) (i : Fin (n + 1)) :
    prefixMinimum h n hn ≤ chronologicalExcess h (n + 1) hn i := by
  let c : Chain h := topChain h (n + 1)
  let t : Fin T := c.selected (topChainIndex h (n + 1) hn i)
  have htTop : t ∈ topTimes h (n + 1) := by
    exact c.selected_mem (topChainIndex h (n + 1) hn i)
  have htTake : t ∈ (rankedTimes h).take (n + 1) :=
    (mem_topTimes_iff h (n + 1) t).mp htTop
  obtain ⟨j, hj⟩ := List.get_of_mem htTake
  have hjlt : j.val < n + 1 := by
    exact j.isLt.trans_le (List.length_take_le (n + 1) (rankedTimes h))
  let jr : Fin (longCount h) := ⟨j.val, by omega⟩
  let last : Fin (longCount h) := ⟨n, by omega⟩
  have hjfull : j.val < (rankedTimes h).length := by
    rw [rankedTimes_length]
    omega
  have hjTime : rankedTimeAt h jr = t := by
    unfold rankedTimeAt
    change (rankedTimes h).get ⟨j.val, hjfull⟩ = t
    rw [List.get_eq_getElem]
    rw [List.get_eq_getElem] at hj
    rw [List.getElem_take] at hj
    exact hj
  have hjle : jr ≤ last := by
    exact Fin.mk_le_mk.mpr (by omega)
  have hanti := rankedExcessAt_antitone h hjle
  change rankedExcessAt h last ≤ excess h t
  calc
    rankedExcessAt h last ≤ rankedExcessAt h jr := hanti
    _ = excess h t := by rw [rankedExcessAt_eq, hjTime]

/-! ## A uniform matching estimate for weights at most two -/

theorem psi_le_four {u v : ℝ} (hv₀ : 0 ≤ v)
    (hu : u ≤ 2) (hv : v ≤ 2) : psi u v ≤ 4 := by
  have huv : u * v ≤ 2 * 2 := mul_le_mul hu hv hv₀ (by norm_num)
  unfold psi
  nlinarith

theorem matchingProduct_le_four_pow {q k : ℕ} {v : Fin (q + 1) → ℝ}
    (hv₀ : ∀ i, 0 ≤ v i) (hv₂ : ∀ i, v i ≤ 2)
    (M : LabeledMatching (Fin (q + 1)) k) :
    matchingProduct v M ≤ 4 ^ k := by
  unfold matchingProduct
  calc
    (∏ i, psi (v (M.left i)) (v (M.right i))) ≤ ∏ _i : Fin k, (4 : ℝ) := by
      apply Finset.prod_le_prod
      · intro i _
        exact psi_nonneg (hv₀ (M.left i)) (hv₀ (M.right i))
      · intro i _
        exact psi_le_four (hv₀ (M.right i))
          (hv₂ (M.left i)) (hv₂ (M.right i))
    _ = 4 ^ k := by simp

theorem Pψ_le_four_pow {q k : ℕ} {v : Fin (q + 1) → ℝ}
    (hv₀ : ∀ i, 0 ≤ v i) (hv₂ : ∀ i, v i ≤ 2)
    (hk : 2 * k ≤ q + 1) : Pψ v k ≤ 4 ^ k := by
  have hcard : 2 * k ≤ Fintype.card (Fin (q + 1)) := by simpa using hk
  obtain ⟨M, hM⟩ := exists_matchingProduct_eq_Pψ_of_card v hcard
  rw [← hM]
  exact matchingProduct_le_four_pow hv₀ hv₂ M

/-- If every augmented-path vertex has weight at most two, the two matching maxima contribute at
most `4^q` altogether. -/
theorem matchingEnvelope_le_four_pow {q : ℕ} {v : Fin (q + 1) → ℝ}
    (hv₀ : ∀ i, 0 ≤ v i) (hv₂ : ∀ i, v i ≤ 2) :
    matchingEnvelope v ≤ 4 ^ q := by
  have hp := Pψ_le_four_pow hv₀ hv₂ (two_kPlus_le q)
  have hm := Pψ_le_four_pow hv₀ hv₂ (two_kMinus_le q)
  have hm₀ : 0 ≤ Pψ v (kMinus q) := by
    have hcard : 2 * kMinus q ≤ Fintype.card (Fin (q + 1)) := by
      simpa using two_kMinus_le q
    exact Pψ_nonneg hv₀ ((labeledMatching_nonempty_iff (kMinus q)).2 hcard)
  calc
    matchingEnvelope v ≤ (4 : ℝ) ^ kPlus q * 4 ^ kMinus q := by
      exact mul_le_mul hp hm hm₀ (pow_nonneg (by norm_num) _)
    _ = 4 ^ q := by rw [← pow_add, kPlus_add_kMinus]

theorem topChain_value_eq_inv_reciprocal {T : ℕ} (h : StepSchedule T)
    {q : ℕ} (hq : q ≤ longCount h) :
    (topChain h q).value =
      ((topChain h q).terminalScale *
        ∏ i : Fin q, (chronologicalLocalBound h q hq i)⁻¹)⁻¹ := by
  rw [topChain_value_eq_chronological h hq]
  rw [mul_inv_rev, Finset.prod_inv_distrib]
  simp only [inv_inv]
  ring

/-! ## Dense prefixes -/

/-- Density forces every augmented-path vertex weight to lie in `(0,2]`. -/
theorem topPathWeight_le_two_of_dense {T : ℕ} {h : StepSchedule T}
    {n : ℕ} (hn : 0 < n) (hq : n + 1 ≤ longCount h)
    (hdense : unresolvedMass h (n + 1) ≤
      (n + 1 : ℝ) * prefixMinimum h n hq)
    (j : Fin (n + 2)) :
    topPathWeight h (n + 1) hq j ≤ 2 := by
  unfold topPathWeight
  split_ifs with hj
  · let i : Fin (n + 1) := ⟨j.val, hj⟩
    let k : Fin (topChain h (n + 1)).length :=
      ⟨j.val, by simpa [topChain_length_of_le h hq] using hj⟩
    have hk : k = topChainIndex h (n + 1) hq i := by
      apply Fin.ext
      rfl
    change 2 * unresolvedMass h (n + 1) /
      (((n + 1 : ℕ) : ℝ) * excess h ((topChain h (n + 1)).selected k)) ≤ 2
    rw [hk]
    change 2 * unresolvedMass h (n + 1) /
      (((n + 1 : ℕ) : ℝ) * chronologicalExcess h (n + 1) hq i) ≤ 2
    have ha := prefixMinimum_le_chronologicalExcess h n hq i
    have hc := chronologicalExcess_pos h (n + 1) hq i
    have hqreal : (0 : ℝ) < n + 1 := by positivity
    have hmass : unresolvedMass h (n + 1) ≤
        (n + 1 : ℝ) * chronologicalExcess h (n + 1) hq i :=
      hdense.trans (mul_le_mul_of_nonneg_left ha hqreal.le)
    norm_num [Nat.cast_add, Nat.cast_one] at ⊢
    apply (div_le_iff₀ (mul_pos hqreal hc)).2
    nlinarith
  ·
    have hden : (((n + 1 : ℕ) : ℝ) - 1) = (n : ℝ) := by norm_num
    rw [hden]
    have hnreal : (0 : ℝ) < n := by exact_mod_cast hn
    have hnOne : (1 : ℝ) ≤ n := by exact_mod_cast hn
    apply (div_le_iff₀ hnreal).2
    nlinarith

/-- A dense prefix of length at least two has a good chronological top-chain value. -/
theorem densePrefix_topChain_value_of_two_le {T : ℕ} {h : StepSchedule T}
    (hh : IsNonnegativeSchedule h) {n : ℕ} (hn : 0 < n)
    (hq : n + 1 ≤ longCount h)
    (hdense : unresolvedMass h (n + 1) ≤
      (n + 1 : ℝ) * prefixMinimum h n hq) :
    (4 * unresolvedMass h (n + 1) * (n + 1 : ℝ) * 8 ^ n)⁻¹ ≤
      (topChain h (n + 1)).value := by
  let D : ℝ := unresolvedMass h (n + 1)
  let v : Fin (n + 2) → ℝ := topPathWeight h (n + 1) hq
  let M : ℝ := matchingEnvelope v
  have hq₂ : 2 ≤ n + 1 := by omega
  have hD : 0 < D := unresolvedMass_pos hh (n + 1)
  have hvpos (i : Fin (n + 2)) : 0 < v i :=
    topPathWeight_pos hh hq₂ hq i
  have hv₂ (i : Fin (n + 2)) : v i ≤ 2 :=
    topPathWeight_le_two_of_dense hn hq hdense i
  have hMle : M ≤ (4 : ℝ) ^ (n + 1) :=
    matchingEnvelope_le_four_pow (fun i ↦ (hvpos i).le) hv₂
  have hpathPos : 0 < parityPathProduct v := parityPathProduct_pos hvpos
  have hpathLe : parityPathProduct v ≤ M :=
    parityPathProduct_le_matchingEnvelope v (fun i ↦ (hvpos i).le)
  have hM : 0 < M := hpathPos.trans_le hpathLe
  have hfourEight : (4 : ℝ) ^ n ≤ 8 ^ n := by
    gcongr
    norm_num
  have hpow : (4 : ℝ) ^ (n + 1) ≤ 4 * 8 ^ n := by
    rw [pow_succ]
    nlinarith [mul_le_mul_of_nonneg_right hfourEight (by norm_num : (0 : ℝ) ≤ 4)]
  have hnquad : 2 * (n : ℝ) ≤ (n + 1 : ℝ) ^ 2 := by
    nlinarith [sq_nonneg (n : ℝ)]
  have hcross :
      2 * D * (n : ℝ) * M ≤
        (n + 1 : ℝ) * (4 * D * (n + 1 : ℝ) * 8 ^ n) := by
    calc
      2 * D * (n : ℝ) * M ≤
          2 * D * (n : ℝ) * (4 : ℝ) ^ (n + 1) := by gcongr
      _ ≤ 2 * D * (n : ℝ) * (4 * 8 ^ n) := by gcongr
      _ = (4 * D * 8 ^ n) * (2 * (n : ℝ)) := by ring
      _ ≤ (4 * D * 8 ^ n) * (n + 1 : ℝ) ^ 2 := by
        exact mul_le_mul_of_nonneg_left hnquad (by positivity)
      _ = (n + 1 : ℝ) * (4 * D * (n + 1 : ℝ) * 8 ^ n) := by ring
  have htargetDen : 0 < 4 * D * (n + 1 : ℝ) * 8 ^ n := by positivity
  have hendpointDen : 0 < 2 * D * (n : ℝ) * M := by
    have hnreal : (0 : ℝ) < n := by exact_mod_cast hn
    positivity
  have hscalar :
      1 / (4 * D * (n + 1 : ℝ) * 8 ^ n) ≤
        (n + 1 : ℝ) / (2 * D * (n : ℝ) * M) := by
    exact (div_le_div_iff₀ htargetDen hendpointDen).2 (by simpa using hcross)
  have hendpoint := topChain_value_ge_matchingEnvelope hh hq₂ hq
  change (4 * D * (n + 1 : ℝ) * 8 ^ n)⁻¹ ≤
    (topChain h (n + 1)).value
  calc
    (4 * D * (n + 1 : ℝ) * 8 ^ n)⁻¹ =
        1 / (4 * D * (n + 1 : ℝ) * 8 ^ n) := by rw [one_div]
    _ ≤ (n + 1 : ℝ) / (2 * D * (n : ℝ) * M) := hscalar
    _ ≤ (topChain h (n + 1)).value := by
      norm_num [Nat.cast_add, Nat.cast_one] at hendpoint
      exact hendpoint

/-- The one-element dense prefix, where the augmented matching construction is not needed. -/
theorem densePrefix_topChain_value_one {T : ℕ} {h : StepSchedule T}
    (hh : IsNonnegativeSchedule h) (hq : 1 ≤ longCount h)
    (hdense : unresolvedMass h 1 ≤ prefixMinimum h 0 hq) :
    (4 * unresolvedMass h 1)⁻¹ ≤ (topChain h 1).value := by
  let c : Chain h := topChain h 1
  let D : ℝ := unresolvedMass h 1
  let i₀ : Fin 1 := 0
  have hlen : c.length = 1 := topChain_length_of_le h hq
  let i : Fin c.length := Fin.cast hlen.symm (Fin.last 0)
  have hi : i = topChainIndex h 1 hq i₀ := by
    apply Fin.ext
    rfl
  have hmass := chronologicalLastMass_add_terminal_le hh 0 hq
  change c.precedingMass (topChainIndex h 1 hq i₀) + c.terminalScale ≤ 2 * D at hmass
  rw [← hi] at hmass
  have hterminal := terminal_localBound_inv_le c hh 0 hlen (D := D) hmass
  have hsum := chronologicalPrecedingMass_sum_le hh hq
  have hUle : c.precedingMass i ≤ D := by
    have hone : chronologicalPrecedingMass h 1 hq i₀ ≤ D := by
      simpa [Fin.sum_univ_succ] using hsum
    simpa only [chronologicalPrecedingMass, hi] using hone
  have hselected : D ≤ excess h (c.selected i) := by
    have hmin := prefixMinimum_le_chronologicalExcess h 0 hq i₀
    have := hdense.trans hmin
    simpa only [D, chronologicalExcess, hi] using this
  have hc : 0 < excess h (c.selected i) := c.selected_excess_pos i
  have hratio : D / excess h (c.selected i) ≤ 1 :=
    (div_le_one hc).2 hselected
  have hfactor :
      1 + 2 * D * (excess h (c.selected i))⁻¹ ≤ 3 := by
    calc
      1 + 2 * D * (excess h (c.selected i))⁻¹ =
          1 + 2 * (D / excess h (c.selected i)) := by
        rw [div_eq_mul_inv]
        ring
      _ ≤ 3 := by nlinarith
  have hfactor₀ : 0 ≤ 1 + 2 * D * (excess h (c.selected i))⁻¹ := by
    have hD := unresolvedMass_pos hh 1
    positivity
  have hterminal' : c.terminalScale * (c.localBound i)⁻¹ ≤ 3 * D := by
    have hmul := mul_le_mul hUle hfactor hfactor₀
      (unresolvedMass_pos hh 1).le
    have hlocal : c.terminalScale * (c.localBound i)⁻¹ ≤
        c.precedingMass i *
          (1 + 2 * D * (excess h (c.selected i))⁻¹) := by
      simpa only [i] using hterminal
    exact hlocal.trans (by nlinarith [hmul])
  have hRpos : 0 < c.terminalScale * (c.localBound i)⁻¹ := by
    exact mul_pos (c.terminalScale_pos hh) (inv_pos.mpr (c.localBound_pos hh i))
  have hD : 0 < D := unresolvedMass_pos hh 1
  have hinv : (4 * D)⁻¹ ≤ (c.terminalScale * (c.localBound i)⁻¹)⁻¹ := by
    apply (inv_le_inv₀ (by positivity) hRpos).2
    nlinarith
  rw [topChain_value_eq_inv_reciprocal h hq]
  have hprod :
      (∏ j : Fin 1, (chronologicalLocalBound h 1 hq j)⁻¹) =
        (c.localBound i)⁻¹ := by
    simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one]
    apply congrArg Inv.inv
    change c.localBound (topChainIndex h 1 hq i₀) = c.localBound i
    rw [hi]
  change (4 * D)⁻¹ ≤ (c.terminalScale * _)⁻¹
  rw [hprod]
  exact hinv

/-! ## Diffuse induction and the bounded-rank estimate -/

/-- At cutoff zero, the empty chain gives the appendix's `(2D₀)⁻¹` bound. -/
theorem boundedRankPrefix_zero {T : ℕ} {h : StepSchedule T}
    (hh : IsNonnegativeSchedule h) :
    (2 * unresolvedMass h 0)⁻¹ ≤ lowerBoundFunctional h := by
  let D : ℝ := unresolvedMass h 0
  have hD : 0 < D := unresolvedMass_pos hh 0
  have hsum : 0 ≤ ∑ t, h t := Finset.sum_nonneg fun t _ ↦ hh t
  have hemptyDen : 0 < 1 + 2 * ∑ t, h t := by linarith
  have heq : 1 + 2 * ∑ t, h t = 2 * D - 1 := by
    dsimp only [D]
    rw [unresolvedMass_zero_eq_total]
    ring
  have hden : 1 + 2 * ∑ t, h t ≤ 2 * D := by
    rw [heq]
    linarith
  have hinv : (2 * D)⁻¹ ≤ (1 + 2 * ∑ t, h t)⁻¹ :=
    (inv_le_inv₀ (by positivity) hemptyDen).2 hden
  exact hinv.trans (emptyValue_le_functional h)

/-- Positive-cutoff bounded-rank prefix estimate.  The induction step is the diffuse alternative;
the dense alternative is supplied by the corresponding chronological top chain. -/
theorem boundedRankPrefix_pos {T : ℕ} {h : StepSchedule T}
    (hh : IsNonnegativeSchedule h) (n : ℕ)
    (hq : n + 1 ≤ longCount h) :
    (4 * unresolvedMass h (n + 1) * (n + 1 : ℝ) * 8 ^ n)⁻¹ ≤
      lowerBoundFunctional h := by
  induction n with
  | zero =>
      let D : ℝ := unresolvedMass h 1
      let a : ℝ := prefixMinimum h 0 hq
      by_cases hdense : D ≤ a
      · have hchain := densePrefix_topChain_value_one hh hq hdense
        simp only [zero_add, Nat.cast_zero, pow_zero, mul_one] at ⊢
        change (4 * D)⁻¹ ≤ lowerBoundFunctional h
        exact hchain.trans (chainValue_le_functional h (topChain h 1))
      · have hdiff : a < D := lt_of_not_ge hdense
        have hrec := unresolvedMass_pred h 0 hq
        change unresolvedMass h 0 = a + D at hrec
        have hD : 0 < D := unresolvedMass_pos hh 1
        have hD₀ : 0 < unresolvedMass h 0 := unresolvedMass_pos hh 0
        have hden : 2 * unresolvedMass h 0 ≤ 4 * D := by
          rw [hrec]
          linarith
        have hinv : (4 * D)⁻¹ ≤ (2 * unresolvedMass h 0)⁻¹ :=
          (inv_le_inv₀ (by positivity) (by positivity)).2 hden
        simp only [zero_add, Nat.cast_zero, pow_zero, mul_one] at ⊢
        change (4 * D)⁻¹ ≤ lowerBoundFunctional h
        exact hinv.trans (boundedRankPrefix_zero hh)
  | succ n ih =>
      let D : ℝ := unresolvedMass h (n + 2)
      let Dprev : ℝ := unresolvedMass h (n + 1)
      let a : ℝ := prefixMinimum h (n + 1) hq
      by_cases hdense : D ≤ (n + 2 : ℝ) * a
      · have hdense' : unresolvedMass h ((n + 1) + 1) ≤
            ((n + 1 : ℕ) + 1 : ℝ) * prefixMinimum h (n + 1) hq := by
          have hnEq : (n + 1) + 1 = n + 2 := by omega
          have hcoef : ((n + 1 : ℕ) : ℝ) + 1 = (n + 2 : ℝ) := by
            push_cast
            ring
          rw [hnEq, hcoef]
          exact hdense
        have hchain := densePrefix_topChain_value_of_two_le hh (n := n + 1)
          (by omega) hq hdense'
        have hfinal := hchain.trans (chainValue_le_functional h (topChain h (n + 2)))
        norm_num [Nat.cast_add, Nat.cast_one, add_assoc] at hfinal ⊢
        exact hfinal
      · have hqprev : n + 1 ≤ longCount h := by omega
        have hIH := ih hqprev
        have hdiff : (n + 2 : ℝ) * a < D := lt_of_not_ge hdense
        have ha : 0 < a := prefixMinimum_pos h (n + 1) hq
        have hqa : a ≤ (n + 2 : ℝ) * a := by
          have hqreal : (1 : ℝ) ≤ n + 2 := by
            exact_mod_cast (by omega : 1 ≤ n + 2)
          nlinarith
        have haD : a ≤ D := hqa.trans hdiff.le
        have hrec := unresolvedMass_pred h (n + 1) hq
        change Dprev = a + D at hrec
        have hDprevLe : Dprev ≤ 2 * D := by
          rw [hrec]
          linarith
        have hD : 0 < D := unresolvedMass_pos hh (n + 2)
        have hDprev : 0 < Dprev := unresolvedMass_pos hh (n + 1)
        have hnat : 2 * (n + 1 : ℝ) ≤ 8 * (n + 2 : ℝ) := by
          exact_mod_cast (by omega : 2 * (n + 1) ≤ 8 * (n + 2))
        have hden :
            4 * Dprev * (n + 1 : ℝ) * 8 ^ n ≤
              4 * D * (n + 2 : ℝ) * 8 ^ (n + 1) := by
          calc
            4 * Dprev * (n + 1 : ℝ) * 8 ^ n ≤
                4 * (2 * D) * (n + 1 : ℝ) * 8 ^ n := by gcongr
            _ = (4 * D * 8 ^ n) * (2 * (n + 1 : ℝ)) := by ring
            _ ≤ (4 * D * 8 ^ n) * (8 * (n + 2 : ℝ)) := by
              exact mul_le_mul_of_nonneg_left hnat (by positivity)
            _ = 4 * D * (n + 2 : ℝ) * 8 ^ (n + 1) := by
              rw [pow_succ]
              ring
        have htargetDen : 0 < 4 * D * (n + 2 : ℝ) * 8 ^ (n + 1) := by
          positivity
        have hprevDen : 0 < 4 * Dprev * (n + 1 : ℝ) * 8 ^ n := by
          positivity
        have hinv :
            (4 * D * (n + 2 : ℝ) * 8 ^ (n + 1))⁻¹ ≤
              (4 * Dprev * (n + 1 : ℝ) * 8 ^ n)⁻¹ :=
          (inv_le_inv₀ htargetDen hprevDen).2 hden
        have hfinal := hinv.trans hIH
        norm_num [D, Dprev, Nat.cast_add, Nat.cast_one, add_assoc] at hfinal ⊢
        exact hfinal

/-- Bounded-rank prefix estimate, including the empty-prefix case. -/
theorem boundedRankPrefix {T : ℕ} {h : StepSchedule T}
    (hh : IsNonnegativeSchedule h) (q₀ : ℕ) (hq₀ : q₀ ≤ longCount h) :
    (if q₀ = 0 then
        (2 * unresolvedMass h 0)⁻¹
      else
        (4 * unresolvedMass h q₀ * (q₀ : ℝ) * 8 ^ (q₀ - 1))⁻¹) ≤
      lowerBoundFunctional h := by
  by_cases hzero : q₀ = 0
  · simpa [hzero] using boundedRankPrefix_zero hh
  · obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hzero
    rw [if_neg (Nat.succ_ne_zero n)]
    simpa only [Nat.succ_sub_one, Nat.cast_succ] using
      boundedRankPrefix_pos hh n hq₀

end

end GDLowerBound.RankAnalysis
