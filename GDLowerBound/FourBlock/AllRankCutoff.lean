import GDLowerBound.FourBlock.AllRankKernelCertificate
import GDLowerBound.FourBlock.ExactAugmentedRank
import GDLowerBound.FourBlock.OutsideInFourBlock
import GDLowerBound.RankAnalysis.Boundary
import GDLowerBound.RankAnalysis.BoundedRank
import GDLowerBound.RankAnalysis.Density
import GDLowerBound.Matching.ScalarBound

/-!
# Exact-envelope cutoff at every sufficiently large rank

This replaces the quadratic matching relaxation in the original rank scan.
Jensen is applied directly to the chronological exact-envelope edges.  The
negative scalar certificate then makes the entire edge product smaller than
one whenever the reciprocal-mass state is at or below `criticalTheta`.
-/

namespace GDLowerBound.FourBlock

open scoped BigOperators
open GDLowerBound.Schedule GDLowerBound.RankAnalysis GDLowerBound.Matching

noncomputable section

theorem chronologicalEdgeLog_average_le_balancedTotal
    {q : ℕ} (hq : 0 < q) (v : Fin (q + 1) → ℝ)
    (hv : ∀ i, 0 < v i) :
    (∑ i : Fin q, logKernel (v i.castSucc) (v i.succ)) / q ≤
      logKernel ((∑ i, v i) / q) ((∑ i, v i) / q) := by
  let u : Fin q → ℝ := fun i ↦ v i.castSucc
  let w : Fin q → ℝ := fun i ↦ v i.succ
  have hj := mean_logKernel_le_logKernel_means hq u w
    (fun i ↦ hv _) (fun i ↦ hv _)
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hsumU : ∑ i, u i ≤ ∑ i, v i := by
    have hs := Fin.sum_univ_castSucc v
    dsimp only [u]
    linarith [hv (Fin.last q)]
  have hsumW : ∑ i, w i ≤ ∑ i, v i := by
    have hs := Fin.sum_univ_succ v
    dsimp only [w]
    linarith [hv 0]
  have hmeanU : finMean u ≤ (∑ i, v i) / q := by
    unfold finMean
    exact (div_le_div_iff_of_pos_right hqR).2 hsumU
  have hmeanW : finMean w ≤ (∑ i, v i) / q := by
    unfold finMean
    exact (div_le_div_iff_of_pos_right hqR).2 hsumW
  have hmeanU0 : 0 < finMean u := by
    unfold finMean
    apply div_pos _ hqR
    exact Finset.sum_pos (fun i _ ↦ hv _) ⟨⟨0, hq⟩, Finset.mem_univ _⟩
  have hmeanW0 : 0 < finMean w := by
    unfold finMean
    apply div_pos _ hqR
    exact Finset.sum_pos (fun i _ ↦ hv _) ⟨⟨0, hq⟩, Finset.mem_univ _⟩
  have hmono := logKernel_mono hmeanU0.le hmeanW0.le
    hmeanU hmeanW (add_pos hmeanU0 hmeanW0)
  exact hj.trans hmono

theorem topPathWeight_mean_le_allRankUCap
    {T q : ℕ} {h : StepSchedule T} (hqCut : allRankCutoff ≤ q)
    (hqRank : q ≤ longCount h)
    (hzeta : zetaState h q ≤ criticalTheta) :
    (∑ i, topPathWeight h q hqRank i) / q ≤ (allRankUCapQ : ℝ) := by
  have hqTwo : 2 ≤ q := by
    have : 2 ≤ allRankCutoff := by norm_num [allRankCutoff]
    omega
  have hqR : (0 : ℝ) < q := by positivity
  have hqm1R : (0 : ℝ) < (q : ℝ) - 1 := by
    have hqRone : (1 : ℝ) < q := by exact_mod_cast (show 1 < q by omega)
    linarith
  have hQqR : (allRankCutoff : ℝ) ≤ q := by exact_mod_cast hqCut
  have hQ0 : (0 : ℝ) < allRankCutoff := by norm_num [allRankCutoff]
  have hQm1 : (0 : ℝ) < (allRankCutoff : ℝ) - 1 := by
    norm_num [allRankCutoff]
  have hden : (allRankCutoff : ℝ) * ((allRankCutoff : ℝ) - 1) ≤
      (q : ℝ) * ((q : ℝ) - 1) := by
    nlinarith
  have haux :
      1 / ((q : ℝ) * ((q : ℝ) - 1)) ≤
        1 / ((allRankCutoff : ℝ) * ((allRankCutoff : ℝ) - 1)) := by
    exact one_div_le_one_div_of_le (mul_pos hQ0 hQm1) hden
  rw [topPathWeight_sum hqTwo hqRank]
  calc
    (2 * (q : ℝ) * zetaState h q + 1 / ((q : ℝ) - 1)) / q =
        2 * zetaState h q +
          1 / ((q : ℝ) * ((q : ℝ) - 1)) := by
      field_simp [hqR.ne', hqm1R.ne']
    _ ≤ 2 * criticalTheta +
          1 / ((allRankCutoff : ℝ) * ((allRankCutoff : ℝ) - 1)) := by
      linarith
    _ ≤ 2 * (allRankThetaUpperQ : ℝ) +
          1 / ((allRankCutoff : ℝ) * ((allRankCutoff : ℝ) - 1)) := by
      linarith [criticalTheta_le_allRankThetaUpper]
    _ = (allRankUCapQ : ℝ) := by
      norm_num [allRankUCapQ, allRankThetaUpperQ, allRankCutoff]

theorem chronologicalEdgeKernelProduct_lt_one_of_zeta_le
    {T q : ℕ} {h : StepSchedule T} (hh : IsNonnegativeSchedule h)
    (hqCut : allRankCutoff ≤ q) (hqRank : q ≤ longCount h)
    (hzeta : zetaState h q ≤ criticalTheta) :
    chronologicalEdgeKernelProduct (topPathWeight h q hqRank) < 1 := by
  have hqTwo : 2 ≤ q := by
    have : 2 ≤ allRankCutoff := by norm_num [allRankCutoff]
    omega
  have hq0 : 0 < q := by omega
  let v := topPathWeight h q hqRank
  have hv : ∀ i, 0 < v i := topPathWeight_pos hh hqTwo hqRank
  have hj := chronologicalEdgeLog_average_le_balancedTotal hq0 v hv
  have hmean := topPathWeight_mean_le_allRankUCap hqCut hqRank hzeta
  have hsum0 : 0 < (∑ i, v i) / q := by
    apply div_pos
    · exact Finset.sum_pos (fun i _ ↦ hv i) ⟨⟨0, Nat.succ_pos q⟩, Finset.mem_univ _⟩
    · positivity
  have hmono := logKernel_mono hsum0.le hsum0.le hmean hmean
    (add_pos hsum0 hsum0)
  have havgNeg :
      (∑ i : Fin q, logKernel (v i.castSucc) (v i.succ)) / q < 0 :=
    (hj.trans hmono).trans_lt logKernel_allRankUCap_neg
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq0
  have hsumNeg :
      (∑ i : Fin q, logKernel (v i.castSucc) (v i.succ)) < 0 := by
    have := (div_lt_iff₀ hqR).mp havgNeg
    simpa using this
  have hproduct : chronologicalEdgeKernelProduct v =
      Real.exp (∑ i : Fin q, logKernel (v i.castSucc) (v i.succ)) := by
    unfold chronologicalEdgeKernelProduct
    rw [Real.exp_sum]
    apply Finset.prod_congr rfl
    intro i hi
    have hk := edgeKernel_pos (hv i.castSucc) (hv i.succ)
    rw [logKernel_eq_log_edgeKernel (hv i.castSucc).le (hv i.succ).le
      (add_pos (hv i.castSucc) (hv i.succ)), Real.exp_log hk]
  rw [hproduct]
  exact Real.exp_lt_one_iff.mpr hsumNeg

/-- If the critical state fails at any sufficiently large rank, the exact
augmented endpoint path gives a uniform functional contribution. -/
theorem quarter_div_unresolvedMass_lt_functional_of_zeta_le
    {T q : ℕ} {h : StepSchedule T} (hh : IsNonnegativeSchedule h)
    (hqCut : allRankCutoff ≤ q) (hqRank : q ≤ longCount h)
    (hzeta : zetaState h q ≤ criticalTheta) :
    (4 : ℝ)⁻¹ / unresolvedMass h q < lowerBoundFunctional h := by
  have hqTwo : 2 ≤ q := by
    have : 2 ≤ allRankCutoff := by norm_num [allRankCutoff]
    omega
  let D := unresolvedMass h q
  let E := chronologicalEdgeKernelProduct (topPathWeight h q hqRank)
  let R := (topChain h q).terminalScale *
    ∏ i : Fin q, (chronologicalLocalBound h q hqRank i)⁻¹
  have hD : 0 < D := unresolvedMass_pos hh q
  have hE : 0 < E := by
    dsimp only [E, chronologicalEdgeKernelProduct]
    exact Finset.prod_pos (fun i _ ↦
      edgeKernel_pos (topPathWeight_pos hh hqTwo hqRank _)
        (topPathWeight_pos hh hqTwo hqRank _))
  have hElt : E < 1 :=
    chronologicalEdgeKernelProduct_lt_one_of_zeta_le hh hqCut hqRank hzeta
  have hR : 0 < R := by
    dsimp only [R]
    apply mul_pos ((topChain h q).terminalScale_pos hh)
    exact Finset.prod_pos (fun i _ ↦
      inv_pos.mpr (chronologicalLocalBound_pos hh q hqRank i))
  have hend := topChain_reciprocalProduct_le_exactAugmentedPath_rank
    hh hqTwo hqRank
  have hqR : (0 : ℝ) < q := by positivity
  have hqOneR : (1 : ℝ) ≤ q := by exact_mod_cast (show 1 ≤ q by omega)
  have hratio : (0 : ℝ) ≤ ((q : ℝ) - 1) / q := by
    exact div_nonneg (sub_nonneg.mpr hqOneR) hqR.le
  have hratioLt : ((q : ℝ) - 1) / q < 1 := by
    exact (div_lt_one hqR).2 (by linarith)
  have hbound : R < 4 * D := by
    calc
      R ≤ (4 * D * ((q : ℝ) - 1) / q) * E := by
        simpa only [D, E, R] using hend
      _ = (4 * D) * (((q : ℝ) - 1) / q * E) := by ring
      _ < (4 * D) * 1 := by
        have hcoeff : 0 < 4 * D := by positivity
        have hprod : ((q : ℝ) - 1) / q * E < 1 := by
          have hEle : E ≤ 1 := hElt.le
          nlinarith [mul_lt_mul_of_pos_left hratioLt hE]
        exact mul_lt_mul_of_pos_left hprod hcoeff
      _ = 4 * D := by ring
  have hinv : (4 * D)⁻¹ < R⁻¹ :=
    (inv_lt_inv₀ (by positivity) hR).2 hbound
  have hquarter : (4 : ℝ)⁻¹ / D = (4 * D)⁻¹ := by
    field_simp [hD.ne']
  rw [hquarter]
  have hvalue : R⁻¹ = (topChain h q).value := by
    dsimp only [R]
    exact (topChain_value_eq_inv_reciprocal h hqRank).symm
  rw [hvalue] at hinv
  exact hinv.trans_le (chainValue_le_functional h (topChain h q))

/-- Absence of the exact-envelope small branch supplies all scalar cutoff
conditions needed by the adjacent-rank Lyapunov argument. -/
theorem criticalCutoffConditions_of_no_small_state
    {T lo : ℕ} {h : StepSchedule T} (hh : IsNonnegativeSchedule h)
    (hlo : allRankCutoff ≤ lo)
    (hlarge : ∀ q ∈ Finset.Icc lo (longCount h),
      criticalTheta < zetaState h q) :
    CutoffConditions criticalP h lo (longCount h) := by
  intro q hqmem
  have hqIcc := Finset.mem_Icc.mp hqmem
  have hqOne : 1 ≤ q := by
    have : 1 ≤ allRankCutoff := by norm_num [allRankCutoff]
    omega
  have hnu := relativeMassIncrement_pos hh hqOne hqIcc.2
  have hdensity := zeta_mul_relativeMassIncrement_le_one hh hqOne hqIcc.2
  have hz := hlarge q hqmem
  have hnuUpper : relativeMassIncrement h q < criticalTheta⁻¹ := by
    rw [inv_eq_one_div]
    apply (lt_div_iff₀ criticalTheta_pos).2
    calc
      relativeMassIncrement h q * criticalTheta =
          criticalTheta * relativeMassIncrement h q := mul_comm _ _
      _ < zetaState h q * relativeMassIncrement h q :=
        mul_lt_mul_of_pos_right hz hnu
      _ ≤ 1 := hdensity
  exact ⟨hz, hnu, hnuUpper, hdensity⟩

end

end GDLowerBound.FourBlock
