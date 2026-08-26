import GDLowerBound.FourBlock.SharpScheduleDrift

/-!
# Finite joint moment/defect rigidity

The endpoint-defect recursion retains the quadratic source exactly.  After
telescoping it yields the finite counterpart of
`U + E / criticalTheta ≤ 2 (betaLower + 1) d`.
-/

namespace GDLowerBound.FourBlock

open scoped BigOperators
open GDLowerBound.Schedule GDLowerBound.RankAnalysis

noncomputable section

def momentDriftConstant : ℝ := 48

private theorem omega_v_le
    {N u v : ℝ} (hN : 1 < N) (hu0 : 0 < u) (hv0 : 0 < v)
    (hsmall : u < N - 1)
    (hmass : v ≤ N * u / (N - 1 - u)) :
    lyapunovOmega N v * v ≤ (N - 1) / N * u := by
  have hden : 0 < N - 1 - u := by linarith
  have hNv : 0 < N + v := by linarith
  have hN0 : 0 < N := by linarith
  have hcross : v * (N - 1 - u) ≤ N * u :=
    (le_div_iff₀ hden).mp hmass
  have hreset : (N - 1) * v / (N + v) ≤ u := by
    apply (div_le_iff₀ hNv).2
    nlinarith
  unfold lyapunovOmega
  have hfactor : 0 ≤ (N - 1) / N := by positivity
  have hs := mul_le_mul_of_nonneg_left hreset hfactor
  calc
    (N - 1) ^ 2 / (N * (N + v)) * v =
        (N - 1) / N * ((N - 1) * v / (N + v)) := by
      field_simp [hN0.ne', hNv.ne']
    _ ≤ (N - 1) / N * u := hs

private theorem endpoint_source_identity
    {N v : ℝ} (hN : 0 < N) (hv : 0 < v) :
    v * lyapunovDrift criticalP N v =
      criticalTheta *
          (2 * (betaLower + 1) * (betaLower - v) -
            (v - betaLower) ^ 2) / N +
        criticalTheta * v * (v + 1) ^ 2 / (N * (N + v)) := by
  have hNv : 0 < N + v := by positivity
  have hb2 : 0 < betaLower + 2 := by linarith [betaLower_pos]
  unfold lyapunovDrift
  rw [show lyapunovTheta criticalP = criticalTheta from rfl,
    criticalTheta_eq]
  field_simp [hN.ne', hv.ne', hNv.ne', betaLower_pos.ne', hb2.ne']
  ring

private theorem moment_error_le
    {N v : ℝ} (hN : 2 ≤ N) (hv0 : 0 < v)
    (hvB : v ≤ criticalP ^ 2 - 1) :
    v * (v + 1) ^ 2 / (N * (N + v)) ≤
      momentDriftConstant / N ^ 2 := by
  have hN0 : 0 < N := by linarith
  have hv3 : v ≤ 3 := by
    unfold criticalP at hvB
    have hb : betaLower * (betaLower + 2) < 3 := by
      norm_num [betaLower]
    nlinarith
  have hv1 : v + 1 ≤ 4 := by linarith
  have hsquare : (v + 1) ^ 2 ≤ 16 := by
    nlinarith [sq_nonneg (v + 1), sq_nonneg (4 - (v + 1))]
  have hnum : v * (v + 1) ^ 2 ≤ 48 := by
    have ht := mul_le_mul hv3 hsquare (sq_nonneg (v + 1))
      (by norm_num : (0 : ℝ) ≤ 3)
    norm_num at ht ⊢
    exact ht
  have hden : N ^ 2 ≤ N * (N + v) := by
    nlinarith
  have hden0 : 0 < N * (N + v) := by positivity
  unfold momentDriftConstant
  calc
    v * (v + 1) ^ 2 / (N * (N + v)) ≤
        48 / (N * (N + v)) :=
      div_le_div_of_nonneg_right hnum hden0.le
    _ ≤ 48 / N ^ 2 :=
      div_le_div_of_nonneg_left (by norm_num) (sq_pos_of_pos hN0) hden

/-- Exact adjacent-rank joint rigidity inequality. -/
theorem scheduleMomentOneStep
    {T Q : ℕ} (hQ : criticalTheta⁻¹ < (Q : ℝ))
    {h : StepSchedule T} (hh : IsNonnegativeSchedule h)
    {ell n : ℕ} (hQell : Q ≤ ell)
    (hcut : CutoffConditions criticalP h ell (longCount h))
    (hn : n ∈ Finset.Ico (ell + 1) (longCount h + 1)) :
    ((relativeMassIncrement h n - betaLower) ^ 2 +
        endpointDefect h (n - 1) / criticalTheta) / (n : ℝ) ≤
      2 * (betaLower + 1) *
          (betaLower - relativeMassIncrement h n) / (n : ℝ) -
        (endpointDefect h n - endpointDefect h (n - 1)) /
          criticalTheta +
        momentDriftConstant / (n : ℝ) ^ 2 := by
  have hnIco := Finset.mem_Ico.mp hn
  have hn_le : n ≤ longCount h := by omega
  have hQpos : 1 ≤ Q := by
    have hQreal : 0 < (Q : ℝ) := (inv_pos.mpr criticalTheta_pos).trans hQ
    exact_mod_cast hQreal
  have hnprev0 : 1 ≤ n - 1 := by omega
  have hnprev_lt : n - 1 < longCount h := by omega
  have hnprev_mem : n - 1 ∈ Finset.Icc ell (longCount h) :=
    Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  have hn_mem : n ∈ Finset.Icc ell (longCount h) :=
    Finset.mem_Icc.mpr ⟨by omega, hn_le⟩
  obtain ⟨hzPrev, hu0, huB, _⟩ := hcut (n - 1) hnprev_mem
  obtain ⟨_, hv0, hvB, _⟩ := hcut n hn_mem
  have hnR : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ n)]
    norm_num
  have hsmall : relativeMassIncrement h (n - 1) < ((n - 1 : ℕ) : ℝ) := by
    have hQcast : (Q : ℝ) ≤ (n - 1 : ℕ) := by
      exact_mod_cast (by omega : Q ≤ n - 1)
    exact huB.trans (hQ.trans_le hQcast)
  have hmass := massIncrementBound hh hnprev0 hnprev_lt hsmall
  have hzrec := zetaRecursion hh hnprev0 hnprev_lt
  have hnSucc : n - 1 + 1 = n := Nat.sub_add_cancel (by omega : 1 ≤ n)
  rw [hnSucc] at hmass hzrec
  let N : ℝ := n
  let u := relativeMassIncrement h (n - 1)
  let v := relativeMassIncrement h n
  let X := zetaState h (n - 1) - criticalTheta
  have hNR : 2 ≤ N := by
    dsimp only [N]
    exact_mod_cast (show 2 ≤ n by omega)
  have hN0 : 0 < N := by linarith
  have hsmallR : u < N - 1 := by
    dsimp only [u, N]
    simpa only [hnR] using hsmall
  have hmassR : v ≤ N * u / (N - 1 - u) := by
    dsimp only [u, v, N]
    rw [hnR] at hmass
    norm_num at hmass
    simpa using hmass
  have homega := omega_v_le (N := N) (u := u) (v := v)
    (by linarith) hu0 hv0 hsmallR hmassR
  have hX : 0 ≤ X := by
    dsimp only [X]
    exact sub_nonneg.mpr hzPrev.le
  have hcontract := mul_le_mul_of_nonneg_right homega hX
  have hsource := endpoint_source_identity hN0 hv0
  have herror := moment_error_le hNR hv0
    (by
      have ht : v < criticalTheta⁻¹ := hvB
      rw [show criticalTheta⁻¹ = criticalP ^ 2 - 1 by
        unfold criticalTheta; exact lyapunovTheta_inv criticalP] at ht
      exact ht.le)
  have hzNext : zetaState h n =
      lyapunovOmega N v * zetaState h (n - 1) + 1 / (N * v) := by
    dsimp only [N, v]
    simpa [lyapunovOmega, hnR, div_eq_mul_inv, mul_assoc, mul_left_comm,
      mul_comm] using hzrec
  have hshift : zetaState h n - criticalTheta =
      lyapunovOmega N v * X + lyapunovDrift criticalP N v := by
    dsimp only [X]
    rw [hzNext]
    unfold lyapunovOmega lyapunovDrift
    rw [show lyapunovTheta criticalP = criticalTheta from rfl]
    have hNv : 0 < N + v := by positivity
    field_simp [hN0.ne', hv0.ne', hNv.ne']
    ring
  have herec : endpointDefect h n ≤
      (N - 1) / N * endpointDefect h (n - 1) +
        v * lyapunovDrift criticalP N v := by
    unfold endpointDefect
    dsimp only [u, v, X] at hcontract ⊢
    rw [hshift]
    nlinarith
  dsimp only [N, u, v] at hsource herror herec ⊢
  have htheta0 := criticalTheta_pos
  have hscaled := div_le_div_of_nonneg_right herec htheta0.le
  rw [hsource] at hscaled
  ring_nf at hscaled herror ⊢
  have hthetaInv : criticalTheta * criticalTheta⁻¹ = 1 :=
    mul_inv_cancel₀ criticalTheta_pos.ne'
  rw [hthetaInv] at hscaled
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  have hcollapse :
      criticalTheta⁻¹ * (n : ℝ) * (n : ℝ)⁻¹ * endpointDefect h (n - 1) =
        criticalTheta⁻¹ * endpointDefect h (n - 1) := by
    field_simp [hn0]
  rw [hcollapse] at hscaled
  norm_num at hscaled
  nlinarith

private theorem sum_endpoint_sub (e : ℕ → ℝ)
    {lo hi : ℕ} (hlohi : lo ≤ hi) :
    ∑ n ∈ Finset.Ico (lo + 1) (hi + 1),
        (e n - e (n - 1)) = e hi - e lo := by
  induction hi, hlohi using Nat.le_induction with
  | base => simp
  | succ hi hlohi ih =>
      rw [Finset.sum_Ico_succ_top (by omega), ih]
      simp only [Nat.add_sub_cancel]
      ring

/-- Telescoped finite joint moment/defect budget. -/
theorem scheduleMomentRigidityBudget
    {T Q : ℕ} (hQ : criticalTheta⁻¹ < (Q : ℝ))
    {h : StepSchedule T} (hh : IsNonnegativeSchedule h)
    {lo hi : ℕ} (hQlo : Q ≤ lo) (hlohi : lo ≤ hi)
    (hhir : hi ≤ longCount h)
    (hcut : CutoffConditions criticalP h lo (longCount h)) :
    ∑ n ∈ Finset.Ico (lo + 1) (hi + 1),
        ((relativeMassIncrement h n - betaLower) ^ 2 +
          endpointDefect h (n - 1) / criticalTheta) / (n : ℝ) ≤
      2 * (betaLower + 1) *
          ∑ n ∈ Finset.Ico (lo + 1) (hi + 1),
            (betaLower - relativeMassIncrement h n) / (n : ℝ) +
        (endpointDefect h lo - endpointDefect h hi) / criticalTheta +
        momentDriftConstant *
          ∑ n ∈ Finset.Ico (lo + 1) (hi + 1),
            1 / (n : ℝ) ^ 2 := by
  have hterm : ∀ n ∈ Finset.Ico (lo + 1) (hi + 1),
      ((relativeMassIncrement h n - betaLower) ^ 2 +
          endpointDefect h (n - 1) / criticalTheta) / (n : ℝ) ≤
        2 * (betaLower + 1) *
            ((betaLower - relativeMassIncrement h n) / (n : ℝ)) -
          (endpointDefect h n - endpointDefect h (n - 1)) /
            criticalTheta +
          momentDriftConstant * (1 / (n : ℝ) ^ 2) := by
    intro n hn
    have hs := scheduleMomentOneStep hQ hh hQlo hcut
      (Finset.mem_Ico.mpr ⟨(Finset.mem_Ico.mp hn).1, by
        have := (Finset.mem_Ico.mp hn).2
        omega⟩)
    ring_nf at hs ⊢
    exact hs
  calc
    ∑ n ∈ Finset.Ico (lo + 1) (hi + 1),
          ((relativeMassIncrement h n - betaLower) ^ 2 +
            endpointDefect h (n - 1) / criticalTheta) / (n : ℝ) ≤
        ∑ n ∈ Finset.Ico (lo + 1) (hi + 1),
          (2 * (betaLower + 1) *
              ((betaLower - relativeMassIncrement h n) / (n : ℝ)) -
            (endpointDefect h n - endpointDefect h (n - 1)) /
              criticalTheta +
            momentDriftConstant * (1 / (n : ℝ) ^ 2)) :=
      Finset.sum_le_sum hterm
    _ = _ := by
      rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
      rw [← Finset.mul_sum]
      rw [← Finset.sum_div,
        sum_endpoint_sub (endpointDefect h) hlohi]
      rw [← Finset.mul_sum]
      ring

end

end GDLowerBound.FourBlock
