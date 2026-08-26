import GDLowerBound.FourBlock.CompressedMatchingCertificate
import GDLowerBound.FourBlock.ScheduleFourBlock
import GDLowerBound.FourBlock.CriticalLyapunov

/-!
# A scalar cutoff for the exact outside-in score

This module supplies the missing large-matching bridge.  Concavity and
symmetry reduce every outside-in score to the balanced scalar kernel.  A
small rational certificate then shows that, beyond rank `8000`, a state at
or below the critical Lyapunov threshold has normalized score less than
`10^-7`.
-/

namespace GDLowerBound.FourBlock

open GDLowerBound.Schedule GDLowerBound.RankAnalysis

noncomputable section

/-- Concavity of the logarithmic kernel for two equally weighted pairs. -/
theorem average_logKernel_le_logKernel_midpoint
    {u₁ v₁ u₂ v₂ : ℝ}
    (hu₁ : 0 < u₁) (hv₁ : 0 < v₁)
    (hu₂ : 0 < u₂) (hv₂ : 0 < v₂) :
    (logKernel u₁ v₁ + logKernel u₂ v₂) / 2 ≤
      logKernel ((u₁ + u₂) / 2) ((v₁ + v₂) / 2) := by
  have hconc := pairLogKernelClosed_concave.2
    (show (u₁, v₁) ∈ positiveQuadrant from ⟨hu₁, hv₁⟩)
    (show (u₂, v₂) ∈ positiveQuadrant from ⟨hu₂, hv₂⟩)
    (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (1 / 2 : ℝ) + 1 / 2 = 1)
  rw [pairLogKernelClosed_eq ⟨hu₁, hv₁⟩,
    pairLogKernelClosed_eq ⟨hu₂, hv₂⟩] at hconc
  have hmidU : 0 < (u₁ + u₂) / 2 := by positivity
  have hmidV : 0 < (v₁ + v₂) / 2 := by positivity
  rw [show (1 / 2 : ℝ) • (u₁, v₁) + (1 / 2 : ℝ) • (u₂, v₂) =
      ((u₁ + u₂) / 2, (v₁ + v₂) / 2) by
        ext <;> simp [smul_eq_mul] <;> ring,
    pairLogKernelClosed_eq ⟨hmidU, hmidV⟩] at hconc
  calc
    (logKernel u₁ v₁ + logKernel u₂ v₂) / 2 =
        (1 / 2 : ℝ) * logKernel u₁ v₁ +
          (1 / 2 : ℝ) * logKernel u₂ v₂ := by ring
    _ ≤ logKernel ((u₁ + u₂) / 2) ((v₁ + v₂) / 2) := by
      simpa only [smul_eq_mul, div_eq_mul_inv] using hconc

/-- At fixed total endpoint mass, the balanced pair maximizes the exact
logarithmic kernel. -/
theorem logKernel_le_balanced {u v : ℝ} (hu : 0 < u) (hv : 0 < v) :
    logKernel u v ≤ logKernel ((u + v) / 2) ((u + v) / 2) := by
  have h := average_logKernel_le_logKernel_midpoint hu hv hv hu
  rw [logKernel_comm v u] at h
  simpa only [add_self_div_two, add_comm u v] using h

/-- The full outside-in score is at most the balanced kernel evaluated at
the mean of all `2k` endpoint weights. -/
theorem outsideInLogScore_average_le_balanced {k : ℕ} (hk : 0 < k)
    (w : Fin (2 * k) → ℝ) (hw : ∀ i, 0 < w i) :
    outsideInLogScore k w / k ≤
      logKernel ((∑ i, w i) / (2 * k)) ((∑ i, w i) / (2 * k)) := by
  let u : Fin k → ℝ := fun i ↦ w (outsideInLeft k i)
  let v : Fin k → ℝ := fun i ↦ w (outsideInRight k i)
  have hmean := mean_logKernel_le_logKernel_means hk u v
    (fun i ↦ hw _) (fun i ↦ hw _)
  have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hbalance := logKernel_le_balanced
    (div_pos (quarterSum_pos hk u (fun i ↦ hw _)) hkR)
    (div_pos (quarterSum_pos hk v (fun i ↦ hw _)) hkR)
  have hsum : (∑ i, u i) + ∑ i, v i = ∑ i, w i := by
    let e : Fin (k + k) ≃ Fin (2 * k) :=
      (Fin.castOrderIso (by omega : k + k = 2 * k)).toEquiv
    have he := e.sum_comp w
    rw [← he, Fin.sum_univ_add]
    apply congrArg₂ (fun x y : ℝ ↦ x + y)
    · apply Finset.sum_congr rfl
      intro i hi
      apply congrArg w
      apply Fin.ext
      simp [u, e, outsideInLeft]
    · calc
        (∑ i, v i) =
            ∑ i : Fin k, (w ∘ e) (Fin.natAdd k (Fin.revPerm i)) := by
          apply Finset.sum_congr rfl
          intro i hi
          apply congrArg w
          apply Fin.ext
          simp [v, e, outsideInRight, Fin.revPerm_apply, Fin.rev]
          omega
        _ = ∑ i : Fin k, (w ∘ e) (Fin.natAdd k i) :=
          Equiv.sum_comp Fin.revPerm
            (fun i : Fin k ↦ (w ∘ e) (Fin.natAdd k i))
  have hmid : (finMean u + finMean v) / 2 = (∑ i, w i) / (2 * k) := by
    unfold finMean
    rw [← hsum]
    field_simp [hkR.ne']
  unfold outsideInLogScore
  change (∑ i, logKernel (u i) (v i)) / k ≤ _
  simpa only [u, v] using hmean.trans (hmid ▸ hbalance)

/-- Rational scale used by the finite scalar cutoff. -/
def exactScoreZCapQ : ℚ :=
  4086960373221890 / 10000000000000000 + 1 / 100000000

def exactScoreUCapQ : ℚ := 2 * exactScoreZCapQ

/-- Compact outward-rounded witness for the balanced kernel at
`2 * exactScoreZCapQ`.  The generator is untrusted; validity is recomputed
below by `native_decide`. -/
def exactScoreKernelWitness : KernelWitness where
  sqrtLower := 67518297841 / 62500000000
  sqrtUpper := 1080292765457 / 1000000000000
  deltaLower := 803539168087 / 1000000000000
  deltaUpper := 100442396011 / 125000000000
  logTotalUpper := -201636379241 / 1000000000000
  logFactorUpper := 398097240433 / 1000000000000

def exactScoreKernelCert : KernelJetCert :=
  exactScoreKernelWitness.toJet exactScoreUCapQ exactScoreUCapQ

theorem exactScoreKernelCert_valid : exactScoreKernelCert.valid = true := by
  native_decide

theorem balancedKernel_at_exactScoreCap_lt :
    logKernel (exactScoreUCapQ : ℝ) (exactScoreUCapQ : ℝ) <
      (1 / 10000000 : ℝ) := by
  have h := (KernelJetCert.sound exactScoreKernelCert_valid).1
  have hrat : exactScoreKernelCert.value.upper < (1 / 10000000 : ℚ) := by
    native_decide
  have hratR : (exactScoreKernelCert.value.upper : ℝ) <
      (1 / 10000000 : ℝ) := by
    norm_num [exactScoreKernelCert, exactScoreKernelWitness,
      KernelWitness.toJet] at hrat ⊢
  exact h.trans_lt hratR

theorem scheduleFourBlock_aux_le_score_cap {m : ℕ} (hm : 2000 ≤ m) :
    1 / ((8 * (m : ℝ)) * ((2 * (m + m) : ℝ) - 1)) ≤
      (1 / 100000000 : ℝ) := by
  have hmR : (2000 : ℝ) ≤ m := by exact_mod_cast hm
  have hm0 : (0 : ℝ) < m := by positivity
  have hfour : 0 < 4 * (m : ℝ) - 1 := by nlinarith
  have hden : 0 < 8 * (m : ℝ) * (4 * (m : ℝ) - 1) := by positivity
  calc
    1 / ((8 * (m : ℝ)) * ((2 * (m + m) : ℝ) - 1)) =
        1 / (8 * (m : ℝ) * (4 * (m : ℝ) - 1)) := by
      congr 2
      norm_num [Nat.cast_add]
      ring
    _ ≤ (1 / 100000000 : ℝ) := by
      apply (div_le_iff₀ hden).2
      nlinarith [sq_nonneg ((m : ℝ) - 2000)]

/-- Scalar cutoff at rank `4m`: below the critical state, the normalized
exact outside-in score is strictly less than `10^-7`. -/
theorem scheduleOutsideInLogScore_average_lt_cutoff_of_zeta_le
    {T m : ℕ} {h : StepSchedule T} (hh : IsNonnegativeSchedule h)
    (hm : 2000 ≤ m) (hq : 2 * (m + m) ≤ longCount h)
    (hzeta : zetaState h (2 * (m + m)) ≤ criticalTheta) :
    outsideInLogScore (m + m) (scheduleFourBlockWeights h hq) /
        (2 * m) < (1 / 10000000 : ℝ) := by
  have hm0 : 0 < m := by omega
  let w := scheduleFourBlockWeights h hq
  have hw : ∀ i, 0 < w i := scheduleFourBlockWeights_pos hh hm0 hq
  have hscore := outsideInLogScore_average_le_balanced (by omega : 0 < m + m) w hw
  have htotal : (∑ i, w i) = fourBlockTotal w :=
    (fourBlockTotal_eq_sum w).symm
  have hmean : (∑ i, w i) / (2 * ((m + m : ℕ) : ℝ)) =
      2 * fourBlockZ w := by
    rw [htotal]
    unfold fourBlockZ
    have hmR : (0 : ℝ) < m := by exact_mod_cast hm0
    norm_num [Nat.cast_mul, Nat.cast_add]
    field_simp [hmR.ne']
    ring
  rw [hmean] at hscore
  have hz := scheduleFourBlockZ_le_zeta_add_aux hh hm0 hq
  have haux := scheduleFourBlock_aux_le_score_cap hm
  have hzcap : fourBlockZ w ≤ (exactScoreZCapQ : ℝ) := by
    dsimp only [w] at hz ⊢
    unfold exactScoreZCapQ
    push_cast
    have htheta : criticalTheta ≤ thetaUpper :=
      criticalTheta_lt_thetaUpper.le
    norm_num [thetaUpper] at htheta
    linarith
  have hzpos : 0 < fourBlockZ w := by
    unfold fourBlockZ
    exact div_pos (fourBlockTotal_pos hm0 hw) (by positivity)
  have hu : 2 * fourBlockZ w ≤ (exactScoreUCapQ : ℝ) := by
    unfold exactScoreUCapQ
    push_cast
    linarith
  have hkernel := logKernel_mono
    (by positivity : 0 ≤ 2 * fourBlockZ w)
    (by positivity : 0 ≤ 2 * fourBlockZ w) hu hu
    (by positivity : 0 < 2 * fourBlockZ w + 2 * fourBlockZ w)
  calc
    outsideInLogScore (m + m) (scheduleFourBlockWeights h hq) / (2 * m) ≤
        logKernel (2 * fourBlockZ w) (2 * fourBlockZ w) := by
      simpa only  [w, Nat.cast_add, Nat.cast_ofNat, Nat.cast_mul, two_mul] using hscore
    _ ≤ logKernel (exactScoreUCapQ : ℝ) (exactScoreUCapQ : ℝ) := hkernel
    _ < (1 / 10000000 : ℝ) := balancedKernel_at_exactScoreCap_lt

end

end GDLowerBound.FourBlock
