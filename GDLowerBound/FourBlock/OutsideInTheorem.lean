import GDLowerBound.FourBlock.PerfectMatchingExchange

/-! # The finite outside-in theorem for the exact envelope kernel -/

namespace GDLowerBound.FourBlock

open scoped BigOperators
open GDLowerBound.Matching

noncomputable section

theorem pairingLogScore_le_outsideIn :
    ∀ (k : ℕ) (w : Fin (2 * k) → ℝ),
      (∀ i, 0 < w i) → Monotone w →
      ∀ e : (Fin k × Bool) ≃ Fin (2 * k),
        pairingLogScore w e ≤ outsideInLogScore k w := by
  intro k
  induction k with
  | zero =>
      intro w hw hmono e
      simp [pairingLogScore, outsideInLogScore]
  | succ k ih =>
      intro w hw hmono e
      obtain ⟨e', row, side, hscore, hzero, hlast⟩ :=
        exists_outerizedPairing w hw hmono e
      let ein : (Fin k × Bool) ≃ Fin (2 * k) :=
        removeOuterPair e' row side hzero hlast
      have hinnerPos : ∀ i, 0 < innerWeight w i := innerWeight_pos hw
      have hinnerMono : Monotone (innerWeight w) := innerWeight_monotone hmono
      have hih := ih (innerWeight w) hinnerPos hinnerMono ein
      calc
        pairingLogScore w e ≤ pairingLogScore w e' := hscore
        _ = logKernel (w 0) (w (outerLast k)) +
            pairingLogScore (innerWeight w) ein := by
          simpa only [ein] using
            pairingLogScore_removeOuter w e' row side hzero hlast
        _ ≤ logKernel (w 0) (w (outerLast k)) +
            outsideInLogScore k (innerWeight w) := add_le_add le_rfl hih
        _ = outsideInLogScore (k + 1) w :=
          (outsideInLogScore_succ w).symm

theorem pairingProduct_le_outsideIn {k : ℕ}
    (w : Fin (2 * k) → ℝ) (hw : ∀ i, 0 < w i)
    (hmono : Monotone w) (e : (Fin k × Bool) ≃ Fin (2 * k)) :
    pairingProduct w e ≤ outsideInProduct k w := by
  rw [pairingProduct_eq_exp_logScore hw,
    outsideInProduct_eq_exp_logScore hw]
  exact Real.exp_le_exp.mpr (pairingLogScore_le_outsideIn k w hw hmono e)

/-- A full labelled matching supplies a permutation of all endpoint labels. -/
noncomputable def matchingEndpointEquiv {k : ℕ}
    (M : LabeledMatching (Fin (2 * k)) k) :
    (Fin k × Bool) ≃ Fin (2 * k) := by
  apply Equiv.ofBijective M.endpoints
  rw [Fintype.bijective_iff_injective_and_card]
  exact ⟨M.endpoints.injective, by simp [Fintype.card_prod, Nat.mul_comm]⟩

theorem edgeMatchingProduct_eq_pairingProduct {k : ℕ}
    (w : Fin (2 * k) → ℝ) (M : LabeledMatching (Fin (2 * k)) k) :
    edgeMatchingProduct w M = pairingProduct w (matchingEndpointEquiv M) := by
  unfold edgeMatchingProduct pairingProduct matchingEndpointEquiv
  rfl

/-- Exact outside-in domination for every perfect labelled matching. -/
theorem edgeMatchingProduct_le_outsideIn {k : ℕ}
    (w : Fin (2 * k) → ℝ) (hw : ∀ i, 0 < w i)
    (hmono : Monotone w) (M : LabeledMatching (Fin (2 * k)) k) :
    edgeMatchingProduct w M ≤ outsideInProduct k w := by
  rw [edgeMatchingProduct_eq_pairingProduct]
  exact pairingProduct_le_outsideIn w hw hmono (matchingEndpointEquiv M)

end

end GDLowerBound.FourBlock
