import GDLowerBound.FourBlock.PerfectMatchingOrder

/-! # Removing a forced outer edge in the outside-in induction -/

namespace GDLowerBound.FourBlock

open scoped BigOperators

noncomputable section

/-- Delete the two outer labels from an interior label. -/
def innerLabel {k : ℕ} (x : Fin (2 * (k + 1)))
    (hx0 : x ≠ 0) (hxlast : x ≠ outerLast k) : Fin (2 * k) :=
  ⟨x.val - 1, by
    have hpos : 0 < x.val := by
      exact Nat.pos_of_ne_zero fun h ↦ hx0 (Fin.ext h)
    have hlt := x.isLt
    have hneLast : x.val ≠ 2 * (k + 1) - 1 := by
      intro h
      apply hxlast
      apply Fin.ext
      simpa [outerLast] using h
    omega⟩

@[simp]
theorem innerLabel_val {k : ℕ} (x : Fin (2 * (k + 1)))
    (hx0 : x ≠ 0) (hxlast : x ≠ outerLast k) :
    (innerLabel x hx0 hxlast).val = x.val - 1 := rfl

/-- Remove a row already known to contain the two outer labels. -/
noncomputable def removeOuterPair {k : ℕ}
    (e : (Fin (k + 1) × Bool) ≃ Fin (2 * (k + 1)))
    (row : Fin (k + 1)) (side : Bool)
    (hzero : e (row, side) = 0)
    (hlast : e (row, !side) = outerLast k) :
    (Fin k × Bool) ≃ Fin (2 * k) := by
  let pos : Fin k × Bool → Fin (k + 1) × Bool :=
    fun p ↦ (row.succAbove p.1, p.2)
  have hnotZero (p : Fin k × Bool) : e (pos p) ≠ 0 := by
    intro hp
    have hsame : pos p = (row, side) := e.injective (hp.trans hzero.symm)
    have hrow := congrArg Prod.fst hsame
    exact Fin.succAbove_ne row p.1 hrow
  have hnotLast (p : Fin k × Bool) : e (pos p) ≠ outerLast k := by
    intro hp
    have hsame : pos p = (row, !side) := e.injective (hp.trans hlast.symm)
    have hrow := congrArg Prod.fst hsame
    exact Fin.succAbove_ne row p.1 hrow
  let f : Fin k × Bool → Fin (2 * k) := fun p ↦
    innerLabel (e (pos p)) (hnotZero p) (hnotLast p)
  apply Equiv.ofBijective f
  rw [Fintype.bijective_iff_injective_and_card]
  constructor
  · intro p q hpq
    have hpval : (e (pos p)).val = (e (pos q)).val := by
      have hval := congrArg Fin.val hpq
      simp only [f, innerLabel_val] at hval
      have hp0 : 0 < (e (pos p)).val := by
        exact Nat.pos_of_ne_zero fun h ↦ hnotZero p (Fin.ext h)
      have hq0 : 0 < (e (pos q)).val := by
        exact Nat.pos_of_ne_zero fun h ↦ hnotZero q (Fin.ext h)
      omega
    have hpos : pos p = pos q := e.injective (Fin.ext hpval)
    have hfst : p.1 = q.1 :=
      Fin.succAbove_right_injective (congrArg Prod.fst hpos)
    have hsnd : p.2 = q.2 := congrArg (fun x : Fin (k + 1) × Bool ↦ x.2) hpos
    exact Prod.ext hfst hsnd
  · simp [Fintype.card_prod, Nat.mul_comm]

theorem removeOuterPair_weight {k : ℕ}
    (w : Fin (2 * (k + 1)) → ℝ)
    (e : (Fin (k + 1) × Bool) ≃ Fin (2 * (k + 1)))
    (row : Fin (k + 1)) (side : Bool)
    (hzero : e (row, side) = 0)
    (hlast : e (row, !side) = outerLast k)
    (p : Fin k × Bool) :
    innerWeight w (removeOuterPair e row side hzero hlast p) =
      w (e (row.succAbove p.1, p.2)) := by
  unfold innerWeight removeOuterPair
  apply congrArg w
  apply Fin.ext
  simp only [Equiv.ofBijective_apply, innerLabel_val]
  have hne : e (row.succAbove p.1, p.2) ≠ 0 := by
    intro hp
    have hsame := e.injective (hp.trans hzero.symm)
    have hrow := congrArg Prod.fst hsame
    exact Fin.succAbove_ne row p.1 hrow
  have hpos : 0 < (e (row.succAbove p.1, p.2)).val := by
    exact Nat.pos_of_ne_zero fun h ↦ hne (Fin.ext h)
  omega

theorem pairingLogScore_removeOuter {k : ℕ}
    (w : Fin (2 * (k + 1)) → ℝ)
    (e : (Fin (k + 1) × Bool) ≃ Fin (2 * (k + 1)))
    (row : Fin (k + 1)) (side : Bool)
    (hzero : e (row, side) = 0)
    (hlast : e (row, !side) = outerLast k) :
    pairingLogScore w e =
      logKernel (w 0) (w (outerLast k)) +
        pairingLogScore (innerWeight w)
          (removeOuterPair e row side hzero hlast) := by
  unfold pairingLogScore
  rw [Fin.sum_univ_succAbove _ row]
  apply congrArg₂ (fun x y : ℝ ↦ x + y)
  · cases side <;>
      simp only [Bool.not_false, Bool.not_true] at hlast ⊢ <;>
      rw [hzero, hlast]
    exact logKernel_comm _ _
  · apply Finset.sum_congr rfl
    intro i _
    rw [removeOuterPair_weight, removeOuterPair_weight]

end

end GDLowerBound.FourBlock
