import GDLowerBound.FourBlock.PerfectMatchingInduction

/-! # Forcing the outer edge by one exact-kernel exchange -/

namespace GDLowerBound.FourBlock

open scoped BigOperators

noncomputable section

/-- Every perfect pairing can be modified, without decreasing its logarithmic
score, so that one row contains the least and greatest labels. -/
theorem exists_outerizedPairing {k : ℕ}
    (w : Fin (2 * (k + 1)) → ℝ) (hw : ∀ i, 0 < w i)
    (hmono : Monotone w)
    (e : (Fin (k + 1) × Bool) ≃ Fin (2 * (k + 1))) :
    ∃ (e' : (Fin (k + 1) × Bool) ≃ Fin (2 * (k + 1)))
      (row : Fin (k + 1)) (side : Bool),
      pairingLogScore w e ≤ pairingLogScore w e' ∧
        e' (row, side) = 0 ∧ e' (row, !side) = outerLast k := by
  let p0 : Fin (k + 1) × Bool := e.symm 0
  let other0 : Fin (k + 1) × Bool := (p0.1, !p0.2)
  let a : Fin (2 * (k + 1)) := e other0
  have hp0 : e p0 = 0 := e.apply_symm_apply 0
  have ha0 : a ≠ 0 := by
    intro ha
    have hpos : other0 = p0 := e.injective (ha.trans hp0.symm)
    have hside := congrArg Prod.snd hpos
    dsimp only [other0] at hside
    simp at hside
  by_cases halast : a = outerLast k
  · exact ⟨e, p0.1, p0.2, le_rfl, hp0, halast⟩
  · let plast : Fin (k + 1) × Bool := e.symm (outerLast k)
    let otherLast : Fin (k + 1) × Bool := (plast.1, !plast.2)
    let b : Fin (2 * (k + 1)) := e otherLast
    have hplast : e plast = outerLast k := e.apply_symm_apply _
    have hlast0 : outerLast k ≠ 0 := by
      apply Fin.ne_of_gt
      change 0 < 2 * (k + 1) - 1
      omega
    have hrow : p0.1 ≠ plast.1 := by
      intro hr
      have hpne : p0 ≠ plast := by
        intro hp
        have := hp0.symm.trans ((congrArg e hp).trans hplast)
        exact hlast0 this.symm
      have hsides : p0.2 ≠ plast.2 := by
        intro hs
        exact hpne (Prod.ext hr hs)
      have hother : other0 = plast := by
        apply Prod.ext
        · exact hr
        · dsimp only [other0]
          cases h0 : p0.2 <;> cases hl : plast.2 <;> simp_all
      apply halast
      exact (congrArg e hother).trans hplast
    let σ : Equiv.Perm (Fin (2 * (k + 1))) :=
      Equiv.swap a (outerLast k)
    let e' : (Fin (k + 1) × Bool) ≃ Fin (2 * (k + 1)) := e.trans σ
    have hezero : e' p0 = 0 := by
      change Equiv.swap a (outerLast k) (e p0) = 0
      rw [hp0]
      exact Equiv.swap_apply_of_ne_of_ne ha0.symm hlast0.symm
    have helast : e' other0 = outerLast k := by
      dsimp only [e', σ, a]
      exact Equiv.swap_apply_left _ _
    have hb0 : b ≠ 0 := by
      intro hb
      have hpos : otherLast = p0 := e.injective (hb.trans hp0.symm)
      exact hrow ((congrArg Prod.fst hpos).symm)
    have hbalast : b ≠ outerLast k := by
      intro hb
      have hpos : otherLast = plast := e.injective (hb.trans hplast.symm)
      have hside := congrArg Prod.snd hpos
      dsimp only [otherLast] at hside
      simp at hside
    have hba : b ≠ a := by
      intro hb
      have hpos : otherLast = other0 := by
        apply e.injective
        exact hb
      exact hrow ((congrArg Prod.fst hpos).symm)
    let f : Fin (k + 1) → ℝ := fun i ↦
      logKernel (w (e (i, false))) (w (e (i, true)))
    let g : Fin (k + 1) → ℝ := fun i ↦
      logKernel (w (e' (i, false))) (w (e' (i, true)))
    have hp0side : e (p0.1, p0.2) = 0 := by
      simpa only [Prod.eta] using hp0
    have haSide : e (p0.1, !p0.2) = a := by
      rfl
    have hplastSide : e (plast.1, plast.2) = outerLast k := by
      simpa only [Prod.eta] using hplast
    have hbSide : e (plast.1, !plast.2) = b := by
      rfl
    have hf0 : f p0.1 = logKernel (w 0) (w a) := by
      dsimp only [f]
      cases hs : p0.2
      · simp only [hs, Bool.not_false] at hp0side haSide
        rw [hp0side, haSide]
      · simp only [hs, Bool.not_true] at hp0side haSide
        rw [haSide, hp0side, logKernel_comm]
    have hflast : f plast.1 = logKernel (w b) (w (outerLast k)) := by
      dsimp only [f]
      cases hs : plast.2
      · simp only [hs, Bool.not_false] at hplastSide hbSide
        rw [hplastSide, hbSide, logKernel_comm]
      · simp only [hs, Bool.not_true] at hplastSide hbSide
        rw [hbSide, hplastSide]
    have hfixOtherLast : e' otherLast = b := by
      change Equiv.swap a (outerLast k) (e otherLast) = b
      change Equiv.swap a (outerLast k) b = b
      exact Equiv.swap_apply_of_ne_of_ne hba hbalast
    have hezeroSide : e' (p0.1, p0.2) = 0 := by
      simpa only [Prod.eta] using hezero
    have helastSide : e' (p0.1, !p0.2) = outerLast k := by
      exact helast
    have hfixLastSide : e' (plast.1, !plast.2) = b := by
      exact hfixOtherLast
    have heplastSide : e' (plast.1, plast.2) = a := by
      change Equiv.swap a (outerLast k) (e (plast.1, plast.2)) = a
      rw [hplastSide]
      exact Equiv.swap_apply_right _ _
    have hg0 : g p0.1 = logKernel (w 0) (w (outerLast k)) := by
      dsimp only [g]
      cases hs : p0.2
      · simp only [hs, Bool.not_false] at hezeroSide helastSide
        rw [hezeroSide, helastSide]
      · simp only [hs, Bool.not_true] at hezeroSide helastSide
        rw [helastSide, hezeroSide, logKernel_comm]
    have hglast : g plast.1 = logKernel (w b) (w a) := by
      dsimp only [g]
      cases hs : plast.2
      · simp only [hs, Bool.not_false] at heplastSide hfixLastSide
        rw [heplastSide, hfixLastSide, logKernel_comm]
      · simp only [hs, Bool.not_true] at heplastSide hfixLastSide
        rw [hfixLastSide, heplastSide]
    have hpair : f p0.1 + f plast.1 ≤ g p0.1 + g plast.1 := by
      rw [hf0, hflast, hg0, hglast]
      have hex := logKernel_exchange_parallel_le
        (a := w 0) (b := w a) (c := w b) (d := w (outerLast k))
        (hw 0) (hmono (Fin.zero_le b)) (hw a) (hmono (by
          change a.val ≤ 2 * (k + 1) - 1
          omega))
      rw [logKernel_comm (w a) (w b)] at hex
      exact hex
    have hoff : ∀ i, i ≠ p0.1 → i ≠ plast.1 → f i = g i := by
      intro i hi0 hilast
      have hfix (side : Bool) : e' (i, side) = e (i, side) := by
        have hnea : e (i, side) ≠ a := by
          intro h
          have hpos : (i, side) = other0 := by
            apply e.injective
            exact h
          exact hi0 (congrArg Prod.fst hpos)
        have hnelast : e (i, side) ≠ outerLast k := by
          intro h
          have hpos : (i, side) = plast :=
            e.injective (h.trans hplast.symm)
          exact hilast (congrArg Prod.fst hpos)
        dsimp only [e', σ]
        exact Equiv.swap_apply_of_ne_of_ne hnea hnelast
      dsimp only [f, g]
      rw [hfix false, hfix true]
    have hscore : pairingLogScore w e ≤ pairingLogScore w e' := by
      unfold pairingLogScore
      exact sum_le_sum_of_eq_off_two f g hrow hpair hoff
    exact ⟨e', p0.1, p0.2, hscore, hezero, helast⟩

end

end GDLowerBound.FourBlock
