import GDLowerBound.FourBlock.CriticalLyapunov
import GDLowerBound.FourBlock.ScaledLog

/-! # Exact-rational checker for the constrained third-endpoint bound -/

namespace GDLowerBound.FourBlock

noncomputable section

def sideBetaLowerQ : ℚ := 8565576222695287 / 10000000000000000
def sideBetaUpperQ : ℚ := 8565576222695288 / 10000000000000000
def sideThetaLowerQ : ℚ := 4086960373221888 / 10000000000000000
def sideThetaUpperQ : ℚ := 40869603732218882 / 100000000000000000
def sideC3Q : ℚ := 4 / 100
def sideD3Q : ℚ := 583 / 10000
def sideLambda3Q : ℚ := 468 / 10000
def sideAlphaQ : ℚ := 358 / 10000
def sideK3LowerQ : ℚ := sideD3Q + sideBetaLowerQ * sideLambda3Q

def qSideSquareDistance (vlo vhi : ℚ) : ℚ :=
  if vhi < sideBetaLowerQ then (sideBetaLowerQ - vhi) ^ 2
  else if sideBetaUpperQ < vlo then (vlo - sideBetaUpperQ) ^ 2
  else 0

def sideG (z v : ℝ) : ℝ :=
  (sideC3Q : ℝ) * (v - betaLower) ^ 2 +
    ((sideD3Q : ℝ) + betaLower * (sideLambda3Q : ℝ)) * v * (z - criticalTheta) -
    (sideAlphaQ : ℝ) * Real.log z

def qSideGBoxLower (zlo zhi vlo vhi : ℚ) : ℚ :=
  sideC3Q * qSideSquareDistance vlo vhi +
    sideK3LowerQ * vlo * max 0 (zlo - sideThetaUpperQ) -
    sideAlphaQ * qScaledLogUpper zhi

def qSideLogConstraintLower (zlo zhi vhi : ℚ) : ℚ :=
  qScaledLogLower zlo -
    sideBetaUpperQ * vhi * max 0 (zhi - sideThetaLowerQ)

theorem qSideSquareDistance_sound {vlo vhi : ℚ} {v : ℝ}
    (hvl : (vlo : ℝ) ≤ v) (hvh : v ≤ (vhi : ℝ)) :
    (qSideSquareDistance vlo vhi : ℝ) ≤ (v - betaLower) ^ 2 := by
  have hbLoEq : (sideBetaLowerQ : ℝ) = betaLower := by
    norm_num [sideBetaLowerQ, betaLower]
  have hbHiEq : (sideBetaUpperQ : ℝ) = betaUpper := by
    norm_num [sideBetaUpperQ, betaUpper]
  unfold qSideSquareDistance
  split_ifs with hlow hhigh
  · have hlowR : (vhi : ℝ) < betaLower := by
      have : (vhi : ℝ) < (sideBetaLowerQ : ℝ) := by exact_mod_cast hlow
      simpa only [hbLoEq] using this
    have hdiff : 0 ≤ betaLower - (vhi : ℝ) := by linarith
    have horder : betaLower - (vhi : ℝ) ≤ betaLower - v := by linarith
    push_cast
    rw [hbLoEq]
    nlinarith [mul_self_le_mul_self hdiff horder]
  · have hhighR : betaUpper < (vlo : ℝ) := by
      have : (sideBetaUpperQ : ℝ) < (vlo : ℝ) := by exact_mod_cast hhigh
      simpa only [hbHiEq] using this
    have hb : betaLower ≤ betaUpper := betaLower_le_betaUpper
    have hdiff : 0 ≤ (vlo : ℝ) - betaUpper := by linarith
    have horder : (vlo : ℝ) - betaUpper ≤ v - betaLower := by linarith
    push_cast
    rw [hbHiEq]
    nlinarith [mul_self_le_mul_self hdiff horder]
  · push_cast
    exact sq_nonneg _

theorem sideDz_lower {zlo : ℚ} {z : ℝ}
    (hzlo : (zlo : ℝ) ≤ z) (hz : criticalTheta ≤ z) :
    (max 0 (zlo - sideThetaUpperQ) : ℚ) ≤ z - criticalTheta := by
  have heq : (sideThetaUpperQ : ℝ) = thetaUpper := by
    norm_num [sideThetaUpperQ, thetaUpper]
  have htheta : criticalTheta ≤ (sideThetaUpperQ : ℝ) := by
    rw [heq]
    exact criticalTheta_lt_thetaUpper.le
  push_cast
  apply max_le
  · linarith
  · linarith

theorem sideDz_upper {zhi : ℚ} {z : ℝ}
    (hzhi : z ≤ (zhi : ℝ)) (hz : criticalTheta ≤ z) :
    z - criticalTheta ≤ (max 0 (zhi - sideThetaLowerQ) : ℚ) := by
  have heq : (sideThetaLowerQ : ℝ) = thetaLower := by
    norm_num [sideThetaLowerQ, thetaLower]
  have htheta : (sideThetaLowerQ : ℝ) ≤ criticalTheta := by
    rw [heq]
    exact thetaLower_lt_criticalTheta.le
  push_cast
  apply le_max_of_le_right
  linarith

theorem qSideGBoxLower_sound {zlo zhi vlo vhi : ℚ} {z v : ℝ}
    (hzlo0 : 0 < zlo) (hzlo : (zlo : ℝ) ≤ z) (hzhi : z ≤ (zhi : ℝ))
    (hz : criticalTheta ≤ z) (hvl0 : 0 ≤ vlo)
    (hvl : (vlo : ℝ) ≤ v) (hvh : v ≤ (vhi : ℝ)) :
    (qSideGBoxLower zlo zhi vlo vhi : ℝ) ≤ sideG z v := by
  have hsquare := qSideSquareDistance_sound hvl hvh
  have hdz := sideDz_lower hzlo hz
  have hvl0R : (0 : ℝ) ≤ vlo := by exact_mod_cast hvl0
  have hv0 : (0 : ℝ) ≤ v := hvl0R.trans hvl
  have hdz0 : (0 : ℝ) ≤ z - criticalTheta := sub_nonneg.mpr hz
  have hdlo0 : (0 : ℝ) ≤ (max 0 (zlo - sideThetaUpperQ) : ℚ) := by positivity
  have hvprod : (vlo : ℝ) * (max 0 (zlo - sideThetaUpperQ) : ℚ) ≤
      v * (z - criticalTheta) :=
    mul_le_mul hvl hdz (by exact_mod_cast hdlo0) hv0
  have hkpos : (0 : ℝ) ≤ sideK3LowerQ := by norm_num [sideK3LowerQ,
    sideD3Q, sideBetaLowerQ, sideLambda3Q]
  have hkprod := mul_le_mul_of_nonneg_left hvprod hkpos
  have hzlo0R : (0 : ℝ) < zlo := by exact_mod_cast hzlo0
  have hzhi0R : (0 : ℝ) < zhi := hzlo0R.trans_le (hzlo.trans hzhi)
  have hzhi0 : (0 : ℚ) < zhi := by exact_mod_cast hzhi0R
  have hlogUpper := qScaledLogUpper_sound hzhi0
  have hlogMono := Real.log_le_log (hzlo0R.trans_le hzlo) hzhi
  have hlog : Real.log z ≤ (qScaledLogUpper zhi : ℝ) := hlogMono.trans hlogUpper
  have hc : (0 : ℝ) ≤ sideC3Q := by norm_num [sideC3Q]
  have ha : (0 : ℝ) ≤ sideAlphaQ := by norm_num [sideAlphaQ]
  have hsqterm := mul_le_mul_of_nonneg_left hsquare hc
  have hlogterm := mul_le_mul_of_nonneg_left hlog ha
  have hkEq : (sideK3LowerQ : ℝ) =
      (sideD3Q : ℝ) + betaLower * (sideLambda3Q : ℝ) := by
    norm_num [sideK3LowerQ, sideD3Q, sideBetaLowerQ,
      sideLambda3Q, betaLower]
  unfold qSideGBoxLower sideG
  push_cast at hkprod hsqterm hlogterm ⊢
  rw [hkEq] at hkprod ⊢
  ring_nf at hkprod hsqterm hlogterm ⊢
  linarith

theorem qSideLogConstraintLower_sound {zlo zhi vhi : ℚ} {z v : ℝ}
    (hzlo0 : 0 < zlo) (hzlo : (zlo : ℝ) ≤ z) (hzhi : z ≤ (zhi : ℝ))
    (hz : criticalTheta ≤ z) (hv0 : 0 ≤ v) (hvh : v ≤ (vhi : ℝ)) :
    (qSideLogConstraintLower zlo zhi vhi : ℝ) ≤
      Real.log z - betaLower * v * (z - criticalTheta) := by
  have hlogLo := qScaledLogLower_sound hzlo0
  have hlogMono := Real.log_le_log (by exact_mod_cast hzlo0) hzlo
  have hlog : (qScaledLogLower zlo : ℝ) ≤ Real.log z := hlogLo.trans hlogMono
  have hdz := sideDz_upper hzhi hz
  have hvhi0 : (0 : ℝ) ≤ vhi := hv0.trans hvh
  have hdz0 : 0 ≤ z - criticalTheta := sub_nonneg.mpr hz
  have hdup0 : (0 : ℝ) ≤ (max 0 (zhi - sideThetaLowerQ) : ℚ) := by positivity
  have hvprod : v * (z - criticalTheta) ≤
      (vhi : ℝ) * (max 0 (zhi - sideThetaLowerQ) : ℚ) :=
    mul_le_mul hvh hdz hdz0 hvhi0
  have hb : betaLower ≤ (sideBetaUpperQ : ℝ) := by
    norm_num [betaLower, sideBetaUpperQ, betaUpper]
  have hright0 : 0 ≤ (vhi : ℝ) * (max 0 (zhi - sideThetaLowerQ) : ℚ) := by
    positivity
  have hleft0 : 0 ≤ v * (z - criticalTheta) := mul_nonneg hv0 hdz0
  have hprod : betaLower * (v * (z - criticalTheta)) ≤
      (sideBetaUpperQ : ℝ) *
        ((vhi : ℝ) * (max 0 (zhi - sideThetaLowerQ) : ℚ)) :=
    (mul_le_mul_of_nonneg_left hvprod betaLower_pos.le).trans
      (mul_le_mul_of_nonneg_right hb hright0)
  unfold qSideLogConstraintLower
  push_cast at hprod ⊢
  ring_nf at hprod ⊢
  linarith

structure SideGBox where
  zlo : ℚ
  zhi : ℚ
  vlo : ℚ
  vhi : ℚ
deriving Repr, DecidableEq

def SideGBox.Mem (b : SideGBox) (z v : ℝ) : Prop :=
  (b.zlo : ℝ) ≤ z ∧ z ≤ (b.zhi : ℝ) ∧ (b.vlo : ℝ) ≤ v ∧ v ≤ (b.vhi : ℝ)

inductive SideGLeaf where
  | infeasible
  | constraint
  | energy
deriving Repr, DecidableEq

def SideGLeaf.valid (qmax target : ℚ) (leaf : SideGLeaf) (b : SideGBox) : Bool :=
  match leaf with
  | .infeasible => decide (0 < b.zlo ∧ 0 ≤ b.vlo ∧ 1 / b.zlo < b.vlo)
  | .constraint => decide (0 < b.zlo ∧ 0 ≤ b.vlo ∧ qScaledLogUpper qmax <
      qSideLogConstraintLower b.zlo b.zhi b.vhi)
  | .energy => decide (0 < b.zlo ∧ 0 ≤ b.vlo ∧ target < qSideGBoxLower b.zlo b.zhi b.vlo b.vhi)

inductive SideGTree where
  | leaf (proof : SideGLeaf)
  | splitZ (mid : ℚ) (left right : SideGTree)
  | splitV (mid : ℚ) (left right : SideGTree)
deriving Repr, DecidableEq

def SideGTree.valid (qmax target : ℚ) : SideGTree → SideGBox → Bool
  | .leaf proof, b => proof.valid qmax target b
  | .splitZ mid left right, b =>
      decide (b.zlo < mid ∧ mid < b.zhi) &&
        left.valid qmax target { b with zhi := mid } &&
        right.valid qmax target { b with zlo := mid }
  | .splitV mid left right, b =>
      decide (b.vlo < mid ∧ mid < b.vhi) &&
        left.valid qmax target { b with vhi := mid } &&
        right.valid qmax target { b with vlo := mid }

theorem SideGLeaf.sound {qmax target : ℚ} {leaf : SideGLeaf} {b : SideGBox}
    (hv : leaf.valid qmax target b = true) {z v : ℝ}
    (hqmax : 0 < qmax) (hz0 : 0 < z) (hz : criticalTheta ≤ z)
    (hv0 : 0 ≤ v) (hvz : v ≤ 1 / z)
    (hconstraint : Real.log z - betaLower * v * (z - criticalTheta) ≤
      Real.log (qmax : ℝ)) (hmem : b.Mem z v) :
    (target : ℝ) < sideG z v := by
  cases leaf with
  | infeasible =>
      have hvp : 0 < b.zlo ∧ 0 ≤ b.vlo ∧ 1 / b.zlo < b.vlo := of_decide_eq_true hv
      rcases hvp with ⟨hbzlo0, hbvlo0, hp⟩
      have hpR : 1 / (b.zlo : ℝ) < (b.vlo : ℝ) := by exact_mod_cast hp
      have hzlo0 : (0 : ℝ) < b.zlo := by exact_mod_cast hbzlo0
      have hinv : 1 / z ≤ 1 / (b.zlo : ℝ) := by
        exact one_div_le_one_div_of_le hzlo0 hmem.1
      exfalso
      linarith [hmem.2.2.1]
  | constraint =>
      have hvp : 0 < b.zlo ∧ 0 ≤ b.vlo ∧ qScaledLogUpper qmax <
          qSideLogConstraintLower b.zlo b.zhi b.vhi := of_decide_eq_true hv
      rcases hvp with ⟨hbzlo0, hbvlo0, hp⟩
      have hlower := qSideLogConstraintLower_sound hbzlo0 hmem.1 hmem.2.1 hz hv0 hmem.2.2.2
      have hqlog := qScaledLogUpper_sound hqmax
      have hpR : (qScaledLogUpper qmax : ℝ) <
          (qSideLogConstraintLower b.zlo b.zhi b.vhi : ℝ) := by exact_mod_cast hp
      exfalso
      linarith
  | energy =>
      have hvp : 0 < b.zlo ∧ 0 ≤ b.vlo ∧
          target < qSideGBoxLower b.zlo b.zhi b.vlo b.vhi := of_decide_eq_true hv
      rcases hvp with ⟨hbzlo0, hbvlo0, hp⟩
      have hlower := qSideGBoxLower_sound hbzlo0 hmem.1 hmem.2.1 hz
        hbvlo0
        hmem.2.2.1 hmem.2.2.2
      have hpR : (target : ℝ) <
          (qSideGBoxLower b.zlo b.zhi b.vlo b.vhi : ℝ) := by exact_mod_cast hp
      linarith

theorem SideGTree.sound {qmax target : ℚ} {tree : SideGTree} {b : SideGBox}
    (ht : tree.valid qmax target b = true) {z v : ℝ}
    (hqmax : 0 < qmax) (hz0 : 0 < z) (hz : criticalTheta ≤ z)
    (hv0 : 0 ≤ v) (hvz : v ≤ 1 / z)
    (hconstraint : Real.log z - betaLower * v * (z - criticalTheta) ≤
      Real.log (qmax : ℝ)) (hmem : b.Mem z v) :
    (target : ℝ) < sideG z v := by
  induction tree generalizing b with
  | leaf proof => exact SideGLeaf.sound ht hqmax hz0 hz hv0 hvz hconstraint hmem
  | splitZ mid left right ihl ihr =>
      change (decide (b.zlo < mid ∧ mid < b.zhi) &&
        left.valid qmax target { b with zhi := mid } &&
        right.valid qmax target { b with zlo := mid }) = true at ht
      have ho := Bool.and_eq_true_iff.mp ht
      have hi := Bool.and_eq_true_iff.mp ho.1
      by_cases hm : z ≤ (mid : ℝ)
      · exact ihl hi.2 ⟨hmem.1, hm, hmem.2.2.1, hmem.2.2.2⟩
      · exact ihr ho.2 ⟨le_of_not_ge hm, hmem.2.1, hmem.2.2.1, hmem.2.2.2⟩
  | splitV mid left right ihl ihr =>
      change (decide (b.vlo < mid ∧ mid < b.vhi) &&
        left.valid qmax target { b with vhi := mid } &&
        right.valid qmax target { b with vlo := mid }) = true at ht
      have ho := Bool.and_eq_true_iff.mp ht
      have hi := Bool.and_eq_true_iff.mp ho.1
      by_cases hm : v ≤ (mid : ℝ)
      · exact ihl hi.2 ⟨hmem.1, hmem.2.1, hmem.2.2.1, hm⟩
      · exact ihr ho.2 ⟨hmem.1, hmem.2.1, le_of_not_ge hm, hmem.2.2.2⟩

end

end GDLowerBound.FourBlock
