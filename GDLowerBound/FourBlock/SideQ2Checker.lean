import GDLowerBound.FourBlock.SideGChecker

/-! # Exact-rational checker for the second-endpoint side bound -/

namespace GDLowerBound.FourBlock

noncomputable section

def sideC2Q : ℚ := 4 / 100
def sideD2Q : ℚ := 188 / 10000
def sideLambda2Q : ℚ := 11 / 1000
def sideK2LowerQ : ℚ := sideD2Q + sideBetaLowerQ * sideLambda2Q
def sideK2UpperQ : ℚ := sideD2Q + sideBetaUpperQ * sideLambda2Q

def sideQ2 (z v : ℝ) : ℝ :=
  (sideC2Q : ℝ) * (v - betaLower) ^ 2 +
    ((sideD2Q : ℝ) + betaLower * (sideLambda2Q : ℝ)) *
      v * (z - criticalTheta) -
    (sideLambda2Q : ℝ) * Real.log z

def qSideQ2BoxLower (zlo zhi : ℚ) : ℚ :=
  sideK2LowerQ * sideBetaLowerQ * max 0 (zlo - sideThetaUpperQ) -
    sideK2UpperQ ^ 2 * max 0 (zhi - sideThetaLowerQ) ^ 2 /
      (4 * sideC2Q) -
    sideLambda2Q * qScaledLogUpper zhi

theorem qSideQ2BoxLower_sound {zlo zhi : ℚ} {z v : ℝ}
    (hzlo0 : 0 < zlo) (hzlo : (zlo : ℝ) ≤ z) (hzhi : z ≤ (zhi : ℝ))
    (hz : criticalTheta ≤ z) :
    (qSideQ2BoxLower zlo zhi : ℝ) ≤ sideQ2 z v := by
  have hdzlo := sideDz_lower hzlo hz
  have hdzhi := sideDz_upper hzhi hz
  have hdz0 : 0 ≤ z - criticalTheta := sub_nonneg.mpr hz
  have hdup0 : (0 : ℝ) ≤ (max 0 (zhi - sideThetaLowerQ) : ℚ) := by
    exact_mod_cast (le_max_left 0 (zhi - sideThetaLowerQ))
  have hklo0 : (0 : ℝ) ≤ sideK2LowerQ := by
    norm_num [sideK2LowerQ, sideD2Q, sideBetaLowerQ, sideLambda2Q]
  have hkhi0 : (0 : ℝ) ≤ sideK2UpperQ := by
    norm_num [sideK2UpperQ, sideD2Q, sideBetaUpperQ, sideLambda2Q]
  have hkorder : (sideK2LowerQ : ℝ) ≤ sideK2UpperQ := by
    norm_num [sideK2LowerQ, sideK2UpperQ, sideD2Q, sideBetaLowerQ,
      sideBetaUpperQ, sideLambda2Q]
  have hbEq : (sideBetaLowerQ : ℝ) = betaLower := by
    norm_num [sideBetaLowerQ, betaLower]
  have hkEq : (sideK2LowerQ : ℝ) =
      (sideD2Q : ℝ) + betaLower * (sideLambda2Q : ℝ) := by
    norm_num [sideK2LowerQ, sideD2Q, sideBetaLowerQ,
      sideLambda2Q, betaLower]
  have hbase := mul_le_mul_of_nonneg_left hdzlo
    (mul_nonneg hklo0 betaLower_pos.le)
  have hprod :
      (sideK2LowerQ : ℝ) * (z - criticalTheta) ≤
        (sideK2UpperQ : ℝ) *
          (max 0 (zhi - sideThetaLowerQ) : ℚ) := by
    exact mul_le_mul hkorder hdzhi hdz0 hkhi0
  have hprodSq :
      ((sideK2LowerQ : ℝ) * (z - criticalTheta)) ^ 2 ≤
        ((sideK2UpperQ : ℝ) *
          (max 0 (zhi - sideThetaLowerQ) : ℚ)) ^ 2 := by
    exact (sq_le_sq₀ (mul_nonneg hklo0 hdz0) (mul_nonneg hkhi0 hdup0)).2 hprod
  have hcpos : (0 : ℝ) < sideC2Q := by norm_num [sideC2Q]
  have hnegative :
      -((sideK2UpperQ : ℝ) ^ 2 *
          (max 0 (zhi - sideThetaLowerQ) : ℚ) ^ 2 /
            (4 * (sideC2Q : ℝ))) ≤
        -((sideK2LowerQ : ℝ) ^ 2 * (z - criticalTheta) ^ 2 /
            (4 * (sideC2Q : ℝ))) := by
    have hden : 0 < (4 : ℝ) * sideC2Q := mul_pos (by norm_num) hcpos
    rw [neg_le_neg_iff, div_le_div_iff₀ hden hden]
    nlinarith [hprodSq]
  have hcomplete :
      -((sideK2LowerQ : ℝ) ^ 2 * (z - criticalTheta) ^ 2 /
          (4 * (sideC2Q : ℝ))) ≤
        (sideC2Q : ℝ) * (v - betaLower) ^ 2 +
          (sideK2LowerQ : ℝ) * (v - betaLower) * (z - criticalTheta) := by
    have hs := sq_nonneg
      (2 * (sideC2Q : ℝ) * (v - betaLower) +
        (sideK2LowerQ : ℝ) * (z - criticalTheta))
    norm_num [sideC2Q] at hs ⊢
    nlinarith
  have hquad := hnegative.trans hcomplete
  have hzlo0R : (0 : Real) < (zlo : Real) := by exact_mod_cast hzlo0
  have hz0 : 0 < z := hzlo0R.trans_le hzlo
  have hzhi0R : (0 : Real) < (zhi : Real) := hz0.trans_le hzhi
  have hzhi0 : (0 : ℚ) < zhi := by exact_mod_cast hzhi0R
  have hlogUpper := qScaledLogUpper_sound hzhi0
  have hlogMono := Real.log_le_log hz0 hzhi
  have hlog := hlogMono.trans hlogUpper
  have hlambda0 : (0 : ℝ) ≤ sideLambda2Q := by norm_num [sideLambda2Q]
  have hlogterm := mul_le_mul_of_nonneg_left hlog hlambda0
  unfold qSideQ2BoxLower sideQ2
  push_cast at hbase hquad hlogterm ⊢
  rw [hbEq]
  rw [hkEq] at hbase hquad ⊢
  ring_nf at hbase hquad hlogterm ⊢
  linarith

structure SideQ2Box where
  zlo : ℚ
  zhi : ℚ
deriving Repr, DecidableEq

def SideQ2Box.Mem (b : SideQ2Box) (z : ℝ) : Prop :=
  (b.zlo : ℝ) ≤ z ∧ z ≤ (b.zhi : ℝ)

inductive SideQ2Tree where
  | leaf
  | split (mid : ℚ) (left right : SideQ2Tree)
deriving Repr, DecidableEq

def SideQ2Tree.valid (target : ℚ) : SideQ2Tree → SideQ2Box → Bool
  | .leaf, b => decide (0 < b.zlo ∧ target < qSideQ2BoxLower b.zlo b.zhi)
  | .split mid left right, b =>
      decide (b.zlo < mid ∧ mid < b.zhi) &&
        left.valid target { b with zhi := mid } &&
        right.valid target { b with zlo := mid }

theorem SideQ2Tree.sound {target : ℚ} {tree : SideQ2Tree} {b : SideQ2Box}
    (ht : tree.valid target b = true) {z v : ℝ}
    (hz : criticalTheta ≤ z) (hmem : b.Mem z) :
    (target : ℝ) < sideQ2 z v := by
  induction tree generalizing b with
  | leaf =>
      have hp : 0 < b.zlo ∧ target < qSideQ2BoxLower b.zlo b.zhi :=
        of_decide_eq_true ht
      have hlower := qSideQ2BoxLower_sound (v := v) hp.1 hmem.1 hmem.2 hz
      have hpR : (target : ℝ) < (qSideQ2BoxLower b.zlo b.zhi : ℝ) := by
        exact_mod_cast hp.2
      linarith
  | split mid left right ihl ihr =>
      change (decide (b.zlo < mid ∧ mid < b.zhi) &&
        left.valid target { b with zhi := mid } &&
        right.valid target { b with zlo := mid }) = true at ht
      have ho := Bool.and_eq_true_iff.mp ht
      have hi := Bool.and_eq_true_iff.mp ho.1
      by_cases hm : z ≤ (mid : ℝ)
      · exact ihl hi.2 ⟨hmem.1, hm⟩
      · exact ihr ho.2 ⟨le_of_not_ge hm, hmem.2⟩

end

end GDLowerBound.FourBlock
