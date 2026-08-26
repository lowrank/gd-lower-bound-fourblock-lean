import GDLowerBound.FourBlock.CentralEnergy

/-! # Exact one-dimensional certificate for the four-block tail proxy -/

namespace GDLowerBound.FourBlock

noncomputable section

def tailQ2LowerQ : ℚ := 9767 / 1000000
def tailG82LowerQ : ℚ := 151 / 5000
def tailR20UpperQ : ℚ := 3 / 20
def tailR30LowerQ : ℚ := 109 / 250
def tailRatioQ : ℚ := 33 / 25
def tailQmaxQ : ℚ := 33 / 50
def tailTargetQ : ℚ := 31 / 1250

def tailArgument (z : ℝ) : ℝ :=
  ((tailRatioQ : ℝ) * tailR30LowerQ - z) / tailR20UpperQ

def tailProxy (z : ℝ) : ℝ :=
  (tailQ2LowerQ : ℝ) + (tailG82LowerQ : ℝ) +
    (centralAlphaQ : ℝ) * Real.log (tailQmaxQ : ℝ) +
    centralEndpointRaw z +
    (centralLambda2Q : ℝ) * Real.log (tailArgument z)

def qTailArgumentLower (zhi : ℚ) : ℚ :=
  (tailRatioQ * tailR30LowerQ - zhi) / tailR20UpperQ

def qTailBoxLower (zlo zhi : ℚ) : ℚ :=
  tailQ2LowerQ + tailG82LowerQ +
    centralAlphaQ * qScaledLogLower tailQmaxQ +
    qCentralEndpointRaw zlo +
    centralLambda2Q * qScaledLogLower (qTailArgumentLower zhi)

theorem qTailBoxLower_sound {zlo zhi : ℚ} {z : ℝ}
    (hzloRange : centralThetaLowerQ ≤ zlo)
    (hzlo : (zlo : ℝ) ≤ z) (hzhi : z ≤ (zhi : ℝ))
    (hzupper : z ≤ (centralZUpperQ : ℝ))
    (harg : 0 < qTailArgumentLower zhi) :
    (qTailBoxLower zlo zhi : ℝ) ≤ tailProxy z := by
  have hzlo0 : (0 : ℚ) < zlo := by
    have htheta : (0 : ℚ) < centralThetaLowerQ := by
      norm_num [centralThetaLowerQ]
    exact htheta.trans_le hzloRange
  have hzlo0R : (0 : ℝ) < zlo := by exact_mod_cast hzlo0
  have hendpoint := centralEndpointRaw_mono
    (by exact_mod_cast hzloRange) hzlo hzupper
  have hendpointQ := coe_qCentralEndpointRaw zlo
  have hqmax0 : (0 : ℚ) < tailQmaxQ := by norm_num [tailQmaxQ]
  have hlogQ := qScaledLogLower_sound hqmax0
  have hargR : (0 : ℝ) < qTailArgumentLower zhi := by exact_mod_cast harg
  have hargOrder : (qTailArgumentLower zhi : ℝ) ≤ tailArgument z := by
    unfold qTailArgumentLower tailArgument
    push_cast
    norm_num [tailRatioQ, tailR30LowerQ, tailR20UpperQ] at hzhi ⊢
    linarith
  have hargActual : 0 < tailArgument z := hargR.trans_le hargOrder
  have hlogArgLo := qScaledLogLower_sound harg
  have hlogArgMono := Real.log_le_log hargR hargOrder
  have hlogArg := hlogArgLo.trans hlogArgMono
  have halpha0 : (0 : ℝ) ≤ centralAlphaQ := by norm_num [centralAlphaQ]
  have hlambda0 : (0 : ℝ) ≤ centralLambda2Q := by norm_num [centralLambda2Q]
  have hqterm := mul_le_mul_of_nonneg_left hlogQ halpha0
  have hargterm := mul_le_mul_of_nonneg_left hlogArg hlambda0
  unfold qTailBoxLower tailProxy
  push_cast at hqterm hargterm ⊢
  rw [hendpointQ] at ⊢
  ring_nf at hqterm hargterm ⊢
  linarith

structure TailBox where
  zlo : ℚ
  zhi : ℚ
deriving Repr, DecidableEq

def TailBox.Mem (b : TailBox) (z : ℝ) : Prop :=
  (b.zlo : ℝ) ≤ z ∧ z ≤ (b.zhi : ℝ)

inductive TailTree where
  | leaf
  | split (mid : ℚ) (left right : TailTree)
deriving Repr, DecidableEq

def TailTree.valid : TailTree → TailBox → Bool
  | .leaf, b => decide
      (centralThetaLowerQ ≤ b.zlo ∧ b.zhi ≤ centralZUpperQ ∧
        0 < qTailArgumentLower b.zhi ∧ tailTargetQ < qTailBoxLower b.zlo b.zhi)
  | .split mid left right, b =>
      decide (b.zlo < mid ∧ mid < b.zhi) &&
        left.valid { b with zhi := mid } && right.valid { b with zlo := mid }

theorem TailTree.sound {tree : TailTree} {b : TailBox}
    (ht : tree.valid b = true) {z : ℝ}
    (hzupper : z ≤ (centralZUpperQ : ℝ)) (hmem : b.Mem z) :
    (tailTargetQ : ℝ) < tailProxy z := by
  induction tree generalizing b with
  | leaf =>
      have hp : centralThetaLowerQ ≤ b.zlo ∧
          b.zhi ≤ centralZUpperQ ∧ 0 < qTailArgumentLower b.zhi ∧
          tailTargetQ < qTailBoxLower b.zlo b.zhi := of_decide_eq_true ht
      have hlower := qTailBoxLower_sound hp.1 hmem.1 hmem.2 hzupper hp.2.2.1
      have hpR : (tailTargetQ : ℝ) <
          (qTailBoxLower b.zlo b.zhi : ℝ) := by exact_mod_cast hp.2.2.2
      linarith
  | split mid left right ihl ihr =>
      change (decide (b.zlo < mid ∧ mid < b.zhi) &&
        left.valid { b with zhi := mid } && right.valid { b with zlo := mid }) = true at ht
      have ho := Bool.and_eq_true_iff.mp ht
      have hi := Bool.and_eq_true_iff.mp ho.1
      by_cases hm : z ≤ (mid : ℝ)
      · exact ihl hi.2 ⟨hmem.1, hm⟩
      · exact ihr ho.2 ⟨le_of_not_ge hm, hmem.2⟩

def tailCertificateBox : TailBox :=
  { zlo := 7982344478949 / 19531250000000, zhi := 119 / 250 }

def tailCertificate : TailTree :=
  .split (17279219478949 / 39062500000000)
    (.split (33243908436847 / 78125000000000)
      (.split (65173286352643 / 156250000000000) .leaf .leaf)
      .leaf)
    .leaf

theorem tailCertificate_valid : tailCertificate.valid tailCertificateBox = true := by
  native_decide

theorem certifiedTailProxy {z : ℝ}
    (hzlo : (7982344478949 / 19531250000000 : ℝ) ≤ z)
    (hzhi : z ≤ (119 / 250 : ℝ)) :
    (31 / 1250 : ℝ) < tailProxy z := by
  have hmem : tailCertificateBox.Mem z := by
    dsimp only [tailCertificateBox, TailBox.Mem]
    push_cast
    exact ⟨hzlo, hzhi⟩
  simpa [tailTargetQ] using
    (TailTree.sound (tree := tailCertificate) (b := tailCertificateBox)
      tailCertificate_valid (by norm_num [centralZUpperQ] at hzhi ⊢; exact hzhi) hmem)

end

end GDLowerBound.FourBlock
