import GDLowerBound.FourBlock.CentralEnergy
import GDLowerBound.FourBlock.CompressedMatchingCertificate
import GDLowerBound.FourBlock.MatchingScale

/-! # Executable recursive central-region certificate checker -/

namespace GDLowerBound.FourBlock

/-- The central certificate is stable under this finite matching error. -/
def centralMatchingFloorQ : ℚ := -1 / 1000000

structure CentralQBox where
  rlo : ℚ
  rhi : ℚ
  slo : ℚ
  shi : ℚ
deriving Repr, DecidableEq

def CentralQBox.aLo (b : CentralQBox) : ℚ := max 0 (2 * b.rlo - b.shi)
def CentralQBox.aHi (b : CentralQBox) : ℚ := b.rhi / 2

def CentralQBox.Mem (b : CentralQBox) (r s : ℝ) : Prop :=
  (b.rlo : ℝ) ≤ r ∧ r ≤ (b.rhi : ℝ) ∧ (b.slo : ℝ) ≤ s ∧ s ≤ (b.shi : ℝ)

inductive CentralLeafProof where
  | order
  | matching (support : MatchingWitness)
  | energy (zlo : ℚ) (support : Option MatchingWitness)
deriving Repr, DecidableEq

def CentralLeafProof.valid (leaf : CentralLeafProof) (b : CentralQBox) : Bool :=
  match leaf with
  | .order => decide (b.shi < 3 * b.rlo / 2 ∨ (1 + b.rhi) / 2 < b.slo)
  | .matching c => decide
      (c.valid = true ∧ c.z = centralZUpperQ ∧
        c.boxUpper b.aLo b.aHi b.rlo b.rhi b.slo b.shi < centralMatchingFloorQ)
  | .energy zlo none => decide
      (centralThetaLowerQ ≤ zlo ∧ zlo ≤ centralZUpperQ ∧
        0 < b.rlo ∧ 0 < b.slo ∧ zlo = centralThetaLowerQ ∧
        31 / 1250 < qCentralEnergyLower zlo b.rlo b.slo)
  | .energy zlo (some c) => decide
      (centralThetaLowerQ ≤ zlo ∧ zlo ≤ centralZUpperQ ∧
        0 < b.rlo ∧ 0 < b.slo ∧ c.valid = true ∧ c.z = zlo ∧
        c.boxUpper b.aLo b.aHi b.rlo b.rhi b.slo b.shi < centralMatchingFloorQ ∧
        31 / 1250 < qCentralEnergyLower zlo b.rlo b.slo)

inductive CentralCertTree where
  | leaf (proof : CentralLeafProof)
  | splitR (mid : ℚ) (left right : CentralCertTree)
  | splitS (mid : ℚ) (left right : CentralCertTree)
deriving Repr, DecidableEq

def CentralCertTree.valid : CentralCertTree → CentralQBox → Bool
  | .leaf proof, b => proof.valid b
  | .splitR mid left right, b =>
      decide (b.rlo < mid ∧ mid < b.rhi) &&
        left.valid { b with rhi := mid } && right.valid { b with rlo := mid }
  | .splitS mid left right, b =>
      decide (b.slo < mid ∧ mid < b.shi) &&
        left.valid { b with shi := mid } && right.valid { b with slo := mid }

theorem CentralQBox.a_mem {b : CentralQBox} {a r s : ℝ}
    (hord : OrderedFourBlocks a r s) (hmem : b.Mem r s) :
    (b.aLo : ℝ) ≤ a ∧ a ≤ (b.aHi : ℝ) := by
  have hd := orderedFourBlocks_domain hord
  rcases hmem with ⟨hrl, hrh, hsl, hsh⟩
  constructor
  · unfold CentralQBox.aLo
    push_cast
    apply max_le
    · exact (le_max_left 0 (2 * r - s)).trans hd.2.2.2.2.1
    · have hmass : 2 * r - s ≤ a :=
        (le_max_right 0 (2 * r - s)).trans hd.2.2.2.2.1
      linarith
  · unfold CentralQBox.aHi
    push_cast
    linarith [hd.2.2.2.2.2]

theorem CentralLeafProof.sound {leaf : CentralLeafProof} {b : CentralQBox}
    (hv : leaf.valid b = true) {z a r s : ℝ}
    (hz0 : 0 < z) (hzlo : (centralThetaLowerQ : ℝ) ≤ z)
    (hzhi : z ≤ (centralZUpperQ : ℝ))
    (ha : 0 < a) (h2 : 0 < r - a) (h3 : 0 < s - r) (h4 : 0 < 1 - s)
    (hord : OrderedFourBlocks a r s)
    (hmatch : (centralMatchingFloorQ : ℝ) ≤ fourBlockMatching z a r s)
    (hmem : b.Mem r s) :
    31 / 1250 < centralEnergy z r s := by
  cases leaf with
  | order =>
      have hvp : b.shi < 3 * b.rlo / 2 ∨ (1 + b.rhi) / 2 < b.slo :=
        of_decide_eq_true hv
      have hd := orderedFourBlocks_domain hord
      rcases hmem with ⟨hrl, hrh, hsl, hsh⟩
      rcases hvp with hleft | hright
      · have hleftR : (b.shi : ℝ) < 3 * (b.rlo : ℝ) / 2 := by exact_mod_cast hleft
        exfalso
        linarith [hd.2.2.1]
      · have hrightR : (1 + (b.rhi : ℝ)) / 2 < (b.slo : ℝ) := by exact_mod_cast hright
        exfalso
        linarith [hd.2.2.2.1]
  | matching c =>
      have hvp : c.valid = true ∧ c.z = centralZUpperQ ∧
          c.boxUpper b.aLo b.aHi b.rlo b.rhi b.slo b.shi < centralMatchingFloorQ :=
        of_decide_eq_true hv
      rcases hvp with ⟨hc, hcz, hupper⟩
      have haBox := CentralQBox.a_mem hord hmem
      have hcert := c.sound hc ha h2 h3 h4 haBox.1 haBox.2
        hmem.1 hmem.2.1 hmem.2.2.1 hmem.2.2.2
      rw [hcz] at hcert
      have hscale := fourBlockMatching_mono_scale hz0 hzhi ha h2 h3 h4
      have hupperR : (c.boxUpper b.aLo b.aHi b.rlo b.rhi b.slo b.shi : ℝ) < (centralMatchingFloorQ : ℝ) := by
        exact_mod_cast hupper
      exfalso
      linarith
  | energy zlo support =>
      cases support with
      | none =>
          have hvp : centralThetaLowerQ ≤ zlo ∧ zlo ≤ centralZUpperQ ∧
              0 < b.rlo ∧ 0 < b.slo ∧ zlo = centralThetaLowerQ ∧
              31 / 1250 < qCentralEnergyLower zlo b.rlo b.slo :=
            of_decide_eq_true hv
          rcases hvp with ⟨hzloRange, hzloUpper, hrlo0, hslo0, hzloEq, henergy⟩
          have hzlower : (zlo : ℝ) ≤ z := by rw [hzloEq]; exact hzlo
          have hzloPosQ : 0 < zlo := by
            rw [hzloEq]
            norm_num [centralThetaLowerQ]
          have hq := qCentralEnergyLower_sound hzloPosQ hrlo0 hslo0
          have hmono := centralEnergy_mono (by exact_mod_cast hzloPosQ)
            (by exact_mod_cast hrlo0) (by exact_mod_cast hslo0)
            (by exact_mod_cast hzloRange) hzlower hzhi hmem.1 hmem.2.2.1
          have henergyR : (((31 / 1250 : ℚ) : ℝ)) <
              (qCentralEnergyLower zlo b.rlo b.slo : ℝ) := by exact_mod_cast henergy
          norm_num at henergyR
          linarith
      | some c =>
          have hvp : centralThetaLowerQ ≤ zlo ∧ zlo ≤ centralZUpperQ ∧
              0 < b.rlo ∧ 0 < b.slo ∧ c.valid = true ∧ c.z = zlo ∧
              c.boxUpper b.aLo b.aHi b.rlo b.rhi b.slo b.shi < centralMatchingFloorQ ∧
              31 / 1250 < qCentralEnergyLower zlo b.rlo b.slo :=
            of_decide_eq_true hv
          rcases hvp with ⟨hzloRange, hzloUpper, hrlo0, hslo0, hc, hcz,
            hupper, henergy⟩
          have hzloPosQ : 0 < zlo := by
            have : 0 < centralThetaLowerQ := by norm_num [centralThetaLowerQ]
            exact this.trans_le hzloRange
          have hzlower : (zlo : ℝ) ≤ z := by
            by_contra hnot
            have hzzlo : z ≤ (zlo : ℝ) := le_of_not_ge hnot
            have haBox := CentralQBox.a_mem hord hmem
            have hcert := c.sound hc ha h2 h3 h4 haBox.1 haBox.2
              hmem.1 hmem.2.1 hmem.2.2.1 hmem.2.2.2
            rw [hcz] at hcert
            have hscale := fourBlockMatching_mono_scale hz0 hzzlo ha h2 h3 h4
            have hupperR :
                (c.boxUpper b.aLo b.aHi b.rlo b.rhi b.slo b.shi : ℝ) < (centralMatchingFloorQ : ℝ) := by
              exact_mod_cast hupper
            linarith
          have hq := qCentralEnergyLower_sound hzloPosQ hrlo0 hslo0
          have hmono := centralEnergy_mono (by exact_mod_cast hzloPosQ)
            (by exact_mod_cast hrlo0) (by exact_mod_cast hslo0)
            (by exact_mod_cast hzloRange) hzlower hzhi hmem.1 hmem.2.2.1
          have henergyR : (((31 / 1250 : ℚ) : ℝ)) <
              (qCentralEnergyLower zlo b.rlo b.slo : ℝ) := by exact_mod_cast henergy
          norm_num at henergyR
          linarith

theorem CentralCertTree.sound {tree : CentralCertTree} {b : CentralQBox}
    (hv : tree.valid b = true) {z a r s : ℝ}
    (hz0 : 0 < z) (hzlo : (centralThetaLowerQ : ℝ) ≤ z)
    (hzhi : z ≤ (centralZUpperQ : ℝ))
    (ha : 0 < a) (h2 : 0 < r - a) (h3 : 0 < s - r) (h4 : 0 < 1 - s)
    (hord : OrderedFourBlocks a r s)
    (hmatch : (centralMatchingFloorQ : ℝ) ≤ fourBlockMatching z a r s)
    (hmem : b.Mem r s) :
    31 / 1250 < centralEnergy z r s := by
  induction tree generalizing b with
  | leaf proof =>
      exact CentralLeafProof.sound hv hz0 hzlo hzhi ha h2 h3 h4 hord hmatch hmem
  | splitR mid left right ihl ihr =>
      change (decide (b.rlo < mid ∧ mid < b.rhi) &&
        left.valid { b with rhi := mid } && right.valid { b with rlo := mid }) = true at hv
      have houter := Bool.and_eq_true_iff.mp hv
      have hinner := Bool.and_eq_true_iff.mp houter.1
      have hrange : b.rlo < mid ∧ mid < b.rhi := of_decide_eq_true hinner.1
      have hl := hinner.2
      have hr := houter.2
      by_cases hm : r ≤ (mid : ℝ)
      · exact ihl (b := { b with rhi := mid }) hl ⟨hmem.1, hm, hmem.2.2.1, hmem.2.2.2⟩
      · exact ihr (b := { b with rlo := mid }) hr ⟨le_of_not_ge hm, hmem.2.1, hmem.2.2.1, hmem.2.2.2⟩
  | splitS mid left right ihl ihr =>
      change (decide (b.slo < mid ∧ mid < b.shi) &&
        left.valid { b with shi := mid } && right.valid { b with slo := mid }) = true at hv
      have houter := Bool.and_eq_true_iff.mp hv
      have hinner := Bool.and_eq_true_iff.mp houter.1
      have hrange : b.slo < mid ∧ mid < b.shi := of_decide_eq_true hinner.1
      have hl := hinner.2
      have hr := houter.2
      by_cases hm : s ≤ (mid : ℝ)
      · exact ihl (b := { b with shi := mid }) hl ⟨hmem.1, hmem.2.1, hmem.2.2.1, hm⟩
      · exact ihr (b := { b with slo := mid }) hr ⟨hmem.1, hmem.2.1, le_of_not_ge hm, hmem.2.2.2⟩

end GDLowerBound.FourBlock
