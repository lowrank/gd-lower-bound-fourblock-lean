import GDLowerBound.FourBlock.CertifiedKernelJet
import GDLowerBound.FourBlock.FourBlockSupporting
import GDLowerBound.FourBlock.IntervalUpper

/-! # Compact explicit supporting-plane certificates -/

namespace GDLowerBound.FourBlock

structure MatchingSupportCert where
  z : ℚ
  a₀ : ℚ
  r₀ : ℚ
  s₀ : ℚ
  k14 : KernelJetCert
  k23 : KernelJetCert
deriving Repr, DecidableEq

def MatchingSupportCert.Valid (c : MatchingSupportCert) : Prop :=
  0 < c.z ∧ 0 < c.a₀ ∧ 0 < c.r₀ - c.a₀ ∧ 0 < c.s₀ - c.r₀ ∧
  0 < 1 - c.s₀ ∧ c.k14.valid = true ∧ c.k23.valid = true ∧
  c.k14.value.u = 8 * c.z * c.a₀ ∧
  c.k14.value.v = 8 * c.z * (1 - c.s₀) ∧
  c.k23.value.u = 8 * c.z * (c.r₀ - c.a₀) ∧
  c.k23.value.v = 8 * c.z * (c.s₀ - c.r₀)

instance (c : MatchingSupportCert) : Decidable c.Valid := by
  unfold MatchingSupportCert.Valid
  infer_instance

def MatchingSupportCert.valid (c : MatchingSupportCert) : Bool := decide c.Valid

def MatchingSupportCert.hUpper (c : MatchingSupportCert) : ℚ :=
  (c.k14.value.upper + c.k23.value.upper) / 2

def MatchingSupportCert.gradALower (c : MatchingSupportCert) : ℚ :=
  4 * c.z * (c.k14.gradULower - c.k23.gradUUpper)

def MatchingSupportCert.gradAUpper (c : MatchingSupportCert) : ℚ :=
  4 * c.z * (c.k14.gradUUpper - c.k23.gradULower)

def MatchingSupportCert.gradRLower (c : MatchingSupportCert) : ℚ :=
  4 * c.z * (c.k23.gradULower - c.k23.gradVUpper)

def MatchingSupportCert.gradRUpper (c : MatchingSupportCert) : ℚ :=
  4 * c.z * (c.k23.gradUUpper - c.k23.gradVLower)

def MatchingSupportCert.gradSLower (c : MatchingSupportCert) : ℚ :=
  4 * c.z * (-c.k14.gradVUpper + c.k23.gradVLower)

def MatchingSupportCert.gradSUpper (c : MatchingSupportCert) : ℚ :=
  4 * c.z * (-c.k14.gradVLower + c.k23.gradVUpper)

def MatchingSupportCert.boxUpper (c : MatchingSupportCert)
    (alo ahi rlo rhi slo shi : ℚ) : ℚ :=
  c.hUpper + qMulUpper c.gradALower c.gradAUpper (alo - c.a₀) (ahi - c.a₀) +
    qMulUpper c.gradRLower c.gradRUpper (rlo - c.r₀) (rhi - c.r₀) +
    qMulUpper c.gradSLower c.gradSUpper (slo - c.s₀) (shi - c.s₀)

theorem MatchingSupportCert.sound {c : MatchingSupportCert}
    (hc : c.valid = true) {alo ahi rlo rhi slo shi : ℚ} {a r s : ℝ}
    (ha : 0 < a) (h2 : 0 < r - a) (h3 : 0 < s - r) (h4 : 0 < 1 - s)
    (hal : (alo : ℝ) ≤ a) (hah : a ≤ (ahi : ℝ))
    (hrl : (rlo : ℝ) ≤ r) (hrh : r ≤ (rhi : ℝ))
    (hsl : (slo : ℝ) ≤ s) (hsh : s ≤ (shi : ℝ)) :
    fourBlockMatching (c.z : ℝ) a r s ≤ (c.boxUpper alo ahi rlo rhi slo shi : ℝ) := by
  have hv : c.Valid := of_decide_eq_true hc
  rcases hv with ⟨hz, ha₀, h20, h30, h40, hk14v, hk23v,
    hk14u, hk14w, hk23u, hk23w⟩
  have h14 := KernelJetCert.sound hk14v
  have h23 := KernelJetCert.sound hk23v
  rw [hk14u, hk14w] at h14
  rw [hk23u, hk23w] at h23
  push_cast at h14 h23
  have hH : fourBlockMatching (c.z : ℝ) c.a₀ c.r₀ c.s₀ ≤ (c.hUpper : ℝ) := by
    unfold fourBlockMatching MatchingSupportCert.hUpper
    push_cast
    linarith [h14.1, h23.1]
  have hga : (c.gradALower : ℝ) ≤ matchingGradA c.z c.a₀ c.r₀ c.s₀ ∧
      matchingGradA c.z c.a₀ c.r₀ c.s₀ ≤ (c.gradAUpper : ℝ) := by
    unfold MatchingSupportCert.gradALower MatchingSupportCert.gradAUpper matchingGradA
    push_cast
    have hz0 : (0 : ℝ) ≤ 4 * c.z := by exact_mod_cast (show 0 ≤ 4 * c.z by positivity)
    constructor
    · exact mul_le_mul_of_nonneg_left (sub_le_sub h14.2.1 h23.2.2.1) hz0
    · exact mul_le_mul_of_nonneg_left (sub_le_sub h14.2.2.1 h23.2.1) hz0
  have hgr : (c.gradRLower : ℝ) ≤ matchingGradR c.z c.a₀ c.r₀ c.s₀ ∧
      matchingGradR c.z c.a₀ c.r₀ c.s₀ ≤ (c.gradRUpper : ℝ) := by
    unfold MatchingSupportCert.gradRLower MatchingSupportCert.gradRUpper matchingGradR
    push_cast
    have hz0 : (0 : ℝ) ≤ 4 * c.z := by exact_mod_cast (show 0 ≤ 4 * c.z by positivity)
    constructor
    · exact mul_le_mul_of_nonneg_left (sub_le_sub h23.2.1 h23.2.2.2.2) hz0
    · exact mul_le_mul_of_nonneg_left (sub_le_sub h23.2.2.1 h23.2.2.2.1) hz0
  have hgs : (c.gradSLower : ℝ) ≤ matchingGradS c.z c.a₀ c.r₀ c.s₀ ∧
      matchingGradS c.z c.a₀ c.r₀ c.s₀ ≤ (c.gradSUpper : ℝ) := by
    unfold MatchingSupportCert.gradSLower MatchingSupportCert.gradSUpper matchingGradS
    push_cast
    have hz0 : (0 : ℝ) ≤ 4 * c.z := by exact_mod_cast (show 0 ≤ 4 * c.z by positivity)
    constructor
    · exact mul_le_mul_of_nonneg_left
        (add_le_add (neg_le_neg h14.2.2.2.2) h23.2.2.2.1) hz0
    · exact mul_le_mul_of_nonneg_left
        (add_le_add (neg_le_neg h14.2.2.2.1) h23.2.2.2.2) hz0
  have hsupp := fourBlockMatching_le_support
    (z := (c.z : ℝ)) (a₀ := (c.a₀ : ℝ)) (r₀ := (c.r₀ : ℝ)) (s₀ := (c.s₀ : ℝ))
    (a := a) (r := r) (s := s)
    (by exact_mod_cast hz) (by exact_mod_cast ha₀) (by exact_mod_cast h20)
    (by exact_mod_cast h30) (by exact_mod_cast h40) ha h2 h3 h4
  have hpa := qMulUpper_sound
    (xl := c.gradALower) (xh := c.gradAUpper)
    (yl := alo - c.a₀) (yh := ahi - c.a₀)
    (x := matchingGradA c.z c.a₀ c.r₀ c.s₀) (y := a - (c.a₀ : ℝ))
    hga.1 hga.2 (by push_cast; linarith) (by push_cast; linarith)
  have hpr := qMulUpper_sound
    (xl := c.gradRLower) (xh := c.gradRUpper)
    (yl := rlo - c.r₀) (yh := rhi - c.r₀)
    (x := matchingGradR c.z c.a₀ c.r₀ c.s₀) (y := r - (c.r₀ : ℝ))
    hgr.1 hgr.2 (by push_cast; linarith) (by push_cast; linarith)
  have hps := qMulUpper_sound
    (xl := c.gradSLower) (xh := c.gradSUpper)
    (yl := slo - c.s₀) (yh := shi - c.s₀)
    (x := matchingGradS c.z c.a₀ c.r₀ c.s₀) (y := s - (c.s₀ : ℝ))
    hgs.1 hgs.2 (by push_cast; linarith) (by push_cast; linarith)
  unfold MatchingSupportCert.boxUpper
  push_cast
  linarith

end GDLowerBound.FourBlock
