import GDLowerBound.FourBlock.AutoGradient
import GDLowerBound.FourBlock.FourBlockSupporting
import GDLowerBound.FourBlock.IntervalUpper

/-!
# Rational supporting-plane bounds for four-block matching

Every definition below is executable over `ℚ`.  The soundness theorem turns
its output into an upper bound for the exact real four-block functional on a
rectangular `(a,r,s)` box.
-/

namespace GDLowerBound.FourBlock

structure QBounds where
  lo : ℚ
  hi : ℚ
deriving Repr, DecidableEq

def qKernelGradUBounds (u v : ℚ) (sqrtSteps : ℕ) : QBounds :=
  ⟨qKernelGradULower u v sqrtSteps, qKernelGradUUpper u v⟩

def qKernelGradVBounds (u v : ℚ) (sqrtSteps : ℕ) : QBounds :=
  ⟨qKernelGradVLower u v sqrtSteps, qKernelGradVUpper u v⟩

def qMatchingHUpper (z a r s : ℚ) (sqrtSteps logSteps : ℕ) : ℚ :=
  (qKernelUpperAuto (8 * z * a) (8 * z * (1 - s)) sqrtSteps logSteps +
    qKernelUpperAuto (8 * z * (r - a)) (8 * z * (s - r)) sqrtSteps logSteps) / 2

def qMatchingGradABounds (z a r s : ℚ) (sqrtSteps : ℕ) : QBounds :=
  let g14 := qKernelGradUBounds (8 * z * a) (8 * z * (1 - s)) sqrtSteps
  let g23 := qKernelGradUBounds (8 * z * (r - a)) (8 * z * (s - r)) sqrtSteps
  ⟨4 * z * (g14.lo - g23.hi), 4 * z * (g14.hi - g23.lo)⟩

def qMatchingGradRBounds (z a r s : ℚ) (sqrtSteps : ℕ) : QBounds :=
  let gu := qKernelGradUBounds (8 * z * (r - a)) (8 * z * (s - r)) sqrtSteps
  let gv := qKernelGradVBounds (8 * z * (r - a)) (8 * z * (s - r)) sqrtSteps
  ⟨4 * z * (gu.lo - gv.hi), 4 * z * (gu.hi - gv.lo)⟩

def qMatchingGradSBounds (z a r s : ℚ) (sqrtSteps : ℕ) : QBounds :=
  let g14 := qKernelGradVBounds (8 * z * a) (8 * z * (1 - s)) sqrtSteps
  let g23 := qKernelGradVBounds (8 * z * (r - a)) (8 * z * (s - r)) sqrtSteps
  ⟨4 * z * (-g14.hi + g23.lo), 4 * z * (-g14.lo + g23.hi)⟩

def qMatchingSupportUpper (z a₀ r₀ s₀ alo ahi rlo rhi slo shi : ℚ)
    (sqrtSteps logSteps : ℕ) : ℚ :=
  let ga := qMatchingGradABounds z a₀ r₀ s₀ sqrtSteps
  let gr := qMatchingGradRBounds z a₀ r₀ s₀ sqrtSteps
  let gs := qMatchingGradSBounds z a₀ r₀ s₀ sqrtSteps
  qMatchingHUpper z a₀ r₀ s₀ sqrtSteps logSteps +
    qMulUpper ga.lo ga.hi (alo - a₀) (ahi - a₀) +
    qMulUpper gr.lo gr.hi (rlo - r₀) (rhi - r₀) +
    qMulUpper gs.lo gs.hi (slo - s₀) (shi - s₀)

theorem qMatchingHUpper_sound {z a r s : ℚ}
    (hz : 0 < z) (ha : 0 < a) (h2 : 0 < r - a)
    (h3 : 0 < s - r) (h4 : 0 < 1 - s) (sqrtSteps logSteps : ℕ) :
    fourBlockMatching (z : ℝ) (a : ℝ) (r : ℝ) (s : ℝ) ≤
      (qMatchingHUpper z a r s sqrtSteps logSteps : ℝ) := by
  have h14 := qKernelUpperAuto_sound
    (u := 8 * z * a) (v := 8 * z * (1 - s)) (by positivity) (by positivity)
    sqrtSteps logSteps
  have h23 := qKernelUpperAuto_sound
    (u := 8 * z * (r - a)) (v := 8 * z * (s - r)) (by positivity) (by positivity)
    sqrtSteps logSteps
  push_cast at h14 h23
  unfold fourBlockMatching qMatchingHUpper
  push_cast
  linarith

theorem qMatchingGradA_bounds_sound {z a r s : ℚ}
    (hz : 0 < z) (ha : 0 < a) (h2 : 0 < r - a)
    (h3 : 0 < s - r) (h4 : 0 < 1 - s) (sqrtSteps : ℕ) :
    (qMatchingGradABounds z a r s sqrtSteps).lo ≤
        matchingGradA (z : ℝ) (a : ℝ) (r : ℝ) (s : ℝ) ∧
      matchingGradA (z : ℝ) (a : ℝ) (r : ℝ) (s : ℝ) ≤
        (qMatchingGradABounds z a r s sqrtSteps).hi := by
  have h14 := qKernelGradU_bounds
    (u := 8 * z * a) (v := 8 * z * (1 - s)) (by positivity) (by positivity) sqrtSteps
  have h23 := qKernelGradU_bounds
    (u := 8 * z * (r - a)) (v := 8 * z * (s - r)) (by positivity) (by positivity) sqrtSteps
  push_cast at h14 h23
  have hzR : (0 : ℝ) ≤ 4 * z := by positivity
  constructor
  · have hsub := sub_le_sub h14.1 h23.2
    have hmul := mul_le_mul_of_nonneg_left hsub hzR
    unfold qMatchingGradABounds qKernelGradUBounds matchingGradA
    push_cast
    exact hmul
  · have hsub := sub_le_sub h14.2 h23.1
    have hmul := mul_le_mul_of_nonneg_left hsub hzR
    unfold qMatchingGradABounds qKernelGradUBounds matchingGradA
    push_cast
    exact hmul

theorem qMatchingGradR_bounds_sound {z a r s : ℚ}
    (hz : 0 < z) (ha : 0 < a) (h2 : 0 < r - a)
    (h3 : 0 < s - r) (h4 : 0 < 1 - s) (sqrtSteps : ℕ) :
    (qMatchingGradRBounds z a r s sqrtSteps).lo ≤
        matchingGradR (z : ℝ) (a : ℝ) (r : ℝ) (s : ℝ) ∧
      matchingGradR (z : ℝ) (a : ℝ) (r : ℝ) (s : ℝ) ≤
        (qMatchingGradRBounds z a r s sqrtSteps).hi := by
  have hu := qKernelGradU_bounds
    (u := 8 * z * (r - a)) (v := 8 * z * (s - r)) (by positivity) (by positivity) sqrtSteps
  have hv := qKernelGradV_bounds
    (u := 8 * z * (r - a)) (v := 8 * z * (s - r)) (by positivity) (by positivity) sqrtSteps
  push_cast at hu hv
  have hzR : (0 : ℝ) ≤ 4 * z := by positivity
  constructor
  · have hmul := mul_le_mul_of_nonneg_left (sub_le_sub hu.1 hv.2) hzR
    unfold qMatchingGradRBounds qKernelGradUBounds qKernelGradVBounds matchingGradR
    push_cast
    exact hmul
  · have hmul := mul_le_mul_of_nonneg_left (sub_le_sub hu.2 hv.1) hzR
    unfold qMatchingGradRBounds qKernelGradUBounds qKernelGradVBounds matchingGradR
    push_cast
    exact hmul

theorem qMatchingGradS_bounds_sound {z a r s : ℚ}
    (hz : 0 < z) (ha : 0 < a) (h2 : 0 < r - a)
    (h3 : 0 < s - r) (h4 : 0 < 1 - s) (sqrtSteps : ℕ) :
    (qMatchingGradSBounds z a r s sqrtSteps).lo ≤
        matchingGradS (z : ℝ) (a : ℝ) (r : ℝ) (s : ℝ) ∧
      matchingGradS (z : ℝ) (a : ℝ) (r : ℝ) (s : ℝ) ≤
        (qMatchingGradSBounds z a r s sqrtSteps).hi := by
  have h14 := qKernelGradV_bounds
    (u := 8 * z * a) (v := 8 * z * (1 - s)) (by positivity) (by positivity) sqrtSteps
  have h23 := qKernelGradV_bounds
    (u := 8 * z * (r - a)) (v := 8 * z * (s - r)) (by positivity) (by positivity) sqrtSteps
  push_cast at h14 h23
  have hzR : (0 : ℝ) ≤ 4 * z := by positivity
  constructor
  · have hmul := mul_le_mul_of_nonneg_left (add_le_add (neg_le_neg h14.2) h23.1) hzR
    unfold qMatchingGradSBounds qKernelGradVBounds matchingGradS
    push_cast
    exact hmul
  · have hmul := mul_le_mul_of_nonneg_left (add_le_add (neg_le_neg h14.1) h23.2) hzR
    unfold qMatchingGradSBounds qKernelGradVBounds matchingGradS
    push_cast
    exact hmul

theorem qMatchingSupportUpper_sound
    {z a₀ r₀ s₀ alo ahi rlo rhi slo shi : ℚ} {a r s : ℝ}
    (hz : 0 < z)
    (ha₀ : 0 < a₀) (h20 : 0 < r₀ - a₀)
    (h30 : 0 < s₀ - r₀) (h40 : 0 < 1 - s₀)
    (ha : 0 < a) (h2 : 0 < r - a) (h3 : 0 < s - r) (h4 : 0 < 1 - s)
    (hal : (alo : ℝ) ≤ a) (hah : a ≤ (ahi : ℝ))
    (hrl : (rlo : ℝ) ≤ r) (hrh : r ≤ (rhi : ℝ))
    (hsl : (slo : ℝ) ≤ s) (hsh : s ≤ (shi : ℝ))
    (sqrtSteps logSteps : ℕ) :
    fourBlockMatching (z : ℝ) a r s ≤
      (qMatchingSupportUpper z a₀ r₀ s₀ alo ahi rlo rhi slo shi
        sqrtSteps logSteps : ℝ) := by
  have hsupp := fourBlockMatching_le_support
    (z := (z : ℝ)) (a₀ := (a₀ : ℝ)) (r₀ := (r₀ : ℝ)) (s₀ := (s₀ : ℝ))
    (a := a) (r := r) (s := s)
    (by exact_mod_cast hz) (by exact_mod_cast ha₀) (by exact_mod_cast h20)
    (by exact_mod_cast h30) (by exact_mod_cast h40) ha h2 h3 h4
  have hH := qMatchingHUpper_sound hz ha₀ h20 h30 h40 sqrtSteps logSteps
  have hga := qMatchingGradA_bounds_sound hz ha₀ h20 h30 h40 sqrtSteps
  have hgr := qMatchingGradR_bounds_sound hz ha₀ h20 h30 h40 sqrtSteps
  have hgs := qMatchingGradS_bounds_sound hz ha₀ h20 h30 h40 sqrtSteps
  have hpa := qMulUpper_sound
    (xl := (qMatchingGradABounds z a₀ r₀ s₀ sqrtSteps).lo)
    (xh := (qMatchingGradABounds z a₀ r₀ s₀ sqrtSteps).hi)
    (yl := alo - a₀) (yh := ahi - a₀)
    (x := matchingGradA (z : ℝ) a₀ r₀ s₀) (y := a - (a₀ : ℝ))
    hga.1 hga.2 (by push_cast; linarith) (by push_cast; linarith)
  have hpr := qMulUpper_sound
    (xl := (qMatchingGradRBounds z a₀ r₀ s₀ sqrtSteps).lo)
    (xh := (qMatchingGradRBounds z a₀ r₀ s₀ sqrtSteps).hi)
    (yl := rlo - r₀) (yh := rhi - r₀)
    (x := matchingGradR (z : ℝ) a₀ r₀ s₀) (y := r - (r₀ : ℝ))
    hgr.1 hgr.2 (by push_cast; linarith) (by push_cast; linarith)
  have hps := qMulUpper_sound
    (xl := (qMatchingGradSBounds z a₀ r₀ s₀ sqrtSteps).lo)
    (xh := (qMatchingGradSBounds z a₀ r₀ s₀ sqrtSteps).hi)
    (yl := slo - s₀) (yh := shi - s₀)
    (x := matchingGradS (z : ℝ) a₀ r₀ s₀) (y := s - (s₀ : ℝ))
    hgs.1 hgs.2 (by push_cast; linarith) (by push_cast; linarith)
  unfold qMatchingSupportUpper
  push_cast
  linarith

end GDLowerBound.FourBlock
